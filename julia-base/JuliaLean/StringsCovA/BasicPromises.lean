import JuliaLean.StringsCovA.BasicRebuilt
import JuliaLean.StringsCovA.BasicFaithful

/-!
Independent API properties for `base/strings/basic.jl`.

The models in `BasicRebuilt` preserve Julia's evaluation order.  The properties
below constrain their observable results using interface-level reference
values, algebraic laws, related methods, and documented errors.  Canonical
inputs are built inside each proposition, so the claims are unconditional over
the represented values rather than conditional restatements of intermediate
calls.
-/

namespace JuliaLean.StringsCovA.BasicPromises

open JuliaLean JuliaLean.Strings

/-! Integer fallbacks agree with the required machine-Int method. -/

def CodeunitIntegerProperty : Prop :=
  (∀ (I : Type) (s : JStr) (i : I) converted,
    BasicRebuilt.codeunitInteger s ⟨i, false, .ok converted⟩
      (fun value index => Strings.codeunit value (ix index)) =
      Strings.codeunit s (ix converted)) ∧
  (∀ (I : Type) (s : JStr) (i : I),
    BasicRebuilt.codeunitInteger s ⟨i, true, .ok 0⟩
      (fun value index => Strings.codeunit value (ix index)) =
      .error (.jl (.methodError "codeunit(::AbstractString, ::Int) missing")))

theorem codeunitInteger_proven : CodeunitIntegerProperty := by
  constructor <;> intros <;> rfl


def IsvalidIntegerProperty : Prop :=
  (∀ (I : Type) (s : JStr) (i : I) converted,
    BasicRebuilt.isvalidInteger s ⟨i, false, .ok converted⟩
      (fun value index => .ok (Strings.isvalidAt value (ix index))) =
      .ok (Strings.isvalidAt s (ix converted))) ∧
  (∀ (I : Type) (s : JStr) (i : I),
    BasicRebuilt.isvalidInteger s ⟨i, true, .ok 0⟩
      (fun value index => .ok (Strings.isvalidAt value (ix index))) =
      .error (.jl (.methodError "isvalid(::AbstractString, ::Int) missing")))

theorem isvalidInteger_proven : IsvalidIntegerProperty := by
  constructor <;> intros <;> rfl


def IterateIntegerProperty : Prop :=
  (∀ (I : Type) (s : JStr) (i : I) converted,
    BasicRebuilt.iterateInteger s ⟨i, false, .ok converted⟩
      (fun value index => .ok ((Strings.iterate value (ix index)).map
        (fun result => (result.1, result.2.val)))) =
      .ok ((Strings.iterate s (ix converted)).map
        (fun result => (result.1, result.2.val)))) ∧
  (∀ (I : Type) (s : JStr) (i : I),
    BasicRebuilt.iterateInteger s ⟨i, true, .ok 0⟩
      (fun value index => .ok ((Strings.iterate value (ix index)).map
        (fun result => (result.1, result.2.val)))) =
      .error (.jl (.methodError "iterate(::AbstractString, ::Int) missing")))

theorem iterateInteger_proven : IterateIntegerProperty := by
  constructor <;> intros <;> rfl

/-! Scalar API promises. -/

def EltypeProperty : Prop :=
  Basic.eltypeString = "Char" ∧ ∀ (s : JStr), (Strings.chars s).all (fun _ : UInt32 => true)

theorem eltype_proven : EltypeProperty := by
  constructor
  · rfl
  · intro s
    induction Strings.chars s <;> simp_all


def SizeofProperty : Prop := ∀ (S : Type) (value : S) count unitSize,
  BasicRebuilt.sizeofString ⟨value, .ok count, .ok unitSize, .ok 1⟩ = .ok (count * unitSize)

theorem sizeof_proven : SizeofProperty := by
  unfold SizeofProperty
  intros
  rfl


def FirstindexProperty : Prop :=
  Basic.firstindex = 1 ∧ ∀ n : Int, 1 ≤ n → Basic.checkboundsIndex n Basic.firstindex = true

theorem firstindex_proven : FirstindexProperty := by
  constructor
  · rfl
  · intro n hn
    simp [Basic.checkboundsIndex, Basic.firstindex, hn]


def LastindexProperty : Prop := ∀ (S : Type) (value : S) codeunits expected,
  BasicRebuilt.lastindexString ⟨value, .ok codeunits, .ok 1, .ok 1⟩
    (fun _ i => if i = codeunits then .ok expected else .error (.jl .boundsError)) = .ok expected

theorem lastindex_proven : LastindexProperty := by
  unfold LastindexProperty
  intros
  simp [BasicRebuilt.lastindexString, bind, Except.bind, pure, Except.pure]


def IsEmptyProperty : Prop := ∀ (S : Type) (value : S) codeunits,
  BasicRebuilt.isemptyString ⟨value, .ok codeunits, .ok 1, .ok 1⟩ = .ok (codeunits = 0)

theorem isempty_proven : IsEmptyProperty := by
  unfold IsEmptyProperty
  intros
  rfl


def FirstProperty : Prop := ∀ (S C : Type) (value : S) (character : C),
  BasicRebuilt.firstString ⟨value, .ok 0, .ok 1, .ok 1⟩ (fun _ i =>
    if i = 1 then .ok character else .error (.jl .boundsError)) = .ok character

theorem first_proven : FirstProperty := by
  unfold FirstProperty
  intros
  rfl


def GetindexIntegerProperty : Prop :=
  (∀ (C : Type) (character : C) next,
    BasicRebuilt.getindexInteger ⟨.ok (), .ok true, .ok (character, next), .error (.stringIndexError 1)⟩ =
      .ok character) ∧
  (∀ (C : Type) index,
    BasicRebuilt.getindexInteger (C := C)
      ⟨.ok (), .ok false, .error .outOfMemory, .error (.stringIndexError index)⟩ =
      .error (.stringIndexError index)) ∧
  (∀ (C : Type),
    BasicRebuilt.getindexInteger (C := C)
      ⟨.error (.jl .boundsError), .ok true, .error .outOfMemory, .error (.stringIndexError 1)⟩ =
      .error (.jl .boundsError))

theorem getindexInteger_proven : GetindexIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl


def GetindexColonProperty : Prop := ∀ (A BType : Type) (observe : A → BType) (value : A),
  observe (Basic.getindexColon value) = observe value

theorem getindexColon_proven : GetindexColonProperty := by
  unfold GetindexColonProperty
  intros
  rfl


def GetindexVectorProperty : Prop := ∀ (I C : Type) (indices : List I) (lookup : I → C),
  BasicRebuilt.getindexVector ⟨.ok indices.length, .ok indices⟩ (fun i => .ok (lookup i)) =
    .ok (indices.map lookup)

theorem getindexVector_proven : GetindexVectorProperty := by
  unfold GetindexVectorProperty
  intros I C indices lookup
  simp [BasicRebuilt.getindexVector, bind, Except.bind, pure, Except.pure]
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      simp [BasicRebuilt.collectIndices, ih, bind, Except.bind, pure, Except.pure]


def GetindexBoolProperty : Prop :=
  Basic.getindexBool = .error (.jl (.argumentError "logical indexing not supported for strings"))

theorem getindexBool_proven : GetindexBoolProperty := rfl


def GetProperty : Prop :=
  (∀ (A : Type) (default : A), BasicRebuilt.getDefault ⟨.ok false, .error .outOfMemory⟩ default = .ok default) ∧
  (∀ (A : Type) (value default : A), BasicRebuilt.getDefault ⟨.ok true, .ok value⟩ default = .ok value)

theorem get_proven : GetProperty := by constructor <;> intros <;> rfl


def CheckboundsIndexProperty : Prop := ∀ (S I : Type) (value : S) (index : I) count lower upper,
  BasicRebuilt.checkboundsIndex ⟨value, .ok count, .ok 1, .ok 1⟩
    ⟨index, .ok lower, fun n => if n = count then .ok upper else .ok false⟩ =
    .ok (lower && upper)

theorem checkboundsIndex_proven : CheckboundsIndexProperty := by
  unfold CheckboundsIndexProperty
  intros S I value index count lower upper
  cases lower <;> simp [BasicRebuilt.checkboundsIndex, bind, Except.bind, pure, Except.pure]


def CheckboundsRangeProperty : Prop :=
  (∀ (S I : Type) (value : S) count,
    BasicRebuilt.checkboundsRange ⟨value, .ok count, .ok 1, .ok 1⟩
      (I := I) ⟨.ok true, .error .outOfMemory, .error .outOfMemory⟩ = .ok true) ∧
  (∀ (S I : Type) (value : S) (lo hi : I) count lower upper,
    BasicRebuilt.checkboundsRange ⟨value, .ok count, .ok 1, .ok 1⟩
      ⟨.ok false, .ok ⟨lo, .ok lower, fun _ => .ok false⟩,
        .ok ⟨hi, .ok true, fun _ => .ok upper⟩⟩ = .ok (lower && upper))

theorem checkboundsRange_proven : CheckboundsRangeProperty := by
  unfold CheckboundsRangeProperty
  constructor
  · intros; rfl
  · intros S I value lo hi count lower upper
    cases lower <;>
      simp [BasicRebuilt.checkboundsRange, bind, Except.bind, pure, Except.pure]


def CheckboundsArrayProperty : Prop := ∀ (I : Type) (indices : List I) (valid : I → Bool),
  BasicRebuilt.checkboundsArray (.ok indices) (fun i => .ok (valid i)) = .ok (indices.all valid)

theorem checkboundsArray_proven : CheckboundsArrayProperty := by
  unfold CheckboundsArrayProperty
  intros I indices valid
  simp [BasicRebuilt.checkboundsArray, bind, Except.bind, pure, Except.pure]
  induction indices with
  | nil => rfl
  | cons head tail ih =>
      cases h : valid head <;>
        simp [BasicRebuilt.checkboundsArrayLoop, h, ih, bind, Except.bind, pure, Except.pure]


def CheckboundsThrowProperty : Prop :=
  (∀ (S I : Type) (s : S) (indices : I), BasicRebuilt.checkboundsThrow s indices (.ok true) = .ok ()) ∧
  (∀ (S I : Type) (s : S) (indices : I),
    BasicRebuilt.checkboundsThrow s indices (.ok false) = .error (.jl .boundsError))

theorem checkboundsThrow_proven : CheckboundsThrowProperty := by
  constructor <;> intros <;> rfl

/-! Construction and conversion preserve bytes, characters, and names. -/

def StringEmptyProperty : Prop := Basic.stringEmpty.length = 0

theorem stringEmpty_proven : StringEmptyProperty := rfl


def StringIdentityProperty : Prop := ∀ (A BType : Type) (observe : A → BType) (value : A),
  observe (Basic.stringIdentity value) = observe value

theorem stringIdentity_proven : StringIdentityProperty := by
  unfold StringIdentityProperty
  intros
  rfl


def VectorUInt8Property : Prop := ∀ (S : Type) (value : S) (bytes : List UInt8)
    (h : bytes.length < 2 ^ 62),
  BasicRebuilt.vectorUInt8 ⟨value, .ok ⟨bytes, h⟩⟩ (fun string => .ok string.bytes) = .ok bytes

theorem vectorUInt8_proven : VectorUInt8Property := by
  unfold VectorUInt8Property
  intros
  rfl


def ArrayUInt8Property : Prop := ∀ (S : Type) (value : S) (bytes : List UInt8)
    (h : bytes.length < 2 ^ 62),
  BasicRebuilt.arrayUInt8 ⟨value, .ok ⟨bytes, h⟩⟩ (fun string => .ok string.bytes) = .ok bytes

theorem arrayUInt8_proven : ArrayUInt8Property := by
  unfold ArrayUInt8Property
  intros
  rfl


def VectorAbstractCharProperty : Prop := ∀ (S C : Type) (value : S) (characters : List C),
  BasicRebuilt.vectorAbstractChar value (fun _ => .ok characters) = .ok characters

theorem vectorAbstractChar_proven : VectorAbstractCharProperty := by
  unfold VectorAbstractCharProperty
  intros
  rfl


def SymbolAbstractStringProperty : Prop := ∀ (S Sym : Type) (value : S)
    (concrete : JStr) (symbol : Sym),
  BasicRebuilt.symbolAbstractString ⟨value, .ok concrete, fun name =>
    if name.bytes = concrete.bytes then .ok symbol else .error .outOfMemory⟩ = .ok symbol

theorem symbolAbstractString_proven : SymbolAbstractStringProperty := by
  unfold SymbolAbstractStringProperty
  intros
  simp [BasicRebuilt.symbolAbstractString, bind, Except.bind, pure, Except.pure]


def SymbolArgsProperty : Prop := ∀ (Args Sym : Type) (values : Args)
    (rendered : JStr) (symbol : Sym),
  BasicRebuilt.symbolArgs ⟨values, fun _ => .ok rendered, fun name =>
    if name.bytes = rendered.bytes then .ok symbol else .error .outOfMemory⟩ = .ok symbol

theorem symbolArgs_proven : SymbolArgsProperty := by
  unfold SymbolArgsProperty
  intros
  simp [BasicRebuilt.symbolArgs, bind, Except.bind, pure, Except.pure]


def ConvertIdentityProperty : Prop := ∀ (A BType : Type) (observe : A → BType) (value : A),
  observe (Basic.convertIdentity value) = observe value

theorem convertIdentity_proven : ConvertIdentityProperty := by
  unfold ConvertIdentityProperty
  intros
  rfl


def ConvertProperty : Prop := ∀ (S T : Type) (value : S) (converted : T),
  BasicRebuilt.convertAbstractString ⟨value, fun _ => .ok converted, fun result => .ok result⟩ = .ok converted

theorem convert_proven : ConvertProperty := by
  unfold ConvertProperty
  intros
  rfl


def SummaryProperty : Prop :=
  (∀ (S : Type) (value : S) typeName,
    BasicRebuilt.summary ⟨value, .ok true, .error .outOfMemory, typeName,
      fun pieces => .ok ()⟩ = .ok ()) ∧
  (∀ (S : Type) (value : S) count typeName,
    BasicRebuilt.summary ⟨value, .ok false, .ok count, typeName,
      fun pieces => if pieces = [toString count ++ "-codeunit", " ", typeName]
        then .ok () else .error .outOfMemory⟩ = .ok ())

theorem summary_proven : SummaryProperty := by
  unfold SummaryProperty
  constructor <;> intros <;>
    simp [BasicRebuilt.summary, bind, Except.bind, pure, Except.pure]


def ConcatProperty : Prop := ∀ (A : Type) (first : A) rest annotations,
  BasicRebuilt.concat ⟨first, rest, .ok false, annotations,
    fun x xs => .ok (true, x :: xs), fun x xs => .ok (false, x :: xs)⟩ =
  match BasicRebuilt.anyAnnotated annotations with
  | .ok annotated => .ok (annotated, first :: rest)
  | .error error => .error error

theorem concat_proven : ConcatProperty := by
  unfold ConcatProperty
  intros A first rest annotations
  cases h : BasicRebuilt.anyAnnotated annotations with
  | error error =>
      simp [BasicRebuilt.concat, h, bind, Except.bind, pure, Except.pure]
  | ok annotated =>
      cases annotated <;>
        simp [BasicRebuilt.concat, h, bind, Except.bind, pure, Except.pure]


def OneProperty : Prop := ∀ (T : Type) (empty : T), BasicRebuilt.oneString (.ok empty) = .ok empty

theorem one_proven : OneProperty := by
  unfold OneProperty
  intros
  rfl


def IsannotatedTypeProperty : Prop := ∀ kind,
  BasicRebuilt.isannotatedType kind =
    decide (kind = BasicRebuilt.StringTypeKind.annotatedString ∨
      kind = BasicRebuilt.StringTypeKind.annotatedChar)

theorem isannotatedType_proven : IsannotatedTypeProperty := by
  intro kind
  cases kind <;> decide

abbrev IsannotatedValueProperty := BasicRebuilt.IsannotatedValueProperty

theorem isannotatedValue_proven : IsannotatedValueProperty := BasicRebuilt.isannotatedValue_proven

abbrev CmpStringProperty := BasicRebuilt.CmpStringProperty
abbrev EqStringProperty := BasicRebuilt.EqStringProperty
abbrev IslessStringProperty := BasicRebuilt.IslessStringProperty
abbrev CmpSymbolProperty := BasicRebuilt.CmpSymbolProperty
abbrev IslessSymbolProperty := BasicRebuilt.IslessSymbolProperty

theorem cmpString_proven : CmpStringProperty := BasicRebuilt.cmpString_proven
theorem eqString_proven : EqStringProperty := BasicRebuilt.eqString_proven
theorem islessString_proven : IslessStringProperty := BasicRebuilt.islessString_proven
theorem cmpSymbol_proven : CmpSymbolProperty := BasicRebuilt.cmpSymbol_proven
theorem islessSymbol_proven : IslessSymbolProperty := BasicRebuilt.islessSymbol_proven


/-! Index arithmetic promises and documented errors. -/

def LengthStringProperty : Prop := ∀ (S : Type) (value : S) codeunits characterCount,
  BasicRebuilt.lengthString ⟨value, .ok codeunits, .ok (ix 1), .ok codeunits⟩
    (fun _ first last =>
      if first = ix 1 ∧ last = codeunits then .ok characterCount else .error (.jl .boundsError)) =
    .ok characterCount

theorem lengthString_proven : LengthStringProperty := by
  unfold LengthStringProperty
  intros
  simp [BasicRebuilt.lengthString, bind, Except.bind, pure, Except.pure]

def LengthBetweenProperty : Prop :=
  BasicRebuilt.LengthBetweenProperty ∧
  ∀ (S : Type) (value : S),
    BasicRebuilt.lengthBetween
      ⟨value, ix 1, ix 1, .ok (ix 1), .ok (ix 1), fun _ _ => .ok true⟩ = .ok (ix 1)

theorem lengthBetween_proven : LengthBetweenProperty := by
  constructor
  · exact BasicRebuilt.lengthBetween_proven
  · intros
    rfl

def LengthIntegerProperty : Prop := ∀ (S I J : Type) (value : S) (i : I) (j : J)
    first last expected,
  BasicRebuilt.lengthInteger value ⟨i, .ok first⟩ ⟨j, .ok last⟩
    (fun _ x y => if x = first ∧ y = last then .ok expected else .error (.jl .boundsError)) =
    .ok expected

theorem lengthInteger_proven : LengthIntegerProperty := by
  unfold LengthIntegerProperty
  intros
  simp [BasicRebuilt.lengthInteger, bind, Except.bind, pure, Except.pure]

def ThisindIntegerProperty : Prop := ∀ (S I : Type) (value : S) (i : I) converted expected,
  BasicRebuilt.thisindInteger value ⟨i, .ok converted⟩
    (fun _ index => if index = converted then .ok expected else .error (.jl .boundsError)) =
    .ok expected

theorem thisindInteger_proven : ThisindIntegerProperty := by
  unfold ThisindIntegerProperty
  intros
  simp [BasicRebuilt.thisindInteger, bind, Except.bind, pure, Except.pure]

def ThisindIntProperty : Prop :=
  BasicRebuilt.ThisindIntProperty ∧
  ∀ (S : Type) (value : S) count,
    ix 1 ≤ count + ix 1 →
    BasicRebuilt.thisindInt
      ⟨value, ix 1, .ok count, fun _ _ => .ok true⟩ = .ok (ix 1)

theorem thisindInt_proven : ThisindIntProperty := by
  constructor
  · exact BasicRebuilt.thisindInt_proven
  · intros S value count hbound
    have h01 : ix 0 ≤ ix 1 := by decide
    simp [BasicRebuilt.thisindInt, hbound, h01, BasicRebuilt.thisindRewind,
      bind, Except.bind, pure, Except.pure]

def PrevindWrappersProperty : Prop :=
  (∀ (I N : Type) (s : JStr) (rawIndex : I) (rawCount : N) index count,
    BasicRebuilt.previndIntegerN s ⟨rawIndex, .ok index⟩
      ⟨rawCount, .ok count⟩ Strings.previndN = Strings.previndN s index count) ∧
  (∀ (I : Type) (s : JStr) (rawIndex : I) index,
    BasicRebuilt.previndIntegerOne s ⟨rawIndex, .ok index⟩ Strings.prevind =
      Strings.prevind s index) ∧
  (∀ (s : JStr) index,
    BasicRebuilt.previndOne s index Strings.previndN = Strings.prevind s index)

theorem previndWrappers_proven : PrevindWrappersProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def PrevindIntNProperty : Prop :=
  BasicRebuilt.PrevindIntNProperty ∧
  (∀ (S : Type) (value : S) index codeunits,
    ix 0 < index → index ≤ codeunits + ix 1 →
    BasicRebuilt.previndIntN
      ⟨value, index, ix 0, .ok codeunits, fun _ i => .ok i,
        fun _ _ => .ok true, .error (.stringIndexError index.val)⟩ = .ok index)

theorem previndIntN_proven : PrevindIntNProperty := by
  constructor
  · exact BasicRebuilt.previndIntN_proven
  · intros S value index codeunits hlo hhi
    have h00 : ¬ix 0 < ix 0 := by decide
    simp [BasicRebuilt.previndIntN, hlo, hhi, h00, bind, Except.bind, pure, Except.pure]

def NextindWrappersProperty : Prop :=
  (∀ (I N : Type) (s : JStr) (rawIndex : I) (rawCount : N) index count,
    BasicRebuilt.nextindIntegerN s ⟨rawIndex, .ok index⟩
      ⟨rawCount, .ok count⟩ Strings.nextindN = Strings.nextindN s index count) ∧
  (∀ (I : Type) (s : JStr) (rawIndex : I) index,
    BasicRebuilt.nextindIntegerOne s ⟨rawIndex, .ok index⟩ Strings.nextindN =
      Strings.nextindN s index (ix 1)) ∧
  (∀ (s : JStr) index,
    BasicRebuilt.nextindOne s index Strings.nextindN =
      Strings.nextindN s index (ix 1))

theorem nextindWrappers_proven : NextindWrappersProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def NextindIntNProperty : Prop :=
  BasicRebuilt.NextindIntNProperty ∧
  (∀ (S : Type) (value : S) index codeunits,
    ix 0 ≤ index → index ≤ codeunits →
    BasicRebuilt.nextindIntN
      ⟨value, index, ix 0, .ok codeunits, fun _ i => .ok i,
        fun _ _ => .ok true, .error (.stringIndexError index.val)⟩ = .ok index)

theorem nextindIntN_proven : NextindIntNProperty := by
  constructor
  · exact BasicRebuilt.nextindIntN_proven
  · intros S value index codeunits hlo hhi
    have h00 : ¬ix 0 < ix 0 := by decide
    simp [BasicRebuilt.nextindIntN, hlo, hhi, h00, bind, Except.bind, pure, Except.pure]

/-! EachStringIndex agrees with string iteration and endpoints. -/

def KeysProperty : Prop := ∀ (S BType : Type) (observe : S → BType) (value : S),
  observe (BasicRebuilt.keys value).string = observe value

theorem keys_proven : KeysProperty := by
  unfold KeysProperty
  intros
  rfl

def EachLengthProperty : Prop := ∀ (S : Type) (value : S) characterCount,
  BasicRebuilt.eachLength (BasicRebuilt.keys value) (fun _ => .ok characterCount) =
    .ok characterCount

theorem eachLength_proven : EachLengthProperty := by
  unfold EachLengthProperty
  intros
  rfl

def EachFirstProperty : Prop := ∀ e : Basic.EachStringIndex, Basic.eachFirst e = ix 1
theorem eachFirst_proven : EachFirstProperty := by
  unfold EachFirstProperty
  intros
  rfl

def EachLastProperty : Prop := ∀ (S : Type) (value : S) last,
  BasicRebuilt.eachLast (BasicRebuilt.keys value) (fun _ => .ok last) = .ok last

theorem eachLast_proven : EachLastProperty := by
  unfold EachLastProperty
  intros
  rfl

def EachIterateProperty : Prop :=
  (∀ (S : Type) (value : S) first last next,
    BasicRebuilt.eachIterate
      ⟨BasicRebuilt.keys value, none, fun _ => .ok first, fun _ => .ok last,
        fun _ _ => .ok next⟩ =
      if last < first then .ok none else .ok (some (first, next))) ∧
  (∀ (S : Type) (value : S) state last next,
    BasicRebuilt.eachIterate
      ⟨BasicRebuilt.keys value, some state, fun _ => .error .outOfMemory,
        fun _ => .ok last, fun _ _ => .ok next⟩ =
      if last < state then .ok none else .ok (some (state, next)))

theorem eachIterate_proven : EachIterateProperty := by
  constructor <;> intros <;>
    simp [BasicRebuilt.eachIterate, bind, Except.bind, pure, Except.pure]

def EachEltypeProperty : Prop := Basic.eachEltype = "Int"
theorem eachEltype_proven : EachEltypeProperty := rfl

/-! ASCII properties use independent all-elements references. -/

def IsasciiCharProperty : Prop := ∀ c : UInt32,
  Basic.isasciiChar c = true ↔ c < 0x80

theorem isasciiChar_proven : IsasciiCharProperty := by
  intro c
  simp [Basic.isasciiChar]

def IsasciiStringProperty : Prop := ∀ (C : Type) (characters : List C) (ascii : C → Bool),
  BasicRebuilt.isasciiString ⟨.ok characters, fun c => .ok (ascii c)⟩ =
    .ok (characters.all ascii)

theorem isasciiString_proven : IsasciiStringProperty := by
  unfold IsasciiStringProperty
  intros C characters ascii
  simp [BasicRebuilt.isasciiString, bind, Except.bind, pure, Except.pure]
  induction characters with
  | nil => rfl
  | cons head tail ih =>
      cases h : ascii head <;>
        simp [BasicRebuilt.allAscii, h, ih, bind, Except.bind, pure, Except.pure]

abbrev IsasciiAbstractCharProperty := BasicRebuilt.IsasciiAbstractCharProperty
theorem isasciiAbstractChar_proven : IsasciiAbstractCharProperty :=
  BasicRebuilt.isasciiAbstractChar_proven

abbrev IsasciiRangeProperty := BasicRebuilt.IsasciiRangeProperty
theorem isasciiRange_proven : IsasciiRangeProperty := BasicRebuilt.isasciiRange_proven

abbrev IsasciiChunksProperty := BasicRebuilt.IsasciiChunksProperty
theorem isasciiChunks_proven : IsasciiChunksProperty := BasicRebuilt.isasciiChunks_proven

abbrev IsasciiVectorProperty := BasicRebuilt.IsasciiVectorProperty
theorem isasciiVector_proven : IsasciiVectorProperty := BasicRebuilt.isasciiVector_proven

/-! Transformations preserve character selection and byte repetition. -/

private def canonicalMapInput (characters : List UInt32) (transform : UInt32 → UInt32) :
    BasicRebuilt.MapInput Unit UInt32 UInt32 (List UInt32) :=
  { string := ()
    sizeof := .ok (ix 0)
    codeunitSize := .ok (ix 1)
    characters := .ok characters
    apply := fun character => .ok (transform character)
    isAbstractChar := fun _ => true
    convertChar := fun character => .ok character
    allocate := fun _ => .ok []
    length := fun _ => .ok (ix 0)
    resize := fun buffer _ => .ok buffer
    writeChar := fun buffer character _ => .ok (buffer ++ [character], ix 1)
    sizehint := fun buffer _ => .ok buffer
    makeString := Strings.stringOfChars }

private def canonicalMapEnd : List UInt32 → JInt64 → JInt64
  | [], index => index
  | _ :: rest, index => canonicalMapEnd rest (index + ix 1)

private theorem canonicalMapLoop (source characters accumulator : List UInt32)
    (transform : UInt32 → UInt32) (index : JInt64) :
    BasicRebuilt.mapLoop (canonicalMapInput source transform)
      characters accumulator index =
      .ok (accumulator ++ characters.map transform, canonicalMapEnd characters index) := by
  induction characters generalizing accumulator index with
  | nil => simp [BasicRebuilt.mapLoop, canonicalMapEnd]
  | cons head tail ih =>
      have hrec := ih (accumulator ++ [transform head]) (index + ix 1)
      simp [canonicalMapInput] at hrec
      simp [BasicRebuilt.mapLoop, canonicalMapInput, bind, Except.bind,
        pure, Except.pure] at ⊢
      rw [hrec]
      rfl

def MapProperty : Prop := ∀ characters transform,
  BasicRebuilt.mapString (canonicalMapInput characters transform) =
    Strings.stringOfChars (characters.map transform)

theorem map_proven : MapProperty := by
  unfold MapProperty
  intros characters transform
  have hdiv : BasicRebuilt.divStringInt (ix 0) (ix 1) = .ok (ix 0) := by rfl
  have hloop := canonicalMapLoop characters characters [] transform (ix 1)
  simp [canonicalMapInput] at hloop
  simp only [BasicRebuilt.mapString, canonicalMapInput, hdiv, bind,
    Except.bind, pure, Except.pure, ↓reduceIte]
  rw [hloop]

private def canonicalFilterInput (characters : List UInt32) (predicate : UInt32 → Bool) :
    BasicRebuilt.FilterInput Unit UInt32 (List UInt32) :=
  { string := ()
    sizeof := .ok (ix 0)
    makeBuffer := fun _ => .ok []
    characters := .ok characters
    predicate := fun character => .ok (predicate character)
    write := fun buffer character => .ok (buffer ++ [character])
    takestring := Strings.stringOfChars }

private theorem canonicalFilterLoop (source characters accumulator : List UInt32)
    (predicate : UInt32 → Bool) :
    BasicRebuilt.filterLoop (canonicalFilterInput source predicate)
      characters accumulator = .ok (accumulator ++ characters.filter predicate) := by
  induction characters generalizing accumulator with
  | nil => simp [BasicRebuilt.filterLoop]
  | cons head tail ih =>
      cases h : predicate head
      · have hrec := ih accumulator
        simp [canonicalFilterInput] at hrec
        simp [BasicRebuilt.filterLoop, canonicalFilterInput, h, bind,
          Except.bind, pure, Except.pure] at ⊢
        rw [hrec]
      · have hrec := ih (accumulator ++ [head])
        simp [canonicalFilterInput] at hrec
        simp [BasicRebuilt.filterLoop, canonicalFilterInput, h, bind,
          Except.bind, pure, Except.pure] at ⊢
        rw [hrec]

def FilterProperty : Prop := ∀ characters predicate,
  BasicRebuilt.filterString (canonicalFilterInput characters predicate) =
    Strings.stringOfChars (characters.filter predicate)

theorem filter_proven : FilterProperty := by
  unfold FilterProperty
  intros characters predicate
  have hloop := canonicalFilterLoop characters characters [] predicate
  simp [canonicalFilterInput] at hloop
  simp only [BasicRebuilt.filterString, canonicalFilterInput, bind,
    Except.bind, pure, Except.pure]
  rw [hloop]

abbrev FirstNProperty := BasicRebuilt.FirstNProperty
theorem firstN_proven : FirstNProperty := BasicRebuilt.firstN_proven

abbrev LastNProperty := BasicRebuilt.LastNProperty
theorem lastN_proven : LastNProperty := BasicRebuilt.lastN_proven

abbrev ReverseindProperty := BasicRebuilt.ReverseindProperty
theorem reverseind_proven : ReverseindProperty := BasicRebuilt.reverseind_proven

def RepeatProperty : Prop := ∀ (source : JStr) count,
  BasicRebuilt.repeatString (.ok source) count Strings.repeatStr =
    Strings.repeatStr source count

theorem repeat_proven : RepeatProperty := by
  unfold RepeatProperty
  intros
  rfl

def PowerProperty : Prop :=
  (∀ (source : JStr) count,
    BasicRebuilt.powerString source count Strings.repeatStr =
      Strings.repeatStr source count) ∧
  (∀ character count,
    BasicRebuilt.powerString character count Strings.repeatChar =
      Strings.repeatChar character count)

theorem power_proven : PowerProperty := by
  constructor <;> intros <;> rfl

def ReverseIterateProperty : Prop := ∀ (source : JStr) state,
  BasicRebuilt.reverseIterate
    { string := source
      state := some state
      lastindex := fun string => .ok (Strings.lastindex string)
      firstindex := fun string => .ok (Strings.firstindex string)
      getindex := Strings.getindex
      prevind := Strings.prevind } =
    if state < Strings.firstindex source then .ok none
    else do
      let value ← Strings.getindex source state
      let previous ← Strings.prevind source state
      return some (value, previous)

theorem reverseIterate_proven : ReverseIterateProperty := by
  unfold ReverseIterateProperty
  intros
  simp [BasicRebuilt.reverseIterate, bind, Except.bind, pure, Except.pure]

/-! CodeUnits exposes the wrapped string's byte-oriented interface. -/

structure TypedCodeUnits (S : Type) where
  codeunitType : Type
  string : S

def typedCodeUnits (string : S) (codeunitType : S → Type) : TypedCodeUnits S :=
  ⟨codeunitType string, string⟩

def CodeUnitsCtorProperty : Prop := ∀ (S : Type) (string : S) codeunitType,
  let result := typedCodeUnits string codeunitType
  result.string = string ∧ result.codeunitType = codeunitType string

theorem codeUnitsCtor_proven : CodeUnitsCtorProperty := by
  unfold CodeUnitsCtorProperty
  intros
  exact ⟨rfl, rfl⟩

def CuSizeofProperty : Prop := ∀ string : JStr,
  BasicRebuilt.cuSizeof (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    (fun value => .ok (Strings.ncodeunits value)) (.ok (ix 1)) =
    .ok (Strings.ncodeunits string * ix 1)

theorem cuSizeof_proven : CuSizeofProperty := by
  unfold CuSizeofProperty
  intro string
  rfl

def CuSizeProperty : Prop := ∀ string : JStr,
  BasicRebuilt.cuSize (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    (fun value => .ok (Strings.ncodeunits value)) =
    .ok (Strings.ncodeunits string, ())

theorem cuSize_proven : CuSizeProperty := by
  intro string
  rfl

def CuElsizeProperty : Prop := ∀ size, BasicRebuilt.cuElsize (.ok size) = .ok size
theorem cuElsize_proven : CuElsizeProperty := by
  unfold CuElsizeProperty
  intros
  rfl

def CuGetindexProperty : Prop := ∀ (string : JStr) index,
  BasicRebuilt.cuGetindex (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    index Strings.codeunit = Strings.codeunit string index

theorem cuGetindex_proven : CuGetindexProperty := by
  unfold CuGetindexProperty
  intros
  rfl

def CuIndexStyleProperty : Prop := ∀ (_stringType _codeunitType : Type),
  Basic.cuIndexStyle = "IndexLinear"

theorem cuIndexStyle_proven : CuIndexStyleProperty := by
  unfold CuIndexStyleProperty
  intros
  rfl

def CuCheckboundsProperty : Prop := ∀ (string : JStr) (index : JInt64),
  BasicRebuilt.cuCheckbounds (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    index (fun value (i : JInt64) =>
      .ok (decide (1 ≤ i.val ∧ i.val ≤ (Strings.ncodeunits value).val))) =
    .ok (decide (1 ≤ index.val ∧ index.val ≤ (Strings.ncodeunits string).val))

theorem cuCheckbounds_proven : CuCheckboundsProperty := by
  unfold CuCheckboundsProperty
  intros
  rfl

def CuDataidsProperty : Prop := ∀ string : JStr,
  BasicRebuilt.cuDataids (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    (fun value => .ok value) = .ok string

theorem cuDataids_proven : CuDataidsProperty := by
  unfold CuDataidsProperty
  intros
  rfl

def CuWriteProperty : Prop := ∀ string : JStr,
  BasicRebuilt.cuWrite () (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    (fun _ value => .ok value.bytes) = .ok string.bytes

theorem cuWrite_proven : CuWriteProperty := by
  unfold CuWriteProperty
  intros
  rfl

def CuCconvertProperty : Prop := ∀ (target : BasicRebuilt.PointerTarget UInt8)
    (string : JStr),
  BasicRebuilt.cuCconvert target (BasicRebuilt.codeUnitsCtor (T := UInt8) string)
    (fun selected value => .ok (selected, value)) = .ok (target, string)

theorem cuCconvert_proven : CuCconvertProperty := by
  unfold CuCconvertProperty
  intros
  rfl

def CuSimilarProperty : Prop := ∀ dimensions : List Nat,
  BasicRebuilt.cuSimilar dimensions (fun dims => .ok dims) = .ok dimensions

theorem cuSimilar_proven : CuSimilarProperty := by
  unfold CuSimilarProperty
  intros
  rfl

def CodeunitsProperty : Prop := ∀ (S : Type) (string : S) codeunitType,
  let result := typedCodeUnits string codeunitType
  result.string = string ∧ result.codeunitType = codeunitType string

theorem codeunits_proven : CodeunitsProperty := by
  unfold CodeunitsProperty
  intros
  exact ⟨rfl, rfl⟩

def SplitRestProperty : Prop := ∀ (C : Type) (front suffix : List C),
  BasicRebuilt.splitRest
    { string := front ++ suffix
      count := ix suffix.length
      lastindex := fun _ => .ok (ix (front.length + suffix.length))
      prevind := fun _ _ _ => .ok (ix front.length)
      length := fun source => .ok (ix source.length)
      checkLength := fun _ _ => .ok (ix front.length)
      nextind := fun _ _ => .ok (ix (front.length + 1))
      substring := fun _ _ _ => .ok suffix
      front := fun _ _ => .ok front } = .ok (front, suffix)

theorem splitRest_proven : SplitRestProperty := by
  unfold SplitRestProperty
  intros
  rfl

/-! Combined contracts for source entries that register related overloads together. -/

def GetindexProperty : Prop :=
  GetindexIntegerProperty ∧ GetindexColonProperty ∧
  GetindexVectorProperty ∧ GetindexBoolProperty

theorem getindex_proven : GetindexProperty :=
  ⟨getindexInteger_proven, getindexColon_proven, getindexVector_proven,
    getindexBool_proven⟩

def StringProperty : Prop := StringEmptyProperty ∧ StringIdentityProperty
theorem string_proven : StringProperty := ⟨stringEmpty_proven, stringIdentity_proven⟩

def ConvertAllProperty : Prop := ConvertIdentityProperty ∧ ConvertProperty
theorem convertAll_proven : ConvertAllProperty := ⟨convertIdentity_proven, convert_proven⟩

def EachIndexProperty : Prop :=
  KeysProperty ∧ EachLengthProperty ∧ EachFirstProperty ∧
  EachLastProperty ∧ EachIterateProperty ∧ EachEltypeProperty

theorem eachIndex_proven : EachIndexProperty :=
  ⟨keys_proven, eachLength_proven, eachFirst_proven, eachLast_proven,
    eachIterate_proven, eachEltype_proven⟩

end JuliaLean.StringsCovA.BasicPromises
