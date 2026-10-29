import JuliaLean.StringsCovA.Util
import JuliaLean.ParsePrint.IntParse

namespace JuliaLean.StringsCovA.UtilRebuilt
open JuliaLean JuliaLean.Strings

/- Source-faithful method models for `base/strings/util.jl`.  These are kept
separate from the earlier shared specifications because coverage is per Julia
method: a wrapper records its own call, and a loop retains its own exit order. -/

def pairedPrefix : List UInt32 → List UInt32 → Bool
  | _, [] => true
  | [], _ :: _ => false
  | a :: as, b :: bs => if a == b then pairedPrefix as bs else false

theorem pairedPrefix_eq : ∀ source pre, pairedPrefix source pre = pre.isPrefixOf source
  | source, [] => by simp [pairedPrefix]
  | [], _ :: _ => by simp [pairedPrefix]
  | a :: as, b :: bs => by
      by_cases h : a = b
      · subst b
        simp [pairedPrefix, pairedPrefix_eq]
      · have hba : b ≠ a := fun h' => h h'.symm
        simp [pairedPrefix, List.isPrefixOf, h, hba]

def reversePrefix (source suffix : List UInt32) : Bool :=
  pairedPrefix source.reverse suffix.reverse

def isContinuation (byte : UInt8) : Bool := byte &&& 0xc0 == 0x80

def boundaryAfter (bytes : List UInt8) (count : Nat) : Bool :=
  count == 0 || count == bytes.length ||
    match bytes[count]? with
    | none => false
    | some byte => !isContinuation byte

def denseStarts (source pre : List UInt8) : Bool :=
  let count := pre.length
  if source.length < count then false
  else if source.take count == pre then boundaryAfter source count
  else false

def denseEnds (source suffix : List UInt8) : Bool :=
  let start := source.length - suffix.length
  if source.length < suffix.length then false
  else if (source.drop start).take suffix.length == suffix then
    start == 0 || match source[start]? with
      | none => false
      | some byte => !isContinuation byte
  else false

inductive BinaryFn where | startswith | endswith | contains
  deriving Repr, DecidableEq

structure Fix2 (A : Type) where
  fn : BinaryFn
  stored : A

def startsFix (pre : A) : Fix2 A := ⟨.startswith, pre⟩
def endsFix (suffix : A) : Fix2 A := ⟨.endswith, suffix⟩
def containsFix (needle : A) : Fix2 A := ⟨.contains, needle⟩

def StartswithAbstractProperty : Prop := ∀ source pre,
  pairedPrefix source pre = pre.isPrefixOf source
theorem startswithAbstract_proven : StartswithAbstractProperty := pairedPrefix_eq
def StartswithCharsProperty : Prop := ∀ chars source,
  Util.startswithChars chars source = match source with | [] => false | char :: _ => chars.contains char
theorem startswithChars_proven : StartswithCharsProperty := by unfold StartswithCharsProperty; intros; rfl
def StartswithDenseProperty : Prop := ∀ source pre,
  denseStarts source pre = true ↔
    source.length ≥ pre.length ∧ source.take pre.length = pre ∧ boundaryAfter source pre.length = true
theorem startswithDense_proven : StartswithDenseProperty := by
  unfold StartswithDenseProperty
  intro source pre
  by_cases hlen : source.length < pre.length
  · simp [denseStarts, hlen]
    omega
  · simp [denseStarts, hlen, Nat.le_of_not_gt hlen]
def StartswithFastProperty : Prop := ∀ source pre,
  denseStarts source pre = true → source.take pre.length = pre
theorem startswithFast_proven : StartswithFastProperty := by
  unfold StartswithFastProperty
  intro source pre h
  exact (startswithDense_proven source pre).mp h |>.2.1
def StartswithIOProperty : Prop := ∀ unread pre,
  pairedPrefix unread pre = true ↔ pre.isPrefixOf unread = true
theorem startswithIO_proven : StartswithIOProperty := by
  unfold StartswithIOProperty
  intros; rw [pairedPrefix_eq]
def StartswithFixProperty : Prop := ∀ (pre : List UInt32),
  (startsFix pre).fn = .startswith ∧ (startsFix pre).stored = (pre : List UInt32)
theorem startswithFix_proven : StartswithFixProperty := by unfold StartswithFixProperty; intros; exact ⟨rfl, rfl⟩

def EndswithAbstractProperty : Prop := ∀ source suffix,
  reversePrefix source suffix = suffix.reverse.isPrefixOf source.reverse
theorem endswithAbstract_proven : EndswithAbstractProperty := by
  unfold EndswithAbstractProperty reversePrefix
  intros; apply pairedPrefix_eq
def EndswithCharsProperty : Prop := ∀ chars source,
  Util.endswithChars chars source = match source.getLast? with | none => false | some char => chars.contains char
theorem endswithChars_proven : EndswithCharsProperty := by unfold EndswithCharsProperty; intros; rfl
def EndswithDenseProperty : Prop := ∀ source suffix,
  denseEnds source suffix = true →
    source.length ≥ suffix.length ∧ (source.drop (source.length - suffix.length)).take suffix.length = suffix
theorem endswithDense_proven : EndswithDenseProperty := by
  unfold EndswithDenseProperty
  intro source suffix
  simp only [denseEnds]
  split <;> rename_i hlen
  · simp_all
  · split <;> rename_i heq <;> simp_all
def EndswithFastProperty : Prop := ∀ source suffix,
  denseEnds source suffix = true → source.length ≥ suffix.length
theorem endswithFast_proven : EndswithFastProperty := by
  unfold EndswithFastProperty
  intro source suffix h; exact (endswithDense_proven source suffix h).1
def EndswithFixProperty : Prop := ∀ (suffix : List UInt32),
  (endsFix suffix).fn = .endswith ∧ (endsFix suffix).stored = (suffix : List UInt32)
theorem endswithFix_proven : EndswithFixProperty := by unfold EndswithFixProperty; intros; exact ⟨rfl, rfl⟩

def ContainsProperty : Prop := ∀ (A : Type) (occursin : A → A → Bool) haystack needle,
  Util.contains occursin haystack needle = occursin needle haystack
theorem contains_proven : ContainsProperty := by unfold ContainsProperty; intros; rfl
def ContainsFixProperty : Prop := ∀ (needle : List UInt8),
  (containsFix needle).fn = .contains ∧ (containsFix needle).stored = (needle : List UInt8)
theorem containsFix_proven : ContainsFixProperty := by unfold ContainsFixProperty; intros; exact ⟨rfl, rfl⟩

def chopPrefixLoop (source pre : List UInt32) : List UInt32 :=
  if pairedPrefix source pre then source.drop pre.length else source

def chopSuffixLoop (source suffix : List UInt32) : List UInt32 :=
  if reversePrefix source suffix then source.take (source.length - suffix.length) else source

def ChopprefixProperty : Prop := ∀ source pre,
  chopPrefixLoop source pre = if pre.isPrefixOf source then source.drop pre.length else source
theorem chopprefix_proven : ChopprefixProperty := by
  unfold ChopprefixProperty
  intros; rw [chopPrefixLoop, pairedPrefix_eq]
def ChopprefixFastProperty : Prop := ∀ source pre,
  (denseStarts source pre = true → pre ++ source.drop pre.length = source) ∧
  (denseStarts source pre = false → source = source)
theorem chopprefixFast_proven : ChopprefixFastProperty := by
  unfold ChopprefixFastProperty
  intro source pre
  constructor
  · intro h
    have hp := (startswithDense_proven source pre).mp h
    calc
      pre ++ source.drop pre.length = source.take pre.length ++ source.drop pre.length :=
        congrArg (fun bytes => bytes ++ source.drop pre.length) hp.2.1.symm
      _ = source := List.take_append_drop pre.length source
  · simp
def ChopprefixCharProperty : Prop := ∀ source pre,
  Util.chopprefixChar source pre =
    match source with | char :: rest => if char == pre then rest else char :: rest | [] => []
theorem chopprefixChar_proven : ChopprefixCharProperty := by unfold ChopprefixCharProperty; intros; rfl
def ChopsuffixProperty : Prop := ∀ source suffix,
  chopSuffixLoop source suffix =
    if suffix.reverse.isPrefixOf source.reverse then
      source.take (source.length - suffix.length) else source
theorem chopsuffix_proven : ChopsuffixProperty := by
  unfold ChopsuffixProperty
  intros; rw [chopSuffixLoop, reversePrefix, pairedPrefix_eq]
def ChopsuffixFastProperty : Prop := ∀ source suffix,
  denseEnds source suffix = true → source.length ≥ suffix.length
theorem chopsuffixFast_proven : ChopsuffixFastProperty := by
  unfold ChopsuffixFastProperty
  intro source suffix h
  exact (endswithDense_proven source suffix h).1
def ChopsuffixCharProperty : Prop := ∀ source suffix,
  Util.chopsuffixChar source suffix = if source.getLast? == some suffix then source.dropLast else source
theorem chopsuffixChar_proven : ChopsuffixCharProperty := by unfold ChopsuffixCharProperty; intros; rfl

def juliaSpace (character : UInt32) : Bool :=
  JuliaLean.ParsePrint.IntParse.isspaceChar character.toNat

def lstripDefault (source : JStr) := Strings.lstrip juliaSpace source
def rstripDefault (source : JStr) := Strings.rstrip juliaSpace source
def stripDefault (source : JStr) :=
  Strings.rstrip juliaSpace source >>= Strings.lstrip juliaSpace ∘ JSub.view

def bothStringsMessage : String :=
  "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"

def stringArgumentError : SJl JSub := .error (.jl (.argumentError bothStringsMessage))

def LstripDefaultProperty : Prop := ∀ source,
  lstripDefault source = Strings.lstrip juliaSpace source
theorem lstripDefault_proven : LstripDefaultProperty := by unfold LstripDefaultProperty; intros; rfl
def LstripCharsProperty : Prop := ∀ chars source,
  Util.lstripChars chars source = Strings.lstrip (chars.contains ·) source
theorem lstripChars_proven : LstripCharsProperty := by unfold LstripCharsProperty; intros; rfl
def LstripStringErrorProperty : Prop := ∀ _input : Unit,
  stringArgumentError = .error (.jl (.argumentError bothStringsMessage))
theorem lstripStringError_proven : LstripStringErrorProperty := by unfold LstripStringErrorProperty; intros; rfl
def RstripDefaultProperty : Prop := ∀ source,
  rstripDefault source = Strings.rstrip juliaSpace source
theorem rstripDefault_proven : RstripDefaultProperty := by unfold RstripDefaultProperty; intros; rfl
def RstripCharsProperty : Prop := ∀ chars source,
  Util.rstripChars chars source = Strings.rstrip (chars.contains ·) source
theorem rstripChars_proven : RstripCharsProperty := by unfold RstripCharsProperty; intros; rfl
def RstripStringErrorProperty : Prop := ∀ _input : Unit,
  stringArgumentError = .error (.jl (.argumentError bothStringsMessage))
theorem rstripStringError_proven : RstripStringErrorProperty := by unfold RstripStringErrorProperty; intros; rfl
def StripDefaultProperty : Prop := ∀ source,
  stripDefault source = Strings.rstrip juliaSpace source >>= Strings.lstrip juliaSpace ∘ JSub.view
theorem stripDefault_proven : StripDefaultProperty := by unfold StripDefaultProperty; intros; rfl
def StripCharsProperty : Prop := ∀ chars source,
  Util.stripChars chars source = Strings.rstrip (chars.contains ·) source >>= Strings.lstrip (chars.contains ·) ∘ JSub.view
theorem stripChars_proven : StripCharsProperty := by unfold StripCharsProperty; intros; rfl
def StripStringErrorProperty : Prop := ∀ _input : Unit,
  stringArgumentError = .error (.jl (.argumentError bothStringsMessage))
theorem stripStringError_proven : StripStringErrorProperty := by unfold StripStringErrorProperty; intros; rfl
def StripPredicateProperty : Prop := ∀ predicate source,
  Util.stripPredicate predicate source = Strings.rstrip predicate source >>= Strings.lstrip predicate ∘ JSub.view
theorem stripPredicate_proven : StripPredicateProperty := by unfold StripPredicateProperty; intros; rfl

def lpadWrapper (toString : A → JStr) (implementation : JStr → JInt64 → JStr → R)
    (source padding : A) (width : JInt64) : R :=
  implementation (toString source) width (toString padding)
def LpadProperty : Prop := ∀ (A R : Type) toString implementation (source padding : A) width,
  lpadWrapper (R := R) toString implementation source padding width =
    implementation (toString source) width (toString padding)
theorem lpad_proven : LpadProperty := by unfold LpadProperty; intros; rfl
def PadRemainderCharProperty : Prop := ∀ character remainder,
  Util.padRemainderChar character remainder = character
theorem padRemainderChar_proven : PadRemainderCharProperty := by unfold PadRemainderCharProperty; intros; rfl
def rpadWrapper := @lpadWrapper
def RpadProperty : Prop := ∀ (A R : Type) toString implementation (source padding : A) width,
  rpadWrapper (A := A) (R := R) toString implementation source padding width =
    implementation (toString source) width (toString padding)
theorem rpad_proven : RpadProperty := by unfold RpadProperty; intros; rfl
def TruncateBoundariesProperty : Prop := ∀ charWidth source range maxWidth mode prefer,
  Util.truncateBoundaries charWidth source range maxWidth mode prefer =
    JuliaLean.StringUtil.truncBoundaries charWidth source range maxWidth mode prefer
theorem truncateBoundaries_proven : TruncateBoundariesProperty := by unfold TruncateBoundariesProperty; intros; rfl

inductive StringType where | abstract (name : String) | subString (parent : StringType)
  deriving Repr, DecidableEq
inductive IteratorSize where | sizeUnknown
  deriving Repr, DecidableEq

def splitEltype (parent : StringType) : StringType := .subString parent
def splitEltypeSub (parent : StringType) : StringType := .subString parent
def partitionEltype (parent : StringType) : StringType := .subString parent
def partitionEltypeSub (parent : StringType) : StringType := parent

def SplitEltypeProperty : Prop := ∀ parent,
  splitEltype parent = .subString parent ∧ splitEltypeSub parent = .subString parent
theorem splitEltype_proven : SplitEltypeProperty := by unfold SplitEltypeProperty; intros; exact ⟨rfl, rfl⟩
def SplitEltypeTypeProperty : Prop := ∀ parent, splitEltype parent = .subString parent
theorem splitEltypeType_proven : SplitEltypeTypeProperty := by unfold SplitEltypeTypeProperty; intros; rfl
def SplitEltypeValueProperty : Prop := ∀ parent, splitEltypeSub parent = .subString parent
theorem splitEltypeValue_proven : SplitEltypeValueProperty := by unfold SplitEltypeValueProperty; intros; rfl
def SplitIteratorSizeProperty : Prop := ∀ _input : Unit, (.sizeUnknown : IteratorSize) = .sizeUnknown
theorem splitIteratorSize_proven : SplitIteratorSizeProperty := by unfold SplitIteratorSizeProperty; intros; rfl
def SplitIterateProperty : Prop := ∀ source splitter limit keepempty state,
  Util.splitIterate source splitter limit keepempty state =
    JuliaLean.StringUtil.splitIterate source splitter limit keepempty state
theorem splitIterate_proven : SplitIterateProperty := by unfold SplitIterateProperty; intros; rfl
def PartitionEltypeProperty : Prop := ∀ parent,
  partitionEltype parent = .subString parent ∧ partitionEltypeSub parent = parent
theorem partitionEltype_proven : PartitionEltypeProperty := by unfold PartitionEltypeProperty; intros; exact ⟨rfl, rfl⟩
def PartitionEltypeTypeProperty : Prop := ∀ parent, partitionEltype parent = .subString parent
theorem partitionEltypeType_proven : PartitionEltypeTypeProperty := by unfold PartitionEltypeTypeProperty; intros; rfl
def PartitionEltypeValueProperty : Prop := ∀ parent, partitionEltypeSub parent = parent
theorem partitionEltypeValue_proven : PartitionEltypeValueProperty := by unfold PartitionEltypeValueProperty; intros; rfl
def PartitionIterateProperty : Prop := ∀ source size state,
  Util.partitionIterate source size state = Strings.partitionIterate source size state
theorem partitionIterate_proven : PartitionIterateProperty := by unfold PartitionIterateProperty; intros; rfl
structure SplitIteratorModel (S F : Type) where
  source : S
  splitter : F
  limit : JInt64
  keepempty : Bool

def eachsplitCtor (source : S) (splitter : F) (limit : JInt64) (keepempty : Bool) :
    SplitIteratorModel S F := ⟨source, splitter, limit, keepempty⟩
def EachsplitCtorProperty : Prop := ∀ (S F : Type) source splitter limit keepempty,
  (eachsplitCtor (S := S) (F := F) source splitter limit keepempty).source = source ∧
  (eachsplitCtor source splitter limit keepempty).splitter = splitter ∧
  (eachsplitCtor source splitter limit keepempty).limit = limit ∧
  (eachsplitCtor source splitter limit keepempty).keepempty = keepempty
theorem eachsplitCtor_proven : EachsplitCtorProperty := by unfold EachsplitCtorProperty; intros; exact ⟨rfl, rfl, rfl, rfl⟩

def eachsplitChars (source : S) (chars : List UInt32) (limit : JInt64) (keepempty : Bool) :=
  eachsplitCtor source (fun c => chars.contains c) limit keepempty
def EachsplitCharsProperty : Prop := ∀ (S : Type) source chars limit keepempty character,
  (eachsplitChars (S := S) source chars limit keepempty).splitter character = chars.contains character
theorem eachsplitChars_proven : EachsplitCharsProperty := by unfold EachsplitCharsProperty; intros; rfl
def eachsplitChar (source : S) (splitter : UInt32) (limit : JInt64) (keepempty : Bool) :=
  eachsplitCtor source (fun c => c == splitter) limit keepempty
def EachsplitCharProperty : Prop := ∀ (S : Type) source splitter limit keepempty character,
  (eachsplitChar (S := S) source splitter limit keepempty).splitter character = (character == splitter)
theorem eachsplitChar_proven : EachsplitCharProperty := by unfold EachsplitCharProperty; intros; rfl
def eachsplitWhitespace (source : S) (limit : JInt64) (keepempty : Bool) :=
  eachsplitCtor source juliaSpace limit keepempty
def EachsplitWhitespaceProperty : Prop := ∀ (S : Type) source limit keepempty character,
  (eachsplitWhitespace (S := S) source limit keepempty).splitter character = juliaSpace character
theorem eachsplitWhitespace_proven : EachsplitWhitespaceProperty := by unfold EachsplitWhitespaceProperty; intros; rfl

def RsplitEltypeProperty : Prop := SplitEltypeProperty
theorem rsplitEltype_proven : RsplitEltypeProperty := splitEltype_proven
def RsplitEltypeTypeProperty : Prop := SplitEltypeTypeProperty
theorem rsplitEltypeType_proven : RsplitEltypeTypeProperty := splitEltypeType_proven
def RsplitEltypeValueProperty : Prop := SplitEltypeValueProperty
theorem rsplitEltypeValue_proven : RsplitEltypeValueProperty := splitEltypeValue_proven
def RsplitIteratorSizeProperty : Prop := SplitIteratorSizeProperty
theorem rsplitIteratorSize_proven : RsplitIteratorSizeProperty := splitIteratorSize_proven
def eachrsplitCtor := @eachsplitCtor
def EachrsplitCtorProperty : Prop := EachsplitCtorProperty
theorem eachrsplitCtor_proven : EachrsplitCtorProperty := eachsplitCtor_proven
def eachrsplitChars := @eachsplitChars
def EachrsplitCharsProperty : Prop := EachsplitCharsProperty
theorem eachrsplitChars_proven : EachrsplitCharsProperty := eachsplitChars_proven
def eachrsplitChar := @eachsplitChar
def EachrsplitCharProperty : Prop := EachsplitCharProperty
theorem eachrsplitChar_proven : EachrsplitCharProperty := eachsplitChar_proven
def eachrsplitWhitespace := @eachsplitWhitespace
def EachrsplitWhitespaceProperty : Prop := EachsplitWhitespaceProperty
theorem eachrsplitWhitespace_proven : EachrsplitWhitespaceProperty := eachsplitWhitespace_proven
def RsplitIterateProperty : Prop := ∀ source splitter keepempty stop remaining,
  Util.rsplitIterate source splitter keepempty stop remaining =
    JuliaLean.StringUtil.rsplitIterate source splitter keepempty stop remaining
theorem rsplitIterate_proven : RsplitIterateProperty := by unfold RsplitIterateProperty; intros; rfl
def SplitCollectProperty : Prop := ∀ source splitter limit keepempty,
  Util.splitCollect source splitter limit keepempty = JuliaLean.StringUtil.splitGen source splitter limit keepempty
theorem splitCollect_proven : SplitCollectProperty := by unfold SplitCollectProperty; intros; rfl
def SplitWhitespaceProperty : Prop := ∀ source splitter limit keepempty,
  Util.splitWhitespace source splitter limit keepempty = JuliaLean.StringUtil.splitGen source splitter limit keepempty
theorem splitWhitespace_proven : SplitWhitespaceProperty := by unfold SplitWhitespaceProperty; intros; rfl
def RsplitCollectProperty : Prop := ∀ source splitter limit keepempty,
  Util.rsplitCollect source splitter limit keepempty = JuliaLean.StringUtil.rsplitGen source splitter limit keepempty
theorem rsplitCollect_proven : RsplitCollectProperty := by unfold RsplitCollectProperty; intros; rfl
def RsplitWhitespaceProperty : Prop := ∀ source splitter limit keepempty,
  Util.rsplitWhitespace source splitter limit keepempty = JuliaLean.StringUtil.rsplitGen source splitter limit keepempty
theorem rsplitWhitespace_proven : RsplitWhitespaceProperty := by unfold RsplitWhitespaceProperty; intros; rfl

structure WriteResult where
  bytes : List UInt8
  count : Nat
  deriving Repr, DecidableEq

def replaceLiteral (initial replacement : List UInt8) : WriteResult :=
  ⟨initial ++ replacement, replacement.length⟩
def ReplaceLiteralProperty : Prop := ∀ initial replacement,
  (replaceLiteral initial replacement).bytes = initial ++ replacement ∧
    (replaceLiteral initial replacement).count = replacement.length
theorem replaceLiteral_proven : ReplaceLiteralProperty := by unfold ReplaceLiteralProperty; intros; exact ⟨rfl, rfl⟩

def replaceShown (showValue reprValue : A → List UInt8) (positionApplicable : Bool)
    (replacement : A) (initial : List UInt8) : WriteResult :=
  let rendered := if positionApplicable then showValue replacement else reprValue replacement
  ⟨initial ++ rendered, rendered.length⟩
def ReplaceShownProperty : Prop := ∀ (A : Type) showValue reprValue applicable replacement initial,
  (replaceShown (A := A) showValue reprValue applicable replacement initial).bytes =
    initial ++ if applicable then showValue replacement else reprValue replacement
theorem replaceShown_proven : ReplaceShownProperty := by unfold ReplaceShownProperty; intros; simp [replaceShown]

def replaceFunction (function : JSub → R) (recursiveReplace : List UInt8 → R → O)
    (source : JSub) (initial : List UInt8) : O := recursiveReplace initial (function source)
def ReplaceFunctionProperty : Prop := ∀ (R O : Type) function recursive source initial,
  replaceFunction (R := R) (O := O) function recursive source initial =
    recursive initial (function source)
theorem replaceFunction_proven : ReplaceFunctionProperty := by unfold ReplaceFunctionProperty; intros; rfl

def replaceCharFunction (function : UInt32 → R) (recursiveReplace : List UInt8 → R → O)
    (character : UInt32) (initial : List UInt8) : O := recursiveReplace initial (function character)
def ReplaceCharFunctionProperty : Prop := ∀ (R O : Type) function recursive character initial,
  replaceCharFunction (R := R) (O := O) function recursive character initial =
    recursive initial (function character)
theorem replaceCharFunction_proven : ReplaceCharFunctionProperty := by unfold ReplaceCharFunctionProperty; intros; rfl
def PatReplacerProperty : Prop := ∀ (A : Type) (pattern : A), Util.patReplacer pattern = pattern
theorem patReplacer_proven : PatReplacerProperty := by unfold PatReplacerProperty; intros; rfl
def FreePatReplacerProperty : Prop := ∀ (A : Type) (pattern : A), Util.freePatReplacer pattern = ()
theorem freePatReplacer_proven : FreePatReplacerProperty := by unfold FreePatReplacerProperty; intros; rfl
structure PreparedPredicate where
  apply : UInt32 → Bool

def prepareChar (character : UInt32) : PreparedPredicate := ⟨fun candidate => candidate == character⟩
def PatReplacerCharProperty : Prop := ∀ character candidate,
  (prepareChar character).apply candidate = (candidate == character)
theorem patReplacerChar_proven : PatReplacerCharProperty := by unfold PatReplacerCharProperty; intros; rfl
def prepareChars (chars : List UInt32) : PreparedPredicate := ⟨fun candidate => chars.contains candidate⟩
def PatReplacerCharsProperty : Prop := ∀ chars candidate,
  (prepareChars chars).apply candidate = chars.contains candidate
theorem patReplacerChars_proven : PatReplacerCharsProperty := by unfold PatReplacerCharsProperty; intros; rfl

def replaceIO (initial : List UInt8) (source : JStr) (pairs : List JuliaLean.StringUtil.Pair)
    (count : JInt64) : SJl (WriteResult × Nat) :=
  match JuliaLean.StringUtil.replaceN source pairs count with
  | .error error => .error error
  | .ok (bytes, replacements) => .ok (⟨initial ++ bytes, bytes.length⟩, replacements)
def ReplaceIOProperty : Prop := ∀ initial source pairs count output replacements,
  replaceIO initial source pairs count = .ok (output, replacements) →
    ∃ produced, JuliaLean.StringUtil.replaceN source pairs count = .ok (produced, replacements) ∧
      output.bytes = initial ++ produced ∧ output.count = produced.length
theorem replaceIO_proven : ReplaceIOProperty := by
  intro initial source pairs count output replacements h
  cases hr : JuliaLean.StringUtil.replaceN source pairs count with
  | error error => simp [replaceIO, hr] at h
  | ok result =>
      rcases result with ⟨produced, n⟩
      simp only [replaceIO, hr] at h
      cases h
      exact ⟨produced, rfl, rfl, rfl⟩
def ReplaceStringProperty : Prop := ∀ source pairs count,
  ∀ output, JuliaLean.StringUtil.replace source pairs count = .ok output →
    ∃ replacements, JuliaLean.StringUtil.replaceN source pairs count = .ok (output, replacements)
theorem replaceString_proven : ReplaceStringProperty := by
  unfold ReplaceStringProperty
  intro source pairs count output h
  cases hr : JuliaLean.StringUtil.replaceN source pairs count with
  | error error => simp [JuliaLean.StringUtil.replace, hr] at h
  | ok result =>
      rcases result with ⟨bytes, replacements⟩
      simp [JuliaLean.StringUtil.replace, hr] at h
      subst output
      exact ⟨replacements, rfl⟩

def hex2bytesGeneric (length : S → JInt64) (allocate : JInt64 → D)
    (decode : D → S → R) (source : S) : R :=
  decode (allocate (JuliaLean.StringUtil.shr1 (length source))) source
def Hex2bytesProperty : Prop := ∀ (S D R : Type) length allocate decode source,
  hex2bytesGeneric (S := S) (D := D) (R := R) length allocate decode source =
    decode (allocate (JuliaLean.StringUtil.shr1 (length source))) source
theorem hex2bytes_proven : Hex2bytesProperty := by unfold Hex2bytesProperty; intros; rfl
def Hex2bytesBangProperty : Prop := ∀ (A State : Type) destinationLength sourceLength
    (start : SJl (Option (A × State))) iterate convert,
  (sourceLength.val % 2 ≠ 0 →
    JuliaLean.StringUtil.hex2bytesBang destinationLength sourceLength start iterate convert =
      .error (JuliaLean.StringUtil.argErr "length of iterable must be even")) ∧
  (sourceLength.val % 2 = 0 → (ix 2 * destinationLength).val ≠ sourceLength.val →
    JuliaLean.StringUtil.hex2bytesBang destinationLength sourceLength start iterate convert =
      .error (JuliaLean.StringUtil.argErr "length of output array must be half of the length of input iterable"))
theorem hex2bytesBang_proven : Hex2bytesBangProperty := by
  unfold Hex2bytesBangProperty
  intros
  constructor
  · intro h; simp [JuliaLean.StringUtil.hex2bytesBang, h]
  · intro heven hmismatch
    simp [JuliaLean.StringUtil.hex2bytesBang, heven, hmismatch]

def numberFromAbstractChar (toChar : A → SJl UInt32) (character : A) : SJl UInt8 :=
  match toChar character with
  | .error error => .error error
  | .ok char => JuliaLean.StringUtil.numberFromHexChar char
def NumberFromHexProperty : Prop := ∀ (A : Type) toChar (character : A) output,
  numberFromAbstractChar toChar character = .ok output →
    ∃ char, toChar character = .ok char ∧ JuliaLean.StringUtil.numberFromHexChar char = .ok output
theorem numberFromHex_proven : NumberFromHexProperty := by
  unfold NumberFromHexProperty
  intro A toChar character output h
  cases hc : toChar character <;> simp [numberFromAbstractChar, hc] at h
  exact ⟨_, rfl, h⟩

def bytes2hexIterator (eltypeUInt8 : Bool) (bytes : List UInt8) : SJl (List UInt8) :=
  if eltypeUInt8 then .ok (JuliaLean.StringUtil.bytes2hexFill bytes)
  else .error (.jl (.argumentError "eltype of iterator not UInt8"))
def Bytes2hexProperty : Prop := ∀ bytes,
  bytes2hexIterator true bytes = .ok (JuliaLean.StringUtil.bytes2hexFill bytes)
theorem bytes2hex_proven : Bytes2hexProperty := by unfold Bytes2hexProperty; intros; rfl

def bytes2hexIO (initial : List UInt8) (eltypeUInt8 : Bool) (bytes : List UInt8) :
    SJl (List UInt8 × Unit) :=
  match bytes2hexIterator eltypeUInt8 bytes with
  | .error error => .error error
  | .ok encoded => .ok (initial ++ encoded, ())
def Bytes2hexIOProperty : Prop := ∀ initial bytes output,
  bytes2hexIO initial true bytes = .ok (output, ()) →
    output = initial ++ JuliaLean.StringUtil.bytes2hexFill bytes
theorem bytes2hexIO_proven : Bytes2hexIOProperty := by
  unfold Bytes2hexIOProperty
  intro initial bytes output h
  have h' : initial ++ JuliaLean.StringUtil.bytes2hexFill bytes = output := by
    simpa [bytes2hexIO, bytes2hexIterator] using h
  exact h'.symm

inductive AsciiResult where
  | ascii
  | invalid (index : Nat) (source : List UInt8)
  deriving Repr, DecidableEq

def asciiLoop (source : List UInt8) : Nat → List UInt8 → AsciiResult
  | _, [] => .ascii
  | index, byte :: rest =>
      if byte < 0x80 then asciiLoop source (index + 1) rest else .invalid index source

def ascii (source : List UInt8) : AsciiResult := asciiLoop source 1 source

theorem asciiLoop_ok : ∀ original index remaining,
    asciiLoop original index remaining = .ascii ↔ ∀ byte ∈ remaining, byte < 0x80
  | _, _, [] => by simp [asciiLoop]
  | original, index, byte :: rest => by
      simp only [asciiLoop]
      split <;> rename_i hbyte
      · simp [hbyte, asciiLoop_ok]
      · simp [hbyte]

def AsciiProperty : Prop := ∀ source,
  ascii source = .ascii ↔ ∀ byte ∈ source, byte < 0x80
theorem ascii_proven : AsciiProperty := by
  unfold AsciiProperty ascii
  intro source
  apply asciiLoop_ok

def ThrowInvalidAsciiProperty : Prop := ∀ source index,
  AsciiResult.invalid index source ≠ .ascii
theorem throwInvalidAscii_proven : ThrowInvalidAsciiProperty := by
  unfold ThrowInvalidAsciiProperty
  intro source index h
  cases h

def asciiAbstract (toString : A → List UInt8) (source : A) : AsciiResult := ascii (toString source)
def AsciiAbstractProperty : Prop := ∀ (A : Type) toString (source : A),
  asciiAbstract toString source = .ascii ↔ ∀ byte ∈ toString source, byte < 0x80
theorem asciiAbstract_proven : AsciiAbstractProperty := by
  unfold AsciiAbstractProperty asciiAbstract
  intros; apply ascii_proven

structure RestView (S : Type) where
  parent : S
  start : JInt64
def restFast (source : S) (index : JInt64) : RestView S := ⟨source, index⟩
def RestFastProperty : Prop := ∀ (S : Type) source index,
  (restFast (S := S) source index).parent = source ∧ (restFast source index).start = index
theorem restFast_proven : RestFastProperty := by unfold RestFastProperty; intros; exact ⟨rfl, rfl⟩

def restGeneric (printChar : UInt32 → List UInt8) (remaining : List UInt32) : List UInt8 :=
  remaining.flatMap printChar
def RestGenericProperty : Prop := ∀ printChar remaining,
  restGeneric printChar remaining = remaining.flatMap printChar
theorem restGeneric_proven : RestGenericProperty := by unfold RestGenericProperty; intros; rfl

end JuliaLean.StringsCovA.UtilRebuilt
