import JuliaLean.base.strings.unicode
import JuliaLean.base.strings.basic
import JuliaLean.base.int
import JuliaLean.base.rational
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.char.encoding

namespace JuliaLean.Proofs.base.strings.unicode

open JuliaLean JuliaLean.Registry
open JuliaLean.base.strings.unicode
open JuliaLean.base.char
open JuliaLean.base.strings.basic
open JuliaLean.base.rational

/-- Unicode scalar values exclude surrogate code points and values above U+10FFFF. -/
def unicodeScalar (u : UInt32) : Bool :=
  u.toNat ≤ 0x10ffff && !(0xd800 ≤ u.toNat && u.toNat ≤ 0xdfff)

def CharConstructorIdentity : Prop :=
  ∀ c : JChar, charOps.toChar c = .ok c

def AbstractCharValiditySpec : Prop :=
  (∀ {C : Type} (ops : AbstractCharOps C) c,
    isvalidAbstractChar ops c =
      Bool.and (Bool.and (!ops.malformed c) (!ops.overlong c))
        (Bool.or (ops.le c ops.d7ff)
          (Bool.and (ops.le ops.e000 c) (ops.le c ops.maxScalar)))) ∧
  (∀ {C : Type} (ops : AbstractCharOps C) c,
    isvalidAbstractCharType ops c = isvalidAbstractChar ops c)

/-- The real Char validity methods accept exactly well-formed scalar encodings. -/
def IsvalidScalarChar : Prop :=
  (∀ c : JChar,
    isvalidAbstractChar charOps c = true ↔
      ismalformed_Char charBitOps c = false ∧ isoverlong_Char c = false ∧
        ∃ u, codepoint_Char charBitOps c = .ok u ∧ unicodeScalar u = true ∧ char_UInt32 u = .ok c) ∧
  (∀ u : UInt32, isvalidUnsigned UInt32.toNat u = unicodeScalar u)

def IsvalidUnsignedContract : Prop :=
  ∀ {U : Type} (toNat : U → Nat) (c : U),
    isvalidUnsigned toNat c =
      Bool.or (toNat c ≤ 0xd7ff)
        (Bool.and (0xe000 ≤ toNat c) (toNat c ≤ 0x10ffff))

/-- Validity agrees with the unsigned code-point overload for constructed Chars. -/
def IsvalidConstructedAgreement : Prop :=
  ∀ u c, char_UInt32 u = .ok c →
    isvalidAbstractChar charOps c = isvalidUnsigned UInt32.toNat u

def IntegerValidityLaws {I : Type} (ops : IntegerValidityOps I) : Prop :=
  (∀ x u, 0 ≤ ops.integer.toInt x → ops.toUnsigned x = .ok u →
    ops.unsignedToNat u = (ops.integer.toInt x).toNat) ∧
  (∀ x, 0 ≤ ops.integer.toInt x → ops.integer.toInt x ≤ 0x10ffff →
    ∃ u, ops.toUnsigned x = .ok u ∧
      ops.unsignedToNat u = (ops.integer.toInt x).toNat) ∧
  (∀ x, ops.integer.toInt x < 0 →
    ops.toUnsigned x = .error (.jl (.inexactError "UInt64")))

def integerValidityOpsInt64 : IntegerValidityOps (JInt .i64) where
  integer := JuliaLean.base.rational.jintOps .i64
  unsignedType := JInt .u64
  toUnsigned x := liftJl (JuliaLean.base.int.convert .u64 x)
  unsignedToNat u := u.val.toNat

def integerValidityOpsBigInt : IntegerValidityOps Int where
  integer := JuliaLean.base.rational.bigIntOps
  unsignedType := JInt .u64
  toUnsigned x := liftJl (JInt.convert (IntTy.u64.name) .u64 x)
  unsignedToNat u := u.val.toNat

def IntegerValidityInstancesContract : Prop :=
  IntegerValidityLaws integerValidityOpsInt64 ∧ IntegerValidityLaws integerValidityOpsBigInt

def IsvalidIntegerBoolTotal : Prop :=
  ∀ {C I : Type} (charOps : AbstractCharOps C) (ops : IntegerValidityOps I),
      IntegerValidityLaws ops → ∀ x : I, ∃ b,
        isvalidInteger charOps ops x = .ok b

def IsvalidIntegerNegativeError : Prop :=
  ∀ {C I : Type} (charOps : AbstractCharOps C) (ops : IntegerValidityOps I),
    IntegerValidityLaws ops → ∀ x : I,
    ops.integer.toInt x < 0 →
    isvalidInteger charOps ops x = .error (.jl (.inexactError "UInt64"))

def IsvalidIntegerScalarContract : Prop :=
  ∀ {C I : Type} (charOps : AbstractCharOps C) (ops : IntegerValidityOps I),
    IntegerValidityLaws ops → ∀ x : I,
    (0 ≤ ops.integer.toInt x → ops.integer.toInt x ≤ 0x10ffff →
      isvalidInteger charOps ops x =
        .ok (decide (ops.integer.toInt x ≤ 0xd7ff ∨
          (0xe000 ≤ ops.integer.toInt x ∧ ops.integer.toInt x ≤ 0x10ffff)))) ∧
    (ops.integer.toInt x < 0 →
      isvalidInteger charOps ops x = .error (.jl (.inexactError "UInt64"))) ∧
    (∀ error, ops.toUnsigned x = .error error →
      isvalidInteger charOps ops x = .error error) ∧
    (0x10ffff < ops.integer.toInt x →
      ∀ u, ops.toUnsigned x = .ok u →
        isvalidInteger charOps ops x = .ok false)

def IsvalidBottomContract : Prop :=
  (∀ {A : Type} (x : A), isvalidUnion x = false) ∧
  (∀ {A : Type} (xs : List A), isvalidUnionVararg xs = .error .methodError)

def UnicodeValidityContract : Prop :=
  CharConstructorIdentity ∧ AbstractCharValiditySpec ∧ IsvalidScalarChar ∧
    IsvalidUnsignedContract ∧ IsvalidConstructedAgreement ∧
    IntegerValidityInstancesContract ∧ IsvalidIntegerScalarContract ∧ IsvalidBottomContract


/-- Case-table results for non-ASCII characters, the ASCII fast paths, and identity mappings. -/
def CaseCharacterTableSpec : Prop :=
  ∀ {C : Type} (charOps : AbstractCharOps C),
  (∀ (P : Utf8proc) c, charOps.isAscii c = true →
    lowercaseAbstractChar charOps P c =
      if inRange charOps charOps.asciiA charOps.asciiZ c then
        liftChar (charOps.addInt c 32) else .ok c) ∧
  (∀ (P : Utf8proc) c, charOps.isAscii c = true →
    uppercaseAbstractChar charOps P c =
      if inRange charOps charOps.asciia charOps.asciiz c then
        liftChar (charOps.subInt c 32) else .ok c) ∧
  (∀ (P : Utf8proc) c, charOps.isAscii c = true →
    titlecaseAbstractChar charOps P c =
      if inRange charOps charOps.asciia charOps.asciiz c then
        liftChar (charOps.subInt c 32) else .ok c) ∧
  (∀ (P : Utf8proc) c u, charOps.isAscii c = false →
    charOps.toUInt32 c = .ok u →
      lowercaseAbstractChar charOps P c = liftChar (charOps.fromUInt32 (P.tolower u)) ∧
      uppercaseAbstractChar charOps P c = liftChar (charOps.fromUInt32 (P.toupper u)) ∧
      titlecaseAbstractChar charOps P c = liftChar (charOps.fromUInt32 (P.totitle u))) ∧
  (∀ (P : Utf8proc) c u, isvalidAbstractChar charOps c = false →
    charOps.malformed c = false → charOps.overlong c = false →
    charOps.toUInt32 c = .ok u → P.tolower u = u →
    charOps.fromUInt32 u = .ok c → lowercaseAbstractChar charOps P c = .ok c) ∧
  (∀ (P : Utf8proc) c u, isvalidAbstractChar charOps c = false →
    charOps.malformed c = false → charOps.overlong c = false →
    charOps.toUInt32 c = .ok u → P.toupper u = u →
    charOps.fromUInt32 u = .ok c → uppercaseAbstractChar charOps P c = .ok c) ∧
  (∀ (P : Utf8proc) c u, isvalidAbstractChar charOps c = false →
    charOps.malformed c = false → charOps.overlong c = false →
    charOps.toUInt32 c = .ok u → P.totitle u = u →
    charOps.fromUInt32 u = .ok c → titlecaseAbstractChar charOps P c = .ok c)

/-- Monadic character mapping, used as the independent sequence specification for String map. -/
def mapCharResults : (JChar → UResult JChar) → List JChar → UResult (List JChar)
  | _, [] => .ok []
  | f, c :: cs => do
      let mapped ← f c
      let rest ← mapCharResults f cs
      pure (mapped :: rest)

def CaseStringMappingSpec : Prop :=
  ∀ {S R CU CT : Type} (ops : StringOps S R JChar CU CT UnicodeError)
    (iterate : S → IterSteps JChar JuliaLean.base.strings.basic.Index UnicodeError) (P : Utf8proc) (s : S)
    (chars : List JChar),
    collectIterSteps (iterate s) = .ok chars →
    uppercaseAbstractString ops iterate (charListBuilder (E := UnicodeError)) charOps P s =
      mapCharResults (uppercaseAbstractChar charOps P) chars ∧
    lowercaseAbstractString ops iterate (charListBuilder (E := UnicodeError)) charOps P s =
      mapCharResults (lowercaseAbstractChar charOps P) chars

/-- The documented String case methods return for every String. -/
def CaseStringNoThrow : Prop :=
  ∀ {R CU CT : Type} (ops : StringOps JString R JChar CU CT UnicodeError)
    (iterate : JString → IterSteps JChar JuliaLean.base.strings.basic.Index UnicodeError) (P : Utf8proc) (s : JString),
    (∃ out, uppercaseAbstractString ops iterate
      (charListBuilder (E := UnicodeError)) charOps P s = .ok out) ∧
    (∃ out, lowercaseAbstractString ops iterate
      (charListBuilder (E := UnicodeError)) charOps P s = .ok out)

def CaseMappingContract : Prop :=
  CaseCharacterTableSpec ∧ CaseStringMappingSpec ∧ CaseStringNoThrow

/-- A valid AnnotatedChar constructor keeps the supplied character and annotations. -/
def AnnotatedCharConstructorLaw {A Ann : Type}
    (ops : AnnotatedCharOps A JChar Ann) : Prop :=
  ∀ c annotations result, ops.construct c annotations = .ok result →
    ops.char result = c ∧ ops.annotations result = annotations

def CaseAnnotatedCharSpec : Prop :=
  ∀ {A Ann : Type} (annotated : AnnotatedCharOps A JChar Ann),
    AnnotatedCharConstructorLaw annotated → ∀ (P : Utf8proc) c d,
      (lowercaseAnnotatedChar charOps annotated P c = .ok d →
        lowercaseAbstractChar charOps P (annotated.char c) = .ok (annotated.char d) ∧
        annotated.annotations d = annotated.annotations c) ∧
      (uppercaseAnnotatedChar charOps annotated P c = .ok d →
        uppercaseAbstractChar charOps P (annotated.char c) = .ok (annotated.char d) ∧
        annotated.annotations d = annotated.annotations c) ∧
      (titlecaseAnnotatedChar charOps annotated P c = .ok d →
        titlecaseAbstractChar charOps P (annotated.char c) = .ok (annotated.char d) ∧
        annotated.annotations d = annotated.annotations c)

/- utf8proc's lowercase and uppercase tests are derived Unicode properties, not category tests. -/
def DerivedCasePredicateSpec : Prop :=
  ∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    (charOps.malformed c = true →
      islowercase charOps P c = .ok false ∧ isuppercase charOps P c = .ok false) ∧
    (charOps.malformed c = false →
      islowercase charOps P c = .ok (P.islower (charOps.unsafeCodepoint c) != 0) ∧
      isuppercase charOps P c = .ok (P.isupper (charOps.unsafeCodepoint c) != 0))
/- Category codes preserve utf8proc results and the above-range sentinel. -/
def CategoryCodeSpec : Prop :=
  (∀ {I : Type} (integerOps : RatIntOps I) (toUInt32 : I → UResult UInt32)
      (P : Utf8proc) (x : I) (u : UInt32),
      0 ≤ integerOps.toInt x → integerOps.toInt x ≤ 0x10ffff → toUInt32 x = .ok u →
      category_code_Integer integerOps.toInt toUInt32 P x = .ok (P.category u)) ∧
  (∀ {I : Type} (integerOps : RatIntOps I) (toUInt32 : I → UResult UInt32)
      (P : Utf8proc) (x : I),
      0x10ffff < integerOps.toInt x →
      category_code_Integer integerOps.toInt toUInt32 P x = .ok 30) ∧
  (∀ {I : Type} (integerOps : RatIntOps I) (toUInt32 : I → UResult UInt32)
      (P : Utf8proc) (x : I) (error : UnicodeError),
      integerOps.toInt x ≤ 0x10ffff → toUInt32 x = .error error →
      category_code_Integer integerOps.toInt toUInt32 P x = .error error) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    charOps.malformed c = true →
    category_code_AbstractChar charOps P c = .ok 31) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    charOps.malformed c = false →
    category_code_AbstractChar charOps P c =
      .ok (if (charOps.unsafeCodepoint c).toNat ≤ 0x10ffff
        then P.category (charOps.unsafeCodepoint c) else 30))

def CategoryCodeIndexContract : Prop :=
  ∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc),
    Utf8procLaws P → CategoryCodeBounds (category_code_AbstractChar charOps P)

/- Category predicates use utf8proc general-category ranges and exact ASCII tests. -/
def CategoryPredicateSpec : Prop :=
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c k,
    category_code_AbstractChar charOps P c = .ok k →
    isletter charOps P c = .ok (decide (UTF8PROC_CATEGORY_LU ≤ k ∧ k ≤ UTF8PROC_CATEGORY_LO)) ∧
    isnumeric charOps P c = .ok (decide (UTF8PROC_CATEGORY_ND ≤ k ∧ k ≤ UTF8PROC_CATEGORY_NO)) ∧
    ispunct charOps P c = .ok (decide (UTF8PROC_CATEGORY_PC ≤ k ∧ k ≤ UTF8PROC_CATEGORY_PO)) ∧
    isprint charOps P c = .ok (decide (UTF8PROC_CATEGORY_LU ≤ k ∧ k ≤ UTF8PROC_CATEGORY_ZS)) ∧
    iscased charOps P c = .ok (decide (k = UTF8PROC_CATEGORY_LU || k = UTF8PROC_CATEGORY_LT || k = UTF8PROC_CATEGORY_LL))) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) c,
    isdigit charOps c = decide (charOps.le charOps.ascii0 c && charOps.le c charOps.ascii9)) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) c,
    isxdigit charOps c = decide (
      (charOps.le charOps.ascii0 c && charOps.le c charOps.ascii9) ||
      (charOps.le charOps.asciia c && charOps.le c charOps.asciif) ||
      (charOps.le charOps.asciiA c && charOps.le c charOps.asciiF))) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) c,
    iscntrl charOps c =
      (charOps.le c charOps.control1f ||
        (charOps.le charOps.del c && charOps.le c charOps.latin1Control))) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c k,
    category_code_AbstractChar charOps P c = .ok k →
    isspace charOps P c = .ok (charOps.eq c charOps.space ||
      (charOps.le charOps.tab c && charOps.le c charOps.cr) || charOps.eq c charOps.nel ||
      (charOps.le charOps.nbsp c && UTF8PROC_CATEGORY_ZS ≤ k && k ≤ UTF8PROC_CATEGORY_ZP))) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c error,
    category_code_AbstractChar charOps P c = .error error →
    (charOps.eq c charOps.space ||
      (charOps.le charOps.tab c && charOps.le c charOps.cr) || charOps.eq c charOps.nel) →
    isspace charOps P c = .ok true)

def UnicodePredicateContract : Prop :=
  DerivedCasePredicateSpec ∧ CategoryPredicateSpec

def CategoryStringsGenericSpec : Prop :=
  ∀ {C I : Type} (charOps : AbstractCharOps C) (integerOps : RatIntOps I)
      (P : Utf8proc) (toUInt32 : I → UResult UInt32),
    (∀ (value : CategoryValue C I) error,
      category_code_Value charOps integerOps P toUInt32 value = .error error →
      category_string charOps integerOps P toUInt32 value = .error error) ∧
    (∀ (value : CategoryValue C I) (category : Int),
      category_code_Value charOps integerOps P toUInt32 value = .ok category →
      category_string charOps integerOps P toUInt32 value =
        match categoryStrings[category.toNat]? with
        | some name => .ok name
        | none => .error .boundsError)

def CategoryStringsCharSpec : Prop :=
  ∀ (P : Utf8proc)
      (charCodeBounds : CategoryCodeBounds (category_code_AbstractChar charOps P)),
    Utf8procLaws P →
    (∀ c error, category_code_AbstractChar charOps P c = .error error →
      category_string_Char charOps P charCodeBounds c = .error error) ∧
    (∀ c category (h : category_code_AbstractChar charOps P c = .ok category),
      category_string_Char charOps P charCodeBounds c =
        .ok (categoryStrings.get ⟨category.toNat, (charCodeBounds c category h).2⟩))

def CategoryStringsSafe : Prop :=
  CategoryStringsGenericSpec ∧ CategoryStringsCharSpec

def CategoryAbbreviationSpec : Prop :=
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    charOps.malformed c = true →
    category_abbrev_AbstractChar charOps P c = .ok "Ma") ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    charOps.malformed c = false → charOps.le c charOps.maxScalar = false →
    category_abbrev_AbstractChar charOps P c = .ok "In") ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    charOps.malformed c = false → charOps.le c charOps.maxScalar = true →
    category_abbrev_AbstractChar charOps P c =
      match charOps.toUInt32 c with
      | .ok u => .ok (P.categoryAbbrev u)
      | .error (.invalidChar _) => .error .invalidChar
      | .error (.codePointError _) => .error .codePointError
      | .error (.unicodeError error) => .error error
      | .error .boundsError => .error .boundsError
      | .error (.showError error) => .error (.showError error)
      | .error (.foreign error) => .error (.jl error)) ∧
  (∀ (P : Utf8proc) c, ismalformed_Char charBitOps c = true →
    category_abbrev_Char P c = "Ma") ∧
  (∀ (P : Utf8proc) c, ismalformed_Char charBitOps c = false → c > charOps.maxScalar →
    category_abbrev_Char P c = "In") ∧
  (∀ (P : Utf8proc) c,
    ismalformed_Char charBitOps c = false → c ≤ charOps.maxScalar →
    category_abbrev_Char P c = P.categoryAbbrev (unsafe_codepoint_Char charBitOps c))

def CategoryContract : Prop :=
  CategoryCodeSpec ∧ CategoryCodeIndexContract ∧ CategoryAbbreviationSpec ∧
    CategoryStringsSafe

/-- Assigned categories occupy exactly utf8proc codes one through private-use. -/
def IsassignedContract : Prop :=
  ∀ {C I : Type} (charOps : AbstractCharOps C) (integerOps : RatIntOps I)
      (P : Utf8proc) (toUInt32 : I → UResult UInt32),
    (∀ (value : CategoryValue C I) (category : Int),
      category_code_Value charOps integerOps P toUInt32 value = .ok category →
      isassigned charOps integerOps P toUInt32 value =
        .ok (UTF8PROC_CATEGORY_CN < category && category ≤ UTF8PROC_CATEGORY_CO)) ∧
    (∀ (x : I) (u : UInt32),
      0 ≤ integerOps.toInt x → integerOps.toInt x ≤ 0x10ffff → toUInt32 x = .ok u →
      isassigned charOps integerOps P toUInt32 (.integer x) =
        .ok (UTF8PROC_CATEGORY_CN < P.category u && P.category u ≤ UTF8PROC_CATEGORY_CO)) ∧
    (∀ (x : I), 0x10ffff < integerOps.toInt x →
      isassigned charOps integerOps P toUInt32 (.integer x) = .ok false) ∧
    (∀ (x : I) (error : UnicodeError),
      integerOps.toInt x ≤ 0x10ffff → toUInt32 x = .error error →
      isassigned charOps integerOps P toUInt32 (.integer x) = .error error)

def IscntrlImpliesValid : Prop :=
  ∀ {C : Type} (charOps : AbstractCharOps C) c,
    iscntrl charOps c = true → isvalidAbstractChar charOps c = true

/-- A reference sum over the characters in iteration order. -/
def textwidthFold {C : Type} (measure : C → UResult Int) : List C → UResult Int
  | [] => .ok 0
  | c :: cs => do
      let width ← measure c
      let rest ← textwidthFold measure cs
      pure (width + rest)

/-- A reference sum over Julia `Int` widths in iteration order. -/
def textwidthIntFold {C : Type} (measure : C → UResult (JInt .i64)) :
    List C → UResult (JInt .i64)
  | [] => .ok (JInt.wrap .i64 0)
  | c :: cs => do
      let width ← measure c
      let rest ← textwidthIntFold measure cs
      pure (JuliaLean.base.int.add width rest)

def TextwidthCharSpec : Prop :=
  ∀ (P : Utf8proc) c,
    let b := JuliaLean.base.strings.basic.bswap32 c
    (b < 0x7f → textwidthChar P c = Int.ofNat (if 0x20 ≤ b then 1 else 0)) ∧
    (0x7f ≤ b → (ismalformed_Char charBitOps c = true ∨ isoverlong_Char c = true) →
      textwidthChar P c = 1) ∧
    (0x7f ≤ b → ismalformed_Char charBitOps c = false → isoverlong_Char c = false →
      textwidthChar P c = P.charwidth (unsafe_codepoint_Char charBitOps c))

def TextwidthAbstractCharSpec : Prop :=
  ∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c,
    textwidthAbstractChar charOps P c =
      match charOps.toChar c with
      | .ok char => .ok (textwidthChar P char)
      | .error error => liftChar (.error error)

def TextwidthSumSpec : Prop :=
  (∀ {S C St : Type}
      (characters : S → UResult (List C))
      (iterateFirst : S → UResult (Option (C × St)))
      (iterateAt : S → St → UResult (Option (C × St)))
      (charOps : CharOps C) (P : Utf8proc) (s : S) (chars : List C),
      characters s = .ok chars →
      (∀ (measure : C → UResult (JInt .i64)),
        JuliaLean.base.reduce.mapreduce_protocol
          JuliaLean.base.iterators.restWithState
          (fun run r st =>
            (((JuliaLean.base.iterators.iterateRest
              (fun i s heap => some (run i s, heap)) r st) ()).get
                (by simp [JuliaLean.base.iterators.iterateRest])).1)
          (Except.mapError UnicodeError.jl JuliaLean.base.reduce._empty_reduce_error)
          measure textwidthAddReducer
          (fun | none => iterateFirst s | some st => iterateAt s st)
          (.value (JInt.wrap .i64 0)) =
          some (textwidthIntFold measure chars)) →
      textwidthAbstractString iterateFirst iterateAt charOps P s =
        some (textwidthIntFold (textwidthAbstractCharInt charOps P) chars)) ∧
  (∀ {C : Type}
      (mapreduce : (C → UResult Int) → (Int → Int → Int) → JString → Int → UResult Int)
      (charOps : CharOps C) (P : Utf8proc) (s : JString) (chars : List C),
      (∀ measure, mapreduce measure (· + ·) s 0 = textwidthFold measure chars) →
      textwidthString mapreduce charOps P s = textwidthFold (textwidthAbstractChar charOps P) chars) ∧
  (∀ {S C : Type}
      (characters : S → UResult (List C))
      (mapreduce : (C → UResult Int) → (Int → Int → Int) → S → Int → UResult Int)
      (charOps : CharOps C) (P : Utf8proc) (s : S) (chars : List C),
      characters s = .ok chars →
      (∀ measure, mapreduce measure (· + ·) s 0 = textwidthFold measure chars) →
      textwidthSubString mapreduce charOps P s = textwidthFold (textwidthAbstractChar charOps P) chars) ∧
  (∀ {C : Type} (getString : Unit → JString)
      (mapreduce : (C → UResult Int) → (Int → Int → Int) → JString → Int → UResult Int)
      (charOps : CharOps C) (P : Utf8proc) (s : Unit),
      textwidthAnnotatedString getString mapreduce charOps P s =
        textwidthString mapreduce charOps P (getString s))

def TextwidthContract : Prop :=
  CharConstructorIdentity ∧ TextwidthAbstractCharSpec ∧ TextwidthCharSpec ∧ TextwidthSumSpec

/-- The required option rejections, in Julia's source order. -/
def normalizeError (kw : NormKw) : Option String :=
  if (kw.compat || kw.stripmark) && !kw.compose && !kw.decompose then
    some "compat=true or stripmark=true require compose=true or decompose=true"
  else if boolNat kw.newline2ls + boolNat kw.newline2ps + boolNat kw.newline2lf > 1 then
    some "only one newline conversion may be specified"
  else none

def normFlagsSpec (kw : NormKw) : Nat :=
  (if kw.stable then UTF8PROC_STABLE else 0) |||
  (if kw.compat then UTF8PROC_COMPAT else 0) |||
  (if kw.decompose then UTF8PROC_DECOMPOSE else if kw.compose then UTF8PROC_COMPOSE else 0) |||
  (if kw.stripignore then UTF8PROC_IGNORE else 0) |||
  (if kw.rejectna then UTF8PROC_REJECTNA else 0) |||
  (if kw.newline2ls then UTF8PROC_NLF2LS else 0) |||
  (if kw.newline2ps then UTF8PROC_NLF2PS else 0) |||
  (if kw.newline2lf then UTF8PROC_NLF2LF else 0) |||
  (if kw.stripcc then UTF8PROC_STRIPCC else 0) |||
  (if kw.casefold then UTF8PROC_CASEFOLD else 0) |||
  (if kw.lump then UTF8PROC_LUMP else 0) |||
  (if kw.stripmark then UTF8PROC_STRIPMARK else 0)

def NormalizeOptionsContract : Prop :=
  ∀ {S B : Type} (ops : Utf8procMapOps JString B) (toString : S → UResult JString)
    (s : S) (kw : NormKw) (transform : CharTransform),
    match normalizeError kw with
    | some message => normalize ops toString s kw transform = .error (.argumentError message)
    | none => normalize ops toString s kw transform =
        utf8proc_mapAbstract ops toString s (Int.ofNat (normFlagsSpec kw)) transform

def NormFormFlags (nf : NormForm) : Option Nat :=
  match nf with
  | .nfc => some (UTF8PROC_STABLE ||| UTF8PROC_COMPOSE)
  | .nfd => some (UTF8PROC_STABLE ||| UTF8PROC_DECOMPOSE)
  | .nfkc => some (UTF8PROC_STABLE ||| UTF8PROC_COMPOSE ||| UTF8PROC_COMPAT)
  | .nfkd => some (UTF8PROC_STABLE ||| UTF8PROC_DECOMPOSE ||| UTF8PROC_COMPAT)
  | .other _ => none

def NormalizeFormContract : Prop :=
  ∀ {S B : Type} (ops : Utf8procMapOps JString B) (toString : S → UResult JString)
    (s : S) (nf : NormForm),
    match NormFormFlags nf with
    | some flags => normalizeForm ops toString s nf =
        utf8proc_mapAbstract ops toString s (Int.ofNat flags) identityTransform
    | none => normalizeForm ops toString s nf =
        .error (.argumentError s!":{normFormName nf} is not one of :NFC, :NFD, :NFKC, :NFKD")

/-- The first utf8proc pass sizes the buffer for the second pass. -/
def Utf8procMapBufferFits : Prop :=
  ∀ {S B : Type} (ops : Utf8procMapOps S B) (s : S) (options : Int)
    (transform : CharTransform) (firstCount : Int) (firstState : transform.state)
    (secondCount : Int) (secondState : transform.state),
    utf8procDecompose ops s options ops.null 0 transform = .ok (firstCount, firstState) →
    utf8procDecompose ops s options (ops.allocate (firstCount * 4)) firstCount
      ({ transform with initial := firstState }) = .ok (secondCount, secondState) →
    secondCount ≤ firstCount
def Utf8procMapAbstractContract : Prop :=
  ∀ {S B : Type} (ops : Utf8procMapOps JString B)
      (toString : S → UResult JString) (s : S) (options : Int)
      (transform : CharTransform),
    (∀ error, toString s = .error error →
      utf8proc_mapAbstract ops toString s options transform = .error error) ∧
    (∀ string, toString s = .ok string →
      utf8proc_mapAbstract ops toString s options transform =
        utf8proc_map ops string options transform)

def Utf8procMapContract : Prop :=
  Utf8procMapBufferFits ∧ Utf8procMapAbstractContract

/-- The titlecase word-separator rule applied to a character sequence. -/
def titlecaseSpecLoop {C : Type} (charOps : CharOps C) (P : Utf8proc)
    (wordsep : C → Bool) (strict : Bool) : List C → Bool → Int32 → C → UResult (List C)
  | [], _, _, _ => .ok []
  | c :: cs, startword, state, c0 => do
      let (breaks, state) ← isgraphemebreakBang charOps P state c0 c
      if breaks && wordsep c then
        let rest ← titlecaseSpecLoop charOps P wordsep strict cs true state c
        pure (c :: rest)
      else
        let mapped ← if startword then titlecaseAbstractChar charOps P c
          else if strict then lowercaseAbstractChar charOps P c else pure c
        let rest ← titlecaseSpecLoop charOps P wordsep strict cs false state c
        pure (mapped :: rest)

def writeCharList {B C : Type} (write : B → C → UResult B) : B → List C → UResult B
  | buffer, [] => .ok buffer
  | buffer, c :: cs => do
      let buffer ← write buffer c
      writeCharList write buffer cs

def TitlecaseStringContract : Prop :=
  (∀ {S C B : Type} (ops : TitlecaseOps S C B) (charOps : AbstractCharOps C)
      (P : Utf8proc) (wordsep : C → Bool) (strict : Bool) (s : S) (chars : List C),
      collectIterSteps (ops.iterate s) = .ok chars →
      titlecaseAbstractString ops charOps P wordsep strict s = do
        let expected ← titlecaseSpecLoop charOps P wordsep strict chars true 0 (ops.zeroChar s)
        let buffer ← ops.newBuffer ()
        let buffer ← writeCharList ops.printChar buffer expected
        ops.takeString buffer) ∧
  (∀ {S C B : Type} (ops : TitlecaseOps S C B) (charOps : AbstractCharOps C)
      (P : Utf8proc) (wordsep : C → Bool) (strict : Bool) (s : S)
      (error : UnicodeError) (buffer : B),
      ops.newBuffer () = .ok buffer → ops.iterate s = .fail error →
      titlecaseAbstractString ops charOps P wordsep strict s = .error error)

/-- The typed callee's law: it visits characters in order and carries every annotation unchanged. -/
def mapAnnotatedChars {C Ann State : Type}
    (step : C → State → UResult (C × State)) :
    List (C × Ann) → State → UResult (List (C × Ann) × State)
  | [], state => .ok ([], state)
  | (c, annotation) :: rest, state => do
      let (mapped, state) ← step c state
      let (mappedRest, state) ← mapAnnotatedChars step rest state
      pure ((mapped, annotation) :: mappedRest, state)

structure AnnotatedStringOps (A C Ann : Type) where
  transform : (C → UResult C) → A → UResult A
  statefulTransform : {State : Type} →
    (C → State → UResult (C × State)) → A → State → UResult A
  characters : A → List (C × Ann)
  build : List (C × Ann) → UResult A
  statelessMapLaw : ∀ (step : C → UResult C) (s : A),
    transform step s = do
      let (mapped, _) ← mapAnnotatedChars
        (fun c _ => do let mapped ← step c; pure (mapped, ())) (characters s) ()
      build mapped
  mapLaw : ∀ {State : Type} (step : C → State → UResult (C × State)) (s : A) (state : State),
    statefulTransform step s state = do
      let (mapped, _) ← mapAnnotatedChars step (characters s) state
      build mapped

def titlecaseStateSpec {C : Type} (charOps : CharOps C) (P : Utf8proc) :
    C → TitleState C → UResult (C × TitleState C) := fun c state => do
  let (breaks, graphemeState) ← isgraphemebreakBang charOps P state.state state.c0 c
  if breaks && state.wordsep c then
    pure (c, { state with startword := true, state := graphemeState, c0 := c })
  else
    let mapped ← if state.startword then titlecaseAbstractChar charOps P c
      else if state.strict then lowercaseAbstractChar charOps P c else pure c
    pure (mapped, { state with startword := false, state := graphemeState, c0 := c })

def TitlecaseAnnotatedContract : Prop :=
  (∀ {A C Ann : Type} (ops : AnnotatedStringOps A C Ann) (charOps : CharOps C)
      (P : Utf8proc) (wordsep : C → Bool) (strict : Bool) (zero : C) (s : A),
      titlecaseAnnotatedString ops.statefulTransform charOps P wordsep strict zero s = do
        let initial : TitleState C := ⟨true, 0, zero, wordsep, strict⟩
        let (mapped, _) ← mapAnnotatedChars (titlecaseStateSpec charOps P) (ops.characters s) initial
        ops.build mapped) ∧
  (∀ {A Sub C : Type} (toAnnotated : Sub → A)
      (transform : {State : Type} → (C → State → UResult (C × State)) →
        A → State → UResult A) (charOps : CharOps C) (P : Utf8proc)
      (wordsep : C → Bool) (strict : Bool) (zero : C) (s : Sub),
      titlecaseAnnotatedSubString toAnnotated transform charOps P wordsep strict zero s =
        titlecaseAnnotatedString transform charOps P wordsep strict zero (toAnnotated s))

def CaseAnnotatedStringContract : Prop :=
  (∀ {A C Ann : Type} (ops : AnnotatedStringOps A C Ann) (charOps : CharOps C)
      (P : Utf8proc) (s : A),
      uppercaseAnnotatedString ops.transform charOps P s = do
        let (mapped, _) ← mapAnnotatedChars
          (fun c _ => do let c ← uppercaseAbstractChar charOps P c; pure (c, ()))
          (ops.characters s) ()
        ops.build mapped) ∧
  (∀ {A C Ann : Type} (ops : AnnotatedStringOps A C Ann) (charOps : CharOps C)
      (P : Utf8proc) (s : A),
      lowercaseAnnotatedString ops.transform charOps P s = do
        let (mapped, _) ← mapAnnotatedChars
          (fun c _ => do let c ← lowercaseAbstractChar charOps P c; pure (c, ()))
          (ops.characters s) ()
        ops.build mapped)

def CaseAnnotatedSubStringContract : Prop :=
  (∀ {A Sub C : Type} (toAnnotated : Sub → A)
      (transform : (C → UResult C) → A → UResult A)
      (charOps : CharOps C) (P : Utf8proc) (s : Sub),
      uppercaseAnnotatedSubString toAnnotated transform charOps P s =
        uppercaseAnnotatedString transform charOps P (toAnnotated s)) ∧
  (∀ {A Sub C : Type} (toAnnotated : Sub → A)
      (transform : (C → UResult C) → A → UResult A)
      (charOps : CharOps C) (P : Utf8proc) (s : Sub),
      lowercaseAnnotatedSubString toAnnotated transform charOps P s =
        lowercaseAnnotatedString transform charOps P (toAnnotated s))
def AnnotatedCaseContract : Prop :=
  CaseAnnotatedCharSpec ∧ CaseAnnotatedStringContract ∧ CaseAnnotatedSubStringContract

def FirstCaseAnnotatedContract : Prop :=
  (∀ {A C Ann : Type} (ops : AnnotatedStringOps A C Ann) (charOps : CharOps C)
      (P : Utf8proc) (s : A),
      uppercasefirstAnnotatedString ops.statefulTransform charOps P s = do
        let step := fun c first =>
          if first then do let c ← titlecaseAbstractChar charOps P c; pure (c, false)
          else pure (c, first)
        let (mapped, _) ← mapAnnotatedChars step (ops.characters s) true
        ops.build mapped) ∧
  (∀ {A C Ann : Type} (ops : AnnotatedStringOps A C Ann) (charOps : CharOps C)
      (P : Utf8proc) (s : A),
      lowercasefirstAnnotatedString ops.statefulTransform charOps P s = do
        let step := fun c first =>
          if first then do let c ← lowercaseAbstractChar charOps P c; pure (c, false)
          else pure (c, first)
        let (mapped, _) ← mapAnnotatedChars step (ops.characters s) true
        ops.build mapped) ∧
  (∀ {A Sub C : Type} (toAnnotated : Sub → A)
      (transform : {State : Type} → (C → State → UResult (C × State)) →
        A → State → UResult A) (charOps : CharOps C) (P : Utf8proc) (s : Sub),
      uppercasefirstAnnotatedSubString toAnnotated transform charOps P s =
        uppercasefirstAnnotatedString transform charOps P (toAnnotated s) ∧
      lowercasefirstAnnotatedSubString toAnnotated transform charOps P s =
        lowercasefirstAnnotatedString transform charOps P (toAnnotated s))

/-- `uppercasefirst` and `lowercasefirst` change only the first character of a nonempty string. -/
def FirstCaseStringContract : Prop :=
  (∀ {S C Sub : Type} (ops : FirstCaseOps S C Sub) (charOps : CharOps C)
      (P : Utf8proc) (s : S), ops.isempty s = true →
      uppercasefirstAbstractString ops charOps P s = .ok JuliaLean.Strings.JStr.empty ∧
      lowercasefirstAbstractString ops charOps P s = .ok JuliaLean.Strings.JStr.empty) ∧
  (∀ {S C Sub : Type} (ops : FirstCaseOps S C Sub) (charOps : CharOps C)
      (P : Utf8proc) (s : S) (c cUpper cLower : C)
      (next : JuliaLean.base.strings.basic.Index) (rest : Sub),
      ops.isempty s = false → ops.getindex s (JInt.lit .i64 1) = .ok c →
      titlecaseAbstractChar charOps P c = .ok cUpper →
      lowercaseAbstractChar charOps P c = .ok cLower →
      ops.nextind s (JInt.lit .i64 1) = .ok next →
      ops.substring s next = .ok rest →
      (ops.equalChar c cUpper = true →
        uppercasefirstAbstractString ops charOps P s = ops.convertString s) ∧
      (ops.equalChar c cUpper = false →
        uppercasefirstAbstractString ops charOps P s = ops.string cUpper rest) ∧
      (ops.equalChar c cLower = true →
        lowercasefirstAbstractString ops charOps P s = ops.convertString s) ∧
      (ops.equalChar c cLower = false →
        lowercasefirstAbstractString ops charOps P s = ops.string cLower rest))

def FirstCaseContract : Prop :=
  FirstCaseStringContract ∧ FirstCaseAnnotatedContract

/-- Grapheme length is the count of stateful boundaries in the character sequence. -/
def graphemeCountSpec {C : Type} (charOps : CharOps C) (P : Utf8proc) :
    List C → C → Int32 → JInt64 → UResult JInt64
  | [], _, _, count => .ok count
  | c :: cs, c0, state, count => do
      let (breaks, state) ← isgraphemebreakBang charOps P state c0 c
      graphemeCountSpec charOps P cs c state
        (count + JInt.lit .i64 (if breaks then 1 else 0))


def graphemeRunSpec {C : Type} (charOps : CharOps C) (P : Utf8proc) :
    List (C × JuliaLean.base.strings.basic.Index) → C → Int32 →
      JuliaLean.base.strings.basic.Index → JuliaLean.base.strings.basic.Index →
      UResult (Int32 × JuliaLean.base.strings.basic.Index × JuliaLean.base.strings.basic.Index)
  | [], _, state, j, k => .ok (state, j, k)
  | (c, next) :: rest, c0, state, j, k => do
      let (breaks, state) ← isgraphemebreakBang charOps P state c0 c
      if breaks then pure (state, j, k)
      else graphemeRunSpec charOps P rest c state k next

def GraphemeAccessTrace {S C Sub : Type} (ops : GraphemeStringOps S C Sub) (s : S) :
    JuliaLean.base.strings.basic.Index → List (C × JuliaLean.base.strings.basic.Index) → Prop
  | index, [] => (ops.ncodeunits s).val < index.val
  | index, (c, next) :: rest =>
      index.val ≤ (ops.ncodeunits s).val ∧
      ops.iterateAt s index = .ok (some (c, next)) ∧ GraphemeAccessTrace ops s next rest

def GraphemeStart {S C Sub : Type} (ops : GraphemeStringOps S C Sub) (s : S) :
    Option (Int32 × JuliaLean.base.strings.basic.Index) →
      Int32 → JuliaLean.base.strings.basic.Index → Prop
  | none, state, index => state = 0 ∧ index = ops.firstindex s
  | some (storedState, storedIndex), state, index =>
      state = storedState ∧ index = storedIndex
def GraphemeIteratorContract : Prop :=
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c1 c2,
    (charOps.malformed c1 = true ∨ charOps.malformed c2 = true) →
      isgraphemebreak charOps P c1 c2 = .ok true) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) state c1 c2,
    (charOps.malformed c1 = true ∨ charOps.malformed c2 = true) →
      isgraphemebreakBang charOps P state c1 c2 = .ok (true, 0)) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) c1 c2 u1 u2,
    charOps.malformed c1 = false → charOps.malformed c2 = false →
    charOps.toUInt32 c1 = .ok u1 → charOps.toUInt32 c2 = .ok u2 →
      isgraphemebreak charOps P c1 c2 = .ok (P.graphemeBreak u1 u2)) ∧
  (∀ {C : Type} (charOps : AbstractCharOps C) (P : Utf8proc) state c1 c2 u1 u2,
    charOps.malformed c1 = false → charOps.malformed c2 = false →
    charOps.toUInt32 c1 = .ok u1 → charOps.toUInt32 c2 = .ok u2 →
      isgraphemebreakBang charOps P state c1 c2 =
        .ok (P.graphemeBreakStateful state u1 u2)) ∧
  (∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub) (charOps : AbstractCharOps C)
      (P : Utf8proc) (g : GraphemeIterator S) (chars : List C),
      collectIterSteps (ops.iterateChars g.s) = .ok chars →
      lengthGraphemeIterator ops charOps P g =
        graphemeCountSpec charOps P chars (ops.zeroChar g.s) 0 (JInt.lit .i64 0)) ∧
  (∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub) (charOps : AbstractCharOps C)
      (P : Utf8proc) (g : GraphemeIterator S) (error : UnicodeError),
      ops.iterateChars g.s = .fail error →
      lengthGraphemeIterator ops charOps P g = .error error) ∧
  (∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub) (charOps : AbstractCharOps C)
      (P : Utf8proc) (s : S)
      (stateInput : Option (Int32 × JuliaLean.base.strings.basic.Index))
      (state : Int32) (i : JuliaLean.base.strings.basic.Index),
      GraphemeStart ops s stateInput state i →
      ops.iterateAt s i = .ok none →
      iterateGraphemeIterator ops charOps P (graphemes s) stateInput =
        some (.ok none)) ∧
  (∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub) (charOps : AbstractCharOps C)
      (P : Utf8proc) (s : S)
      (stateInput : Option (Int32 × JuliaLean.base.strings.basic.Index))
      (state : Int32) (i : JuliaLean.base.strings.basic.Index) (c0 : C)
      (k : JuliaLean.base.strings.basic.Index)
      (steps : List (C × JuliaLean.base.strings.basic.Index)) (stateFinal : Int32)
      (j next : JuliaLean.base.strings.basic.Index) (sub : Sub),
      GraphemeStart ops s stateInput state i →
      ops.iterateAt s i = .ok (some (c0, k)) →
      GraphemeAccessTrace ops s k steps →
      graphemeRunSpec charOps P steps c0 state i k = .ok (stateFinal, j, next) →
      ops.substring s i j = .ok sub →
      iterateGraphemeIterator ops charOps P (graphemes s) stateInput =
        some (.ok (some (sub, (stateFinal, next))))) ∧
  (∀ {S : Type} (s : S), (graphemes s).s = s) ∧
  (∀ (subStringType : Type → Type) (S : Type),
    eltypeGrapheme subStringType S = subStringType S ∧
    eltypeGraphemeSubString subStringType S = subStringType S)

def GraphemePresentationContract : Prop :=
  (∀ {S : Type} (equal : S → S → Bool) (g1 g2 : GraphemeIterator S),
    eqGraphemeIterator equal g1 g2 = equal g1.s g2.s) ∧
  (∀ {S : Type} (hashString : S → UInt64 → UInt64) (g : GraphemeIterator S) h,
    hashGraphemeIterator hashString g h = hashString g.s h) ∧
  (∀ {S : Type} (less : S → S → Bool) (g1 g2 : GraphemeIterator S),
    islessGraphemeIterator less g1 g2 = less g1.s g2.s) ∧
  (∀ {S IO C Sub : Type} (ops : GraphemeStringOps S C Sub) (charOps : CharOps C)
      (P : Utf8proc) (typeName : Type → String) (string : S → String)
      (toString : JInt64 → String) (print : IO → List String → IO)
      (io : IO) (g : GraphemeIterator S) (len : JInt64),
      lengthGraphemeIterator ops charOps P g = .ok len →
      showGraphemeIterator ops charOps P typeName string toString print io g =
        .ok (print io ["length-", toString len, " GraphemeIterator{", typeName S,
          "} for \"", string g.s, "\""]))

def GraphemesContract : Prop :=
  GraphemeIteratorContract ∧ GraphemePresentationContract

/-! Nothing to promise:
utf8proc_error@153: internal conversion of an utf8proc error string to `ErrorException`; its propagation is covered by the normalization properties.
utf8proc_custom_func@156: typed C callback adapter; no user-facing behavior beyond the callback conversion contract.
-/

/-! ## Julia method coverage -/
/-!
| Julia method | Property statement |
|---|---|
| `isvalid(c::AbstractChar)`@58 | `AbstractCharValiditySpec`, `IsvalidScalarChar` |
| `isvalid(::Type{<:AbstractChar}, c::Unsigned)`@59 | `IsvalidUnsignedContract` |
| `isvalid(::Type{T}, c::Integer)`@60 | `IsvalidIntegerBoolTotal`, `IsvalidIntegerScalarContract` |
| `isvalid(::Type{<:AbstractChar}, c::AbstractChar)`@61 | `AbstractCharValiditySpec` |
| `isvalid(::Type{Union{}}, value)`@62 | `IsvalidBottomContract` |
| `isvalid(::Type{Union{}}, slurp...)`@63 | `IsvalidBottomContract` |
| `utf8proc_error(result)`@153 | Nothing to promise |
| `utf8proc_custom_func(codepoint, callback)`@156 | Nothing to promise |
| `utf8proc_decompose(..., identity)`@159 | `Utf8procMapBufferFits` |
| `utf8proc_decompose(..., F)`@165 | `Utf8procMapBufferFits` |
| `utf8proc_map(String, SubString)`@173 | `Utf8procMapBufferFits` |
| `utf8proc_map(AbstractString)`@199 | `Utf8procMapAbstractContract`, `Utf8procMapBufferFits` |
| `normalize(::AbstractString; kwargs...)`@202 | `NormalizeOptionsContract` |
| `normalize(::AbstractString, ::Symbol)`@243 | `NormalizeFormContract` |
| `textwidth(::AbstractChar)`@270 | `TextwidthAbstractCharSpec` |
| `textwidth(::Char)`@272 | `TextwidthCharSpec` |
| `textwidth(::AbstractString)`@295 | `TextwidthSumSpec` |
| `textwidth(::String)`@297 | `TextwidthSumSpec` |
| `textwidth(::SubString{String})`@298 | `TextwidthSumSpec` |
| `textwidth(::AnnotatedString)`@300 | `TextwidthContract` |
| `lowercase(::AbstractChar)`@318 | `CaseCharacterTableSpec` |
| `lowercase(::AnnotatedChar)`@321 | `CaseAnnotatedCharSpec` |
| `uppercase(::AbstractChar)`@339 | `CaseCharacterTableSpec` |
| `uppercase(::AnnotatedChar)`@342 | `CaseAnnotatedCharSpec` |
| `titlecase(::AbstractChar)`@364 | `CaseCharacterTableSpec` |
| `titlecase(::AnnotatedChar)`@367 | `CaseAnnotatedCharSpec` |
| `category_code(::AbstractChar)`@372 | `CategoryCodeSpec` |
| `category_code(::Integer)`@379 | `CategoryCodeSpec` |
| `category_abbrev(::AbstractChar)`@384 | `CategoryAbbreviationSpec` |
| `category_abbrev(::Char)`@392 | `CategoryAbbreviationSpec` |
| `category_string(c)`@400 | `CategoryStringsSafe` |
| `category_string(::Char)`@403 | `CategoryStringsSafe` |
| `isassigned(c)`@405 | `IsassignedContract` |
| `islowercase(::AbstractChar)`@429 | `DerivedCasePredicateSpec` |
| `isuppercase(::AbstractChar)`@458 | `DerivedCasePredicateSpec` |
| `iscased(::AbstractChar)`@472 | `CategoryPredicateSpec` |
| `isdigit(::AbstractChar)`@499 | `CategoryPredicateSpec` |
| `isletter(::AbstractChar)`@522 | `CategoryPredicateSpec` |
| `isnumeric(::AbstractChar)`@549 | `CategoryPredicateSpec` |
| `iscntrl(::AbstractChar)`@568 | `IscntrlImpliesValid`, `CategoryPredicateSpec` |
| `ispunct(::AbstractChar)`@594 | `CategoryPredicateSpec` |
| `isspace(::AbstractChar)`@624 | `CategoryPredicateSpec` |
| `isprint(::AbstractChar)`@642 | `CategoryPredicateSpec` |
| `isxdigit(::AbstractChar)`@659 | `CategoryPredicateSpec` |
| `uppercase(::AbstractString)`@676 | `CaseStringMappingSpec`, `CaseStringNoThrow` |
| `uppercase(::AnnotatedString)`@677 | `CaseAnnotatedStringContract` |
| `uppercase(::SubString{<:AnnotatedString})`@678 | `CaseAnnotatedSubStringContract` |
| `lowercase(::AbstractString)`@693 | `CaseStringMappingSpec`, `CaseStringNoThrow` |
| `lowercase(::AnnotatedString)`@694 | `CaseAnnotatedStringContract` |
| `lowercase(::SubString{<:AnnotatedString})`@695 | `CaseAnnotatedSubStringContract` |
| `titlecase(::AbstractString)`@723 | `TitlecaseStringContract` |
| `titlecase(::AnnotatedString)`@745 | `TitlecaseAnnotatedContract` |
| `titlecase(::SubString{<:AnnotatedString})`@761 | `TitlecaseAnnotatedContract` |
| `uppercasefirst(::AbstractString)`@780 | `FirstCaseStringContract` |
| `uppercasefirst(::AnnotatedString)`@789 | `FirstCaseAnnotatedContract` |
| `uppercasefirst(::SubString{<:AnnotatedString})`@798 | `FirstCaseAnnotatedContract` |
| `lowercasefirst(::AbstractString)`@814 | `FirstCaseStringContract` |
| `lowercasefirst(::AnnotatedString)`@823 | `FirstCaseAnnotatedContract` |
| `lowercasefirst(::SubString{<:AnnotatedString})`@832 | `FirstCaseAnnotatedContract` |
| `isgraphemebreak(::AbstractChar, ::AbstractChar)`@837 | `GraphemeIteratorContract` |
| `isgraphemebreak!(::Ref{Int32}, ::AbstractChar, ::AbstractChar)`@844 | `GraphemeIteratorContract` |
| `graphemes(::AbstractString)`@858 | `GraphemeIteratorContract` |
| `eltype(::Type{GraphemeIterator{S}})`@860 | `GraphemeIteratorContract` |
| `eltype(::Type{GraphemeIterator{SubString{S}}})`@861 | `GraphemeIteratorContract` |
| `length(::GraphemeIterator)`@863 | `GraphemeIteratorContract` |
| `iterate(::GraphemeIterator, state)`@874 | `GraphemeIteratorContract` |
| `==(::GraphemeIterator, ::GraphemeIterator)`@892 | `GraphemePresentationContract` |
| `hash(::GraphemeIterator, ::UInt)`@893 | `GraphemePresentationContract` |
| `isless(::GraphemeIterator, ::GraphemeIterator)`@894 | `GraphemePresentationContract` |
| `show(::IO, ::GraphemeIterator)`@896 | `GraphemePresentationContract` |
-/
theorem abstractCharValiditySpec_proven : AbstractCharValiditySpec := by
  constructor
  · intro C ops c
    rfl
  · intro C ops c
    rfl

theorem charConstructorIdentity_proven : CharConstructorIdentity := by
  intro c
  rfl

theorem isvalidUnsignedContract_proven : IsvalidUnsignedContract := by
  intro U toNat c
  rfl

theorem isvalidBottomContract_proven : IsvalidBottomContract := by

  constructor
  · intro A x
    rfl
  · intro A xs
    rfl

theorem normalizeFormContract_proven : NormalizeFormContract := by
  intro S B ops toString s nf
  cases nf <;> rfl

theorem derivedCasePredicateSpec_proven : DerivedCasePredicateSpec := by
  intro C charOps P c
  constructor
  · intro hm
    simp [islowercase, isuppercase, hm]
  · intro hm
    simp [islowercase, isuppercase, hm]

theorem graphemePresentationContract_proven : GraphemePresentationContract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S equal g1 g2
    rfl
  · intro S hashString g h
    rfl
  · intro S less g1 g2
    rfl
  · intro S IO C Sub ops charOps P typeName string toString print io g len h
    rw [showGraphemeIterator, h]
    rfl

namespace UnicodeAnnotationProofs

private theorem annotatedCharMapPreserves {A Ann : Type}
    (ops : AnnotatedCharOps A JChar Ann)
    (law : ∀ c annotations result, ops.construct c annotations = .ok result →
      ops.char result = c ∧ ops.annotations result = annotations)
    (f : JChar → UResult JChar) (c d : A)
    (h : (do let mapped ← f (ops.char c); ops.construct mapped (ops.annotations c)) = .ok d) :
    f (ops.char c) = .ok (ops.char d) ∧ ops.annotations d = ops.annotations c := by
  cases hf : f (ops.char c) with
  | error error => simp [hf, Except.bind, Bind.bind] at h
  | ok mapped =>
    cases hc : ops.construct mapped (ops.annotations c) with
    | error error => simp [hf, hc, Except.bind, Bind.bind] at h
    | ok result =>
      have hd : result = d := by simpa [hf, hc, Except.bind, Bind.bind] using h
      subst d
      have hfields := law mapped (ops.annotations c) result hc
      exact ⟨by simpa [hf] using congrArg (fun x : JChar => (Except.ok x : UResult JChar)) hfields.1.symm,
        hfields.2⟩

theorem caseAnnotatedCharSpec_proven : CaseAnnotatedCharSpec := by
  intro A Ann ops law P c d
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact annotatedCharMapPreserves ops law (lowercaseAbstractChar charOps P) c d
      (by simpa [lowercaseAnnotatedChar, Except.bind, Bind.bind] using h)
  · intro h
    exact annotatedCharMapPreserves ops law (uppercaseAbstractChar charOps P) c d
      (by simpa [uppercaseAnnotatedChar, Except.bind, Bind.bind] using h)
  · intro h
    exact annotatedCharMapPreserves ops law (titlecaseAbstractChar charOps P) c d
      (by simpa [titlecaseAnnotatedChar, Except.bind, Bind.bind] using h)

theorem caseAnnotatedStringContract_proven : CaseAnnotatedStringContract := by
  refine ⟨?_, ?_⟩
  · intro A C Ann ops charOps P s
    simpa [uppercaseAnnotatedString, mapAnnotatedChars] using
      ops.statelessMapLaw (uppercaseAbstractChar charOps P) s
  · intro A C Ann ops charOps P s
    simpa [lowercaseAnnotatedString, mapAnnotatedChars] using
      ops.statelessMapLaw (lowercaseAbstractChar charOps P) s

theorem caseAnnotatedSubStringContract_proven : CaseAnnotatedSubStringContract := by
  refine ⟨?_, ?_⟩
  · intro A Sub C toAnnotated transform charOps P s
    rfl
  · intro A Sub C toAnnotated transform charOps P s
    rfl

theorem annotatedCaseContract_proven : AnnotatedCaseContract :=
  ⟨caseAnnotatedCharSpec_proven,
    ⟨caseAnnotatedStringContract_proven, caseAnnotatedSubStringContract_proven⟩⟩

theorem titlecaseAnnotatedContract_proven : TitlecaseAnnotatedContract := by
  refine ⟨?_, ?_⟩
  · intro A C Ann ops charOps P wordsep strict zero s
    let initial : TitleState C := ⟨true, 0, zero, wordsep, strict⟩
    let step : C → TitleState C → UResult (C × TitleState C) := titlecaseStateSpec charOps P
    change ops.statefulTransform step s initial = _
    exact ops.mapLaw step s initial
  · intro A Sub C toAnnotated transform charOps P wordsep strict zero s
    rfl

theorem firstCaseAnnotatedContract_proven : FirstCaseAnnotatedContract := by
  refine ⟨?_, ?_, ?_⟩
  · intro A C Ann ops charOps P s
    simpa [uppercasefirstAnnotatedString, mapAnnotatedChars] using
      ops.mapLaw (fun c first =>
        if first then do let c ← titlecaseAbstractChar charOps P c; pure (c, false)
        else pure (c, first)) s true
  · intro A C Ann ops charOps P s
    simpa [lowercasefirstAnnotatedString, mapAnnotatedChars] using
      ops.mapLaw (fun c first =>
        if first then do let c ← lowercaseAbstractChar charOps P c; pure (c, false)
        else pure (c, first)) s true
  · intro A Sub C toAnnotated transform charOps P s
    constructor <;> rfl


theorem firstCaseStringContract_proven : FirstCaseStringContract := by
  refine ⟨?_, ?_⟩
  · intro S C Sub ops charOps P s he
    constructor
    · simp [uppercasefirstAbstractString, he, pure, Except.pure]
    · simp [lowercasefirstAbstractString, he, pure, Except.pure]
  · intro S C Sub ops charOps P s c cUpper cLower next rest hne hget htitle hlower hnext hsub
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro heq
      simp [uppercasefirstAbstractString, hne, hget, htitle, hnext, hsub, heq,
        Bind.bind, Except.bind, pure, Except.pure]
    · intro hneq
      simp [uppercasefirstAbstractString, hne, hget, htitle, hnext, hsub, hneq,
        Bind.bind, Except.bind, pure, Except.pure]
    · intro heq
      simp [lowercasefirstAbstractString, hne, hget, hlower, hnext, hsub, heq,
        Bind.bind, Except.bind, pure, Except.pure]
    · intro hneq
      simp [lowercasefirstAbstractString, hne, hget, hlower, hnext, hsub, hneq,
        Bind.bind, Except.bind, pure, Except.pure]

theorem firstCaseContract_proven : FirstCaseContract :=
  ⟨firstCaseStringContract_proven, firstCaseAnnotatedContract_proven⟩
end UnicodeAnnotationProofs


namespace UnicodeValidityProofs

private theorem validUnsignedNatEqInt (x : Int) (hnon : 0 ≤ x) (hmax : x ≤ 0x10ffff) :
    Bool.or (x.toNat ≤ 0xd7ff)
      (Bool.and (0xe000 ≤ x.toNat) (x.toNat ≤ 0x10ffff)) =
      decide (x ≤ 0xd7ff ∨ (0xe000 ≤ x ∧ x ≤ 0x10ffff)) := by
  by_cases hD : x ≤ 0xd7ff
  · have hnD : x.toNat ≤ 0xd7ff := by omega
    simp [hD, hnD]
  · by_cases hE : 0xe000 ≤ x
    · have hnE : 0xe000 ≤ x.toNat := by omega
      have hnM : x.toNat ≤ 0x10ffff := by omega
      simp [hD, hE, hnE, hnM, hmax]
    · have hnD : ¬ x.toNat ≤ 0xd7ff := by omega
      have hnE : ¬ 0xe000 ≤ x.toNat := by omega
      simp [hD, hE, hnD, hnE]

theorem isvalidIntegerScalarContract_proven : IsvalidIntegerScalarContract := by
  intro C I charOps ops hlaws x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hnon hmax
    obtain ⟨u, hu, hNat⟩ := hlaws.2.1 x hnon hmax
    have hBool : isvalidUnsigned ops.unsignedToNat u =
        decide (ops.integer.toInt x ≤ 0xd7ff ∨
          (0xe000 ≤ ops.integer.toInt x ∧ ops.integer.toInt x ≤ 0x10ffff)) := by
      simp only [isvalidUnsigned, hNat]
      exact validUnsignedNatEqInt _ hnon hmax
    calc
      JuliaLean.base.strings.unicode.isvalidInteger charOps ops x =
          .ok (isvalidUnsigned ops.unsignedToNat u) := by
        simp [JuliaLean.base.strings.unicode.isvalidInteger, hu, Functor.map, Except.map]
      _ = .ok (decide (ops.integer.toInt x ≤ 0xd7ff ∨
          (0xe000 ≤ ops.integer.toInt x ∧ ops.integer.toInt x ≤ 0x10ffff))) :=
        congrArg (fun b : Bool => (.ok b : UResult Bool)) hBool
  · intro hneg
    simp [JuliaLean.base.strings.unicode.isvalidInteger, hlaws.2.2 x hneg, Functor.map, Except.map]
  · intro error herr
    simp [JuliaLean.base.strings.unicode.isvalidInteger, herr, Functor.map, Except.map]
  · intro hbig u hu
    have hnon : 0 ≤ ops.integer.toInt x := by omega
    have hNat := hlaws.1 x u hnon hu
    have hgt : 0x10ffff < ops.unsignedToNat u := by
      rw [hNat]
      omega
    have hBool : isvalidUnsigned ops.unsignedToNat u = false := by
      unfold isvalidUnsigned
      have hD : ¬ ops.unsignedToNat u ≤ 0xd7ff := by omega
      have hE : 0xe000 ≤ ops.unsignedToNat u := by omega
      have hM : ¬ ops.unsignedToNat u ≤ 0x10ffff := by omega
      simp [hD, hE, hM]
    calc
      JuliaLean.base.strings.unicode.isvalidInteger charOps ops x =
          .ok (isvalidUnsigned ops.unsignedToNat u) := by
        simp [JuliaLean.base.strings.unicode.isvalidInteger, hu, Functor.map, Except.map]
      _ = .ok false := congrArg (fun b : Bool => (.ok b : UResult Bool)) hBool

end UnicodeValidityProofs

namespace UnicodeAssignedProofs

theorem isassignedContract_proven : IsassignedContract := by
  intro C I charOps integerOps P toUInt32
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro value category h
    simp [isassigned, h, Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
  · intro x u hnon hmax hu
    simp [isassigned, category_code_Value, category_code_Integer, hmax, hu,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]
  · intro x hbig
    have hnot : ¬ integerOps.toInt x ≤ 0x10ffff := by omega
    simp [isassigned, category_code_Value, category_code_Integer, hnot,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map] <;> decide
  · intro x error hmax herr
    simp [isassigned, category_code_Value, category_code_Integer, hmax, herr,
      Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map]

end UnicodeAssignedProofs

namespace UnicodePredicateProofs

private theorem intBeqDecideEq (a b : Int) : (a == b) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp [h, beq_eq_false_iff_ne]

theorem categoryPredicateSpec_proven : CategoryPredicateSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C charOps P c k hcat
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [isletter, hcat, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [isnumeric, hcat, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [ispunct, hcat, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [isprint, hcat, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [iscased, hcat, Bind.bind, Except.bind, Pure.pure, Except.pure, intBeqDecideEq]
  · intro C charOps c
    unfold isdigit
    cases h : (charOps.le charOps.ascii0 c && charOps.le c charOps.ascii9) <;> simp [h]
  · intro C charOps c
    unfold isxdigit
    cases h : ((charOps.le charOps.ascii0 c && charOps.le c charOps.ascii9) ||
        (charOps.le charOps.asciia c && charOps.le c charOps.asciif) ||
        (charOps.le charOps.asciiA c && charOps.le c charOps.asciiF)) <;> simp [h]
  · intro C charOps c
    rfl
  · intro C charOps P c k hcat
    cases hs : charOps.eq c charOps.space <;>
      cases ht : charOps.le charOps.tab c <;>
      cases hr : charOps.le c charOps.cr <;>
      cases hn : charOps.eq c charOps.nel <;>
      cases hb : charOps.le charOps.nbsp c <;>
      simp [isspace, hcat, hs, ht, hr, hn, hb, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro C charOps P c error hcat hwhite
    cases hs : charOps.eq c charOps.space <;>
      cases ht : charOps.le charOps.tab c <;>
      cases hr : charOps.le c charOps.cr <;>
      cases hn : charOps.eq c charOps.nel <;>
      simp_all [isspace, hcat, hs, ht, hr, hn, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem unicodePredicateContract_proven : UnicodePredicateContract :=
  ⟨derivedCasePredicateSpec_proven, categoryPredicateSpec_proven⟩

end UnicodePredicateProofs

namespace UnicodeTextwidthProofs

theorem textwidthAbstractCharSpec_proven : TextwidthAbstractCharSpec := by
  unfold TextwidthAbstractCharSpec
  intro C ops P c
  cases h : ops.toChar c with
  | error err =>
    cases err <;>
      simp [textwidthAbstractChar, h, liftChar, Bind.bind, Except.bind, Pure.pure, Except.pure]
  | ok char =>
    simp [textwidthAbstractChar, h, liftChar, Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem bswapNotAscii (b : UInt32) (h : 0x7f ≤ b) : ¬ b < 0x7f := by
  intro hlt
  have hgeNat : 0x7f ≤ b.toNat := UInt32.le_iff_toNat_le.mp h
  have hltNat : b.toNat < 0x7f := UInt32.lt_iff_toNat_lt.mp hlt
  omega

theorem textwidthCharSpec_proven : TextwidthCharSpec := by
  unfold TextwidthCharSpec
  intro P c
  dsimp
  constructor
  · intro h
    simp [textwidthChar, h]
  · constructor
    · intro h hbad
      rcases hbad with hmal | hover
      · have hnot := bswapNotAscii (JuliaLean.base.strings.basic.bswap32 c) h
        simp [textwidthChar, h, hmal, hnot]
      · have hnot := bswapNotAscii (JuliaLean.base.strings.basic.bswap32 c) h
        simp [textwidthChar, h, hover, hnot]
    · intro h hmal hover
      have hnot := bswapNotAscii (JuliaLean.base.strings.basic.bswap32 c) h
      simp [textwidthChar, h, hmal, hover, hnot]

theorem textwidthSumSpec_proven : TextwidthSumSpec := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S C St characters iterateFirst iterateAt charOps P s chars hchars hmapreduce
    exact hmapreduce (textwidthAbstractCharInt charOps P)
  · intro C mapreduce charOps P s chars hmapreduce
    exact hmapreduce (textwidthAbstractChar charOps P)
  · intro S C characters mapreduce charOps P s chars hchars hmapreduce
    exact hmapreduce (textwidthAbstractChar charOps P)
  · intro C getString mapreduce charOps P s
    rfl

theorem textwidthContract_proven : TextwidthContract :=
  ⟨charConstructorIdentity_proven, textwidthAbstractCharSpec_proven,
    textwidthCharSpec_proven, textwidthSumSpec_proven⟩

end UnicodeTextwidthProofs
def caseCounterexampleUtf8proc : Utf8proc where
  toupper _ := 0
  tolower _ := 0
  totitle _ := 0
  category _ := 0
  categoryString _ := ""
  categoryAbbrev _ := ""
  islower _ := 0
  isupper _ := 0
  charwidth _ := 0
  graphemeBreak _ _ := true
  graphemeBreakStateful state _ _ := (true, state)

def caseCounterexampleStringOps : StringOps JString Unit JChar UInt8 Unit UnicodeError where
  ncodeunits _ := int 0
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit _ _ := .ok 0
  isvalid _ _ := .ok true
  iterateFirst _ := .ok none
  iterateAt _ _ := .ok none
  iterationBound _ := 0
  thisind _ i := .ok i
  prevind _ i _ := .ok i
  nextind _ i _ := .ok i
  lastindex _ := .ok (int 0)
  getindexSlice _ _ _ := .ok ()
  checkbounds _ _ := .ok ()
  checkboundsBool _ _ := .ok true
  boundsError _ _ := .boundsError
  stringIndexError _ _ := .boundsError
  methodError _ := .methodError
  argumentError _ := .argumentError ""
  tupleTypeError := .typeError
  isBoundsError _ := false
  characters _ := .ok []
  sameReference _ _ := true
  equalChar _ _ := true
  lessChar _ _ := false

def caseCounterexampleIter (_ : JString) :
    IterSteps JChar JuliaLean.base.strings.basic.Index UnicodeError := .fail .invalidChar

theorem caseMappingError :
    lowercaseAbstractString caseCounterexampleStringOps caseCounterexampleIter
      (charListBuilder (E := UnicodeError)) charOps caseCounterexampleUtf8proc
      JuliaLean.Strings.JStr.empty = .error .invalidChar := by
  simp [lowercaseAbstractString, mapString, mapChars, caseCounterexampleIter,
    caseCounterexampleStringOps, sizeofString, int, charListBuilder,
    JuliaLean.base.operators.max, JuliaLean.base.operators.islessReal,
    JuliaLean.base.operators.ifelseValue, Except.bind, Bind.bind]

theorem caseMappingContract_refuted : ¬ CaseMappingContract := by
  intro h
  obtain ⟨_, ⟨out, hlower⟩⟩ :=
    h.2.2 caseCounterexampleStringOps caseCounterexampleIter caseCounterexampleUtf8proc
      JuliaLean.Strings.JStr.empty
  simp [caseMappingError] at hlower

theorem iscntrlImpliesValid_refuted : ¬ IscntrlImpliesValid := by
  intro h
  have hc : iscntrl charOps (0x80000000 : JChar) = true := by decide
  have hv := h charOps (0x80000000 : JChar) hc
  have hbad : isvalidAbstractChar charOps (0x80000000 : JChar) = false := by decide
  rw [hbad] at hv
  cases hv

def alwaysNegativeIntegerOps : IntegerValidityOps Int where
  integer := { JuliaLean.base.rational.bigIntOps with toInt := fun _ => -1 }
  unsignedType := JInt .u64
  toUnsigned _ := .error (.jl (.inexactError "UInt64"))
  unsignedToNat u := u.val.toNat

theorem alwaysNegativeIntegerOps_laws : IntegerValidityLaws alwaysNegativeIntegerOps := by
  constructor
  · intro x u hn hu
    simp [alwaysNegativeIntegerOps] at hn
  · constructor
    · intro x hn hmax
      simp [alwaysNegativeIntegerOps] at hn
    · intro x hn
      rfl

theorem isvalidIntegerBoolTotal_refuted : ¬ IsvalidIntegerBoolTotal := by
  intro h
  obtain ⟨b, hb⟩ := h charOps alwaysNegativeIntegerOps
    alwaysNegativeIntegerOps_laws (0 : Int)
  simp [JuliaLean.base.strings.unicode.isvalidInteger, alwaysNegativeIntegerOps,
    Functor.map, Except.map] at hb

def changingDecomposeOps : Utf8procMapOps JString Bool where
  sizeof _ := 0
  decompose _ _ buffer _ _ := if buffer then 1 else 0
  decomposeCustom := fun {_State} _ _ _ _ _ _ state => .ok (0, state)
  null := false
  allocate _ := true
  reencode _ _ _ := 0
  resize buffer _ := buffer
  string _ _ := .ok JuliaLean.Strings.JStr.empty
  errorMessage _ := ""

theorem utf8procMapContract_refuted : ¬ Utf8procMapContract := by
  intro h
  have hfirst : utf8procDecompose changingDecomposeOps JuliaLean.Strings.JStr.empty 0 false 0
      identityTransform = .ok (0, ()) := by
    rfl
  have hsecond : utf8procDecompose changingDecomposeOps JuliaLean.Strings.JStr.empty 0
      (changingDecomposeOps.allocate (0 * 4)) 0
      ({ identityTransform with initial := () }) = .ok (1, ()) := by
    rfl
  have hfits := h.1 changingDecomposeOps JuliaLean.Strings.JStr.empty 0 identityTransform 0 () 1 () hfirst hsecond
  omega

def overlengthChar : JChar := 0xe9a9a5bf

theorem isvalidScalarChar_refuted : ¬ IsvalidScalarChar := by
  intro h
  have hvalid : isvalidAbstractChar charOps overlengthChar = true := by decide
  have hproperty := (h.1 overlengthChar).mp hvalid
  rcases hproperty with ⟨_, _, u, hcode, hscalar, _⟩
  have hdecoded : codepoint_Char charBitOps overlengthChar = .ok 0x26997f := by rfl
  rw [hdecoded] at hcode
  have hu : u = (0x26997f : UInt32) := by cases hcode; rfl
  have hnotScalar : unicodeScalar (0x26997f : UInt32) = false := by decide
  rw [hu, hnotScalar] at hscalar
  cases hscalar

theorem unicodeValidityContract_refuted : ¬ UnicodeValidityContract := by
  intro h
  exact isvalidScalarChar_refuted h.2.2.1

namespace UnicodeNormalizeProofs
def normalizeWithFlags {A : Type} (kw : NormKw) (finish : Nat -> UResult A) : UResult A := do
  let mut flags := 0
  if kw.stable then flags := flags ||| UTF8PROC_STABLE
  if kw.compat then flags := flags ||| UTF8PROC_COMPAT
  if kw.decompose then
    flags := flags ||| UTF8PROC_DECOMPOSE
  else if kw.compose then
    flags := flags ||| UTF8PROC_COMPOSE
  else if kw.compat || kw.stripmark then
    throw (.argumentError "compat=true or stripmark=true require compose=true or decompose=true")
  if kw.stripignore then flags := flags ||| UTF8PROC_IGNORE
  if kw.rejectna then flags := flags ||| UTF8PROC_REJECTNA
  if boolNat kw.newline2ls + boolNat kw.newline2ps + boolNat kw.newline2lf > 1 then
    throw (.argumentError "only one newline conversion may be specified")
  if kw.newline2ls then flags := flags ||| UTF8PROC_NLF2LS
  if kw.newline2ps then flags := flags ||| UTF8PROC_NLF2PS
  if kw.newline2lf then flags := flags ||| UTF8PROC_NLF2LF
  if kw.stripcc then flags := flags ||| UTF8PROC_STRIPCC
  if kw.casefold then flags := flags ||| UTF8PROC_CASEFOLD
  if kw.lump then flags := flags ||| UTF8PROC_LUMP
  if kw.stripmark then flags := flags ||| UTF8PROC_STRIPMARK
  finish flags

set_option maxHeartbeats 10000000 in
theorem normalizeWithFlagsContract {A : Type} (kw : NormKw)
    (finish : Nat -> UResult A) :
    normalizeWithFlags kw finish =
      match normalizeError kw with
      | some message => .error (.argumentError message)
      | none => finish (normFlagsSpec kw) := by
  cases kw with
  | mk stable compat compose decompose stripignore rejectna newline2ls newline2ps newline2lf
      stripcc casefold lump stripmark =>
      cases stable <;> cases compat <;> cases compose <;> cases decompose <;>
      cases stripignore <;> cases rejectna <;> cases newline2ls <;> cases newline2ps <;>
      cases newline2lf <;> cases stripcc <;> cases casefold <;> cases lump <;>
      cases stripmark <;>
      simp [normalizeWithFlags, normalizeError, normFlagsSpec, boolNat,
        Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, Nat.or_assoc, Nat.or_comm]

theorem normalizeEqWithFlags {S B : Type} (ops : Utf8procMapOps JString B)
    (toString : S -> UResult JString) (s : S) (kw : NormKw) (transform : CharTransform) :
    normalize ops toString s kw transform =
      normalizeWithFlags kw (fun flags =>
        utf8proc_mapAbstract ops toString s (Int.ofNat flags) transform) := by
  rfl

theorem normalizeOptionsContract_proven : NormalizeOptionsContract := by
  intro S B ops toString s kw transform
  rw [normalizeEqWithFlags]
  cases h : normalizeError kw <;> simp [normalizeWithFlagsContract, h]

end UnicodeNormalizeProofs
namespace UnicodeGraphemes

private theorem graphemeLengthLoop_matches {C : Type} (charOps : CharOps C) (P : Utf8proc) :
    ∀ (steps : IterSteps C JuliaLean.base.strings.basic.Index UnicodeError)
      chars c0 (state : Int32) count,
      collectIterSteps steps = .ok chars →
      graphemeLengthLoop charOps P steps c0 state count =
        graphemeCountSpec charOps P chars c0 state count := by
  intro steps
  induction steps with
  | done =>
      intro chars c0 state count h
      simp [collectIterSteps] at h
      subst chars
      simp [graphemeLengthLoop, graphemeCountSpec]
  | fail error =>
      intro chars c0 state count h
      simp [collectIterSteps] at h
  | yield c iterState next ih =>
      intro chars c0 state count h
      cases htail : collectIterSteps (next iterState) with
      | error error =>
          simp [collectIterSteps, htail, Functor.map, Except.map,
            Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      | ok rest =>
          have hchars : chars = c :: rest := by
            simpa [collectIterSteps, htail, Functor.map, Except.map,
              Bind.bind, Except.bind, Pure.pure, Except.pure] using h.symm
          subst chars
          cases hb : isgraphemebreakBang charOps P state c0 c with
          | error error =>
              simp [graphemeLengthLoop, graphemeCountSpec, hb, htail,
                Bind.bind, Except.bind, Pure.pure, Except.pure]
          | ok result =>
              rcases result with ⟨breaks, stateNext⟩
              simp [graphemeLengthLoop, graphemeCountSpec, hb,
                ih iterState rest c stateNext
                  (count + JInt.lit .i64 (if breaks then 1 else 0)) htail,
                Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem graphemeBreakProperties :
    (∀ {C : Type} (charOps : CharOps C) (P : Utf8proc) c1 c2,
      (charOps.malformed c1 = true ∨ charOps.malformed c2 = true) →
        isgraphemebreak charOps P c1 c2 = .ok true) ∧
    (∀ {C : Type} (charOps : CharOps C) (P : Utf8proc) state c1 c2,
      (charOps.malformed c1 = true ∨ charOps.malformed c2 = true) →
        isgraphemebreakBang charOps P state c1 c2 = .ok (true, 0)) ∧
    (∀ {C : Type} (charOps : CharOps C) (P : Utf8proc) c1 c2 u1 u2,
      charOps.malformed c1 = false → charOps.malformed c2 = false →
      charOps.toUInt32 c1 = .ok u1 → charOps.toUInt32 c2 = .ok u2 →
        isgraphemebreak charOps P c1 c2 = .ok (P.graphemeBreak u1 u2)) ∧
    (∀ {C : Type} (charOps : CharOps C) (P : Utf8proc) state c1 c2 u1 u2,
      charOps.malformed c1 = false → charOps.malformed c2 = false →
      charOps.toUInt32 c1 = .ok u1 → charOps.toUInt32 c2 = .ok u2 →
        isgraphemebreakBang charOps P state c1 c2 =
          .ok (P.graphemeBreakStateful state u1 u2)) := by
  constructor
  · intro C charOps P c1 c2 h
    rcases h with h1 | h2
    · simp [isgraphemebreak, h1, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [isgraphemebreak, h2, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · constructor
    · intro C charOps P state c1 c2 h
      rcases h with h1 | h2
      · simp [isgraphemebreakBang, h1, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · simp [isgraphemebreakBang, h2, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · constructor
      · intro C charOps P c1 c2 u1 u2 h1 h2 hu1 hu2
        simp [isgraphemebreak, h1, h2, hu1, hu2, liftChar,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      · intro C charOps P state c1 c2 u1 u2 h1 h2 hu1 hu2
        simp [isgraphemebreakBang, h1, h2, hu1, hu2, liftChar,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

private theorem graphemeLengthProperties :
    (∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
        (charOps : AbstractCharOps C) (P : Utf8proc) (g : GraphemeIterator S)
        (chars : List C),
        collectIterSteps (ops.iterateChars g.s) = .ok chars →
        lengthGraphemeIterator ops charOps P g =
          graphemeCountSpec charOps P chars (ops.zeroChar g.s) 0 (JInt.lit .i64 0)) ∧
    (∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
        (charOps : AbstractCharOps C) (P : Utf8proc) (g : GraphemeIterator S)
        (error : UnicodeError),
        ops.iterateChars g.s = .fail error →
        lengthGraphemeIterator ops charOps P g = .error error) := by
  constructor
  · intro S C Sub ops charOps P g chars h
    unfold lengthGraphemeIterator
    exact graphemeLengthLoop_matches charOps P (ops.iterateChars g.s) chars
      (ops.zeroChar g.s) 0 (JInt.lit .i64 0) h
  · intro S C Sub ops charOps P g error h
    simp [lengthGraphemeIterator, graphemeLengthLoop, h]

private theorem graphemeIteratorEndContract :
    ∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
      (charOps : AbstractCharOps C) (P : Utf8proc) (s : S)
      (stateInput : Option (Int32 × _root_.JuliaLean.base.strings.basic.Index))
      (state : Int32) (i : _root_.JuliaLean.base.strings.basic.Index),
      GraphemeStart ops s stateInput state i →
      ops.iterateAt s i = .ok none →
      iterateGraphemeIterator ops charOps P (graphemes s) stateInput =
        some (.ok none) := by
  intro S C Sub ops charOps P s stateInput state i hstart hAt
  cases stateInput with
  | none =>
      rcases hstart with ⟨hstate, hi⟩
      subst state
      subst i
      simp [iterateGraphemeIterator, graphemes, hAt]
  | some pair =>
      rcases pair with ⟨state0, i0⟩
      rcases hstart with ⟨hstate, hi⟩
      subst state
      subst i
      simp [iterateGraphemeIterator, graphemes, hAt]

private theorem graphemeIdentityProperties :
    (∀ {S : Type} (s : S), (graphemes s).s = s) ∧
    (∀ (subStringType : Type → Type) (S : Type),
      eltypeGrapheme subStringType S = subStringType S ∧
      eltypeGraphemeSubString subStringType S = subStringType S) := by
  constructor
  · intro S s
    rfl
  · intro subStringType S
    exact ⟨rfl, rfl⟩

private theorem graphemePresentationContract_proven : GraphemePresentationContract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S equal g1 g2
    rfl
  · intro S hashString g h
    rfl
  · intro S less g1 g2
    rfl
  · intro S IO C Sub ops charOps P typeName string toString print io g len hlen
    simp [showGraphemeIterator, hlen, Bind.bind, Except.bind, Pure.pure, Except.pure]
private theorem graphemeIterLoop_matches
    {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
    (charOps : CharOps C) (P : Utf8proc) (s : S) :
    ∀ (steps : List (C × JuliaLean.base.strings.basic.Index)) c0 state j k
      stateFinal jFinal next,
      GraphemeAccessTrace ops s k steps →
      graphemeRunSpec charOps P steps c0 state j k =
        .ok (stateFinal, jFinal, next) →
      graphemeIterLoop ops charOps P s state c0 j k =
        some (.ok (stateFinal, jFinal, next)) := by
  intro steps
  induction steps with
  | nil =>
      intro c0 state j k stateFinal jFinal next htrace hrun
      have hafter : (ops.ncodeunits s).val < k.val := htrace
      simp [graphemeRunSpec] at hrun
      rcases hrun with ⟨rfl, rfl, rfl⟩
      have hstop : ¬ k.val ≤ (ops.ncodeunits s).val := by omega
      rw [graphemeIterLoop.eq_1]
      simp only [if_neg hstop]
  | cons pair rest ih =>
      rcases pair with ⟨c, ell⟩
      intro c0 state j k stateFinal jFinal next htrace hrun
      rcases htrace with ⟨hbefore, hAt, htail⟩
      have hbefore' : k.val ≤ (ops.ncodeunits s).val := hbefore
      cases hb : isgraphemebreakBang charOps P state c0 c with
      | error error =>
          simp [graphemeRunSpec, hb, Bind.bind, Except.bind, Pure.pure, Except.pure] at hrun
      | ok result =>
          rcases result with ⟨breaks, stateNext⟩
          cases breaks
          · have htailRun :
                graphemeRunSpec charOps P rest c stateNext k ell =
                  .ok (stateFinal, jFinal, next) := by
              simpa [graphemeRunSpec, hb, Bind.bind, Except.bind, Pure.pure, Except.pure] using hrun
            have hloop := ih c stateNext k ell stateFinal jFinal next htail htailRun
            rw [graphemeIterLoop.eq_1]
            simpa only [if_pos hbefore', hAt, hb] using hloop
          · have htuple : (stateNext, j, k) = (stateFinal, jFinal, next) := by
              simpa [graphemeRunSpec, hb, Bind.bind, Except.bind, Pure.pure, Except.pure] using hrun
            cases htuple
            rw [graphemeIterLoop.eq_1]
            simp only [if_pos hbefore', hAt, hb]

private theorem graphemeIteratorRunContract :
    ∀ {S C Sub : Type} (ops : GraphemeStringOps S C Sub)
      (charOps : CharOps C) (P : Utf8proc) (s : S)
      (stateInput : Option (Int32 × JuliaLean.base.strings.basic.Index))
      (state : Int32) (i : JuliaLean.base.strings.basic.Index) (c0 : C)
      (k : JuliaLean.base.strings.basic.Index)
      (steps : List (C × JuliaLean.base.strings.basic.Index))
      (stateFinal : Int32) (j next : JuliaLean.base.strings.basic.Index) (sub : Sub),
      GraphemeStart ops s stateInput state i →
      ops.iterateAt s i = .ok (some (c0, k)) →
      GraphemeAccessTrace ops s k steps →
      graphemeRunSpec charOps P steps c0 state i k = .ok (stateFinal, j, next) →
      ops.substring s i j = .ok sub →
      iterateGraphemeIterator ops charOps P (graphemes s) stateInput =
        some (.ok (some (sub, (stateFinal, next)))) := by
  intro S C Sub ops charOps P s stateInput state i c0 k steps stateFinal j next sub
    hstart hFirst hTrace hRun hSub
  have hloop := graphemeIterLoop_matches ops charOps P s steps c0 state i k
    stateFinal j next hTrace hRun
  cases stateInput with
  | none =>
      rcases hstart with ⟨hstate, hi⟩
      subst state
      subst i
      simp [iterateGraphemeIterator, graphemes, hFirst, hloop, hSub]
  | some pair =>
      rcases pair with ⟨state0, i0⟩
      rcases hstart with ⟨hstate, hi⟩
      subst state
      subst i
      simp [iterateGraphemeIterator, graphemes, hFirst, hloop, hSub]

private theorem graphemeIteratorContract_proven : GraphemeIteratorContract := by
  obtain ⟨hbreak, hbreakBang, hbreakCodepoint, hbreakBangCodepoint⟩ :=
    graphemeBreakProperties
  obtain ⟨hlength, hlengthError⟩ := graphemeLengthProperties
  obtain ⟨hidentity, heltype⟩ := graphemeIdentityProperties
  exact ⟨hbreak, hbreakBang, hbreakCodepoint, hbreakBangCodepoint, hlength,
    hlengthError, graphemeIteratorEndContract, graphemeIteratorRunContract,
    hidentity, heltype⟩

theorem graphemesContract_proven : GraphemesContract :=
  ⟨graphemeIteratorContract_proven, graphemePresentationContract_proven⟩
end UnicodeGraphemes

namespace UnicodeConstructedValidityProofs

open JuliaLean.base.int JuliaLean.Proofs.base.int


theorem jUInt32_pattern (c : UInt32) : pattern (jUInt32 c) = c.toNat := by
  have hval : (jUInt32 c).val = Int.ofNat c.toNat := by
    rw [jUInt32]
    change wrapInt .u32 (Int.ofNat c.toNat) = _
    apply wrapInt_of_inRange
    have hc := UInt32.toNat_lt c
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  rw [pattern_of_unsigned (by decide : IntTy.u32.signed = false), hval]
  rfl

theorem not_toNat (c : UInt32) : (~~~c).toNat = 4294967295 - c.toNat := by
  rw [UInt32.toNat_not]
  rfl

theorem leadingOnes_val (c : UInt32) :
    (leadingOnesUInt32 c).val = Int.ofNat (JuliaLean.Strings.clo32 c) := by
  rw [leadingOnesUInt32, leading_ones_Integer, leading_zeros_val, pattern_bnot, jUInt32_pattern]
  have hb : IntTy.u32.bits = 32 := rfl
  rw [hb]
  have hc := UInt32.toNat_lt c
  have hnot := not_toNat c
  unfold JuliaLean.Strings.clo32 JuliaLean.Strings.clz32
  have hp : 2 ^ 32 - 1 - c.toNat = 4294967295 - c.toNat := rfl
  rw [hp]
  by_cases h0 : 4294967295 - c.toNat = 0
  · have hz : ~~~c = 0 := UInt32.toNat_inj.mp (by rw [hnot, UInt32.toNat_zero]; exact h0)
    rw [if_pos h0, if_pos hz]
    rfl
  · have hz : ¬ ~~~c = 0 := by
      intro h
      have h' := congrArg UInt32.toNat h
      rw [hnot, UInt32.toNat_zero] at h'
      exact h0 h'
    rw [if_neg h0, if_neg hz, hnot]
    simp only [Int.ofNat_eq_coe]
    omega

theorem findCtz : ∀ (n x : Nat),
    ((List.range n).find? (fun i => x.testBit i)).getD n = JuliaLean.Strings.ctzAux x n
  | 0, _ => rfl
  | n + 1, x => by
    have ih := findCtz n (x / 2)
    have hfun : ((fun i => x.testBit i) ∘ Nat.succ) = (fun i => (x / 2).testBit i) := by
      funext i
      simp [Function.comp, Nat.testBit_succ]
    rw [List.range_succ_eq_map, List.find?_cons, List.find?_map, hfun]
    unfold JuliaLean.Strings.ctzAux
    by_cases hx : x % 2 = 1
    · have hb : x.testBit 0 = true := by rw [Nat.testBit_zero]; simp [hx]
      rw [hb, if_pos hx]
      rfl
    · have hb : x.testBit 0 = false := by rw [Nat.testBit_zero]; simp [hx]
      rw [hb, if_neg hx]
      cases h : (List.range n).find? (fun i => (x / 2).testBit i) with
      | none =>
          rw [h] at ih
          simp only [Option.map_none, Option.getD_none] at ih ⊢
          omega
      | some v =>
          rw [h] at ih
          simp only [Option.map_some, Option.getD_some] at ih ⊢
          omega

theorem ctz32_eq (c : UInt32) : JuliaLean.Strings.ctz32 c = JuliaLean.Strings.ctzAux c.toNat 32 := by
  unfold JuliaLean.Strings.ctz32
  split
  · next h => subst h; rfl
  · rfl

theorem ctz32_le (c : UInt32) : JuliaLean.Strings.ctz32 c ≤ 32 := by
  rw [ctz32_eq]
  exact JuliaLean.MissingChar.CharPf.ctzAux_le 32 c.toNat

theorem trailing_lit (c : UInt32) :
    trailingZerosUInt32 c = JInt.lit .i64 (Int.ofNat (JuliaLean.Strings.ctz32 c)) := by
  apply jint_eq
  rw [trailingZerosUInt32, trailing_zeros_val, jUInt32_pattern]
  have hb : IntTy.u32.bits = 32 := rfl
  rw [hb, findCtz, ← ctz32_eq]
  have hle := ctz32_le c
  change _ = wrapInt .i64 _
  rw [wrapInt_of_inRange]
  · rfl
  · simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega

theorem band56 : ∀ t : Fin 33,
    band (JInt.lit .i64 (Int.ofNat t.val)) (JInt.lit .i64 56) =
      JInt.lit .i64 (Int.ofNat (JuliaLean.Strings.land56 t.val)) := by
  decide

theorem land56_le (t : Nat) : JuliaLean.Strings.land56 t ≤ t := Nat.and_le_left

theorem litVal (n : Nat) (h : n ≤ 64) : (JInt.lit .i64 (Int.ofNat n)).val = Int.ofNat n := by
  change wrapInt .i64 _ = _
  apply wrapInt_of_inRange
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  omega

private theorem intBeq (a b : Int) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

theorem ismalformed_bridge (c : UInt32) :
    ismalformed_Char charBitOps c = JuliaLean.Strings.ismalformed c := by
  have hl := leadingOnes_val c
  have ht := trailing_lit c
  have hle := ctz32_le c
  have hband := band56 ⟨JuliaLean.Strings.ctz32 c, by omega⟩
  have hl56 := land56_le (JuliaLean.Strings.ctz32 c)
  have hv := litVal (JuliaLean.Strings.land56 (JuliaLean.Strings.ctz32 c)) (by omega)
  unfold ismalformed_Char JuliaLean.Strings.ismalformed
  dsimp only [charBitOps]
  rw [hl, ht, hband, hv]
  have hushr : ∀ x k, JuliaLean.base.char.ushr32 x k = JuliaLean.Strings.ushr32 x k := fun _ _ => rfl
  simp only [hushr, intBeq, Int.mul_comm, Int.ofNat_eq_coe, Int.toNat_natCast]

theorem isoverlong_bridge (c : UInt32) :
    isoverlong_Char c = JuliaLean.Strings.isoverlong c := by
  unfold isoverlong_Char is_overlong_enc JuliaLean.Strings.isoverlong JuliaLean.Strings.isOverlongEnc
  rfl

theorem shl32_eq (x : UInt32) (k : Nat) (hk : k < 32) : shl32 x k = x <<< UInt32.ofNat k := by
  unfold shl32
  rw [if_pos hk]

theorem shlZero (x : UInt32) : x <<< (0 : UInt32) = x := by
  apply UInt32.toNat_inj.mp
  rw [JuliaLean.MissingChar.CharPf.shl0, Nat.mul_one]
  exact Nat.mod_eq_of_lt (UInt32.toNat_lt x)

theorem shlZero' (x : UInt32) : x <<< UInt32.ofNat 0 = x := shlZero x

theorem charUInt32_old (u c : UInt32) (h : char_UInt32 u = .ok c) :
    JuliaLean.Strings.charOfU32 u = .ok c := by
  unfold char_UInt32 at h
  unfold JuliaLean.Strings.charOfU32
  by_cases h1 : u < 0x80
  · simp only [h1, if_true] at h ⊢
    rw [shl32_eq u 24 (by decide)] at h
    first
      | (have hc := Except.ok.inj h; subst hc; rfl)
      | (subst h; rfl)
  · by_cases h2 : u < 0x00200000
    · simp only [h1, h2, if_false, if_true] at h ⊢
      simp only [shl32_eq _ _ (by decide : (0 : Nat) < 32), shl32_eq _ _ (by decide : (2 : Nat) < 32),
        shl32_eq _ _ (by decide : (4 : Nat) < 32), shl32_eq _ _ (by decide : (6 : Nat) < 32),
        shl32_eq _ _ (by decide : (16 : Nat) < 32), shl32_eq _ _ (by decide : (8 : Nat) < 32)] at h
      simp only [decide_true, Bool.not_true, Bool.false_eq_true, if_false, shlZero, shlZero'] at h ⊢
      first
        | (have hc := Except.ok.inj h; subst hc; rfl)
        | (subst h; rfl)
    · simp only [h1, h2, if_false] at h
      cases h

theorem isvalidConstructedAgreement_proven : IsvalidConstructedAgreement := by
  intro u c h
  have hold := charUInt32_old u c h
  have hv := JuliaLean.MissingChar.isvalidCharCodepoint_proven u c hold
  have hm : charOps.malformed c = JuliaLean.Strings.ismalformed c := by
    dsimp only [charOps]
    exact ismalformed_bridge c
  have ho : charOps.overlong c = JuliaLean.Strings.isoverlong c := by
    dsimp only [charOps]
    exact isoverlong_bridge c
  have hbr : isvalidAbstractChar charOps c = JuliaLean.Strings.isvalidChar c := by
    unfold isvalidAbstractChar
    simp only [Id.run, hm, ho]
    dsimp only [charOps]
    rfl
  rw [hbr, hv]
  rfl

end UnicodeConstructedValidityProofs

namespace UnicodeCategoryProofs

/-! Proofs of `CategoryContract` and `CategoryStringsSafe`. The `Char` table-access equations
are proved for an arbitrary operations record, so the kernel never evaluates the category
code of a symbolic `Char`. -/

theorem categoryStringsGenericSpec_proven : CategoryStringsGenericSpec := by
  intro C I charOps integerOps P toUInt32
  constructor
  · intro value error hcode
    unfold category_string
    rw [hcode]
    rfl
  · intro value category hcode
    unfold category_string
    rw [hcode]
    rfl

theorem categoryCodeSpec_proven : CategoryCodeSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro I integerOps toUInt32 P x u _ hle hu
    unfold category_code_Integer
    rw [if_pos hle, hu]
    rfl
  · intro I integerOps toUInt32 P x hgt
    unfold category_code_Integer
    rw [if_neg (by omega)]
    rfl
  · intro I integerOps toUInt32 P x error hle herr
    unfold category_code_Integer
    rw [if_pos hle, herr]
    rfl
  · intro C charOps P c hmal
    unfold category_code_AbstractChar
    rw [if_pos hmal]
  · intro C charOps P c hmal
    unfold category_code_AbstractChar category_code_Integer
    rw [if_neg (by simp [hmal])]
    by_cases hle : (charOps.unsafeCodepoint c).toNat ≤ 0x10ffff
    · rw [if_pos (by simp only [Int.ofNat_eq_coe]; omega), if_pos hle]
      rfl
    · rw [if_neg (by simp only [Int.ofNat_eq_coe]; omega), if_neg hle]
      rfl

private theorem categoryStringsLength : categoryStrings.length = 32 := rfl

theorem categoryCodeIndexContract_proven : CategoryCodeIndexContract := by
  intro C charOps P hlaws value category hcode
  rw [categoryStringsLength]
  unfold category_code_AbstractChar category_code_Integer at hcode
  by_cases hmal : charOps.malformed value = true
  · rw [if_pos hmal] at hcode
    cases hcode
    decide
  · rw [if_neg hmal] at hcode
    by_cases hle : (charOps.unsafeCodepoint value).toNat ≤ 0x10ffff
    · rw [if_pos (by simp only [Int.ofNat_eq_coe]; omega)] at hcode
      cases hcode
      have hu : charOps.unsafeCodepoint value ≤ 0x10ffff := by
        rw [UInt32.le_iff_toNat_le]
        exact hle
      obtain ⟨h0, h29⟩ := hlaws.1 _ hu
      refine ⟨h0, ?_⟩
      omega
    · rw [if_neg (by simp only [Int.ofNat_eq_coe]; omega)] at hcode
      cases hcode
      decide

theorem categoryAbbreviationSpec_proven : CategoryAbbreviationSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C charOps P c hmal
    unfold category_abbrev_AbstractChar
    rw [if_pos hmal]
    rfl
  · intro C charOps P c hmal hle
    unfold category_abbrev_AbstractChar
    rw [if_neg (by simp [hmal]), if_pos (by simp [hle])]
    rfl
  · intro C charOps P c hmal hle
    unfold category_abbrev_AbstractChar
    rw [if_neg (by simp [hmal]), if_neg (by simp [hle])]
    cases h : charOps.toUInt32 c with
    | ok u => rfl
    | error e => cases e <;> rfl
  · intro P c hmal
    unfold category_abbrev_Char
    rw [if_pos hmal]
  · intro P c hmal hgt
    unfold category_abbrev_Char
    rw [if_neg (by simp [hmal]), if_pos (by simpa using hgt)]
  · intro P c hmal hle
    unfold category_abbrev_Char
    rw [if_neg (by simp [hmal]), if_neg (by simpa using hle)]

theorem categoryStringCharOk (ops : CharOps JChar) (P : Utf8proc)
    (bounds : CategoryCodeBounds (category_code_AbstractChar ops P)) (c : JChar) (k : Int)
    (hcode : category_code_AbstractChar ops P c = .ok k) :
    category_string_Char ops P bounds c = .ok (categoryStrings.get ⟨k.toNat, (bounds c k hcode).2⟩) := by
  unfold category_string_Char
  split
  · next e hb => cases hb.symm.trans hcode
  · next v hb =>
      have hv : v = k := Except.ok.inj (hb.symm.trans hcode)
      subst hv
      rfl

theorem categoryStringCharError (ops : CharOps JChar) (P : Utf8proc)
    (bounds : CategoryCodeBounds (category_code_AbstractChar ops P)) (c : JChar)
    (e : UnicodeError) (hcode : category_code_AbstractChar ops P c = .error e) :
    category_string_Char ops P bounds c = .error e := by
  unfold category_string_Char
  split
  · next e' hb =>
      cases hb.symm.trans hcode
      rfl
  · next v hb => cases hb.symm.trans hcode

theorem categoryStringsCharSpec_proven : CategoryStringsCharSpec := fun P bounds _ =>
  ⟨fun c e h => categoryStringCharError charOps P bounds c e h,
    fun c k h => categoryStringCharOk charOps P bounds c k h⟩

theorem categoryStringsSafe_proven : CategoryStringsSafe :=
  ⟨categoryStringsGenericSpec_proven, categoryStringsCharSpec_proven⟩

theorem categoryContract_proven : CategoryContract :=
  ⟨categoryCodeSpec_proven, categoryCodeIndexContract_proven,
    categoryAbbreviationSpec_proven, categoryStringsSafe_proven⟩

end UnicodeCategoryProofs

def provenEntry (value : Entry) (thmName : Lean.Name) : Entry :=
  { value with status := .proven, thm := some thmName }

def refutedEntry (value : Entry) (thmName : Lean.Name) (issue : String) : Entry :=
  { value with status := .refuted, thm := some thmName, issue := issue }

/-- Pending statements for the source-mirrored Unicode methods. -/
def entry (id : String) (juliaFns : List String) (statement source : String)
    (property : Lean.Name) (notes : String := "") : Entry :=
  { id := id, juliaFile := "base/strings/unicode.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo, prop := property,
    thm := none, notes := notes }

end JuliaLean.Proofs.base.strings.unicode

/-! Partial results for the frozen titlecase contract. -/

namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean
open JuliaLean.base.strings.basic
open JuliaLean.base.strings.unicode
open JuliaLean.Proofs.base.strings.unicode

/-- The second conjunct of the requested contract: an initial iterator error
is propagated after successful buffer construction. -/
theorem titlecaseString_initialIteratorError
    {S C B : Type} (ops : TitlecaseOps S C B) (charOps : AbstractCharOps C)
    (P : Utf8proc) (wordsep : C → Bool) (strict : Bool) (s : S)
    (error : UnicodeError) (buffer : B)
    (hbuffer : ops.newBuffer () = .ok buffer)
    (hiterate : ops.iterate s = .fail error) :
    titlecaseAbstractString ops charOps P wordsep strict s = .error error := by
  simp only [titlecaseAbstractString, hbuffer, hiterate, titlecaseLoop,
    Functor.map, Except.map, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Buffer-construction errors have priority in the source program. -/
theorem titlecaseString_bufferError
    {S C B : Type} (ops : TitlecaseOps S C B) (charOps : AbstractCharOps C)
    (P : Utf8proc) (wordsep : C → Bool) (strict : Bool) (s : S)
    (error : UnicodeError) (hbuffer : ops.newBuffer () = .error error) :
    titlecaseAbstractString ops charOps P wordsep strict s = .error error := by
  simp only [titlecaseAbstractString, hbuffer, Functor.map, Except.map, Bind.bind, Except.bind]

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.Proofs.base.strings.unicode
open JuliaLean.Registry

def entries : List Entry := [
  { (entry "regexunicode-titlecase-nonstrict"
    ["titlecase(::AbstractString)", "titlecase(::AbstractChar)",
      "isgraphemebreak!(::Ref{Int32}, ::AbstractChar, ::AbstractChar)"]
    "With strict=false, titlecase replaces exactly the word-initial nonseparators with titlecase(c), where a separator begins a new grapheme."
    "base/strings/unicode.jl:723-742 (titlecase docstring and loop)" ``TitlecaseStringContract) with notes := "Prop compares different fallible-callback evaluation orders without the laws needed to preserve error priority." },
  provenEntry (entry "regexunicode-normalize-options" ["normalize(::AbstractString; kwargs...)"]
    "normalize rejects incompatible keywords before utf8proc and otherwise passes the documented flag bits."
    "base/strings/unicode.jl:202-241 (keyword validation and utf8proc flags)" ``NormalizeOptionsContract)
    ``UnicodeNormalizeProofs.normalizeOptionsContract_proven,
  refutedEntry (entry "regexunicode-uppercase-malformed"
    ["uppercase(::AbstractString)", "lowercase(::AbstractString)",
      "uppercase(::AbstractChar)", "lowercase(::AbstractChar)"]
    "uppercase and lowercase return for every String."
    "base/strings/unicode.jl:318-340,676-694 (case mapping methods and docstrings)" ``CaseMappingContract
    "The retained counterexample is repro/regexunicode-uppercase-malformed.jl.") ``caseMappingContract_refuted
    "related #54343 (closed); none found (queries: issues: uppercase invalid UTF-8; issues: uppercase invalid string; issues: uppercase malformed; issues: lowercase InvalidCharError; issues: lowercase invalid UTF-8)",
  refutedEntry (entry "regexunicode-iscntrl-malformed" ["iscntrl(::AbstractChar)"]
    "iscntrl(c) implies a valid character for every AbstractChar."
    "base/strings/unicode.jl:568 (iscntrl definition)"
    ``IscntrlImpliesValid "The retained counterexample is repro/regexunicode-iscntrl-malformed.jl.") ``iscntrlImpliesValid_refuted
    "none found (queries: issues: iscntrl; issues: iscntrl malformed)",
  refutedEntry (entry "regexunicode-isvalid-char-negative" ["isvalid(::Type{<:AbstractChar}, ::Integer)"]
    "isvalid(T, x) returns a Bool for every Integer x."
    "base/strings/unicode.jl:60 (integer conversion to Unsigned)"
    ``IsvalidIntegerBoolTotal "The negative conversion counterexample is retained in repro/missingchar-isvalid-char-negative.jl.") ``isvalidIntegerBoolTotal_refuted
    "duplicate PR #64323 (merged); queries: issues: isvalid Char InexactError; issues: isvalid Char negative",
  provenEntry (entry "missingchar-isvalid-char-negative" ["isvalid(::Type{<:AbstractChar}, ::Integer)"]
    "For any AbstractChar type and Integer representation, nonnegative values within the Unicode range are valid exactly for scalar code points; negative unsigned conversions throw InexactError."
    "base/strings/unicode.jl:59-60 (unsigned validity and integer conversion)" ``IsvalidIntegerScalarContract)
    ``UnicodeValidityProofs.isvalidIntegerScalarContract_proven,
  provenEntry (entry "missingchar-isvalid-char-codepoint"
    ["isvalid(::Char)", "isvalid(::Type{Char}, ::Unsigned)"]
    "For every accepted code point u, isvalid(Char(u)) equals isvalid(Char, u)."
    "base/strings/unicode.jl:58-59 (Char and unsigned validity)" ``IsvalidConstructedAgreement)
    ``UnicodeConstructedValidityProofs.isvalidConstructedAgreement_proven,
  provenEntry (entry "memsafety-unicode-category" ["category_string(::Char)", "category_code(::Char)"]
    "category_string indexes its 32-entry table safely for every Char, including malformed values."
    "base/strings/unicode.jl:372-403 (category range and table access)" ``CategoryStringsSafe)
    ``UnicodeCategoryProofs.categoryStringsSafe_proven,
  refutedEntry (entry "stringscovb-unicode-isvalid" ["isvalid"]
    "Character validity accepts exactly canonical UTF-8 encodings of Unicode scalar values and rejects malformed or overlong storage."
    "base/strings/unicode.jl:58-63 (validity methods)"
    ``UnicodeValidityContract "The counterexample is repro/stringscovb-unicode-isvalid.jl.") ``unicodeValidityContract_refuted
    "none found (queries: issues: ismalformed; issues: isvalid Char reinterpret; issues: isvalid char codepoint 0x10ffff; issues: ismalformed continuation bytes; prs: ismalformed)",
  refutedEntry (entry "stringscovb-normalize-impure-chartransform"
    ["utf8proc_map", "utf8proc_decompose", "utf8proc_custom_func", "utf8proc_error", "normalize"]
    "The second utf8proc decomposition never exceeds the buffer sized by the first pass, and AbstractString conversion errors propagate before mapping."
    "base/strings/unicode.jl:153-241; two-pass buffer-size invariant and AbstractString wrapper"
    ``Utf8procMapContract
    "The retained stateful-callback counterexample is repro/stringscovb-normalize-impure-chartransform.jl.") ``utf8procMapContract_refuted
    "none found (queries: issues: normalize chartransform; prs: normalize chartransform; issues: utf8proc_map; prs: utf8proc_map buffer)",
  provenEntry (entry "stringscovb-unicode-normalize" ["normalize"]
    "The four named normalization forms select their documented flags, and an unsupported name throws ArgumentError."
    "base/strings/unicode.jl:202-251 (keyword and named forms)" ``NormalizeFormContract)
    ``normalizeFormContract_proven,
  provenEntry (entry "stringscovb-unicode-textwidth" ["textwidth"]
    "Character width follows the ASCII, malformed, and utf8proc cases, and string width sums character widths in iteration order."
    "base/strings/unicode.jl:270-300 (textwidth methods)" ``TextwidthContract)
    ``UnicodeTextwidthProofs.textwidthContract_proven,
  provenEntry (entry "stringscovb-unicode-case-annotated" ["lowercase", "uppercase", "titlecase"]
    "Annotated case mappings use the character mapping and preserve every annotation."
    "base/strings/unicode.jl:321-367,677-762 (annotated mapping methods)" ``AnnotatedCaseContract)
    ``UnicodeAnnotationProofs.annotatedCaseContract_proven,
  provenEntry (entry "stringscovb-unicode-category" ["category_code", "category_abbrev", "category_string"]
    "Category lookup returns utf8proc categories, uses the malformed and too-high abbreviations, and keeps category-string indexing within the table."
    "base/strings/unicode.jl:372-405 (category wrappers)" ``CategoryContract)
    ``UnicodeCategoryProofs.categoryContract_proven,
  provenEntry (entry "stringscovb-isassigned-negative" ["isassigned"]
    "For code points, isassigned reports whether the category lies after Cn through Co; integers above 0x10ffff return false, and negative conversion errors propagate."
    "base/strings/unicode.jl:405 (assigned-category predicate)" ``IsassignedContract)
    ``UnicodeAssignedProofs.isassignedContract_proven,
  provenEntry (entry "stringscovb-unicode-predicates"
    ["islowercase", "isuppercase", "iscased", "isdigit", "isxdigit", "isspace",
      "isletter", "isnumeric", "ispunct", "isprint", "iscntrl"]
    "Unicode predicates follow utf8proc's derived properties and category ranges, with exact ASCII digit and hexadecimal ranges."
    "base/strings/unicode.jl:429-659 (character predicate methods)" ``UnicodePredicateContract)
    ``UnicodePredicateProofs.unicodePredicateContract_proven,
  provenEntry (entry "stringscovb-unicode-titlecase" ["titlecase"]
    "Annotated titlecase follows the grapheme and word-state transform, and the SubString wrapper converts then delegates."
    "base/strings/unicode.jl:745-762 (annotated titlecase methods)" ``TitlecaseAnnotatedContract)
    ``UnicodeAnnotationProofs.titlecaseAnnotatedContract_proven,
  provenEntry (entry "stringscovb-unicode-firstcase" ["uppercasefirst", "lowercasefirst"]
    "First-character case mapping preserves empty strings, changes only the first character, and annotated SubString wrappers delegate after conversion."
    "base/strings/unicode.jl:780-832 (first-character case methods)" ``FirstCaseContract)
    ``UnicodeAnnotationProofs.firstCaseContract_proven,
  provenEntry (entry "stringscovb-unicode-graphemes"
    ["isgraphemebreak", "isgraphemebreak!", "graphemes", "length", "iterate",
      "eltype", "==", "hash", "isless", "show"]
    "Grapheme breaking and iteration follow utf8proc's stateful boundaries, and iterator presentation agrees with the represented string."
    "base/strings/unicode.jl:837-896 (grapheme methods)" ``GraphemesContract)
    ``UnicodeGraphemes.graphemesContract_proven,
  refutedEntry (entry "missingchar-isvalid-overlength"
    ["isvalid(::Char)", "isvalid(::Type{<:AbstractChar}, ::Unsigned)"]
    "isvalid(Char, c) is true exactly when c stores the canonical, well-formed UTF-8 encoding of a Unicode scalar value."
    "base/strings/unicode.jl:58-59; base/char.jl:46-50 (validity definition and Char contract)"
    ``IsvalidScalarChar "The original reproducer remains at repro/missingchar-isvalid-overlength.jl.") ``isvalidScalarChar_refuted
    "none found (queries: issues: ismalformed; issues: isvalid Char reinterpret; issues: isvalid char codepoint 0x10ffff; issues: ismalformed continuation bytes; prs: ismalformed)",
]

end JuliaLean.Proofs.base.strings.unicode

