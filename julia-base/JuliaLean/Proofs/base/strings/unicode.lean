import JuliaLean.base.strings.unicode
import JuliaLean.base.strings.basic
import JuliaLean.base.int
import JuliaLean.base.rational
import JuliaLean.Registry.Types

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
  toUnsigned x := liftJl (JInt.convert .u64 x)
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
      category_string_Char P charCodeBounds c = .error error) ∧
    (∀ c category (h : category_code_AbstractChar charOps P c = .ok category),
      category_string_Char P charCodeBounds c =
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
      | .error .boundsError => .error .boundsError
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
  (∀ {S C : Type}
      (characters : S → UResult (List C))
      (mapreduce : (C → UResult Int) → (Int → Int → Int) → S → Int → UResult Int)
      (charOps : CharOps C) (P : Utf8proc) (s : S) (chars : List C),
      characters s = .ok chars →
      (∀ measure, mapreduce measure (· + ·) s 0 = textwidthFold measure chars) →
      textwidthAbstractString mapreduce charOps P s =
        textwidthFold (textwidthAbstractChar charOps P) chars) ∧
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
/-- Pending statements for the source-mirrored Unicode methods. -/
def entry (id : String) (juliaFns : List String) (statement source : String)
    (property : Lean.Name) (notes : String := "") : Entry :=
  { id := id, juliaFile := "base/strings/unicode.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo, prop := property,
    thm := none, notes := notes }

def entries : List Entry := [
  entry "regexunicode-titlecase-nonstrict"
    ["titlecase(::AbstractString)", "titlecase(::AbstractChar)",
      "isgraphemebreak!(::Ref{Int32}, ::AbstractChar, ::AbstractChar)"]
    "With strict=false, titlecase replaces exactly the word-initial nonseparators with titlecase(c), where a separator begins a new grapheme."
    "base/strings/unicode.jl:723-742 (titlecase docstring and loop)" ``TitlecaseStringContract,
  entry "regexunicode-normalize-options" ["normalize(::AbstractString; kwargs...)"]
    "normalize rejects incompatible keywords before utf8proc and otherwise passes the documented flag bits."
    "base/strings/unicode.jl:202-241 (keyword validation and utf8proc flags)" ``NormalizeOptionsContract,
  entry "regexunicode-uppercase-malformed"
    ["uppercase(::AbstractString)", "lowercase(::AbstractString)",
      "uppercase(::AbstractChar)", "lowercase(::AbstractChar)"]
    "uppercase and lowercase return for every String."
    "base/strings/unicode.jl:318-340,676-694 (case mapping methods and docstrings)" ``CaseMappingContract
    "The retained counterexample is repro/regexunicode-uppercase-malformed.jl.",
  entry "regexunicode-iscntrl-malformed" ["iscntrl(::AbstractChar)"]
    "iscntrl(c) implies a valid character for every AbstractChar."
    "base/strings/unicode.jl:568 (iscntrl definition)"
    ``IscntrlImpliesValid "The retained counterexample is repro/regexunicode-iscntrl-malformed.jl.",
  entry "regexunicode-isvalid-char-negative" ["isvalid(::Type{<:AbstractChar}, ::Integer)"]
    "isvalid(T, x) returns a Bool for every Integer x."
    "base/strings/unicode.jl:60 (integer conversion to Unsigned)"
    ``IsvalidIntegerBoolTotal "The negative conversion counterexample is retained in repro/missingchar-isvalid-char-negative.jl.",
  entry "missingchar-isvalid-char-negative" ["isvalid(::Type{<:AbstractChar}, ::Integer)"]
    "For any AbstractChar type and Integer representation, nonnegative values within the Unicode range are valid exactly for scalar code points; negative unsigned conversions throw InexactError."
    "base/strings/unicode.jl:59-60 (unsigned validity and integer conversion)"
    ``IsvalidIntegerScalarContract "The negative conversion counterexample is retained in repro/missingchar-isvalid-char-negative.jl.",
  entry "missingchar-isvalid-char-codepoint"
    ["isvalid(::Char)", "isvalid(::Type{Char}, ::Unsigned)"]
    "For every accepted code point u, isvalid(Char(u)) equals isvalid(Char, u)."
    "base/strings/unicode.jl:58-59 (Char and unsigned validity)" ``IsvalidConstructedAgreement,
  entry "memsafety-unicode-category" ["category_string(::Char)", "category_code(::Char)"]
    "category_string indexes its 32-entry table safely for every Char, including malformed values."
    "base/strings/unicode.jl:372-403 (category range and table access)" ``CategoryStringsSafe,
  entry "stringscovb-unicode-isvalid" ["isvalid"]
    "Character validity accepts exactly canonical UTF-8 encodings of Unicode scalar values and rejects malformed or overlong storage."
    "base/strings/unicode.jl:58-63 (validity methods)" ``UnicodeValidityContract,
  entry "stringscovb-normalize-impure-chartransform"
    ["utf8proc_map", "utf8proc_decompose", "utf8proc_custom_func", "utf8proc_error", "normalize"]
    "The second utf8proc decomposition never exceeds the buffer sized by the first pass, and AbstractString conversion errors propagate before mapping."
    "base/strings/unicode.jl:153-241; two-pass buffer-size invariant and AbstractString wrapper"
    ``Utf8procMapContract
    "The retained stateful-callback counterexample is repro/stringscovb-normalize-impure-chartransform.jl.",
  entry "stringscovb-unicode-normalize" ["normalize"]
    "The four named normalization forms select their documented flags, and an unsupported name throws ArgumentError."
    "base/strings/unicode.jl:202-251 (keyword and named forms)" ``NormalizeFormContract,
  entry "stringscovb-unicode-textwidth" ["textwidth"]
    "Character width follows the ASCII, malformed, and utf8proc cases, and string width sums character widths in iteration order."
    "base/strings/unicode.jl:270-300 (textwidth methods)" ``TextwidthContract,
  entry "stringscovb-unicode-case-annotated" ["lowercase", "uppercase", "titlecase"]
    "Annotated case mappings use the character mapping and preserve every annotation."
    "base/strings/unicode.jl:321-367,677-762 (annotated mapping methods)" ``AnnotatedCaseContract,
  entry "stringscovb-unicode-category" ["category_code", "category_abbrev", "category_string"]
    "Category lookup returns utf8proc categories, uses the malformed and too-high abbreviations, and keeps category-string indexing within the table."
    "base/strings/unicode.jl:372-405 (category wrappers)" ``CategoryContract,
  entry "stringscovb-isassigned-negative" ["isassigned"]
    "For code points, isassigned reports whether the category lies after Cn through Co; integers above 0x10ffff return false, and negative conversion errors propagate."
    "base/strings/unicode.jl:405 (assigned-category predicate)" ``IsassignedContract
    "The retained negative-input counterexample is repro/stringscovb-isassigned-negative.jl.",
  entry "stringscovb-unicode-predicates"
    ["islowercase", "isuppercase", "iscased", "isdigit", "isxdigit", "isspace",
      "isletter", "isnumeric", "ispunct", "isprint", "iscntrl"]
    "Unicode predicates follow utf8proc's derived properties and category ranges, with exact ASCII digit and hexadecimal ranges."
    "base/strings/unicode.jl:429-659 (character predicate methods)" ``UnicodePredicateContract,
  entry "stringscovb-unicode-titlecase" ["titlecase"]
    "Annotated titlecase follows the grapheme and word-state transform, and the SubString wrapper converts then delegates."
    "base/strings/unicode.jl:745-762 (annotated titlecase methods)" ``TitlecaseAnnotatedContract,
  entry "stringscovb-unicode-firstcase" ["uppercasefirst", "lowercasefirst"]
    "First-character case mapping preserves empty strings, changes only the first character, and annotated SubString wrappers delegate after conversion."
    "base/strings/unicode.jl:780-832 (first-character case methods)" ``FirstCaseContract,
  entry "stringscovb-unicode-graphemes"
    ["isgraphemebreak", "isgraphemebreak!", "graphemes", "length", "iterate",
      "eltype", "==", "hash", "isless", "show"]
    "Grapheme breaking and iteration follow utf8proc's stateful boundaries, and iterator presentation agrees with the represented string."
    "base/strings/unicode.jl:837-896 (grapheme methods)" ``GraphemesContract,
  entry "missingchar-isvalid-overlength"
    ["isvalid(::Char)", "isvalid(::Type{<:AbstractChar}, ::Unsigned)"]
    "isvalid(Char, c) is true exactly when c stores the canonical, well-formed UTF-8 encoding of a Unicode scalar value."
    "base/strings/unicode.jl:58-59; base/char.jl:46-50 (validity definition and Char contract)"
    ``IsvalidScalarChar "The original reproducer remains at repro/missingchar-isvalid-overlength.jl."
]

end JuliaLean.Proofs.base.strings.unicode

