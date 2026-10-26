import JuliaLean.Strings

/-! Coverage models for `base/strings/basic.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Basic

open JuliaLean JuliaLean.Strings

/-- Integer fallbacks at lines 107-108,143-144,156-157. -/
def integerFallback {α : Type} (isMachineInt : Bool) (dispatch : Int → SJl α) (i : Int) : SJl α :=
  if isMachineInt then .error (.jl (.methodError "missing Int method")) else dispatch i

def IntegerFallbacks : Prop :=
  ∀ (α : Type) isInt (codeunit isvalid iterate : Int → SJl α) i,
    integerFallback isInt codeunit i = (if isInt then .error (.jl (.methodError "missing Int method")) else codeunit i) ∧
    integerFallback isInt isvalid i = (if isInt then .error (.jl (.methodError "missing Int method")) else isvalid i) ∧
    integerFallback isInt iterate i = (if isInt then .error (.jl (.methodError "missing Int method")) else iterate i)

theorem integerFallbacks : IntegerFallbacks := by
  unfold IntegerFallbacks
  intros
  constructor
  · rfl
  constructor <;> rfl

/-- Generic scalar methods at lines 161,178-228. -/
def eltypeString : String := "Char"
def sizeof (ncu unitBytes : Int) : Int := ncu * unitBytes
def firstindex : Int := 1
def lastindex (this : Int → Int) (ncu : Int) : Int := this ncu
def isempty (ncu : Int) : Bool := ncu == 0
def first {α : Type} (get : Int → SJl α) := get firstindex
def getindex {α : Type} (inbounds valid : Int → Bool) (iter : Int → α) (i : Int) : SJl α :=
  if !inbounds i then .error (.jl .boundsError)
  else if valid i then .ok (iter i) else .error (.stringIndexError i)
def getindexColon {α : Type} (s : α) : α := s
def getindexVector {α : Type} (get : Int → α) (is : List Int) : List α := is.map get
def getindexBool : SJl Unit := .error (.jl (.argumentError "logical indexing not supported for strings"))
def getDefault {α : Type} (inbounds : Int → Bool) (get : Int → α) (i : Int) (default : α) : α :=
  if inbounds i then get i else default
def checkboundsIndex (ncu i : Int) : Bool := decide (1 ≤ i ∧ i ≤ ncu)
def checkboundsRange (ncu lo hi : Int) : Bool := hi < lo || decide (1 ≤ lo ∧ hi ≤ ncu)
def checkboundsAll (check : Int → Bool) (is : List Int) : Bool := is.all check
def checkboundsThrow (ok : Bool) : Jl Unit := if ok then .ok () else .error .boundsError
def stringEmpty : List UInt8 := []
def stringIdentity {α : Type} (s : α) : α := s
def vectorBytes (toString : α → List UInt8) (s : α) : List UInt8 := toString s
def vectorChars (collect : α → List β) (s : α) : List β := collect s
def symbolString (intern : List UInt8 → Nat) (toString : α → List UInt8) (s : α) := intern (toString s)
def symbolArgs (render : List α → List UInt8) (intern : List UInt8 → Nat) (xs : List α) := intern (render xs)
def convertIdentity {α : Type} (s : α) : α := s
def convertString (ctor : α → β) (s : α) : β := ctor s

def ScalarBasics : Prop :=
  eltypeString = "Char" ∧
  (∀ n u, sizeof n u = n * u) ∧ firstindex = 1 ∧
  (∀ this n, lastindex this n = this n) ∧ (∀ n, isempty n = (n == 0)) ∧
  (∀ (α : Type) (get : Int → SJl α), first get = get 1) ∧
  (∀ (α : Type) inb valid (iter : Int → α) i, getindex inb valid iter i =
    if !inb i then .error (.jl .boundsError) else if valid i then .ok (iter i) else .error (.stringIndexError i)) ∧
  (∀ (α : Type) (s : α), getindexColon s = s) ∧
  (∀ (α : Type) get is, getindexVector (α := α) get is = is.map get) ∧
  getindexBool = .error (.jl (.argumentError "logical indexing not supported for strings")) ∧
  (∀ (α : Type) inb get i (d : α), getDefault inb get i d = if inb i then get i else d) ∧
  (∀ n i, checkboundsIndex n i = decide (1 ≤ i ∧ i ≤ n)) ∧
  (∀ n lo hi, checkboundsRange n lo hi = (hi < lo || decide (1 ≤ lo ∧ hi ≤ n))) ∧
  (∀ check is, checkboundsAll check is = is.all check) ∧
  (∀ ok, checkboundsThrow ok = if ok then .ok () else .error .boundsError) ∧
  stringEmpty = [] ∧
  (∀ (α : Type) (s : α), stringIdentity s = s) ∧
  (∀ (α : Type) toString (s : α), vectorBytes toString s = toString s) ∧
  (∀ (α β : Type) collect (s : α), vectorChars (β := β) collect s = collect s) ∧
  (∀ (α : Type) intern toString (s : α), symbolString intern toString s = intern (toString s)) ∧
  (∀ (α : Type) render intern (xs : List α), symbolArgs render intern xs = intern (render xs)) ∧
  (∀ (α : Type) (s : α), convertIdentity s = s) ∧
  (∀ (α β : Type) ctor (s : α), convertString (β := β) ctor s = ctor s)

theorem scalarBasics : ScalarBasics := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- Summary, concatenation, annotation, and comparison methods; lines 232-363. -/
def summary (ncu : Nat) (typeName : String) : String :=
  (if ncu = 0 then "empty" else toString ncu ++ "-codeunit") ++ " " ++ typeName
def concat (annotated : Bool) (plain annotatedJoin : List α → β) (xs : List α) : β :=
  if annotated then annotatedJoin xs else plain xs
def oneString (empty : α) : α := empty
def isannotatedType (isBottom isAnnotatedString isAnnotatedChar : Bool) : Bool :=
  !isBottom && (isAnnotatedString || isAnnotatedChar)
def isannotatedValue (typeCheck : α → Bool) (s : α) : Bool := typeCheck s
def cmpString (a b : JStr) : Int := cmpGeneric a b
def eqString (a b : JStr) : Bool := cmpString a b == 0
def islessString (a b : JStr) : Bool := decide (cmpString a b < 0)
def cmpSymbol (strcmp : Nat → Nat → Int) (a b : Nat) : Int := Int.sign (strcmp a b)
def islessSymbol (strcmp : Nat → Nat → Int) (a b : Nat) : Bool := decide (cmpSymbol strcmp a b < 0)

def PresentationComparison : Prop :=
  (∀ n t, summary n t = (if n = 0 then "empty" else toString n ++ "-codeunit") ++ " " ++ t) ∧
  (∀ (α β : Type) ann plain annotatedJoin (xs : List α),
    concat (β := β) ann plain annotatedJoin xs = if ann then annotatedJoin xs else plain xs) ∧
  (∀ (α : Type) (x : α), oneString x = x) ∧
  (∀ b s c, isannotatedType b s c = (!b && (s || c))) ∧
  (∀ (α : Type) f (x : α), isannotatedValue f x = f x) ∧
  (∀ a b, cmpString a b = cmpGeneric a b) ∧
  (∀ a b, eqString a b = (cmpGeneric a b == 0)) ∧
  (∀ a b, islessString a b = decide (cmpGeneric a b < 0)) ∧
  (∀ strcmp a b, cmpSymbol strcmp a b = Int.sign (strcmp a b)) ∧
  (∀ strcmp a b, islessSymbol strcmp a b = decide (Int.sign (strcmp a b) < 0))

theorem presentationComparison : PresentationComparison := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- Generic length and index arithmetic; lines 396-573. -/
def lengthString (s : JStr) := Strings.length s
def lengthBetween (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def thisindInteger (s : JStr) (i : JInt64) := Strings.thisind s i
def previndInteger (s : JStr) (i n : JInt64) := Strings.previndN s i n
def previndOne (s : JStr) (i : JInt64) := Strings.prevind s i
def nextindInteger (s : JStr) (i n : JInt64) := Strings.nextindN s i n
def nextindOne (s : JStr) (i : JInt64) := Strings.nextind s i

def IndexArithmetic : Prop :=
  (∀ s, lengthString s = Strings.length s) ∧
  (∀ s i j, lengthBetween s i j = Strings.lengthRange s i j) ∧
  (∀ s i, thisindInteger s i = Strings.thisind s i) ∧
  (∀ s i n, previndInteger s i n = Strings.previndN s i n) ∧
  (∀ s i, previndOne s i = Strings.prevind s i) ∧
  (∀ s i n, nextindInteger s i n = Strings.nextindN s i n) ∧
  (∀ s i, nextindOne s i = Strings.nextind s i)

theorem indexArithmetic : IndexArithmetic := by
  repeat' apply And.intro
  all_goals intros <;> rfl

structure EachStringIndex where s : JStr

def keys (s : JStr) : EachStringIndex := ⟨s⟩
def eachLength (e : EachStringIndex) := Strings.length e.s
def eachFirst (_e : EachStringIndex) := ix 1
def eachLast (e : EachStringIndex) := Strings.lastindex e.s
def eachIterate (e : EachStringIndex) (state : JInt64) : Option (JInt64 × JInt64) :=
  if state.val > (Strings.ncodeunits e.s).val then none
  else match Strings.nextind e.s state with | .ok n => some (state, n) | .error _ => none
def eachEltype : String := "Int"
def isasciiChar (c : UInt32) : Bool := decide (c < 0x80)
def isasciiString (s : JStr) : Bool := Strings.isascii s
def isasciiRange (bytes : List UInt8) (first last : Int) := Strings.isasciiRange bytes first last
def isasciiChunks (chunk : Int) (bytes : List UInt8) (first last : Int) :=
  Strings.isasciiChunksLoop chunk bytes last bytes.length first
def isasciiVector (bytes : List UInt8) : Bool := bytes.all (· < 0x80)

def EachIndexAscii : Prop :=
  (∀ s, keys s = ⟨s⟩) ∧ (∀ e, eachLength e = Strings.length e.s) ∧
  (∀ e, eachFirst e = ix 1) ∧ (∀ e, eachLast e = Strings.lastindex e.s) ∧
  (∀ e st, eachIterate e st = if st.val > (Strings.ncodeunits e.s).val then none else
    match Strings.nextind e.s st with | .ok n => some (st, n) | .error _ => none) ∧
  eachEltype = "Int" ∧
  (∀ c, isasciiChar c = decide (c < 0x80)) ∧
  (∀ s, isasciiString s = Strings.isascii s) ∧
  (∀ b f l, isasciiRange b f l = Strings.isasciiRange b f l) ∧
  (∀ c b f l, isasciiChunks c b f l = Strings.isasciiChunksLoop c b l b.length f) ∧
  (∀ b, isasciiVector b = b.all (· < 0x80))

theorem eachIndexAscii : EachIndexAscii := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-- Mapping, filtering, slicing, repetition, and reverse iteration; lines 657-776. -/
def mapString (f : UInt32 → UInt32) (s : JStr) : SJl JStr := stringOfChars ((Strings.chars s).map f)
def filterString (f : UInt32 → Bool) (s : JStr) : SJl JStr := stringOfChars ((Strings.chars s).filter f)
def firstN (s : JStr) (n : JInt64) := Strings.firstN s n
def lastN (s : JStr) (n : JInt64) := Strings.lastN s n
def reverseind (this : Int → Int) (ncu i : Int) : Int := this (ncu - i + 1)
def repeatString (toString : α → JStr) (s : α) (r : JInt64) := Strings.repeatStr (toString s) r
def powerString (repeatFn : α → Int → β) (s : α) (r : Int) : β := repeatFn s r
def reverseIterate {α : Type} (first get prev : Int → α) (i : Int) : Option (α × α) :=
  if i < 1 then none else some (get i, prev i)

def TransformSlices : Prop :=
  (∀ f s, mapString f s = stringOfChars ((Strings.chars s).map f)) ∧
  (∀ f s, filterString f s = stringOfChars ((Strings.chars s).filter f)) ∧
  (∀ s n, firstN s n = Strings.firstN s n) ∧ (∀ s n, lastN s n = Strings.lastN s n) ∧
  (∀ this n i, reverseind this n i = this (n - i + 1)) ∧
  (∀ (α : Type) toString (s : α) r, repeatString toString s r = Strings.repeatStr (toString s) r) ∧
  (∀ (α β : Type) repeatFn (s : α) r, powerString (β := β) repeatFn s r = repeatFn s r) ∧
  (∀ (α : Type) first get prev (i : Int), reverseIterate (α := α) first get prev i =
    if i < 1 then none else some (get i, prev i))

theorem transformSlices : TransformSlices := by
  repeat' apply And.intro
  all_goals intros <;> rfl

structure CodeUnits where bytes : List UInt8

def codeUnitsCtor (bytes : List UInt8) : CodeUnits := ⟨bytes⟩
def cuSizeof (s : CodeUnits) : Nat := s.bytes.length
def cuSize (s : CodeUnits) : Nat × Unit := (s.bytes.length, ())
def cuElsize : Nat := 1
def cuGetindex (s : CodeUnits) (i : Nat) : UInt8 := s.bytes.getD (i - 1) 0
def cuIndexStyle : String := "IndexLinear"
def cuCheckbounds (s : CodeUnits) (i : Int) : Bool := decide (1 ≤ i ∧ i ≤ s.bytes.length)
def cuDataids (id : List UInt8 → List Nat) (s : CodeUnits) := id s.bytes
def cuWrite (write : List UInt8 → Nat) (s : CodeUnits) := write s.bytes
def cuCconvert (convert : List UInt8 → Nat) (s : CodeUnits) := convert s.bytes
def cuSimilar (make : Nat → List UInt8) (n : Nat) := make n
def codeunits (bytes : List UInt8) : CodeUnits := codeUnitsCtor bytes
def splitRest (split : JStr → Int → JStr × JSub) (s : JStr) (n : Int) := split s n

def CodeUnitWrappers : Prop :=
  (∀ b, codeUnitsCtor b = ⟨b⟩) ∧ (∀ s, cuSizeof s = s.bytes.length) ∧
  (∀ s, cuSize s = (s.bytes.length, ())) ∧ cuElsize = 1 ∧
  (∀ s i, cuGetindex s i = s.bytes.getD (i - 1) 0) ∧ cuIndexStyle = "IndexLinear" ∧
  (∀ s i, cuCheckbounds s i = decide (1 ≤ i ∧ i ≤ s.bytes.length)) ∧
  (∀ id s, cuDataids id s = id s.bytes) ∧ (∀ write s, cuWrite write s = write s.bytes) ∧
  (∀ convert s, cuCconvert convert s = convert s.bytes) ∧
  (∀ make n, cuSimilar make n = make n) ∧ (∀ b, codeunits b = ⟨b⟩) ∧
  (∀ split s n, splitRest split s n = split s n)

theorem codeUnitWrappers : CodeUnitWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.Basic
