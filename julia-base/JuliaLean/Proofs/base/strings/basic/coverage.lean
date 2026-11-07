import JuliaLean.base.strings.basic
import JuliaLean.Proofs.base.strings.string.entries

/-! Coverage models for `base/strings/basic.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Basic

open JuliaLean JuliaLean.Strings

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
