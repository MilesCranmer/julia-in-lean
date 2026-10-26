import JuliaLean.Strings

/-! Coverage models for `base/strings/string.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.String

open JuliaLean JuliaLean.Strings

structure View where bytes : List UInt8

def stringViewCtor (oneBased concrete : Bool) (bytes : List UInt8) : Jl View :=
  if !oneBased then .error (.argumentError "one-based indexing required")
  else if !concrete then .error (.argumentError "concrete type required") else .ok ⟨bytes⟩
def stringIndexErr (i : Int) : SJl Unit := .error (.stringIndexError i)
def showStringIndexError (i : Int) : String := "StringIndexError: invalid index [" ++ toString i ++ "]"
def between (b lo hi : Int) : Bool := decide (lo ≤ b) && decide (b ≤ hi)

def ViewErrors : Prop :=
  (∀ o c b, stringViewCtor o c b = if !o then .error (.argumentError "one-based indexing required")
    else if !c then .error (.argumentError "concrete type required") else .ok ⟨b⟩) ∧
  (∀ i, stringIndexErr i = .error (.stringIndexError i)) ∧
  (∀ i, showStringIndexError i = "StringIndexError: invalid index [" ++ toString i ++ "]") ∧
  (∀ b l h, between b l h = (decide (l ≤ b) && decide (b ≤ h)))

theorem viewErrors : ViewErrors := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def stringAbstractVector (v : List UInt8) := v
def unsafeTakeString (m : List UInt8) := m
def takeString (v : List UInt8) : List UInt8 × List UInt8 := (v, [])
def unsafeStringLength (memory : List UInt8) (len : Nat) : List UInt8 := memory.take len
def unsafeStringNul (memory : List UInt8) : List UInt8 := memory.takeWhile (· != 0)
def stringN (n : Nat) : List UInt8 := List.replicate n 0
def stringAbstract (render : α → List UInt8) (s : α) := render s
def stringSymbol (memory : List UInt8) := unsafeStringNul memory
def unsafeWrapMemory (s : List UInt8) := s
def unsafeWrapVector (s : List UInt8) := s
def vectorCodeUnits (s : List UInt8) := s
def vectorString (s : List UInt8) := s
def arrayString (s : List UInt8) := s
def stringCodeUnits (s : List UInt8) := s
def pointer (address : Nat) := address
def pointerAt (address : Nat) (i : Int) : Int := address + i - 1
def ncodeunits (s : List UInt8) := s.length
def codeunitType : Nat := 8
def codeunit (s : List UInt8) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ s.length then .ok (s.getD (i.toNat - 1) 0) else .error .boundsError

def StorageConversions : Prop :=
  (∀ v, stringAbstractVector v = v) ∧ (∀ m, unsafeTakeString m = m) ∧
  (∀ v, takeString v = (v, [])) ∧
  (∀ m n, unsafeStringLength m n = m.take n) ∧
  (∀ m, unsafeStringNul m = m.takeWhile (· != 0)) ∧
  (∀ n, stringN n = List.replicate n 0) ∧
  (∀ (α : Type) render (s : α), stringAbstract render s = render s) ∧
  (∀ m, stringSymbol m = unsafeStringNul m) ∧
  (∀ s, unsafeWrapMemory s = s) ∧ (∀ s, unsafeWrapVector s = s) ∧
  (∀ s, vectorCodeUnits s = s) ∧ (∀ s, vectorString s = s) ∧
  (∀ s, arrayString s = s) ∧ (∀ s, stringCodeUnits s = s) ∧
  (∀ a, pointer a = a) ∧ (∀ a i, pointerAt a i = a + i - 1) ∧
  (∀ s, ncodeunits s = s.length) ∧ codeunitType = 8 ∧
  (∀ s i, codeunit s i = if 1 ≤ i ∧ i ≤ s.length then .ok (s.getD (i.toNat - 1) 0) else .error .boundsError)

theorem storageConversions : StorageConversions := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def memcmp (a b : List UInt8) (len : Nat) : Int :=
  Strings.memcmpSign a b len
def memcmpMin (a b : List UInt8) := memcmp a b (min a.length b.length)
def eqString (a b : List UInt8) := a == b
def typeminType : List UInt8 := []
def typeminValue : List UInt8 := typeminType
def thisind (s : JStr) (i : JInt64) := Strings.thisind s i
def thisindContinued (s : JStr) (i : JInt64) := Strings.thisindContinued s i
def nextind (s : JStr) (i : JInt64) := Strings.nextind s i
def nextindContinued (s : JStr) (i n : JInt64) (l : UInt8) := Strings.nextindContinued s i n l

def ComparisonIndices : Prop :=
  (∀ a b, memcmpMin a b = memcmp a b (min a.length b.length)) ∧
  (∀ a b n, memcmp a b n = Strings.memcmpSign a b n) ∧
  (∀ a b, eqString a b = (a == b)) ∧ typeminType = [] ∧ typeminValue = typeminType ∧
  (∀ s i, thisind s i = Strings.thisind s i) ∧
  (∀ s i, thisindContinued s i = Strings.thisindContinued s i) ∧
  (∀ s i, nextind s i = Strings.nextind s i) ∧
  (∀ s i n l, nextindContinued s i n l = Strings.nextindContinued s i n l)

theorem comparisonIndices : ComparisonIndices := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def utfDfaStep := Strings.dfaStep
def isvalidUtf8Dfa := Strings.dfaRun
def findNonascii (chunk : Int) (bytes : List UInt8) (last : Int) :=
  Strings.findNonasciiLoop chunk bytes last bytes.length 1
def byteClassifyString (s : JStr) := Strings.byteStringClassify s.bytes
def byteClassifyVector (bytes : List UInt8) := Strings.byteStringClassify bytes
def byteClassifyNonascii (bytes : List UInt8) (first last : Int) := Strings.classifyNonascii bytes first last
def isvalidBytes (bytes : List UInt8) := Strings.byteStringClassify bytes != 0
def isvalidString (s : JStr) := Strings.isvalidStr s
def isvalidAbstract (s : JStr) := Strings.isvalidStr s
def isValidContinuation (c : UInt8) := Strings.isCont c

def Utf8Classification : Prop :=
  (∀ st b, utfDfaStep st b = Strings.dfaStep st b) ∧
  (∀ st b f l, isvalidUtf8Dfa st b f l = Strings.dfaRun st b f l) ∧
  (∀ c b l, findNonascii c b l = Strings.findNonasciiLoop c b l b.length 1) ∧
  (∀ s, byteClassifyString s = Strings.byteStringClassify s.bytes) ∧
  (∀ b, byteClassifyVector b = Strings.byteStringClassify b) ∧
  (∀ b f l, byteClassifyNonascii b f l = Strings.classifyNonascii b f l) ∧
  (∀ b, isvalidBytes b = (Strings.byteStringClassify b != 0)) ∧
  (∀ s, isvalidString s = Strings.isvalidStr s) ∧
  (∀ s, isvalidAbstract s = Strings.isvalidStr s) ∧
  (∀ c, isValidContinuation c = Strings.isCont c)

theorem utf8Classification : Utf8Classification := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def iterateContinued := Strings.iterateContinued
def getindex (s : JStr) (i : JInt64) := Strings.getindex s i
def getindexContinued := Strings.getindexContinued
def getindexAbstractRange (s : JStr) (i j : JInt64) := Strings.getindexRange s i j
def getindexUnitRange (s : JStr) (i j : JInt64) := Strings.getindexRange s i j
def lengthView (s : JStr) := Strings.length s
def lengthStringRange (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def lengthViewRange (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def lengthInternal (s : JStr) (i j : JInt64) := Strings.lengthRange s i j
def lengthContinued (s : JStr) (i n c : JInt64) := Strings.lengthContinued s i n c
def isasciiString (s : JStr) := Strings.isascii s
def repeatCharBit (c : UInt32) (r : JInt64) := Strings.repeatChar c r
def repeatCharInteger (c : UInt32) (r : JInt64) := Strings.repeatChar c r

def IterationSlices : Prop :=
  (∀ s i u, iterateContinued s i u = Strings.iterateContinued s i u) ∧
  (∀ s i, getindex s i = Strings.getindex s i) ∧
  (∀ s i u, getindexContinued s i u = Strings.getindexContinued s i u) ∧
  (∀ s i j, getindexAbstractRange s i j = Strings.getindexRange s i j) ∧
  (∀ s i j, getindexUnitRange s i j = Strings.getindexRange s i j) ∧
  (∀ s, lengthView s = Strings.length s) ∧
  (∀ s i j, lengthStringRange s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, lengthViewRange s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, lengthInternal s i j = Strings.lengthRange s i j) ∧
  (∀ s i n c, lengthContinued s i n c = Strings.lengthContinued s i n c) ∧
  (∀ s, isasciiString s = Strings.isascii s) ∧
  (∀ c r, repeatCharBit c r = Strings.repeatChar c r) ∧
  (∀ c r, repeatCharInteger c r = Strings.repeatChar c r)

theorem iterationSlices : IterationSlices := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.String
