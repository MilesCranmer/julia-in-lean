import JuliaLean.Core
import JuliaLean.IntFuncsCov.Hashing
import JuliaLean.Strings.Search

namespace JuliaLean.StringsCovA.LazyFaithful

open JuliaLean

abbrev JString := Strings.JStr
abbrev Index := JInt64
abbrev Word := IntFuncsCov.Hashing.Word

inductive LazyError where
  | methodError (target : String)
  | argumentErrorFlags (flags : List String)
  | parseError (code : Nat)
  | printError (code : Nat)
  | stringError (error : Strings.SErr)
  deriving Repr, DecidableEq

abbrev LazyResult (α : Type) := Except LazyError α

def liftStringResult : Strings.SJl α → LazyResult α
  | .ok value => .ok value
  | .error error => .error (.stringError error)

def liftIntResult : Jl α → LazyResult α
  | .ok value => .ok value
  | .error error => .error (.stringError (.jl error))

/--
An arbitrary captured Julia value. `identity` represents the value stored in
the source tuple. `print` is its dynamically dispatched `print(io, value)`
behavior on the actual mutable output buffer, including seeks, truncation, and
exceptions. Its Boolean arguments are the `:compact` and `:limit` IOContext
properties. `base/strings/lazy.jl:36-42,94-97`.
-/
structure Part where
  identity : Nat
  print : Bool → Bool → JString → LazyResult JString

structure Lazy where
  parts : List Part
  compact : Bool
  cache : Option JString

structure PartsField where
  converted : LazyResult (List Part)

structure CacheField where
  converted : LazyResult (Option JString)

/-- `_LazyString(parts, str) = new(parts, false, str)`, `base/strings/lazy.jl:41`. -/
def privateCtor (parts : PartsField) (str : CacheField) : LazyResult Lazy :=
  do
    let values ← parts.converted
    let cached ← str.converted
    return ⟨values, false, cached⟩

def PrivateCtorProperty : Prop :=
  (∀ parts cached,
    privateCtor ⟨.ok parts⟩ ⟨.ok cached⟩ = .ok ⟨parts, false, cached⟩) ∧
  (∀ error str, privateCtor ⟨.error error⟩ str = .error error) ∧
  (∀ parts error, privateCtor ⟨.ok parts⟩ ⟨.error error⟩ = .error error)

theorem privateCtor_proven : PrivateCtorProperty := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- `LazyString(args...; compact::Bool=false)`, `base/strings/lazy.jl:42`. -/
def ctor (args : List Part) (compact : Bool := false) : Lazy :=
  ⟨args, compact, none⟩

def CtorProperty : Prop := ∀ args compact,
  (ctor args compact).parts = args ∧
  (ctor args compact).compact = compact ∧
  (ctor args compact).cache = none

theorem ctor_proven : CtorProperty := by
  intro args compact
  exact ⟨rfl, rfl, rfl⟩

structure MacroExpr where
  identity : Nat
  deriving Repr, DecidableEq

inductive MacroPart where
  | literal (value : JString)
  | escaped (expr : MacroExpr)
  deriving Repr, DecidableEq

structure MacroExpansion where
  parts : List MacroPart
  compact : Bool
  deriving Repr, DecidableEq

structure Parsed (start : Index) where
  expr : MacroExpr
  next : Index
  advances : start.val < next.val

abbrev ParseAtom :=
  (text : JString) → (start : Index) → String → LazyResult (Parsed start)

/-- `text[first:last]` with Julia's range indexing and UTF-8 checks. -/
def textSliceInclusive (text : JString) (first last : Index) : LazyResult JString :=
  liftStringResult (Strings.getindexRange text first last)

/--
The `while` loop of `@lazy_str`, `base/strings/lazy.jl:77-85`. Each successful
parse advances past at least the dollar byte, so `ncodeunits(text)+1` iterations
cannot truncate the loop. The zero branch is consequently unreachable from
`lazyStr` while the loop condition holds.
-/
def lazyLoop (parseatom : ParseAtom) (filename : String) (text : JString) :
    Nat → Index → Index → List MacroPart → LazyResult (List MacroPart)
  | 0, _, _, parts => .ok parts
  | fuel + 1, lastidx, idx, parts => do
      let found ← liftStringResult (Strings.findnextChar 0x24000000 text idx)
      match found with
      | none =>
          if lastidx.val ≤ (Strings.lastindex text).val then
            let literal ← textSliceInclusive text lastidx (Strings.lastindex text)
            return parts ++ [.literal literal]
          else
            return parts
      | some dollar =>
          let parts ←
            if lastidx.val < dollar.val then
              let previous ← liftStringResult (Strings.prevind text dollar)
              let literal ← textSliceInclusive text lastidx previous
              pure (parts ++ [.literal literal])
            else
              pure parts
          let parseidx := dollar + Strings.ix 1
          let parsed ← parseatom text parseidx filename
          lazyLoop parseatom filename text fuel parsed.next parsed.next
            (parts ++ [.escaped parsed.expr])

/-- `macro lazy_str(text, flags...)`, `base/strings/lazy.jl:73-87`. -/
def lazyStr (parseatom : ParseAtom) (sourceFile : String) (text : JString)
    (flags : List String) : LazyResult MacroExpansion :=
  let compact := flags == ["c"]
  if !flags.isEmpty && !compact then
    .error (.argumentErrorFlags flags)
  else do
    let parts ← lazyLoop parseatom sourceFile text (text.bytes.length + 1)
      (Strings.ix 1) (Strings.ix 1) []
    return ⟨parts, compact⟩

def LazyStrProperty : Prop :=
  (∀ parseatom sourceFile text flags,
    flags ≠ [] → flags ≠ ["c"] →
    lazyStr parseatom sourceFile text flags = .error (.argumentErrorFlags flags)) ∧
  (∀ parseatom sourceFile text flags expansion,
    lazyStr parseatom sourceFile text flags = .ok expansion →
    expansion.compact = (flags == ["c"]))

theorem lazyStr_proven : LazyStrProperty := by
  constructor
  · intro parseatom sourceFile text flags hne hnc
    simp [lazyStr, hne, hnc]
  · intro parseatom sourceFile text flags expansion h
    by_cases bad : !flags.isEmpty && !(flags == ["c"])
    · unfold lazyStr at h
      rw [if_pos bad] at h
      contradiction
    · cases hl : lazyLoop parseatom sourceFile text (text.bytes.length + 1)
          (Strings.ix 1) (Strings.ix 1) [] with
      | error error =>
          unfold lazyStr at h
          rw [if_neg bad, hl] at h
          cases h
      | ok parts =>
          unfold lazyStr at h
          rw [if_neg bad, hl] at h
          cases h
          rfl

/-- Execute `foreach(Fix1(print, io), parts)` from left to right. -/
def printParts (compact limit : Bool) : List Part → JString → LazyResult JString
  | [], output => .ok output
  | part :: parts, output => do
      let output ← part.print compact limit output
      printParts compact limit parts output

/-- The `sprint` block at `base/strings/lazy.jl:92-98`. -/
def sprintParts (parts : List Part) (compact : Bool) : LazyResult JString :=
  printParts compact compact parts Strings.JStr.empty

structure StringCall where
  outcome : LazyResult JString
  cache : Option JString

/--
`String(l::LazyString)`, `base/strings/lazy.jl:89-101`. `concurrent` is the
cache value after printing finishes or throws. A successful compare-exchange
stores this task's string exactly when it is still `nothing`.
-/
def toString (l : Lazy) (concurrent : Option JString) : StringCall :=
  match l.cache with
  | some old => ⟨.ok old, some old⟩
  | none =>
      match sprintParts l.parts l.compact with
      | .error error => ⟨.error error, concurrent⟩
      | .ok rendered =>
          match concurrent with
          | none => ⟨.ok rendered, some rendered⟩
          | some old => ⟨.ok old, some old⟩

def ToStringProperty : Prop :=
  (∀ parts compact cached concurrent,
    toString ⟨parts, compact, some cached⟩ concurrent = ⟨.ok cached, some cached⟩) ∧
  (∀ parts compact rendered,
    sprintParts parts compact = .ok rendered →
    toString ⟨parts, compact, none⟩ none = ⟨.ok rendered, some rendered⟩) ∧
  (∀ parts compact rendered competing,
    sprintParts parts compact = .ok rendered →
    toString ⟨parts, compact, none⟩ (some competing) = ⟨.ok competing, some competing⟩) ∧
  (∀ parts compact error concurrent,
    sprintParts parts compact = .error error →
    toString ⟨parts, compact, none⟩ concurrent = ⟨.error error, concurrent⟩) ∧
  (∀ part compact output,
    printParts compact compact [part] output = part.print compact compact output)

theorem toString_proven : ToStringProperty := by
  refine ⟨fun _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro parts compact rendered h
    simp only [toString]
    rw [h]
  · intro parts compact rendered competing h
    simp only [toString]
    rw [h]
  · intro parts compact error concurrent h
    simp only [toString]
    rw [h]
  · intro part compact output
    cases h : part.print compact compact output with
    | error error => rw [printParts, h]; rfl
    | ok next => rw [printParts, h]; rfl

structure UnaryCall (α : Type) where
  outcome : LazyResult α
  cache : Option JString

structure BinaryCall (α : Type) where
  outcome : LazyResult α
  leftCache : Option JString
  rightCache : Option JString

inductive IntegerValue where
  | int (value : JInt64)
  | other (value : Int)

def integerToInt : IntegerValue → LazyResult JInt64
  | .int value => .ok value
  | .other value => liftIntResult (JInt.convert .i64 value)

/-- `hash(s::LazyString, h)`, `base/strings/lazy.jl:103`. -/
def hash (s : Lazy) (h : Word) (secret : Word × Word × Word × Word)
    (concurrent : Option JString) : UnaryCall Word :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      ⟨.ok (IntFuncsCov.Hashing.hashBytes string.bytes h secret), call.cache⟩

def HashProperty : Prop :=
  (∀ s h secret concurrent string,
    (toString s concurrent).outcome = .ok string →
    (hash s h secret concurrent).outcome =
      .ok (IntFuncsCov.Hashing.hashBytes string.bytes h secret) ∧
    (hash s h secret concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s h secret concurrent error,
    (toString s concurrent).outcome = .error error →
    (hash s h secret concurrent).outcome = .error error ∧
    (hash s h secret concurrent).cache = (toString s concurrent).cache)

theorem hash_proven : HashProperty := by
  constructor <;> intro s h secret concurrent value hs <;> simp [hash, hs]

/-- `lastindex(s::LazyString)`, `base/strings/lazy.jl:104`. -/
def lastindex (s : Lazy) (concurrent : Option JString) : UnaryCall JInt64 :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok (Strings.lastindex string), call.cache⟩

def LastindexProperty : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (lastindex s concurrent).outcome = .ok (Strings.lastindex string) ∧
    (lastindex s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (lastindex s concurrent).outcome = .error error ∧
    (lastindex s concurrent).cache = (toString s concurrent).cache)

theorem lastindex_proven : LastindexProperty := by
  constructor <;> intro s concurrent value hs <;> simp [lastindex, hs]

/-- `iterate(s::LazyString)`, `base/strings/lazy.jl:105`. -/
def iterate0 (s : Lazy) (concurrent : Option JString) :
    UnaryCall (Option (UInt32 × JInt64)) :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok (Strings.iterate string (Strings.ix 1)), call.cache⟩

def Iterate0Property : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (iterate0 s concurrent).outcome = .ok (Strings.iterate string (Strings.ix 1)) ∧
    (iterate0 s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (iterate0 s concurrent).outcome = .error error ∧
    (iterate0 s concurrent).cache = (toString s concurrent).cache)

theorem iterate0_proven : Iterate0Property := by
  constructor <;> intro s concurrent value hs <;> simp [iterate0, hs]

/-- `iterate(s::LazyString, i::Integer)`, `base/strings/lazy.jl:106`. -/
def iterateAt (s : Lazy) (i : IntegerValue) (concurrent : Option JString) :
    UnaryCall (Option (UInt32 × JInt64)) :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      match integerToInt i with
      | .error error => ⟨.error error, call.cache⟩
      | .ok index => ⟨.ok (Strings.iterate string index), call.cache⟩

def IterateAtProperty : Prop :=
  (∀ s i concurrent string index,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .ok index →
    (iterateAt s i concurrent).outcome = .ok (Strings.iterate string index) ∧
    (iterateAt s i concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s i concurrent error,
    (toString s concurrent).outcome = .error error →
    (iterateAt s i concurrent).outcome = .error error) ∧
  (∀ s i concurrent string error,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .error error →
    (iterateAt s i concurrent).outcome = .error error)

theorem iterateAt_proven : IterateAtProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i concurrent string index hs hi
    simp [iterateAt, hs, hi]
  · intro s i concurrent error hs
    simp [iterateAt, hs]
  · intro s i concurrent string error hs hi
    simp [iterateAt, hs, hi]

/-- `isequal(a::LazyString, b::LazyString)`, `base/strings/lazy.jl:107`. -/
def isequal (a b : Lazy) (leftConcurrent rightConcurrent : Option JString) :
    BinaryCall Bool :=
  let left := toString a leftConcurrent
  match left.outcome with
  | .error error => ⟨.error error, left.cache, b.cache⟩
  | .ok leftString =>
      let right := toString b rightConcurrent
      match right.outcome with
      | .error error => ⟨.error error, left.cache, right.cache⟩
      | .ok rightString =>
          ⟨.ok (leftString.bytes == rightString.bytes), left.cache, right.cache⟩

def IsequalProperty : Prop :=
  (∀ a b leftConcurrent rightConcurrent leftString rightString,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .ok rightString →
    (isequal a b leftConcurrent rightConcurrent).outcome =
      .ok (leftString.bytes == rightString.bytes)) ∧
  (∀ a b leftConcurrent rightConcurrent error,
    (toString a leftConcurrent).outcome = .error error →
    (isequal a b leftConcurrent rightConcurrent).outcome = .error error) ∧
  (∀ a b leftConcurrent rightConcurrent leftString error,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .error error →
    (isequal a b leftConcurrent rightConcurrent).outcome = .error error)

theorem isequal_proven : IsequalProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b leftConcurrent rightConcurrent leftString rightString hl hr
    simp [isequal, hl, hr]
  · intro a b leftConcurrent rightConcurrent error hl
    simp [isequal, hl]
  · intro a b leftConcurrent rightConcurrent leftString error hl hr
    simp [isequal, hl, hr]

/-- `==(a::LazyString, b::LazyString)`, `base/strings/lazy.jl:108`. -/
def eq (a b : Lazy) (leftConcurrent rightConcurrent : Option JString) :
    BinaryCall Bool :=
  let left := toString a leftConcurrent
  match left.outcome with
  | .error error => ⟨.error error, left.cache, b.cache⟩
  | .ok leftString =>
      let right := toString b rightConcurrent
      match right.outcome with
      | .error error => ⟨.error error, left.cache, right.cache⟩
      | .ok rightString =>
          ⟨.ok (leftString.bytes == rightString.bytes), left.cache, right.cache⟩

def EqProperty : Prop :=
  (∀ a b leftConcurrent rightConcurrent leftString rightString,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .ok rightString →
    (eq a b leftConcurrent rightConcurrent).outcome =
      .ok (leftString.bytes == rightString.bytes)) ∧
  (∀ a b leftConcurrent rightConcurrent error,
    (toString a leftConcurrent).outcome = .error error →
    (eq a b leftConcurrent rightConcurrent).outcome = .error error) ∧
  (∀ a b leftConcurrent rightConcurrent leftString error,
    (toString a leftConcurrent).outcome = .ok leftString →
    (toString b rightConcurrent).outcome = .error error →
    (eq a b leftConcurrent rightConcurrent).outcome = .error error)

theorem eq_proven : EqProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b leftConcurrent rightConcurrent leftString rightString hl hr
    simp [eq, hl, hr]
  · intro a b leftConcurrent rightConcurrent error hl
    simp [eq, hl]
  · intro a b leftConcurrent rightConcurrent leftString error hl hr
    simp [eq, hl, hr]

/-- `ncodeunits(s::LazyString)`, `base/strings/lazy.jl:109`. -/
def ncodeunits (s : Lazy) (concurrent : Option JString) : UnaryCall JInt64 :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok (Strings.ncodeunits string), call.cache⟩

def NcodeunitsProperty : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (ncodeunits s concurrent).outcome = .ok (Strings.ncodeunits string) ∧
    (ncodeunits s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (ncodeunits s concurrent).outcome = .error error ∧
    (ncodeunits s concurrent).cache = (toString s concurrent).cache)

theorem ncodeunits_proven : NcodeunitsProperty := by
  constructor <;> intro s concurrent value hs <;> simp [ncodeunits, hs]

inductive JuliaType where
  | uint8
  deriving Repr, DecidableEq

/-- `codeunit(s::LazyString) = codeunit("")`, `base/strings/lazy.jl:110`. -/
def codeunitType (_s : Lazy) : JuliaType := .uint8

def CodeunitTypeProperty : Prop := ∀ s, codeunitType s = .uint8

theorem codeunitType_proven : CodeunitTypeProperty := by
  intro s
  rfl

/-- `codeunit(s::LazyString, i::Integer)`, `base/strings/lazy.jl:111`. -/
def codeunitAt (s : Lazy) (i : IntegerValue) (concurrent : Option JString) :
    UnaryCall UInt8 :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      match integerToInt i with
      | .error error => ⟨.error error, call.cache⟩
      | .ok index => ⟨liftStringResult (Strings.codeunit string index), call.cache⟩

def CodeunitAtProperty : Prop :=
  (∀ s i concurrent string index,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .ok index →
    (codeunitAt s i concurrent).outcome = liftStringResult (Strings.codeunit string index) ∧
    (codeunitAt s i concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s i concurrent error,
    (toString s concurrent).outcome = .error error →
    (codeunitAt s i concurrent).outcome = .error error) ∧
  (∀ s i concurrent string error,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .error error →
    (codeunitAt s i concurrent).outcome = .error error)

theorem codeunitAt_proven : CodeunitAtProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i concurrent string index hs hi
    simp [codeunitAt, hs, hi]
  · intro s i concurrent error hs
    simp [codeunitAt, hs]
  · intro s i concurrent string error hs hi
    simp [codeunitAt, hs, hi]

structure CodeUnits where
  string : JString
  deriving Repr, DecidableEq

/-- `codeunits(s::LazyString)`, `base/strings/lazy.jl:112`. -/
def codeunits (s : Lazy) (concurrent : Option JString) : UnaryCall CodeUnits :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string => ⟨.ok ⟨string⟩, call.cache⟩

def CodeunitsProperty : Prop :=
  (∀ s concurrent string,
    (toString s concurrent).outcome = .ok string →
    (codeunits s concurrent).outcome = .ok ⟨string⟩ ∧
    (codeunits s concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s concurrent error,
    (toString s concurrent).outcome = .error error →
    (codeunits s concurrent).outcome = .error error ∧
    (codeunits s concurrent).cache = (toString s concurrent).cache)

theorem codeunits_proven : CodeunitsProperty := by
  constructor <;> intro s concurrent value hs <;> simp [codeunits, hs]

/-- `isvalid(s::LazyString, i::Integer)`, `base/strings/lazy.jl:113`. -/
def isvalid (s : Lazy) (i : IntegerValue) (concurrent : Option JString) :
    UnaryCall Bool :=
  let call := toString s concurrent
  match call.outcome with
  | .error error => ⟨.error error, call.cache⟩
  | .ok string =>
      match integerToInt i with
      | .error error => ⟨.error error, call.cache⟩
      | .ok index => ⟨.ok (Strings.isvalidAt string index), call.cache⟩

def IsvalidProperty : Prop :=
  (∀ s i concurrent string index,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .ok index →
    (isvalid s i concurrent).outcome = .ok (Strings.isvalidAt string index) ∧
    (isvalid s i concurrent).cache = (toString s concurrent).cache) ∧
  (∀ s i concurrent error,
    (toString s concurrent).outcome = .error error →
    (isvalid s i concurrent).outcome = .error error) ∧
  (∀ s i concurrent string error,
    (toString s concurrent).outcome = .ok string →
    integerToInt i = .error error →
    (isvalid s i concurrent).outcome = .error error)

theorem isvalid_proven : IsvalidProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro s i concurrent string index hs hi
    simp [isvalid, hs, hi]
  · intro s i concurrent error hs
    simp [isvalid, hs]
  · intro s i concurrent string error hs hi
    simp [isvalid, hs, hi]

end JuliaLean.StringsCovA.LazyFaithful
