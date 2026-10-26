import JuliaLean.Core

/-! Models for `base/strings/stringview.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.StringView

structure View where
  bytes : List UInt8
  address : Nat := 0
  deriving DecidableEq

structure SubView where
  parent : View
  offset : Nat
  ncodeunits : Nat
  deriving DecidableEq

/-- `StringView(v)`; `base/strings/stringview.jl:8`. -/
def ctor (v : List UInt8) (address : Nat := 0) : View := ⟨v, address⟩

/-- `Vector{UInt8}(s)` and `Array{UInt8}(s)`; `base/strings/stringview.jl:9-10`. -/
def toVector (s : View) : List UInt8 := s.bytes
def toArray (s : View) : List UInt8 := toVector s

/-- Both `String` conversion methods; `base/strings/stringview.jl:11,26`. -/
def toString (s : View) : List UInt8 := s.bytes

/-- `copy(s::StringView)`; `base/strings/stringview.jl:12`. -/
def copy (s : View) : View := ⟨s.bytes, s.address⟩

/-- `Symbol(s::DenseStringViewAndSub)`; `base/strings/stringview.jl:14-16`. -/
def toSymbol (intern : List UInt8 → Nat) (s : View) : Nat := intern s.bytes

/-- Pointer methods; `base/strings/stringview.jl:18-21`. -/
def pointer (s : View) : Nat := s.address
def pointerAt (s : View) (i : Int) : Int := s.address + i - 1
def subPointer (s : SubView) : Nat := s.parent.address + s.offset
def subPointerAt (s : SubView) (i : Int) : Int := s.parent.address + s.offset + i - 1

/-- `unsafe_convert` methods; `base/strings/stringview.jl:23-24`. -/
def unsafeConvertU8 (s : View) : Nat := pointer s
def unsafeConvertI8 (s : View) : Nat := pointer s

/-- `cconvert` methods; `base/strings/stringview.jl:28-29`. -/
def cconvertU8 (s : View) : View := s
def cconvertI8 (s : View) : View := s

/-- `sizeof` and `ncodeunits`; `base/strings/stringview.jl:85-86`. -/
def sizeof (s : View) : Nat := s.bytes.length
def ncodeunits (s : View) : Nat := s.bytes.length

/-- `codeunit(::StringView)` and indexed `codeunit`; `base/strings/stringview.jl:87-88`. -/
def codeunitType (_s : View) : Nat := 8
def codeunit (s : View) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ s.bytes.length then .ok (s.bytes.getD (i.toNat - 1) 0)
  else .error .boundsError

/-- `codeunits` for a view and subview; `base/strings/stringview.jl:89-90`. -/
def codeunits (s : View) : List UInt8 := s.bytes
def subCodeunits (s : SubView) : List UInt8 := (s.parent.bytes.drop s.offset).take s.ncodeunits

/-- UTF-8 `cmp` and `==` operate on code units; `base/strings/stringview.jl:94-95`. -/
def cmp (cmpBytes : List UInt8 → List UInt8 → Int) (a b : View) : Int := cmpBytes a.bytes b.bytes
def eq (a b : View) : Bool := a.bytes == b.bytes

inductive BackingKind where
  | codeUnits | vector | subarray
  deriving DecidableEq

/-- Whether the backing type supports the source's `V()` expression. -/
def emptyBacking : BackingKind → Jl (List UInt8)
  | .codeUnits | .vector => .ok []
  | .subarray => .error (.methodError "SubArray()")

/-- `typemin(::Type{StringView{CodeUnits{UInt8,String}}})`; line 98. -/
def typeminCodeUnits : View := ⟨[], 0⟩

/-- Generic `typemin(::Type{StringView{V}})`; line 99. -/
def typeminType (kind : BackingKind) : Jl View := do
  let bytes ← emptyBacking kind
  .ok ⟨bytes, 0⟩

/-- Value `typemin`, `one`, and `oneunit`; lines 100-102. -/
def typeminValue (kind : BackingKind) : Jl View := typeminType kind
def one (kind : BackingKind) : Jl View := typeminType kind
def oneunit (kind : BackingKind) : Jl View := typeminType kind

/-- `isascii(s)`; `base/strings/stringview.jl:105`. -/
def isascii (s : View) : Bool := s.bytes.all (· < 0x80)

/-- `hash`; `base/strings/stringview.jl:108-110`. -/
def hash (hashBytes : List UInt8 → UInt64 → UInt64) (s : View) (h : UInt64) : UInt64 :=
  hashBytes s.bytes h

/-- `write` and `print`; `base/strings/stringview.jl:113-114`. -/
def write (emit : List UInt8 → Nat) (s : View) : Nat := emit s.bytes
def print (emit : List UInt8 → Nat) (s : View) : Unit := let _ := write emit s; ()

/-- `thisind` and `nextind` forward to the UTF-8 helpers; lines 116-120. -/
def thisind (f : List UInt8 → Int → Jl Int) (s : View) (i : Int) := f s.bytes i
def nextind (f : List UInt8 → Int → Jl Int) (s : View) (i : Int) := f s.bytes i

/-- `isvalid`; `base/strings/stringview.jl:122`. -/
def isvalid (this : List UInt8 → Int → Int) (s : View) (i : Int) : Bool :=
  decide (1 ≤ i ∧ i ≤ s.bytes.length) && decide (this s.bytes i = i)

/-- `getindex(s::StringView, r::UnitRange{Int})`; lines 126-137. -/
def getindexRange (valid : List UInt8 → Int → Bool) (next : List UInt8 → Int → Int)
    (s : View) (i j : Int) : Jl View :=
  if j < i then .ok ⟨[], s.address⟩
  else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
  else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
  else
    let stop := next s.bytes j - 1
    .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat, s.address + i.toNat - 1⟩

/-- `chomp`; `base/strings/stringview.jl:139-151`. -/
def chomp (s : View) : View :=
  let bytes := match s.bytes.reverse with
    | 0x0a :: 0x0d :: rest => rest.reverse
    | 0x0a :: rest => rest.reverse
    | _ => s.bytes
  ⟨bytes, s.address⟩

/-- `replace(io, s, pairs...; count)`; `base/strings/stringview.jl:153-155`. -/
def replace {α : Type} (replaceImpl : View → List α → Int → α)
    (s : View) (pairs : List α) (count : Int) : α := replaceImpl s pairs count

def StorageContract : Prop :=
  (∀ v a, ctor v a = ⟨v, a⟩) ∧
  (∀ s, toVector s = s.bytes) ∧ (∀ s, toArray s = s.bytes) ∧
  (∀ s, toString s = s.bytes) ∧ (∀ s, copy s = ⟨s.bytes, s.address⟩) ∧
  (∀ intern s, toSymbol intern s = intern s.bytes) ∧
  (∀ s, pointer s = s.address) ∧ (∀ s i, pointerAt s i = s.address + i - 1) ∧
  (∀ s, subPointer s = s.parent.address + s.offset) ∧
  (∀ s i, subPointerAt s i = s.parent.address + s.offset + i - 1) ∧
  (∀ s, unsafeConvertU8 s = pointer s) ∧ (∀ s, unsafeConvertI8 s = pointer s) ∧
  (∀ s, cconvertU8 s = s) ∧ (∀ s, cconvertI8 s = s)

theorem storageContract : StorageContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ByteContract : Prop :=
  (∀ s, sizeof s = s.bytes.length) ∧ (∀ s, ncodeunits s = s.bytes.length) ∧
  (∀ s, codeunitType s = 8) ∧
  (∀ s i, codeunit s i = if 1 ≤ i ∧ i ≤ s.bytes.length then
    .ok (s.bytes.getD (i.toNat - 1) 0) else .error .boundsError) ∧
  (∀ s, codeunits s = s.bytes) ∧
  (∀ s, subCodeunits s = (s.parent.bytes.drop s.offset).take s.ncodeunits) ∧
  (∀ cmpBytes a b, cmp cmpBytes a b = cmpBytes a.bytes b.bytes) ∧
  (∀ a b, eq a b = (a.bytes == b.bytes))

theorem byteContract : ByteContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def EmptyOperations : Prop :=
  typeminCodeUnits = ⟨[], 0⟩ ∧
  ∀ kind, typeminType kind = .ok ⟨[], 0⟩ ∧ typeminValue kind = .ok ⟨[], 0⟩ ∧
    one kind = .ok ⟨[], 0⟩ ∧ oneunit kind = .ok ⟨[], 0⟩

theorem emptyOperations_refuted : ¬ EmptyOperations := by
  intro h
  have hs := (h.2 .subarray).1
  change (Except.error (.methodError "SubArray()") : Jl View) = .ok ⟨[], 0⟩ at hs
  cases hs

def BehaviorContract : Prop :=
  (∀ s, isascii s = s.bytes.all (· < 0x80)) ∧
  (∀ hashBytes s h, hash hashBytes s h = hashBytes s.bytes h) ∧
  (∀ emit s, write emit s = emit s.bytes) ∧
  (∀ emit s, print emit s = ()) ∧
  (∀ f s i, thisind f s i = f s.bytes i) ∧
  (∀ f s i, nextind f s i = f s.bytes i) ∧
  (∀ this s i, isvalid this s i =
    (decide (1 ≤ i ∧ i ≤ s.bytes.length) && decide (this s.bytes i = i)))

theorem behaviorContract : BehaviorContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def SliceChompReplaceContract : Prop :=
  (∀ valid next s i j, getindexRange valid next s i j =
    if j < i then .ok ⟨[], s.address⟩
    else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
    else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
    else let stop := next s.bytes j - 1
      .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat,
        s.address + i.toNat - 1⟩) ∧
  (∀ s, chomp s =
    let bytes := match s.bytes.reverse with
      | 0x0a :: 0x0d :: rest => rest.reverse
      | 0x0a :: rest => rest.reverse
      | _ => s.bytes
    ⟨bytes, s.address⟩) ∧
  (∀ (α : Type) (impl : View → List α → Int → α) s pairs count,
    replace impl s pairs count = impl s pairs count)

theorem sliceChompReplaceContract : SliceChompReplaceContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.StringView
