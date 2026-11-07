import JuliaLean.base.strings.search
import JuliaLean.base.char
import JuliaLean.Proofs.base.char
import JuliaLean.Registry.Types

/-!
# Specifications of `base/strings/search.jl`

Proof and refutation theorems are recorded alongside their registry entries.
`TextView` and `ByteView` describe contents independently of the search
algorithms. Their interface laws describe the primitive string, array,
conversion, iterator and C-library calls. They impose no well-formed-UTF-8
precondition: a text may contain every UInt8 value, including malformed or
truncated character encodings.
-/

namespace JuliaLean.Proofs.base.strings.search

open JuliaLean JuliaLean.base.strings.search JuliaLean.Registry
open JuliaLean.base.iterators (Exec)

/-- A string's byte storage and indexed sequence of decoded characters. -/
structure TextView (S C : Type) where
  bytes : S → List UInt8
  characters : S → List (Index × C)

def validAt {S C : Type} (v : TextView S C) (s : S) (i : Index) : Prop :=
  ∃ c, (i, c) ∈ v.characters s

def endIndex {S C : Type} (v : TextView S C) (s : S) : Int :=
  Int.ofNat (v.bytes s).length + 1

def lastIndex {S C : Type} (v : TextView S C) (s : S) : Index :=
  ((v.characters s).getLast?.map (·.1)).getD (int 0)

def nextPosition {S C : Type} (v : TextView S C) (s : S) (i : Index) : Index :=
  (((v.characters s).filter (fun p => p.1.val > i.val)).head?.map (·.1)).getD (int (endIndex v s))

def prevPosition {S C : Type} (v : TextView S C) (s : S) (i : Index) : Index :=
  (((v.characters s).filter (fun p => p.1.val < i.val)).getLast?.map (·.1)).getD (int 0)

/-- Primitive AbstractString laws, including errors and index progression. -/
structure TextLaws {S C E : Type} (ops : SearchStringOps S C E) (v : TextView S C) : Prop where
  sizeFits : ∀ s, Int.ofNat (v.bytes s).length ≤ IntTy.max .i64
  ncodeunits : ∀ s, (ops.ncodeunits s).val = Int.ofNat (v.bytes s).length
  iterationBound : ∀ s, (v.bytes s).length ≤ ops.iterationBound s
  sorted : ∀ s, (v.characters s).Pairwise (fun a b => a.1.val < b.1.val)
  indices : ∀ s p, p ∈ v.characters s → 1 ≤ p.1.val ∧ p.1.val < endIndex v s
  nonempty : ∀ s, (v.characters s).isEmpty = (v.bytes s).isEmpty
  first : ∀ s p, (v.characters s).head? = some p → p.1 = int 1
  lastindex : ∀ s, ops.lastindex s = .ok (lastIndex v s)
  isvalid : ∀ s i, ops.isvalid s i = .ok ((v.characters s).any (fun p => p.1 == i))
  getindex : ∀ s i c, (i, c) ∈ v.characters s → ops.getindex s i = .ok c
  nextind : ∀ s i, validAt v s i ∨ i = int 0 → ops.nextind s i = .ok (nextPosition v s i)
  prevind : ∀ s i, validAt v s i ∨ i.val = endIndex v s →
    ops.prevind s i = .ok (prevPosition v s i)
  iterate : ∀ s i c, (i, c) ∈ v.characters s →
    ops.iterate s i = .ok (some (c, nextPosition v s i))

/-- Integer conversion succeeds precisely on the representable Int values. -/
def IntegerLaws {I E : Type} (ix : IntegerOps I E) : Prop :=
  (∀ i, IntTy.min .i64 ≤ ix.value i → ix.value i ≤ IntTy.max .i64 →
    ix.toInt i = .ok (int (ix.value i))) ∧
  (∀ i j, ix.toInt i = .ok j → j.val = ix.value i)

/-- Raw Char bytes are packed in the high bytes of the UInt32 representation. -/
structure CharEncoding (ncodeunits : JChar → Index) where
  bytes : JChar → List UInt8
  nonempty : ∀ c, (bytes c).isEmpty = false
  length : ∀ c, (bytes c).length ≤ 4
  ncodeunits_eq : ∀ c, (ncodeunits c).val = Int.ofNat (bytes c).length
  packed : ∀ c, c.toNat = ((bytes c).zipIdx.foldl
    (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0)

/-- `chars` measures every character as the encoding does. -/
def CharOpsLaws {C E : Type} (chars : CharOps C E) (ncodeunits : JChar → Index) : Prop :=
  ∀ c, chars.ncodeunits c = .ok (ncodeunits c)

/-- A vector store reads back the memory it last stored. -/
def VectorStoreLaws {α E H : Type} (vec : VectorStore α E H) : Prop :=
  ∀ h m, vec.memory (vec.setMemory h m) = m

/-- From `h`, the store computation `m` returns a vector whose contents are `xs`. -/
def VectorResult {α E H : Type} (vec : VectorStore α E H) (m : Exec E H Nat) (h : H)
    (xs : List α) : Prop :=
  ∃ a h', m h = some (.ok a, h') ∧ (vec.memory h').contents a = xs.map some

/-- UTF-8 string iteration preserves arbitrary input bytes. Standalone bytes
cannot occur inside a character with more than one byte. -/
structure Utf8TextLaws {S E : Type} (ops : SearchStringOps S JChar E)
    (v : TextView S JChar) (ncodeunitsChar : JChar → Index)
    (enc : CharEncoding ncodeunitsChar) : Prop extends TextLaws ops v where
  concatenation : ∀ s, (v.characters s).flatMap (fun p => enc.bytes p.2) = v.bytes s
  offsets : ∀ s k p, (v.characters s)[k]? = some p →
    p.1.val = 1 + Int.ofNat (((v.characters s).take k).flatMap (fun q => enc.bytes q.2)).length
  standalone : ∀ s p b, p ∈ v.characters s → b ∈ enc.bytes p.2 →
    (b.toNat < 128 ∨ 247 < b.toNat) → enc.bytes p.2 = [b]

structure ByteView (A B : Type) where
  first : A → Int
  elements : A → List B

def byteAt {A B : Type} (v : ByteView A B) (a : A) (i : Int) : Option B :=
  (v.elements a)[(i - v.first a).toNat]?

/-- Abstract byte-vector axes may have any representable first index. -/
structure ByteLaws {A B E : Type} (ops : ByteOps A B E) (v : ByteView A B) : Prop where
  firstindex : ∀ a, (ops.firstindex a).val = v.first a
  lastindex : ∀ a, (ops.lastindex a).val = v.first a + Int.ofNat (v.elements a).length - 1
  length : ∀ a, (ops.length a).val = Int.ofNat (v.elements a).length
  getindex : ∀ a k b, (v.elements a)[k]? = some b →
    ops.getindex a (int (v.first a + Int.ofNat k)) = .ok b
  getindexOutside : ∀ a i, i.val < v.first a ∨
    v.first a + Int.ofNat (v.elements a).length ≤ i.val →
    ops.getindex a i = .error (ops.boundsError a i.val)
  byteValue : ∀ b, -128 ≤ ops.value b ∧ ops.value b ≤ 255

/-- Least/greatest matching positions, stated without reference to a search loop. -/
def FirstIndex {E : Type} (accepts : Int → Prop) (start : Int)
    (result : Except E (Option Index)) : Prop :=
  (∀ i, result = .ok (some i) ↔
    start ≤ i.val ∧ accepts i.val ∧ ∀ j, start ≤ j → accepts j → i.val ≤ j) ∧
  (result = .ok none ↔ ∀ j, start ≤ j → ¬ accepts j)

def LastIndex {E : Type} (accepts : Int → Prop) (start : Int)
    (result : Except E (Option Index)) : Prop :=
  (∀ i, result = .ok (some i) ↔
    i.val ≤ start ∧ accepts i.val ∧ ∀ j, j ≤ start → accepts j → j ≤ i.val) ∧
  (result = .ok none ↔ ∀ j, j ≤ start → ¬ accepts j)

def charMatches {S C : Type} (v : TextView S C) (p : C → Prop) (s : S) (i : Int) : Prop :=
  ∃ k c, (k, c) ∈ v.characters s ∧ k.val = i ∧ p c

def byteMatches {A B : Type} (v : ByteView A B) (equal : B → Bool) (a : A) (i : Int) : Prop :=
  v.first a ≤ i ∧ ∃ b, byteAt v a i = some b ∧ equal b = true

/-- A contiguous byte subsequence, using numeric Int8/UInt8 equality. -/
def byteSequenceAt {A T B C E : Type} (sops : ByteOps A B E) (tops : ByteOps T C E)
    (sv : ByteView A B) (tv : ByteView T C) (s : A) (t : T) (i : Int) : Prop :=
  sv.first s ≤ i ∧ i + Int.ofNat (tv.elements t).length ≤
    sv.first s + Int.ofNat (sv.elements s).length ∧
  ∀ k b, (tv.elements t)[k]? = some b →
    ∃ a, byteAt sv s (i + Int.ofNat k) = some a ∧ sops.value a = tops.value b

/-- A character-sequence match and its inclusive Julia character endpoints. -/
def textSequenceAt {S T C : Type} (sv : TextView S C) (pattern : T → List C)
    (s : S) (t : T) (r : MatchRange) : Prop :=
  if (pattern t).isEmpty then r.first.val = r.last.val + 1 ∧
    1 ≤ r.first.val ∧ r.first.val ≤ endIndex sv s
  else ∃ k, ((sv.characters s)[k]?.map (·.1)) = some r.first ∧
    (((sv.characters s).drop k).take (pattern t).length).map (·.2) = pattern t ∧
    (((sv.characters s)[k + (pattern t).length - 1]?.map (·.1)) = some r.last)

def FirstRange {E : Type} (accepts : MatchRange → Prop) (start : Int)
    (result : Except E (Option MatchRange)) : Prop :=
  (∀ r, result = .ok (some r) ↔ accepts r ∧ start ≤ r.first.val ∧
    ∀ q, accepts q → start ≤ q.first.val → r.first.val ≤ q.first.val) ∧
  (result = .ok none ↔ ∀ r, start ≤ r.first.val → ¬ accepts r)

def LastRange {E : Type} (accepts : MatchRange → Prop) (start : Int)
    (result : Except E (Option MatchRange)) : Prop :=
  (∀ r, result = .ok (some r) ↔ accepts r ∧ r.last.val ≤ start ∧
    ∀ q, accepts q → q.last.val ≤ start → q.first.val ≤ r.first.val) ∧
  (result = .ok none ↔ ∀ r, r.last.val ≤ start → ¬ accepts r)

/-- The search `m` returns (it terminates) with a result satisfying `P`. -/
def Returns {E α : Type} (m : SearchM E α) (P : Except E α → Prop) : Prop :=
  ∃ x, m.run = some x ∧ P x

/-- C memory search laws concern only the external C calls and preservation. -/
structure CMemoryLaws {A B E : Type} (ops : DenseOps A B E) (v : ByteView A B) : Prop where
  bytes : ByteLaws ops.toByteOps v
  nonnull : ∀ a, (ops.pointer a).val ≠ 0
  addressRange : ∀ a, (ops.pointer a).val + Int.ofNat (v.elements a).length < 2 ^ 64
  memchr : ∀ a start count needle,
    0 ≤ start → 0 ≤ count → start + count ≤ Int.ofNat (v.elements a).length →
    ops.memchrCall a (JInt.wrap .u64 ((ops.pointer a).val + start)) needle
      (JInt.wrap .u64 count) =
    .ok (match ((v.elements a).drop start.toNat).take count.toNat |>.findIdx?
        (fun b => (ops.value b) % 256 == needle.val % 256) with
      | none => JInt.wrap .u64 0
      | some offset => JInt.wrap .u64 ((ops.pointer a).val + start + Int.ofNat offset))
  memrchr : ∀ a count needle, 0 ≤ count → count ≤ Int.ofNat (v.elements a).length →
    ops.memrchrCall a (ops.pointer a) needle (JInt.wrap .u64 count) =
    .ok (match ((v.elements a).take count.toNat).reverse.findIdx?
        (fun b => (ops.value b) % 256 == needle.val % 256) with
      | none => JInt.wrap .u64 0
      | some offset => JInt.wrap .u64 ((ops.pointer a).val + count - 1 - Int.ofNat offset))

/-- The codeunits view has one-based byte axes and the same underlying bytes. -/
def CodeunitLaws {S A E : Type} (codeunits : S → A) (bytes : DenseOps A UInt8 E)
    (v : TextView S JChar) (bv : ByteView A UInt8) : Prop :=
  CMemoryLaws bytes bv ∧ (∀ s, bv.first (codeunits s) = 1) ∧
    (∀ s, bv.elements (codeunits s) = v.bytes s) ∧
    (∀ b, bytes.value b = Int.ofNat b.toNat)

/-- Iterating `it` from state `st` returns the elements `xs` in order, then `nothing`. -/
inductive Yields {E X St : Type} (it : Option St → SearchM E (Option (X × St))) :
    Option St → List X → Prop where
  | nil {st} (stop : (it st).run = some (.ok none)) : Yields it st []
  | cons {st x st' xs} (step : (it st).run = some (.ok (some (x, st'))))
      (tail : Yields it (some st') xs) : Yields it st (x :: xs)

structure DenseLaws {S T A D E : Type} (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) {ncodeunits : JChar → Index} (enc : CharEncoding ncodeunits) : Prop where
  source : Utf8TextLaws cfg.source sv ncodeunits enc
  pattern : Utf8TextLaws cfg.pattern tv ncodeunits enc
  chars : CharOpsLaws cfg.chars ncodeunits
  toChar : ∀ c, cfg.chars.toChar c = .ok c
  codeunits : CodeunitLaws cfg.codeunitsSource cfg.sourceBytes sv bv
  patternBytes : ByteLaws cfg.patternBytes pv
  patternFirst : ∀ t, pv.first (cfg.codeunitsPattern t) = 1
  patternContents : ∀ t, pv.elements (cfg.codeunitsPattern t) = tv.bytes t
  patternValues : ∀ b, cfg.patternBytes.value b = Int.ofNat b.toNat
  sizeof : ∀ s, (JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val = Int.ofNat (sv.bytes s).length

structure BytePatternLaws {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) : Prop where
  source : ByteLaws cfg.source sv
  pattern : ByteLaws cfg.pattern tv
  findnext : ∀ a c i, sv.first a ≤ i.val →
    FirstIndex (byteMatches sv (fun b => cfg.source.value b == cfg.pattern.value c) a) i.val
      (cfg.findnext c a i)
  findprev : ∀ a c i, i.val < sv.first a + Int.ofNat (sv.elements a).length →
    LastIndex (byteMatches sv (fun b => cfg.source.value b == cfg.pattern.value c) a) i.val
      (cfg.findprev c a i)
  findprevAboveLast : ∀ a c i,
    (cfg.source.lastindex a).val < i.val →
    cfg.findprev c a i = .error (cfg.source.boundsError a i.val)

def byteRangeAt {A T B C E : Type} (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) (a : A) (t : T) (r : MatchRange) : Prop :=
  byteSequenceAt cfg.source cfg.pattern sv tv a t r.first.val ∧
    r.last.val + 1 = r.first.val + Int.ofNat (tv.elements t).length

/-- Julia string slicing returns the complete character at the inclusive stop. -/
def SliceLaws {E : Type} (v : TextView JString JChar)
    (slice : JString → Index → Index → Except E JString) : Prop :=
  (∀ s, v.bytes s = s.bytes) ∧ ∀ s i j t,
    slice s i j = .ok t ↔
      (j.val < i.val ∧ 1 ≤ i.val ∧ i.val ≤ endIndex v s ∧ t.bytes = []) ∨
      (i.val ≤ j.val ∧ validAt v s i ∧ validAt v s j ∧
        t.bytes = (s.bytes.drop (i.val - 1).toNat).take ((nextPosition v s j).val - i.val).toNat)

/-- A regexp engine is external to search.jl. Both callbacks are the methods
of regex.jl; `accepts` is its documented matching relation. -/
structure RegexInterface (S P E : Type) where
  findnext : P → S → Index → Except E (Option MatchRange)
  eachmatchRanges : P → S → Except E (List MatchRange)
  accepts : P → S → MatchRange → Prop

/-- The list obtained by repeatedly calling findnext, using the documented
non-overlapping advancement rule. -/
def repeatedFindnext {S P E : Type}
    (findnext : P → S → Index → Except E (Option MatchRange))
    (firstindex : S → Index) (lastindex : S → Except E Index)
    (nextind : S → Index → Except E Index) (iterationBound : S → Nat)
    (p : P) (s : S) : Except E (List MatchRange) := do
  let last ← lastindex s
  let rec loop : Nat → Index → List MatchRange → Except E (List MatchRange)
    | 0, _, ranges => .ok ranges
    | fuel + 1, start, ranges => do
        match ← findnext p s start with
        | none => pure ranges
        | some range =>
            let ranges := ranges ++ [range]
            let stop := if rangeEmpty range then range.first else range.last
            if stop.val > last.val then return ranges
            loop fuel (← nextind s stop) ranges
  loop (iterationBound s + 2) (firstindex s) []
structure RegexInterfaceLaws {S P E : Type} (ops : RegexInterface S P E)
    (string : SearchStringOps S JChar E) (v : TextView S JChar) : Prop where
  next : ∀ p s i r, 1 ≤ i.val → i.val ≤ endIndex v s →
    ops.findnext p s i = .ok (some r) →
    ops.accepts p s r ∧ i.val ≤ r.first.val ∧
      ∀ q, ops.accepts p s q → i.val ≤ q.first.val → r.first.val ≤ q.first.val
  nextNone : ∀ p s i, 1 ≤ i.val → i.val ≤ endIndex v s →
    (ops.findnext p s i = .ok none ↔ ∀ r, i.val ≤ r.first.val → ¬ ops.accepts p s r)
  eachmatch : ∀ p s rs, ops.eachmatchRanges p s = .ok rs →
    (∀ r ∈ rs, ops.accepts p s r) ∧ rs.Pairwise (fun a b => a.last.val < b.first.val)
  eachmatchComplete : ∀ p s rs, ops.eachmatchRanges p s = .ok rs →
    ∀ r, ops.accepts p s r →
      (∃ q ∈ rs, q = r ∨ (q.first.val ≤ r.first.val ∧ r.first.val ≤ q.last.val))
  eachmatchFindnext : ∀ p s rs, ops.eachmatchRanges p s = .ok rs →
    repeatedFindnext ops.findnext JuliaLean.base.strings.basic.firstindexString
      string.lastindex string.nextind string.iterationBound p s = .ok rs

/-- The final byte returned for any stored Char, including malformed Char values, is the final byte of its encoded representation. -/
def LastUtf8ByteSpec : Prop :=
∀ (E : Type) (ncodeunits : JChar → Index) (encoding : CharEncoding ncodeunits) (c : JChar),
    (encoding.bytes c).getLast?.map (Except.ok (ε := E)) =
      some (lastUtf8Byte (fun c => .ok (ncodeunits c)) c)

/-- The bloom mask has exactly one bit set, at the input value modulo 64. -/
def BloomBitSpec : Prop :=
∀ (B E : Type) (value : B → Int) (b : B) (mask : UInt64),
    byteBloom (E := E) value b = .ok mask →
      ∀ k : Fin 64, mask.toNat.testBit k.val = decide (k.val = (value b % 64).toNat)

/-- memchr returns the least matching byte index in the requested suffix, restores offset axes, and returns nothing exactly when the suffix has no match. -/
def MemchrFirstSpec : Prop :=
(∀ (A E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8),
    CMemoryLaws ops v → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      FirstIndex (byteMatches v (fun x => x == b) a) i.val (memchrUInt8 ops a b i)) ∧
  (∀ (A E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)),
    CMemoryLaws ops v → (∀ b, ops.value b = b.val) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      FirstIndex (byteMatches v (fun x => x.val == b.val) a) i.val (memchrInt8 ops a b i))
theorem memchrFirstSpec_proven : MemchrFirstSpec := by
  unfold MemchrFirstSpec
  constructor
  · intro A E ops v hmem hvalue a b i hstart hstop
    let len := Int.ofNat (v.elements a).length
    let off := i.val - v.first a
    let count := len - off
    have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
    have hlast : (ops.lastindex a).val = v.first a + len - 1 := by
      simpa [len] using hmem.bytes.lastindex a
    have hlen : len ≤ IntTy.max .i64 := by
      have h := (ops.length a).property.2
      rw [hmem.bytes.length a] at h
      exact h
    have hiBounds : IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 := i.property
    have hfirstBounds := (ops.firstindex a).property
    have hlastBounds := (ops.lastindex a).property
    have hstopLen : i.val < v.first a + len := by simpa [len] using hstop
    have hoff : 0 ≤ off := by dsimp [off]; omega
    have hoffLtLen : off < len := by dsimp [off]; omega
    have hcount : 0 ≤ count := by dsimp [count, off]; omega
    have htotal : off + count ≤ len := by dsimp [count]; omega
    have hstartIndex : (ops.firstindex a).val ≤ i.val := by rw [hfirst]; exact hstart
    have hstopIndex : i.val < (ops.firstindex a).val + len := by
      rw [← hfirst] at hstopLen
      exact hstopLen
    have hlastIndex : (ops.lastindex a).val = (ops.firstindex a).val + len - 1 := by
      calc
        (ops.lastindex a).val = v.first a + len - 1 := hlast
        _ = (ops.firstindex a).val + len - 1 := by rw [hfirst]
    have hoffLeLen : off ≤ len := by omega
    have hoffRange : IntTy.min .i64 ≤ off ∧ off ≤ IntTy.max .i64 := by
      constructor
      · calc
          IntTy.min .i64 ≤ 0 := by decide
          _ ≤ off := by omega
      · calc
          off ≤ len := hoffLeLen
          _ ≤ IntTy.max .i64 := hlen
    have hsubNonneg : 0 ≤ (ops.lastindex a).val - i.val := by
      rw [hlastIndex]
      omega
    have hsubLeLen : (ops.lastindex a).val - i.val ≤ len := by
      rw [hlastIndex]
      omega
    have hsubRange : IntTy.min .i64 ≤ (ops.lastindex a).val - i.val ∧
        (ops.lastindex a).val - i.val ≤ IntTy.max .i64 := by
      constructor
      · calc
          IntTy.min .i64 ≤ 0 := by decide
          _ ≤ (ops.lastindex a).val - i.val := hsubNonneg
      · calc
          (ops.lastindex a).val - i.val ≤ len := hsubLeLen
          _ ≤ IntTy.max .i64 := hlen
    have hcountRange : IntTy.min .i64 ≤ count ∧ count ≤ IntTy.max .i64 := by
      constructor <;> omega
    have hsubRangeExpr : IntTy.min .i64 ≤ v.first a + len - 1 - i.val ∧
        v.first a + len - 1 - i.val ≤ IntTy.max .i64 := by
      rw [← hlast]
      exact hsubRange
    have hstartArg : (i - ops.firstindex a).val = off := by
      change wrapInt .i64 (i.val - (ops.firstindex a).val) = off
      rw [hfirst]
      exact wrapInt_of_inRange .i64 off hoffRange
    have hsub : (ops.lastindex a - i).val =
        v.first a + len - 1 - i.val := by
      change wrapInt .i64 ((ops.lastindex a).val - i.val) =
        v.first a + len - 1 - i.val
      rw [hlast]
      exact wrapInt_of_inRange .i64 _ hsubRangeExpr
    have hcountFormula : v.first a + len - 1 - i.val + 1 = count := by
      change v.first a + len - 1 - i.val + 1 = len - (i.val - v.first a)
      omega
    have hcountArg : (ops.lastindex a - i + int 1).val = count := by
      change wrapInt .i64 ((ops.lastindex a - i).val + (int 1).val) = count
      rw [hsub]
      have hone : (int 1).val = 1 := by decide
      rw [hone, hcountFormula]
      exact wrapInt_of_inRange .i64 count hcountRange
    have hmaxI64U64 : IntTy.max .i64 ≤ IntTy.max .u64 := by decide
    have hcountU64 : IntTy.min .u64 ≤ count ∧ count ≤ IntTy.max .u64 := by
      constructor
      · change 0 ≤ count
        exact hcount
      · calc
          count ≤ IntTy.max .i64 := hcountRange.2
          _ ≤ IntTy.max .u64 := hmaxI64U64
    have hcountCall :
        JInt.rem .u64 (ops.lastindex a - i + int 1) = JInt.wrap .u64 count := by
      apply Subtype.ext
      change wrapInt .u64 (ops.lastindex a - i + int 1).val = wrapInt .u64 count
      rw [hcountArg]
    have hsum : off + count = len := by dsimp [count]; omega
    have hnatSum : off.toNat + count.toNat = (v.elements a).length := by
      have hoffCast : (off.toNat : Int) = off := Int.toNat_of_nonneg hoff
      have hcountCast : (count.toNat : Int) = count := Int.toNat_of_nonneg hcount
      have hlenNonneg : 0 ≤ len := by dsimp [len]; omega
      have hlenCast : (len.toNat : Int) = len := Int.toNat_of_nonneg hlenNonneg
      have hsumCast : (off.toNat : Int) + count.toNat = (len.toNat : Int) := by
        rw [hoffCast, hcountCast, hlenCast]
        exact hsum
      exact_mod_cast hsumCast
    have hdropLen : ((v.elements a).drop off.toNat).length = count.toNat := by
      rw [List.length_drop]
      omega
    have hguard :
        (List.findIdx? (fun x : UInt8 =>
          ops.value x % 256 == (JInt.wrap .i32 (Int.ofNat b.toNat)).val % 256)
          ((v.elements a).drop off.toNat)).bind
          (Option.guard fun k => decide (k < count.toNat)) =
        List.findIdx? (fun x : UInt8 =>
          ops.value x % 256 == (JInt.wrap .i32 (Int.ofNat b.toNat)).val % 256)
          ((v.elements a).drop off.toNat) := by
      cases hfind : List.findIdx?
          (fun x : UInt8 => ops.value x % 256 ==
            (JInt.wrap .i32 (Int.ofNat b.toNat)).val % 256)
          ((v.elements a).drop off.toNat) with
      | none => rfl
      | some k =>
        have hk : k < ((v.elements a).drop off.toNat).length :=
          (List.findIdx?_eq_some_iff_getElem.mp hfind).1
        rw [hdropLen] at hk
        have hkInt : (k : Int) < count := by
          have hk' : (k : Int) < (count.toNat : Int) := by exact_mod_cast hk
          rw [Int.toNat_of_nonneg hcount] at hk'
          exact hk'
        simp [hfind, hkInt]
    have hneedle : (JInt.wrap .i32 (Int.ofNat b.toNat)).val = Int.ofNat b.toNat := by
      have hb := b.toNat_lt
      change wrapInt .i32 (Int.ofNat b.toNat) = Int.ofNat b.toNat
      apply wrapInt_of_inRange
      constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
    have hbyteEqual : ∀ x : UInt8,
        ((ops.value x % 256 == (JInt.wrap .i32 (Int.ofNat b.toNat)).val % 256) =
          (x == b)) := by
      intro x
      rw [hvalue x, hneedle]
      have hxlt : x.toNat < 256 := by simpa using x.toNat_lt
      have hblt : b.toNat < 256 := by simpa using b.toNat_lt
      have hxmod : Int.ofNat x.toNat % 256 = Int.ofNat x.toNat :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hxlt)
      have hbmod : Int.ofNat b.toNat % 256 = Int.ofNat b.toNat :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hblt)
      rw [hxmod, hbmod]
      by_cases heq : x.toNat = b.toNat
      · have hxb : x = b := UInt8.toNat.inj heq
        subst b
        simp
      · have hneInt : Int.ofNat x.toNat ≠ Int.ofNat b.toNat := by
          intro h
          apply heq
          exact Int.ofNat_inj.mp h
        have hneByte : x ≠ b := by
          intro h
          apply heq
          exact congrArg UInt8.toNat h
        have hIntFalse : (Int.ofNat x.toNat == Int.ofNat b.toNat) = false := by
          rw [beq_eq_false_iff_ne]
          exact hneInt
        have hByteFalse : (x == b) = false := by
          rw [beq_eq_false_iff_ne]
          exact hneByte
        rw [hIntFalse, hByteFalse]
    have hrelNat : ∀ j, i.val ≤ j →
        (j - v.first a).toNat = off.toNat + (j - i.val).toNat := by
      intro j hj
      have hdecomp : j - v.first a = off + (j - i.val) := by dsimp [off]; omega
      have hwhole : 0 ≤ j - v.first a := by omega
      have htail : 0 ≤ j - i.val := by omega
      have hoffCast : (off.toNat : Int) = off := Int.toNat_of_nonneg hoff
      have htailCast : ((j - i.val).toNat : Int) = j - i.val :=
        Int.toNat_of_nonneg htail
      have hwholeCast : ((j - v.first a).toNat : Int) = j - v.first a :=
        Int.toNat_of_nonneg hwhole
      have hsumCast : ((off.toNat + (j - i.val).toNat : Nat) : Int) =
          j - v.first a := by
        calc
          _ = (off.toNat : Int) + ((j - i.val).toNat : Int) := by push_cast; rfl
          _ = off + (j - i.val) := by rw [hoffCast, htailCast]
          _ = j - v.first a := hdecomp.symm
      apply Int.ofNat_inj.mp
      calc
        ((j - v.first a).toNat : Int) = j - v.first a := hwholeCast
        _ = (off.toNat + (j - i.val).toNat : Nat) := hsumCast.symm
    have hdropMatch : ∀ j, i.val ≤ j →
        byteMatches v (fun x => x == b) a j →
        ((v.elements a).drop off.toNat)[(j - i.val).toNat]? = some b := by
      intro j hj hmatch
      dsimp [byteMatches, byteAt] at hmatch
      rcases hmatch with ⟨_, x, hget, heq⟩
      have hx : x = b := by simpa only [beq_iff_eq] using heq
      subst x
      rw [List.getElem?_drop, ← hrelNat j hj]
      exact hget
    have hcall := hmem.memchr a off count
      (JInt.wrap .i32 (Int.ofNat b.toNat)) hoff hcount htotal
    simp only [FirstIndex, memchrUInt8, JInt.rem, hstartArg, hcountArg, hcountCall]
    rw [hcall]
    simp only [List.findIdx?_take]
    rw [hguard]
    simp only [hbyteEqual]
    simp [byteMatches, byteAt, hvalue, hmem.bytes.firstindex, hmem.bytes.lastindex,
      hmem.bytes.length]
    cases hfind : List.findIdx? (fun x : UInt8 => x == b) ((v.elements a).drop off.toNat) with
    | none =>
      have hnoAccept : ∀ j, i.val ≤ j →
          ¬ byteMatches v (fun x => x == b) a j := by
        intro j hj hmatch
        have hget := hdropMatch j hj hmatch
        rcases List.getElem?_eq_some_iff.mp hget with ⟨hd, hv⟩
        have hmemDrop : b ∈ (v.elements a).drop off.toNat :=
          List.mem_iff_getElem.mpr ⟨(j - i.val).toNat, hd, hv⟩
        have hfalse := (List.findIdx?_eq_none_iff.mp hfind) b hmemDrop
        simp at hfalse
      simp [hfind, JInt.wrap, wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      have hnoRaw : ∀ j, i.val ≤ j → v.first a ≤ j →
          ¬ (v.elements a)[(j - v.first a).toNat]? = some b := by
        intro j hj hfirstJ hget
        have hm : byteMatches v (fun x => x == b) a j := by
          dsimp [byteMatches, byteAt]
          exact ⟨hfirstJ, b, hget, by simp⟩
        exact hnoAccept j hj hm
      constructor
      · intro a1 b1
        constructor
        · intro h
          cases h
        · intro h
          rcases h with ⟨hstart, ⟨hfirstJ, hget⟩, _⟩
          have hm : byteMatches v (fun x => x == b) a a1 := by
            dsimp [byteMatches, byteAt]
            exact ⟨hfirstJ, b, hget, by simp⟩
          exact (hnoAccept a1 hstart hm).elim
      · constructor
        · intro _ j hj hfirstJ
          exact hnoRaw j hj hfirstJ
        · intro h
          rfl
    | some k =>
      rcases List.findIdx?_eq_some_iff_getElem.mp hfind with
        ⟨hkBound, hpred, hbefore⟩
      have hmatchEq : (List.drop off.toNat (v.elements a))[k] = b := by
        simpa only [beq_iff_eq] using hpred
      have hdropGet : (List.drop off.toNat (v.elements a))[k]? = some b := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hkBound, hmatchEq⟩
      have hkInt : (k : Int) < count := by
        rw [hdropLen] at hkBound
        have hkNat : (k : Int) < (count.toNat : Int) := by exact_mod_cast hkBound
        rw [Int.toNat_of_nonneg hcount] at hkNat
        exact hkNat
      have hiOffset : i.val = (ops.firstindex a).val + off := by
        rw [hfirst]
        dsimp [off]
        omega
      let idx : Int := i.val + (k : Int)
      have hidxBase : idx = (ops.firstindex a).val + off + (k : Int) := by
        dsimp [idx]
        rw [hiOffset]
      have hindexUpper : idx ≤ (ops.lastindex a).val := by
        rw [hidxBase, hlastIndex]
        have hsmall : off + (k : Int) < len := by
          dsimp [count] at hsum
          omega
        omega
      have hindexBounds : IntTy.min .i64 ≤ idx ∧ idx ≤ IntTy.max .i64 := by
        constructor
        · dsimp [idx]
          omega
        · calc
            idx ≤ (ops.lastindex a).val := hindexUpper
            _ ≤ IntTy.max .i64 := hlastBounds.2
      have hindexVal : (int idx).val = idx := by
        change wrapInt .i64 idx = idx
        exact wrapInt_of_inRange .i64 idx hindexBounds
      have haddrLen : (ops.pointer a).val + len < 2 ^ 64 := by
        simpa [len] using hmem.addressRange a
      have hsmall : off + (k : Int) < len := by
        dsimp [count] at hsum
        omega
      have hptrSumLt : (ops.pointer a).val + off + (k : Int) < 2 ^ 64 := by omega
      have hptrNonneg : 0 ≤ (ops.pointer a).val := by
        have hp := (ops.pointer a).property.1
        change 0 ≤ (ops.pointer a).val at hp
        exact hp
      have hptrRange : IntTy.min .u64 ≤ (ops.pointer a).val + off + (k : Int) ∧
          (ops.pointer a).val + off + (k : Int) ≤ IntTy.max .u64 := by
        constructor
        · change 0 ≤ (ops.pointer a).val + off + (k : Int)
          omega
        · change (ops.pointer a).val + off + (k : Int) ≤ 2 ^ 64 - 1
          omega
      have hptrWrap :
          (JInt.wrap .u64 ((ops.pointer a).val + off + (k : Int))).val =
            (ops.pointer a).val + off + (k : Int) := by
        change wrapInt .u64 _ = _
        exact wrapInt_of_inRange .u64 _ hptrRange
      have hptrNonzero : (ops.pointer a).val + off + (k : Int) ≠ 0 := by
        intro hz
        have hp := hmem.nonnull a
        change (ops.pointer a).val ≠ 0 at hp
        omega
      have hiOffsetV : i.val = v.first a + off := by
        simpa [hfirst] using hiOffset
      have hmap : (ops.pointer a).val + off + (k : Int) -
          (ops.pointer a).val + v.first a = idx := by
        dsimp [idx]
        rw [hiOffsetV]
        omega
      have hidxStart : v.first a ≤ idx := by
        dsimp [idx]
        rw [hiOffsetV]
        omega
      have hidxOffset : (idx - i.val).toNat = k := by
        have hdiff : idx - i.val = (k : Int) := by
          dsimp [idx]
          omega
        rw [hdiff]
        rfl
      have hgetIdx : (v.elements a)[(idx - v.first a).toNat]? = some b := by
        rw [hrelNat idx (by dsimp [idx]; omega), hidxOffset]
        simpa only [List.getElem?_drop] using hdropGet
      have hleast : ∀ j, i.val ≤ j → byteMatches v (fun x => x == b) a j →
          idx ≤ j := by
        intro j hj hmatch
        by_cases hle : idx ≤ j
        · exact hle
        · have hdLt : (j - i.val).toNat < k := by
            dsimp [idx] at hle
            omega
          have hget := hdropMatch j hj hmatch
          rcases List.getElem?_eq_some_iff.mp hget with ⟨hd, hv⟩
          have hfalse := hbefore (j - i.val).toNat hdLt
          rw [hv] at hfalse
          simp at hfalse
      have hacceptIdx : byteMatches v (fun x => x == b) a idx := by
        dsimp [byteMatches, byteAt]
        exact ⟨hidxStart, b, hgetIdx, by simp⟩
      simp [hfind, hindexVal, hptrWrap, hptrNonzero, hmap, Functor.map, Except.map]
      constructor
      · intro a1 b1
        constructor
        · intro heq
          have hval : idx = a1 := by
            have hv := congrArg (fun q : Index => q.val) heq
            simpa [hindexVal] using hv
          subst a1
          refine ⟨by dsimp [idx]; omega, ⟨hidxStart, hgetIdx⟩, ?_⟩
          intro j hj hfirstJ hget
          have hm : byteMatches v (fun x => x == b) a j := by
            dsimp [byteMatches, byteAt]
            exact ⟨hfirstJ, b, hget, by simp⟩
          exact hleast j hj hm
        · intro h
          rcases h with ⟨hstart, ⟨hfirstJ, hget⟩, hmin⟩
          have hm : byteMatches v (fun x => x == b) a a1 := by
            dsimp [byteMatches, byteAt]
            exact ⟨hfirstJ, b, hget, by simp⟩
          have hidxLe : idx ≤ a1 := hleast a1 hstart hm
          have hidxAfter : i.val ≤ idx := by dsimp [idx]; omega
          have ha1Le : a1 ≤ idx := hmin idx hidxAfter hidxStart hgetIdx
          have heqIdx : idx = a1 := by omega
          apply Subtype.ext
          simpa [hindexVal] using heqIdx
      · exact ⟨idx, by dsimp [idx]; omega, hidxStart, hgetIdx⟩
  · intro A E ops v hmem hvalue a b i hstart hstop
    let len := Int.ofNat (v.elements a).length
    let off := i.val - v.first a
    let count := len - off
    have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
    have hlast : (ops.lastindex a).val = v.first a + len - 1 := by
      simpa [len] using hmem.bytes.lastindex a
    have hlen : len ≤ IntTy.max .i64 := by
      have h := (ops.length a).property.2
      rw [hmem.bytes.length a] at h
      exact h
    have hiBounds : IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 := i.property
    have hfirstBounds := (ops.firstindex a).property
    have hlastBounds := (ops.lastindex a).property
    have hstopLen : i.val < v.first a + len := by simpa [len] using hstop
    have hoff : 0 ≤ off := by dsimp [off]; omega
    have hoffLtLen : off < len := by dsimp [off]; omega
    have hcount : 0 ≤ count := by dsimp [count, off]; omega
    have htotal : off + count ≤ len := by dsimp [count]; omega
    have hstartIndex : (ops.firstindex a).val ≤ i.val := by rw [hfirst]; exact hstart
    have hstopIndex : i.val < (ops.firstindex a).val + len := by
      rw [← hfirst] at hstopLen
      exact hstopLen
    have hlastIndex : (ops.lastindex a).val = (ops.firstindex a).val + len - 1 := by
      calc
        (ops.lastindex a).val = v.first a + len - 1 := hlast
        _ = (ops.firstindex a).val + len - 1 := by rw [hfirst]
    have hoffLeLen : off ≤ len := by omega
    have hoffRange : IntTy.min .i64 ≤ off ∧ off ≤ IntTy.max .i64 := by
      constructor
      · calc
          IntTy.min .i64 ≤ 0 := by decide
          _ ≤ off := by omega
      · calc
          off ≤ len := hoffLeLen
          _ ≤ IntTy.max .i64 := hlen
    have hsubNonneg : 0 ≤ (ops.lastindex a).val - i.val := by
      rw [hlastIndex]
      omega
    have hsubLeLen : (ops.lastindex a).val - i.val ≤ len := by
      rw [hlastIndex]
      omega
    have hsubRange : IntTy.min .i64 ≤ (ops.lastindex a).val - i.val ∧
        (ops.lastindex a).val - i.val ≤ IntTy.max .i64 := by
      constructor
      · calc
          IntTy.min .i64 ≤ 0 := by decide
          _ ≤ (ops.lastindex a).val - i.val := hsubNonneg
      · calc
          (ops.lastindex a).val - i.val ≤ len := hsubLeLen
          _ ≤ IntTy.max .i64 := hlen
    have hcountRange : IntTy.min .i64 ≤ count ∧ count ≤ IntTy.max .i64 := by
      constructor <;> omega
    have hsubRangeExpr : IntTy.min .i64 ≤ v.first a + len - 1 - i.val ∧
        v.first a + len - 1 - i.val ≤ IntTy.max .i64 := by
      rw [← hlast]
      exact hsubRange
    have hstartArg : (i - ops.firstindex a).val = off := by
      change wrapInt .i64 (i.val - (ops.firstindex a).val) = off
      rw [hfirst]
      exact wrapInt_of_inRange .i64 off hoffRange
    have hsub : (ops.lastindex a - i).val =
        v.first a + len - 1 - i.val := by
      change wrapInt .i64 ((ops.lastindex a).val - i.val) =
        v.first a + len - 1 - i.val
      rw [hlast]
      exact wrapInt_of_inRange .i64 _ hsubRangeExpr
    have hcountFormula : v.first a + len - 1 - i.val + 1 = count := by
      change v.first a + len - 1 - i.val + 1 = len - (i.val - v.first a)
      omega
    have hcountArg : (ops.lastindex a - i + int 1).val = count := by
      change wrapInt .i64 ((ops.lastindex a - i).val + (int 1).val) = count
      rw [hsub]
      have hone : (int 1).val = 1 := by decide
      rw [hone, hcountFormula]
      exact wrapInt_of_inRange .i64 count hcountRange
    have hmaxI64U64 : IntTy.max .i64 ≤ IntTy.max .u64 := by decide
    have hcountU64 : IntTy.min .u64 ≤ count ∧ count ≤ IntTy.max .u64 := by
      constructor
      · change 0 ≤ count
        exact hcount
      · calc
          count ≤ IntTy.max .i64 := hcountRange.2
          _ ≤ IntTy.max .u64 := hmaxI64U64
    have hcountCall :
        JInt.rem .u64 (ops.lastindex a - i + int 1) = JInt.wrap .u64 count := by
      apply Subtype.ext
      change wrapInt .u64 (ops.lastindex a - i + int 1).val = wrapInt .u64 count
      rw [hcountArg]
    have hsum : off + count = len := by dsimp [count]; omega
    have hnatSum : off.toNat + count.toNat = (v.elements a).length := by
      have hoffCast : (off.toNat : Int) = off := Int.toNat_of_nonneg hoff
      have hcountCast : (count.toNat : Int) = count := Int.toNat_of_nonneg hcount
      have hlenNonneg : 0 ≤ len := by dsimp [len]; omega
      have hlenCast : (len.toNat : Int) = len := Int.toNat_of_nonneg hlenNonneg
      have hsumCast : (off.toNat : Int) + count.toNat = (len.toNat : Int) := by
        rw [hoffCast, hcountCast, hlenCast]
        exact hsum
      exact_mod_cast hsumCast
    have hdropLen : ((v.elements a).drop off.toNat).length = count.toNat := by
      rw [List.length_drop]
      omega
    have hcall := hmem.memchr a off count (JInt.wrap .i32 b.val) hoff hcount htotal
    have hguard :
        (List.findIdx? (fun x : JInt .i8 =>
          ops.value x % 256 == (JInt.wrap .i32 b.val).val % 256)
          ((v.elements a).drop off.toNat)).bind
          (Option.guard fun k => decide (k < count.toNat)) =
        List.findIdx? (fun x : JInt .i8 =>
          ops.value x % 256 == (JInt.wrap .i32 b.val).val % 256)
          ((v.elements a).drop off.toNat) := by
      cases hfind : List.findIdx? (fun x : JInt .i8 =>
          ops.value x % 256 == (JInt.wrap .i32 b.val).val % 256)
          ((v.elements a).drop off.toNat) with
      | none => rfl
      | some k =>
        have hk : k < ((v.elements a).drop off.toNat).length :=
          (List.findIdx?_eq_some_iff_getElem.mp hfind).1
        rw [hdropLen] at hk
        have hkInt : (k : Int) < count := by
          have hk' : (k : Int) < (count.toNat : Int) := by exact_mod_cast hk
          rw [Int.toNat_of_nonneg hcount] at hk'
          exact hk'
        simp [hfind, hkInt]
    have hneedle : (JInt.wrap .i32 b.val).val = b.val := by
      change wrapInt .i32 b.val = b.val
      have hb : IntTy.min .i32 ≤ b.val ∧ b.val ≤ IntTy.max .i32 := by
        constructor
        · calc
            IntTy.min .i32 ≤ IntTy.min .i8 := by decide
            _ ≤ b.val := b.property.1
        · calc
            b.val ≤ IntTy.max .i8 := b.property.2
            _ ≤ IntTy.max .i32 := by decide
      exact wrapInt_of_inRange .i32 b.val hb
    have hmodEq : ∀ x : JInt .i8, x.val % 256 = b.val % 256 ↔ x.val = b.val := by
      intro x
      have hx : -128 ≤ x.val ∧ x.val ≤ 127 := by
        simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using x.property
      have hb : -128 ≤ b.val ∧ b.val ≤ 127 := by
        simpa [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] using b.property
      constructor
      · intro hmod
        omega
      · intro heq
        rw [heq]
    have hbyteEqual : ∀ x : JInt .i8,
        ((ops.value x % 256 == (JInt.wrap .i32 b.val).val % 256) =
          (x.val == b.val)) := by
      intro x
      rw [hvalue x, hneedle]
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      exact hmodEq x
    have hrelNat : ∀ j, i.val ≤ j →
        (j - v.first a).toNat = off.toNat + (j - i.val).toNat := by
      intro j hj
      have hdecomp : j - v.first a = off + (j - i.val) := by dsimp [off]; omega
      have hwhole : 0 ≤ j - v.first a := by omega
      have htail : 0 ≤ j - i.val := by omega
      have hoffCast : (off.toNat : Int) = off := Int.toNat_of_nonneg hoff
      have htailCast : ((j - i.val).toNat : Int) = j - i.val :=
        Int.toNat_of_nonneg htail
      have hwholeCast : ((j - v.first a).toNat : Int) = j - v.first a :=
        Int.toNat_of_nonneg hwhole
      have hsumCast : ((off.toNat + (j - i.val).toNat : Nat) : Int) =
          j - v.first a := by
        calc
          _ = (off.toNat : Int) + ((j - i.val).toNat : Int) := by push_cast; rfl
          _ = off + (j - i.val) := by rw [hoffCast, htailCast]
          _ = j - v.first a := hdecomp.symm
      apply Int.ofNat_inj.mp
      calc
        ((j - v.first a).toNat : Int) = j - v.first a := hwholeCast
        _ = (off.toNat + (j - i.val).toNat : Nat) := hsumCast.symm
    have hdropMatch : ∀ j, i.val ≤ j →
        byteMatches v (fun x => x.val == b.val) a j →
        ((v.elements a).drop off.toNat)[(j - i.val).toNat]? = some b := by
      intro j hj hmatch
      dsimp [byteMatches, byteAt] at hmatch
      rcases hmatch with ⟨_, x, hget, heq⟩
      have hxval : x.val = b.val := by simpa only [beq_iff_eq] using heq
      have hx : x = b := by
        apply Subtype.ext
        exact hxval
      subst x
      rw [List.getElem?_drop, ← hrelNat j hj]
      exact hget
    simp only [FirstIndex, memchrInt8, JInt.rem, hstartArg, hcountArg, hcountCall]
    rw [hcall]
    simp only [List.findIdx?_take]
    rw [hguard]
    simp only [hbyteEqual]
    cases hfind : List.findIdx? (fun x : JInt .i8 => x.val == b.val)
        ((v.elements a).drop off.toNat) with
    | none =>
      have hnoAccept : ∀ j, i.val ≤ j →
          ¬ byteMatches v (fun x => x.val == b.val) a j := by
        intro j hj hmatch
        have hget := hdropMatch j hj hmatch
        rcases List.getElem?_eq_some_iff.mp hget with ⟨hd, hv⟩
        have hmemDrop : b ∈ (v.elements a).drop off.toNat :=
          List.mem_iff_getElem.mpr ⟨(j - i.val).toNat, hd, hv⟩
        have hfalse := (List.findIdx?_eq_none_iff.mp hfind) b hmemDrop
        simp at hfalse
      simp [hfind, JInt.wrap, wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      have hnoRaw : ∀ j, i.val ≤ j →
          ¬ byteMatches v (fun x => x.val == b.val) a j := by
        intro j hj hmatch
        exact hnoAccept j hj hmatch
      constructor
      · intro a1 b1
        constructor
        · intro h
          cases h
        · intro h
          rcases h with ⟨hstart, hmatch, _⟩
          exact (hnoAccept a1 hstart hmatch).elim
      · constructor
        · intro h j hj
          exact hnoRaw j hj
        · intro h
          rfl
    | some k =>
      rcases List.findIdx?_eq_some_iff_getElem.mp hfind with
        ⟨hkBound, hpred, hbefore⟩
      have hmatchEq : (List.drop off.toNat (v.elements a))[k] = b := by
        have hval : (List.drop off.toNat (v.elements a))[k].val = b.val := by
          simpa only [beq_iff_eq] using hpred
        apply Subtype.ext
        exact hval
      have hdropGet : (List.drop off.toNat (v.elements a))[k]? = some b := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨hkBound, hmatchEq⟩
      have hkInt : (k : Int) < count := by
        rw [hdropLen] at hkBound
        have hkNat : (k : Int) < (count.toNat : Int) := by exact_mod_cast hkBound
        rw [Int.toNat_of_nonneg hcount] at hkNat
        exact hkNat
      have hiOffset : i.val = (ops.firstindex a).val + off := by
        rw [hfirst]
        dsimp [off]
        omega
      let idx : Int := i.val + (k : Int)
      have hidxBase : idx = (ops.firstindex a).val + off + (k : Int) := by
        dsimp [idx]
        rw [hiOffset]
      have hindexUpper : idx ≤ (ops.lastindex a).val := by
        rw [hidxBase, hlastIndex]
        have hsmall : off + (k : Int) < len := by
          dsimp [count] at hsum
          omega
        omega
      have hindexBounds : IntTy.min .i64 ≤ idx ∧ idx ≤ IntTy.max .i64 := by
        constructor
        · dsimp [idx]
          omega
        · calc
            idx ≤ (ops.lastindex a).val := hindexUpper
            _ ≤ IntTy.max .i64 := hlastBounds.2
      have hindexVal : (int idx).val = idx := by
        change wrapInt .i64 idx = idx
        exact wrapInt_of_inRange .i64 idx hindexBounds
      have haddrLen : (ops.pointer a).val + len < 2 ^ 64 := by
        simpa [len] using hmem.addressRange a
      have hsmall : off + (k : Int) < len := by
        dsimp [count] at hsum
        omega
      have hptrSumLt : (ops.pointer a).val + off + (k : Int) < 2 ^ 64 := by omega
      have hptrNonneg : 0 ≤ (ops.pointer a).val := by
        have hp := (ops.pointer a).property.1
        change 0 ≤ (ops.pointer a).val at hp
        exact hp
      have hptrRange : IntTy.min .u64 ≤ (ops.pointer a).val + off + (k : Int) ∧
          (ops.pointer a).val + off + (k : Int) ≤ IntTy.max .u64 := by
        constructor
        · change 0 ≤ (ops.pointer a).val + off + (k : Int)
          omega
        · change (ops.pointer a).val + off + (k : Int) ≤ 2 ^ 64 - 1
          omega
      have hptrWrap :
          (JInt.wrap .u64 ((ops.pointer a).val + off + (k : Int))).val =
            (ops.pointer a).val + off + (k : Int) := by
        change wrapInt .u64 _ = _
        exact wrapInt_of_inRange .u64 _ hptrRange
      have hptrNonzero : (ops.pointer a).val + off + (k : Int) ≠ 0 := by
        intro hz
        have hp := hmem.nonnull a
        change (ops.pointer a).val ≠ 0 at hp
        omega
      have hiOffsetV : i.val = v.first a + off := by
        simpa [hfirst] using hiOffset
      have hmap : (ops.pointer a).val + off + (k : Int) -
          (ops.pointer a).val + v.first a = idx := by
        dsimp [idx]
        rw [hiOffsetV]
        omega
      have hmapIndex : (ops.pointer a).val + off + (k : Int) -
          (ops.pointer a).val + (ops.firstindex a).val = idx := by
        rw [hfirst]
        exact hmap
      have hraw : (int ((ops.pointer a).val + off + (k : Int) -
          (ops.pointer a).val + (ops.firstindex a).val)).val = idx := by
        rw [hmapIndex]
        exact hindexVal
      have hidxStart : v.first a ≤ idx := by
        dsimp [idx]
        rw [hiOffsetV]
        omega
      have hidxOffset : (idx - i.val).toNat = k := by
        have hdiff : idx - i.val = (k : Int) := by
          dsimp [idx]
          omega
        rw [hdiff]
        rfl
      have hgetIdx : (v.elements a)[(idx - v.first a).toNat]? = some b := by
        rw [hrelNat idx (by dsimp [idx]; omega), hidxOffset]
        simpa only [List.getElem?_drop] using hdropGet
      have hleast : ∀ j, i.val ≤ j → byteMatches v (fun x => x.val == b.val) a j →
          idx ≤ j := by
        intro j hj hmatch
        by_cases hle : idx ≤ j
        · exact hle
        · have hdLt : (j - i.val).toNat < k := by
            dsimp [idx] at hle
            omega
          have hget := hdropMatch j hj hmatch
          rcases List.getElem?_eq_some_iff.mp hget with ⟨hd, hv⟩
          have hfalse := hbefore (j - i.val).toNat hdLt
          rw [hv] at hfalse
          simp at hfalse
      have hacceptIdx : byteMatches v (fun x => x.val == b.val) a idx := by
        dsimp [byteMatches, byteAt]
        exact ⟨hidxStart, b, hgetIdx, by simp⟩
      simp [hfind, hindexVal, hptrWrap, hptrNonzero, hmap, Functor.map, Except.map]
      constructor
      · intro a1 b1
        constructor
        · intro heq
          have hval : idx = a1 := by
            have hv := congrArg (fun q : Index => q.val) heq
            exact hraw.symm.trans hv
          subst a1
          refine ⟨by dsimp [idx]; omega, hacceptIdx, ?_⟩
          intro j hj hmatch
          exact hleast j hj hmatch
        · intro h
          rcases h with ⟨hstart, hmatch, hmin⟩
          have hidxLe : idx ≤ a1 := hleast a1 hstart hmatch
          have hidxAfter : i.val ≤ idx := by dsimp [idx]; omega
          have ha1Le : a1 ≤ idx := hmin idx hidxAfter hacceptIdx
          have heqIdx : idx = a1 := by omega
          apply Subtype.ext
          exact hraw.trans heqIdx
      · exact ⟨idx, by dsimp [idx]; omega, hacceptIdx⟩

/-- memrchr returns the greatest matching byte index in the requested prefix, restores offset axes, and returns nothing exactly when the prefix has no match. -/
def MemrchrLastSpec : Prop :=
(∀ (A E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8),
    CMemoryLaws ops v → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      LastIndex (byteMatches v (fun x => x == b) a) i.val (memrchrUInt8 ops a b i)) ∧
  (∀ (A E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)),
    CMemoryLaws ops v → (∀ b, ops.value b = b.val) →
    ∀ a b i, v.first a ≤ i.val → i.val < v.first a + Int.ofNat (v.elements a).length →
      LastIndex (byteMatches v (fun x => x.val == b.val) a) i.val (memrchrInt8 ops a b i))
private theorem intNatSubPred (n k : Nat) (hk : k < n) :
    Int.ofNat n - 1 - (k : Int) = Int.ofNat (n - 1 - k) := by
  have hkplus : Int.ofNat (k + 1) = (k : Int) + 1 := by
    simp
  have hsubcast : Int.ofNat (n - (k + 1)) =
      Int.ofNat n - Int.ofNat (k + 1) := Int.ofNat_sub (Nat.succ_le_of_lt hk)
  calc
    Int.ofNat n - 1 - (k : Int) =
        Int.ofNat n - Int.ofNat (k + 1) := by rw [hkplus]; omega
    _ = Int.ofNat (n - (k + 1)) := hsubcast.symm
    _ = Int.ofNat (n - 1 - k) := by congr 1; omega

private theorem reverseFindIdxLast {B : Type} (xs : List B) (pred : B → Bool) (k : Nat)
    (hfind : xs.reverse.findIdx? pred = some k) :
    (∃ x, xs[xs.length - 1 - k]? = some x ∧ pred x = true) ∧
    ∀ d, xs.length - 1 - k < d → ∀ x, xs[d]? = some x → pred x = true → False := by
  rcases List.findIdx?_eq_some_iff_getElem.mp hfind with ⟨hk, hpred, hbefore⟩
  have hkLen : k < xs.length := by simpa using hk
  have hrevGet : xs.reverse[k]? = some (xs.reverse[k]) := by
    rw [List.getElem?_eq_some_iff]
    exact ⟨hk, rfl⟩
  have hget : xs[xs.length - 1 - k]? = some (xs.reverse[k]) := by
    rw [List.getElem?_reverse hkLen] at hrevGet
    exact hrevGet
  refine ⟨⟨xs.reverse[k], hget, hpred⟩, ?_⟩
  intro d hd x hgetD hpredD
  have hdLen : d < xs.length := (List.getElem?_eq_some_iff.mp hgetD).1
  let m := xs.length - 1 - d
  have hmLen : m < xs.length := by dsimp [m]; omega
  have hmK : m < k := by dsimp [m]; omega
  have hrevD : xs.reverse[m]? = some x := by
    rw [List.getElem?_reverse hmLen]
    have hidx : xs.length - 1 - m = d := by dsimp [m]; omega
    simpa [hidx] using hgetD
  rcases List.getElem?_eq_some_iff.mp hrevD with ⟨_, hval⟩
  have hfalse := hbefore m hmK
  rw [hval, hpredD] at hfalse
  simp at hfalse

private theorem lastIndexPrefixFound {A B E : Type}
    (v : ByteView A B) (a : A) (pred : B → Bool) (start finish : Int)
    (n k : Nat) (hstart : start = v.first a)
    (hfinish : finish = start + Int.ofNat n - 1)
    (hlen : n ≤ (v.elements a).length)
    (hstartRange : IntTy.min .i64 ≤ start ∧ start ≤ IntTy.max .i64)
    (hfinishRange : IntTy.min .i64 ≤ finish ∧ finish ≤ IntTy.max .i64)
    (hfind : ((v.elements a).take n).reverse.findIdx? pred = some k) :
    LastIndex (byteMatches v pred a) finish
      (.ok (some (int (start + Int.ofNat (n - 1 - k)))) : Except E (Option Index)) := by
  let xs := (v.elements a).take n
  have hxsLen : xs.length = n := by
    dsimp [xs]
    simp only [List.length_take]
    omega
  have hk : k < n := by
    have hk' := (List.findIdx?_eq_some_iff_getElem.mp hfind).1
    simpa [xs, List.length_reverse, List.length_take, Nat.min_eq_left hlen] using hk'
  let d := n - 1 - k
  have hd : d < n := by dsimp [d]; omega
  have hlastFound := reverseFindIdxLast xs pred k hfind
  rcases hlastFound.1 with ⟨x, hgetXs, hpredD⟩
  rw [hxsLen] at hgetXs
  have hgetV : (v.elements a)[d]? = some x := by
    simpa [xs, d, List.getElem?_take, hd] using hgetXs
  let idx : Int := start + Int.ofNat d
  have hidxFirst : v.first a ≤ idx := by
    dsimp [idx]
    rw [hstart]
    omega
  have hidxFinish : idx ≤ finish := by
    dsimp [idx]
    rw [hfinish]
    dsimp [d]
    omega
  have hidxBounds : IntTy.min .i64 ≤ idx ∧ idx ≤ IntTy.max .i64 := by
    constructor
    · calc
        IntTy.min .i64 ≤ start := hstartRange.1
        _ ≤ idx := by rw [hstart]; exact hidxFirst
    · calc
        idx ≤ finish := hidxFinish
        _ ≤ IntTy.max .i64 := hfinishRange.2
  have hidxVal : (int idx).val = idx := by
    change wrapInt .i64 idx = idx
    exact wrapInt_of_inRange .i64 idx hidxBounds
  have hidxDelta : (idx - v.first a).toNat = d := by
    dsimp [idx]
    rw [hstart]
    omega
  have hmatchIdx : byteMatches v pred a idx := by
    dsimp [byteMatches, byteAt]
    exact ⟨hidxFirst, x, by simpa [hidxDelta] using hgetV, hpredD⟩
  have hnoAfter := hlastFound.2
  rw [hxsLen] at hnoAfter
  have hnoLater : ∀ j, j ≤ finish → byteMatches v pred a j → j ≤ idx := by
    intro j hj hmatch
    rcases hmatch with ⟨_, x', hgetJ, hpredJ⟩
    have hjNonneg : 0 ≤ j - v.first a := by omega
    have hfinishAxis : finish = v.first a + Int.ofNat n - 1 := by
      calc
        finish = start + Int.ofNat n - 1 := hfinish
        _ = v.first a + Int.ofNat n - 1 := by rw [hstart]
    have hji : j - v.first a < Int.ofNat n := by
      rw [hfinishAxis] at hj
      omega
    have hdJCast : (((j - v.first a).toNat : Nat) : Int) = j - v.first a :=
      Int.toNat_of_nonneg hjNonneg
    have hdJ : (j - v.first a).toNat < n := by
      have hcast : ((j - v.first a).toNat : Int) < Int.ofNat n := by
        rw [hdJCast]
        exact hji
      exact Int.ofNat_lt.mp hcast
    have hgetOrig : (v.elements a)[(j - v.first a).toNat]? = some x' := by
      simpa only [byteAt] using hgetJ
    have hgetXs : xs[(j - v.first a).toNat]? = some x' := by
      dsimp [xs]
      simp only [List.getElem?_take, if_pos hdJ]
      exact hgetOrig
    by_cases hle : j ≤ idx
    · exact hle
    · have hleInt : Int.ofNat d < j - v.first a := by
        dsimp [idx] at hle
        rw [hstart] at hle
        omega
      have hdLater : d < (j - v.first a).toNat := by
        rw [← hdJCast] at hleInt
        exact Int.ofNat_lt.mp hleInt
      have hfalse := hnoAfter _ hdLater x' hgetXs hpredJ
      exact hfalse.elim
  unfold LastIndex
  constructor
  · intro i
    constructor
    · intro heq
      have hidxEq : int (start + Int.ofNat (n - 1 - k)) = i := by
        simpa only [Except.ok.injEq, Option.some.injEq] using heq
      have hidxOut : (int (start + Int.ofNat (n - 1 - k))).val = idx := by
        simpa [idx, d] using hidxVal
      rw [← hidxEq, hidxOut]
      exact ⟨hidxFinish, hmatchIdx, hnoLater⟩
    · intro h
      rcases h with ⟨hiFinish, hmatch, hgreatest⟩
      have hiLe : i.val ≤ idx := hnoLater i.val hiFinish hmatch
      have idxLe : idx ≤ i.val := hgreatest idx hidxFinish hmatchIdx
      have hival : i.val = idx := by omega
      have hidxOut : (int (start + Int.ofNat (n - 1 - k))).val = idx := by
        simpa [idx, d] using hidxVal
      have hidxEq : int (start + Int.ofNat (n - 1 - k)) = i := by
        apply Subtype.ext
        rw [hidxOut]
        exact hival.symm
      exact congrArg (fun q : Index => Except.ok (some q)) hidxEq
  · constructor
    · intro heq
      cases heq
    · intro hnone
      exact (hnone idx hidxFinish hmatchIdx).elim
private def memrchrRaw {A B E : Type} (ops : DenseOps A B E)
    (needle : JInt .i32) (a : A) (i : Index) : Except E (Option Index) := do
  let fst := ops.firstindex a
  let p := ops.pointer a
  let q ← ops.memrchrCall a p needle (JInt.rem .u64 (i - fst + int 1))
  pure (if q.val = 0 then none else some (int (q.val - p.val + fst.val)))

private theorem memrchrLastCoreCandidate {A B E : Type} [BEq B] [LawfulBEq B]
    (ops : DenseOps A B E) (v : ByteView A B) (hmem : CMemoryLaws ops v)
    (b : B) (needle : JInt .i32)
    (hbyteEqual : ∀ x : B,
      (ops.value x % 256 == needle.val % 256) = (x == b))
    (a : A) (i : Index)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    LastIndex (byteMatches v (fun x => x == b) a) i.val
      (memrchrRaw ops needle a i) := by
  let len : Int := Int.ofNat (v.elements a).length
  let off : Int := i.val - v.first a
  let count : Int := off + 1
  let fst := ops.firstindex a
  let cPred : B → Bool := fun x => ops.value x % 256 == needle.val % 256
  have hfirst : fst.val = v.first a := hmem.bytes.firstindex a
  have hlast : (ops.lastindex a).val = v.first a + len - 1 := by
    simpa [len] using hmem.bytes.lastindex a
  have hlenBound : len ≤ IntTy.max .i64 := by
    have h := (ops.length a).property.2
    rw [hmem.bytes.length a] at h
    exact h
  have hstopLen : i.val < v.first a + len := by simpa [len] using hstop
  have hoff : 0 ≤ off := by dsimp [off]; omega
  have hoffLtLen : off < len := by dsimp [off]; omega
  have hcount : 0 ≤ count := by dsimp [count]; omega
  have hcountLe : count ≤ len := by dsimp [count]; omega
  have hcountRange : IntTy.min .i64 ≤ count ∧ count ≤ IntTy.max .i64 := by
    constructor
    · calc
        IntTy.min .i64 ≤ 0 := by decide
        _ ≤ count := hcount
    · calc
        count ≤ len := hcountLe
        _ ≤ IntTy.max .i64 := hlenBound
  have hfirstBounds := fst.property
  have hiBounds : IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 := i.property
  have hoffRange : IntTy.min .i64 ≤ off ∧ off ≤ IntTy.max .i64 := by
    constructor
    · have : IntTy.min .i64 ≤ 0 := by decide
      omega
    · omega
  have hstartArg : (i - fst).val = off := by
    change wrapInt .i64 (i.val - fst.val) = off
    rw [hfirst]
    exact wrapInt_of_inRange .i64 off hoffRange
  have hone : (int 1).val = 1 := by decide
  have hcountArg : (i - fst + int 1).val = count := by
    change wrapInt .i64 ((i - fst).val + (int 1).val) = count
    rw [hstartArg, hone]
    exact wrapInt_of_inRange .i64 count hcountRange
  have hcountI64U64 : IntTy.max .i64 ≤ IntTy.max .u64 := by decide
  have hcountU64 : IntTy.min .u64 ≤ count ∧ count ≤ IntTy.max .u64 := by
    constructor
    · change 0 ≤ count
      exact hcount
    · calc
        count ≤ IntTy.max .i64 := hcountRange.2
        _ ≤ IntTy.max .u64 := hcountI64U64
  have hcountCall : JInt.rem .u64 (i - fst + int 1) = JInt.wrap .u64 count := by
    apply Subtype.ext
    change wrapInt .u64 (i - fst + int 1).val = wrapInt .u64 count
    rw [hcountArg]
  have hcountArgSource : (i - ops.firstindex a + int 1).val = count := by
    simpa [fst] using hcountArg
  have hcountCallSource :
      JInt.rem .u64 (i - ops.firstindex a + int 1) = JInt.wrap .u64 count := by
    simpa [fst] using hcountCall
  have hcall := hmem.memrchr a count needle hcount hcountLe
  have hcpredEq : cPred = (fun x : B => x == b) := funext hbyteEqual
  let n := count.toNat
  have hcountCast : (Int.ofNat n) = count := Int.toNat_of_nonneg hcount
  have hnLen : n ≤ (v.elements a).length := by
    have hcountLeNat : Int.ofNat n ≤ Int.ofNat (v.elements a).length := by
      rw [hcountCast]
      simpa [len] using hcountLe
    exact Int.ofNat_le.mp hcountLeNat
  have hfinish : i.val = v.first a + Int.ofNat n - 1 := by
    rw [hcountCast]
    dsimp [count, off]
    omega
  have hstartRange : IntTy.min .i64 ≤ v.first a ∧ v.first a ≤ IntTy.max .i64 := by
    rw [← hfirst]
    exact hfirstBounds
  have hfinishRange : IntTy.min .i64 ≤ i.val ∧ i.val ≤ IntTy.max .i64 := i.property
  have hinner := congrArg
    (fun result : Except E Pointer =>
      Except.bind result (fun q => Except.ok (ops.pointer a, q))) hcall
  let projectPair : Pointer × Pointer → Option Index := fun pq =>
    if pq.2.val = 0 then none
    else some (int (pq.2.val - pq.1.val + (ops.firstindex a).val))
  have hzeroBounds : IntTy.min .u64 ≤ 0 ∧ 0 ≤ IntTy.max .u64 := by
    constructor <;> decide
  have hzeroVal : (JInt.wrap .u64 0).val = 0 := by
    change wrapInt .u64 0 = 0
    exact wrapInt_of_inRange .u64 0 hzeroBounds
  by_cases hfind : ((v.elements a).take n).reverse.findIdx? cPred = none
  · have hfindA := hfind
    rw [hcpredEq] at hfindA
    have hnoMatch : ∀ j, j ≤ i.val → ¬ byteMatches v (fun x => x == b) a j := by
      intro j hj hmatch
      rcases hmatch with ⟨_, x, hget, hpred⟩
      have hx : x = b := by simpa only [beq_iff_eq] using hpred
      subst x
      have hjNonneg : 0 ≤ j - v.first a := by omega
      have hji : j - v.first a < count := by dsimp [count, off]; omega
      have hdCast : (((j - v.first a).toNat : Nat) : Int) = j - v.first a :=
        Int.toNat_of_nonneg hjNonneg
      have hdNat : (j - v.first a).toNat < n := by
        have hjiNat := hji
        rw [← hdCast, ← hcountCast] at hjiNat
        exact Int.ofNat_lt.mp hjiNat
      have hgetBytes : (v.elements a)[(j - v.first a).toNat]? = some b := by
        simpa only [byteAt] using hget
      have hgetPrefix : ((v.elements a).take n)[(j - v.first a).toNat]? = some b := by
        simpa only [List.getElem?_take, if_pos hdNat] using hgetBytes
      have hprefixLen : ((v.elements a).take n).length = n := by
        simp [List.length_take, Nat.min_eq_left hnLen]
      have hdPrefix : (j - v.first a).toNat < ((v.elements a).take n).length := by
        rw [hprefixLen]
        exact hdNat
      have hmem : b ∈ ((v.elements a).take n).reverse := by
        rw [List.mem_reverse]
        exact List.mem_iff_getElem.mpr ⟨(j - v.first a).toNat, hdPrefix,
          (List.getElem?_eq_some_iff.mp hgetPrefix).2⟩
      have hfalse := (List.findIdx?_eq_none_iff.mp hfindA) b hmem
      simp at hfalse
    have hresult : memrchrRaw ops needle a i = .ok none := by
      simp only [memrchrRaw, JInt.rem, hcountArgSource]
      change Except.bind
          (ops.memrchrCall a (ops.pointer a) needle (JInt.wrap .u64 count))
          (fun q : Pointer => Except.ok (projectPair (ops.pointer a, q))) = .ok none
      rw [hcall]
      simp [Except.bind, projectPair, hfind, cPred, n, hzeroVal]
    rw [hresult]
    unfold LastIndex
    constructor
    · intro j
      constructor
      · intro heq
        simp at heq
      · intro h
        rcases h with ⟨hj, hmatch, _⟩
        exact (hnoMatch j hj hmatch).elim
    · constructor
      · intro _
        exact hnoMatch
      · intro _
        rfl
  · rcases Option.ne_none_iff_exists'.mp hfind with ⟨k, hfind⟩
    have hfindA := hfind
    rw [hcpredEq] at hfindA
    have hprefix := lastIndexPrefixFound (E := E) v a (fun x => x == b) (v.first a) i.val n k
      rfl hfinish hnLen hstartRange hfinishRange hfindA
    have hk : k < n := by
      have hk' := (List.findIdx?_eq_some_iff_getElem.mp hfind).1
      simpa [List.length_reverse, List.length_take, Nat.min_eq_left hnLen] using hk'
    have hkInt : (k : Int) < count := by
      have hkNat : (k : Int) < (n : Int) := by exact_mod_cast hk
      rw [← hcountCast]
      exact hkNat
    let hptr := ops.pointer a
    have hptrNonneg : 0 ≤ hptr.val := hptr.property.1
    have haddrLen : hptr.val + len < 2 ^ 64 := by
      simpa [len, hptr] using hmem.addressRange a
    have hsmall : 0 ≤ count - 1 - (k : Int) ∧ count - 1 - (k : Int) < len := by
      rw [← hcountCast]
      dsimp [len]
      constructor <;> omega
    have hptrRaw : hptr.val + count - 1 - (k : Int) ≠ 0 := by
      intro hzero
      have hp : hptr.val ≠ 0 := by simpa [hptr] using hmem.nonnull a
      omega
    have hptrRange : IntTy.min .u64 ≤ hptr.val + count - 1 - (k : Int) ∧
        hptr.val + count - 1 - (k : Int) ≤ IntTy.max .u64 := by
      constructor
      · change 0 ≤ hptr.val + count - 1 - (k : Int)
        omega
      · change hptr.val + count - 1 - (k : Int) ≤ 2 ^ 64 - 1
        omega
    have hptrWrap : (JInt.wrap .u64 (hptr.val + count - 1 - (k : Int))).val =
        hptr.val + count - 1 - (k : Int) := by
      change wrapInt .u64 _ = _
      exact wrapInt_of_inRange .u64 _ hptrRange
    have hfirstOut : (ops.firstindex a).val = v.first a := hfirst
    have hsub := intNatSubPred n k hk
    have hidxMap : hptr.val + count - 1 - (k : Int) - hptr.val + (ops.firstindex a).val =
        v.first a + Int.ofNat (n - 1 - k) := by
      calc
        _ = count - 1 - (k : Int) + v.first a := by rw [hfirstOut]; omega
        _ = Int.ofNat n - 1 - (k : Int) + v.first a := by rw [← hcountCast]
        _ = Int.ofNat (n - 1 - k) + v.first a := by rw [hsub]
        _ = v.first a + Int.ofNat (n - 1 - k) := by omega
    have hidxMapCall : (ops.pointer a).val + count - 1 - (k : Int) -
        (ops.pointer a).val + (ops.firstindex a).val =
        v.first a + Int.ofNat (n - 1 - k) := by simpa [hptr] using hidxMap
    have hptrRawCall : (ops.pointer a).val + count - 1 - (k : Int) ≠ 0 := by
      simpa [hptr] using hptrRaw
    have hptrWrapCall : (JInt.wrap .u64
        ((ops.pointer a).val + count - 1 - (k : Int))).val =
        (ops.pointer a).val + count - 1 - (k : Int) := by
      simpa [hptr] using hptrWrap
    let hidx := v.first a + Int.ofNat (n - 1 - k)
    have hidxRange : IntTy.min .i64 ≤ hidx ∧ hidx ≤ IntTy.max .i64 := by
      constructor
      · calc
          IntTy.min .i64 ≤ v.first a := hstartRange.1
          _ ≤ hidx := by dsimp [hidx]; omega
      · calc
          hidx ≤ i.val := by rw [hfinish]; dsimp [hidx]; omega
          _ ≤ IntTy.max .i64 := hfinishRange.2
    have hidxVal : (int hidx).val = hidx := by
      change wrapInt .i64 hidx = hidx
      exact wrapInt_of_inRange .i64 hidx hidxRange
    have hresult : memrchrRaw ops needle a i =
        .ok (some (int hidx)) := by
      simp only [memrchrRaw, JInt.rem, hcountArgSource]
      change Except.bind
          (ops.memrchrCall a (ops.pointer a) needle (JInt.wrap .u64 count))
          (fun q : Pointer => Except.ok (projectPair (ops.pointer a, q))) =
          .ok (some (int hidx))
      rw [hcall]
      simp [Except.bind, projectPair, hfind, cPred, n, hidx,
        hptrWrapCall, hptrRawCall, hidxMapCall, hidxVal, Functor.map, Except.map]
    rw [hresult]
    simpa [hidx] using hprefix

private theorem memrchrLastUInt8 {A E : Type} (ops : DenseOps A UInt8 E)
    (v : ByteView A UInt8) (hmem : CMemoryLaws ops v)
    (hvalue : ∀ b, ops.value b = Int.ofNat b.toNat)
    (a : A) (b : UInt8) (i : Index)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    LastIndex (byteMatches v (fun x => x == b) a) i.val
      (memrchrUInt8 ops a b i) := by
  let needle := JInt.wrap .i32 (Int.ofNat b.toNat)
  have hneedle : needle.val = Int.ofNat b.toNat := by
    have hb := b.toNat_lt
    change wrapInt .i32 (Int.ofNat b.toNat) = Int.ofNat b.toNat
    apply wrapInt_of_inRange
    constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  have hbyteEqual : ∀ x : UInt8,
      (ops.value x % 256 == needle.val % 256) = (x == b) := by
    intro x
    rw [hvalue x, hneedle]
    have hxlt : x.toNat < 256 := by simpa using x.toNat_lt
    have hblt : b.toNat < 256 := by simpa using b.toNat_lt
    have hxmod : Int.ofNat x.toNat % 256 = Int.ofNat x.toNat :=
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hxlt)
    have hbmod : Int.ofNat b.toNat % 256 = Int.ofNat b.toNat :=
      Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hblt)
    rw [hxmod, hbmod]
    by_cases heq : x.toNat = b.toNat
    · have hxb : x = b := UInt8.toNat.inj heq
      subst b
      simp
    · have hneInt : Int.ofNat x.toNat ≠ Int.ofNat b.toNat := by
        intro h
        apply heq
        exact Int.ofNat_inj.mp h
      have hneByte : x ≠ b := by
        intro h
        apply heq
        exact congrArg UInt8.toNat h
      have hIntFalse : (Int.ofNat x.toNat == Int.ofNat b.toNat) = false := by
        rw [beq_eq_false_iff_ne]
        exact hneInt
      have hByteFalse : (x == b) = false := by
        rw [beq_eq_false_iff_ne]
        exact hneByte
      rw [hIntFalse, hByteFalse]
  have hcore := memrchrLastCoreCandidate ops v hmem b needle hbyteEqual a i hstart hstop
  simpa [memrchrRaw, memrchrUInt8, needle] using hcore

private theorem int8Pred {A E : Type} (ops : DenseOps A (JInt .i8) E)
    (b : JInt .i8) (needle : JInt .i32)
    (hvalue : ∀ x, ops.value x = x.val) (hneedle : needle.val = b.val) :
    ∀ x : JInt .i8, (ops.value x % 256 == needle.val % 256) = (x == b) := by
  intro x
  rw [hvalue x, hneedle]
  by_cases heq : x.val = b.val
  · have hxb : x = b := Subtype.ext heq
    subst b
    simp
  · have hmod : x.val % 256 ≠ b.val % 256 := by
      intro h
      have hx := x.property
      have hb := b.property
      simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx hb
      omega
    have hmodFalse : (x.val % 256 == b.val % 256) = false := by
      rw [beq_eq_false_iff_ne]
      exact hmod
    have hne : x ≠ b := by
      intro h
      exact heq (congrArg Subtype.val h)
    have heqFalse : (x == b) = false := by
      rw [beq_eq_false_iff_ne]
      exact hne
    rw [hmodFalse, heqFalse]

private theorem memrchrLastInt8 {A E : Type} (ops : DenseOps A (JInt .i8) E)
    (v : ByteView A (JInt .i8)) (hmem : CMemoryLaws ops v)
    (hvalue : ∀ b, ops.value b = b.val)
    (a : A) (b : JInt .i8) (i : Index)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    LastIndex (byteMatches v (fun x => x.val == b.val) a) i.val
      (memrchrInt8 ops a b i) := by
  let needle := JInt.wrap .i32 b.val
  have hneedle : needle.val = b.val := by
    change wrapInt .i32 b.val = b.val
    apply wrapInt_of_inRange
    have hb := b.property
    constructor <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hb ⊢ <;> omega
  have hbyteEqual : ∀ x : JInt .i8,
      (ops.value x % 256 == needle.val % 256) = (x == b) :=
    int8Pred ops b needle hvalue hneedle
  have hcore := memrchrLastCoreCandidate ops v hmem b needle hbyteEqual a i hstart hstop
  have hEq : ∀ x : JInt .i8, (x == b) = (x.val == b.val) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩
  simpa [memrchrRaw, memrchrInt8, needle, byteMatches, hEq] using hcore

theorem memrchrLastSpec_proven : MemrchrLastSpec := by
  unfold MemrchrLastSpec
  constructor
  · intro A E ops v hmem hvalue a b i hstart hstop
    exact memrchrLastUInt8 ops v hmem hvalue a b i hstart hstop
  · intro A E ops v hmem hvalue a b i hstart hstop
    have hbyteValue : ∀ b : JInt .i8, ops.value b = b.val := hvalue
    exact memrchrLastInt8 ops v hmem hbyteValue a b i hstart hstop

/-- Dense signed and unsigned byte findnext returns the first match at or after the start, rejects a start below the array, and preserves Int conversion errors. -/
def DenseByteForwardSpec : Prop :=
(∀ (A I E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b start, match ix.toInt start with
      | .error e => findnextUInt8 ops ix b a start = .error e
      | .ok i => if i.val < v.first a then
          findnextUInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else FirstIndex (byteMatches v (fun x => x == b) a) i.val (findnextUInt8 ops ix b a start)) ∧
  (∀ (A I E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = b.val) →
    ∀ a b start, match ix.toInt start with
      | .error e => findnextInt8 ops ix b a start = .error e
      | .ok i => if i.val < v.first a then
          findnextInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else FirstIndex (byteMatches v (fun x => x.val == b.val) a) i.val (findnextInt8 ops ix b a start))

/-- Dense signed and unsigned byte findprev returns the last match at or before the start, rejects a start above the array, and preserves Int conversion errors. -/
def DenseByteReverseSpec : Prop :=
(∀ (A I E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b start, match ix.toInt start with
      | .error e => findprevUInt8 ops ix b a start = .error e
      | .ok i => if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
          findprevUInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else LastIndex (byteMatches v (fun x => x == b) a) i.val (findprevUInt8 ops ix b a start)) ∧
  (∀ (A I E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)) (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix → (∀ b, ops.value b = b.val) →
    ∀ a b start, match ix.toInt start with
      | .error e => findprevInt8 ops ix b a start = .error e
      | .ok i => if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
          findprevInt8 ops ix b a start = .error (ops.boundsError a i.val)
        else LastIndex (byteMatches v (fun x => x.val == b.val) a) i.val (findprevInt8 ops ix b a start))

namespace Round3

open JuliaLean JuliaLean.base.strings.search JuliaLean.Registry
open JuliaLean.base.iterators (Exec)
open JuliaLean.Proofs.base.strings.search

structure PrimitiveTextLaws {S R C CU CT E : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (v : TextView S C) : Prop where
  sizeFits : ∀ s, Int.ofNat (v.bytes s).length ≤ IntTy.max .i64
  ncodeunits : ∀ s, (ops.ncodeunits s).val = Int.ofNat (v.bytes s).length
  iterationBound : ∀ s, (v.bytes s).length ≤ ops.iterationBound s
  sorted : ∀ s, (v.characters s).Pairwise (fun a b => a.1.val < b.1.val)
  indices : ∀ s p, p ∈ v.characters s → 1 ≤ p.1.val ∧ p.1.val < endIndex v s
  nonempty : ∀ s, (v.characters s).isEmpty = (v.bytes s).isEmpty
  first : ∀ s p, (v.characters s).head? = some p → p.1 = int 1
  isvalid : ∀ s i, ops.isvalid s i = .ok ((v.characters s).any (fun p => p.1 == i))
  iterate : ∀ s i c, (i, c) ∈ v.characters s →
    ops.iterateAt s i = .ok (some (c, nextPosition v s i))

/-- The earliest accepted character is returned, and absence returns nothing.
Only a valid start (or the one-past-end start) is required. All basic.jl index
and bounds operations are invoked through modelStringOps and fromBasic. -/
def PredicateForwardSpec : Prop :=
  ∀ (S R C CU CT I E : Type)
    (primitive : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (intString : Index → String) (v : TextView S C)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (accepted : C → Bool),
    PrimitiveTextLaws primitive v → IntegerLaws ix →
    (∀ c, (testf c).run = some (.ok (accepted c))) →
    ∀ s start, 1 ≤ ix.value start → ix.value start ≤ endIndex v s →
      (validAt v s (int (ix.value start)) ∨ ix.value start = endIndex v s) →
      Returns
        (findnextPredicate
          (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
          ix testf s start)
        (FirstIndex (charMatches v (fun c => accepted c = true) s) (ix.value start))

/-- The latest accepted character at or before a valid start is returned;
zero and one-past-end return nothing. Every accepted reverse start is covered. -/
def PredicateReverseSpec : Prop :=
  ∀ (S R C CU CT I E : Type)
    (primitive : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (intString : Index → String) (v : TextView S C)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (accepted : C → Bool),
    PrimitiveTextLaws primitive v → IntegerLaws ix →
    (∀ c, (testf c).run = some (.ok (accepted c))) →
    ∀ s start, 0 ≤ ix.value start → ix.value start ≤ endIndex v s →
      (validAt v s (int (ix.value start)) ∨ ix.value start = 0 ∨
        ix.value start = endIndex v s) →
      if ix.value start = endIndex v s then
        (findprevPredicate
          (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
          ix testf s start).run = some (.ok none)
      else Returns
        (findprevPredicate
          (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
          ix testf s start)
        (LastIndex (charMatches v (fun c => accepted c = true) s) (ix.value start))


/-- A failing predicate at the first tested position after a false-only prefix
propagates its exact exception in both directions, through the real index models. -/
def PredicateErrorSpec : Prop :=
  ∀ (S R C CU CT E : Type)
    (primitive : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (intString : Index → String) (v : TextView S C) (testf : C → SearchM E Bool),
    PrimitiveTextLaws primitive v → ∀ s start i c e,
    validAt v s start → (i, c) ∈ v.characters s → (testf c).run = some (.error e) →
      (((start.val ≤ i.val ∧ ∀ j d, (j, d) ∈ v.characters s →
          start.val ≤ j.val → j.val < i.val → (testf d).run = some (.ok false)) →
        (findnextPredicate
          (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
          indexOps testf s start).run = some (.error e)) ∧
       ((i.val ≤ start.val ∧ ∀ j d, (j, d) ∈ v.characters s →
          i.val < j.val → j.val ≤ start.val → (testf d).run = some (.ok false)) →
        (findprevPredicate
          (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
          indexOps testf s start).run = some (.error e)))

end Round3
namespace Round7

open JuliaLean JuliaLean.base.strings.search JuliaLean.Registry
open JuliaLean.base.iterators (Exec)
open JuliaLean.Proofs.base.strings.search
open JuliaLean.Proofs.base.strings.search.Round3

/-- Predicate search throws an error for every old invalid-start domain and when `Int(i)` cannot convert the start. It does not claim a named error type and retains the maximum virtual-string length. Source: base/strings/search.jl:343-354,668-679; docs: base/array.jl:2441-2451,2629-2639 and the Strings manual, “Unicode and UTF-8”. -/
def PredicateStartErrorsAnyErrorSpec : Prop :=
  ∀ (S R C CU CT I E : Type)
    (primitive : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (intString : Index → String) (v : TextView S C)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool),
    PrimitiveTextLaws primitive v → IntegerLaws ix → ∀ s start,
      ((∀ e, ix.toInt start = .error e →
          (∃ searchError, (findnextPredicate
            (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
            ix testf s start).run = some (.error searchError)) ∧
          (∃ searchError, (findprevPredicate
            (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
            ix testf s start).run = some (.error searchError))) ∧
       (∀ i, ix.toInt start = .ok i →
          (((i.val < 1 ∨ endIndex v s < i.val) →
            ∃ e, (findnextPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              ix testf s start).run = some (.error e)) ∧
           ((i.val < 0 ∨ endIndex v s < i.val) →
            ∃ e, (findprevPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              ix testf s start).run = some (.error e)) ∧
           ((1 ≤ i.val ∧ i.val < endIndex v s ∧ ¬ validAt v s i) →
            (∃ e, (findnextPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              ix testf s start).run = some (.error e)) ∧
            (∃ e, (findprevPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              ix testf s start).run = some (.error e))))))

end Round7


/-- Every occurrence of a byte classified standalone begins a one-byte character, even when the surrounding input contains malformed UTF-8 bytes. -/
def StandalonePositionsSpec : Prop :=
∀ (S E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (ncodeunitsChar : JChar → Index) (enc : CharEncoding ncodeunitsChar),
    Utf8TextLaws ops v ncodeunitsChar enc → ∀ s b k,
      isStandaloneByte b = true → (v.bytes s)[k]? = some b →
      ∃ c, (int (Int.ofNat k + 1), c) ∈ v.characters s ∧ enc.bytes c = [b]

/-- Forward character-position iteration yields the least complete matching character from a valid start and returns nothing exactly when no such character remains. -/
def ForwardIteratorSpec : Prop :=
∀ (S A C E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (ncu : JChar → Index) (encoding : CharEncoding ncu),
    Utf8TextLaws ops v ncu encoding → CharOpsLaws chars ncu → CodeunitLaws codeunits bytes v bv →
    ∀ s target c start, chars.toChar target = .ok c →
      (validAt v s start ∨ start.val = endIndex v s) →
      FirstIndex (charMatches v (fun d => d = c) s) start.val
        (do let iter ← fwCharPosIter chars s target
            tryNext (fun it st => fwIterate ops bytes codeunits chars.ncodeunits it st) iter start)

/-- Reverse character-position iteration yields the greatest complete matching character at or before a valid start and returns nothing exactly when none remains. -/
def ReverseIteratorSpec : Prop :=
∀ (S A C E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (ncu : JChar → Index) (encoding : CharEncoding ncu),
    Utf8TextLaws ops v ncu encoding → CharOpsLaws chars ncu → CodeunitLaws codeunits bytes v bv →
    ∀ s target c start, chars.toChar target = .ok c →
      (validAt v s start ∨ start.val = 0) →
      LastIndex (charMatches v (fun d => d = c) s) start.val
        (do let iter ← rvCharPosIter chars s target
            tryNext (fun it st => rvIterate ops bytes codeunits chars.ncodeunits it (some st)) iter start)

/-- Character findnext and findprev return the first or last matching decoded character at valid string indices, including for malformed input bytes. -/
def CharSearchSpec : Prop :=
∀ (S A C I E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (ncu : JChar → Index) (encoding : CharEncoding ncu) (ix : IntegerOps I E),
    Utf8TextLaws ops v ncu encoding → CharOpsLaws chars ncu → CodeunitLaws codeunits bytes v bv →
    IntegerLaws ix → ∀ s target c start, chars.toChar target = .ok c →
      ((validAt v s (int (ix.value start)) ∨ ix.value start = endIndex v s) →
        FirstIndex (charMatches v (fun d => d = c) s) (ix.value start)
          (findnextChar ops bytes codeunits chars ix target s start)) ∧
      ((validAt v s (int (ix.value start)) ∨ ix.value start = 0) →
        LastIndex (charMatches v (fun d => d = c) s) (ix.value start)
          (findprevChar ops bytes codeunits chars ix target s start))

/-- Character searches throw BoundsError for starts outside their bounds. Only the
forward Char method also rejects an interior byte position with StringIndexError. -/
def CharStartErrorsSpec : Prop :=
  ∀ (S A C I E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (ncu : JChar → Index) (encoding : CharEncoding ncu) (ix : IntegerOps I E),
    Utf8TextLaws ops v ncu encoding → CharOpsLaws chars ncu → CodeunitLaws codeunits bytes v bv →
    IntegerLaws ix → ∀ s target c start, chars.toChar target = .ok c →
      ((ix.value start < 1 ∨ endIndex v s < ix.value start) →
        findnextChar ops bytes codeunits chars ix target s start =
          .error (ops.boundsError s (ix.value start))) ∧
      ((ix.value start < 0 ∨ endIndex v s < ix.value start) →
        findprevChar ops bytes codeunits chars ix target s start =
          .error (ops.boundsError s (ix.value start))) ∧
      ((1 ≤ ix.value start ∧ ix.value start < endIndex v s ∧
        ¬ validAt v s (int (ix.value start))) →
        findnextChar ops bytes codeunits chars ix target s start =
          .error (ops.stringIndexError s (int (ix.value start))))

/-- Character findall returns all and only the matching character indices in increasing order, including in malformed UTF-8 strings. -/
def FindallCharSpec : Prop :=
∀ (S A C E H : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (chars : CharOps C E) (ncu : JChar → Index) (encoding : CharEncoding ncu)
    (vec : VectorStore Index E H) (findallBytes : UInt8 → A → Exec E H Nat),
    Utf8TextLaws ops v ncu encoding → CharOpsLaws chars ncu → CodeunitLaws codeunits bytes v bv →
    VectorStoreLaws vec →
    (∀ b a h, VectorResult vec (findallBytes b a) h
      (((bv.elements a).zipIdx.filter (fun p => p.1 == b)).map
        (fun p => int (bv.first a + Int.ofNat p.2)))) →
    ∀ s target c h, chars.toChar target = .ok c →
      VectorResult vec (findallChar ⟨ops, bytes, codeunits, chars⟩ vec findallBytes target s) h
        (((v.characters s).filter (fun p => p.2 == c)).map (·.1))

/-- String findnext returns exactly the earliest complete match range at or after a valid start and returns nothing exactly when no matching range exists. -/
def DenseForwardSpec : Prop :=
∀ (S T A D I E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu) (ix : IntegerOps I E),
    DenseLaws cfg sv tv bv pv enc → IntegerLaws ix → ∀ s t start,
      1 ≤ ix.value start → ix.value start ≤ endIndex sv s →
      (validAt sv s (int (ix.value start)) ∨ ix.value start = endIndex sv s) →
      Returns (denseNext cfg ix t s start)
        (FirstRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t)
          (ix.value start))

/-- Every range returned by string findnext indexes the complete needle: slicing the haystack by that range succeeds and equals the needle, including for invalid input bytes. -/
def FindnextMatches : Prop :=
∀ (A D E : Type) (cfg : DenseStringSearch JString JString A D E)
    (sv tv : TextView JString JChar) (bv : ByteView A UInt8) (pv : ByteView D UInt8)
    (ncu : JChar → Index) (enc : CharEncoding ncu) (slice : JString → Index → Index → Except E JString),
    DenseLaws cfg sv tv bv pv enc → SliceLaws sv slice → (∀ t, tv.bytes t = t.bytes) →
    ∀ t s i r, (denseNext cfg indexOps t s i).run = some (.ok (some r)) → slice s r.first r.last = .ok t

/-- String findfirst and findlast return the earliest and latest complete
occurrence ranges, including the empty-pattern range at lastindex. -/
def DenseFirstLastSpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu),
    DenseLaws cfg sv tv bv pv enc → ∀ s t,
      Returns (denseFirst cfg t s)
        (FirstRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t) 1) ∧
      Returns (denseLast cfg t s)
        (LastRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t)
          (lastIndex sv s).val)
/-- For an empty pattern, reverse search follows the documented empty-range
contract and the source's three cases. -/
def DenseReverseEmptySpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu),
    DenseLaws cfg sv tv bv pv enc → ∀ s t i, tv.bytes t = [] →
      ((i.val > (JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val →
        (densePrev cfg indexOps t s i).run = some (.ok (some ⟨int 0, int (-1)⟩))) ∧
       (i.val = 0 →
        (densePrev cfg indexOps t s i).run = some (.ok (some ⟨int 1, int 0⟩))) ∧
       (i.val ≤ (JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val → i.val ≠ 0 →
        (densePrev cfg indexOps t s i).run = some (.ok (some ⟨i, i - int 1⟩))))

/-- Every successful findprev range matches the pattern and ends at or before
the requested start. -/
def FindprevLatest : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu),
    DenseLaws cfg sv tv bv pv enc → ∀ t s i r,
      0 ≤ i.val → i.val ≤ endIndex sv s →
      (densePrev cfg indexOps t s i).run = some (.ok (some r)) →
      textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r ∧
      r.last.val ≤ i.val

/-- For nonempty needles, string findprev returns exactly the latest complete match whose inclusive end is at or before the start, or nothing if none exists. -/
def DenseReverseSpec : Prop :=
∀ (S T A D I E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu) (ix : IntegerOps I E),
    DenseLaws cfg sv tv bv pv enc → IntegerLaws ix → ∀ s t start,
      (tv.bytes t).isEmpty = false →
      0 ≤ ix.value start → ix.value start ≤ endIndex sv s →
      (validAt sv s (int (ix.value start)) ∨ ix.value start = 0 ∨ ix.value start = endIndex sv s) →
      Returns (densePrev cfg ix t s start)
        (LastRange (textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t)
          (ix.value start))

/-- An empty string pattern matches the empty range at the requested valid start, including one past the final code unit. -/
def EmptyPatternStartSpec : Prop :=
∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu),
    DenseLaws cfg sv tv bv pv enc → ∀ s t i, tv.bytes t = [] →
      1 ≤ i.val → i.val ≤ endIndex sv s →
      (validAt sv s i ∨ i.val = endIndex sv s) →
      (denseNext cfg indexOps t s i).run = some (.ok (some ⟨i, i - int 1⟩)) ∧
      (densePrev cfg indexOps t s i).run = some (.ok (some ⟨i, i - int 1⟩))

/-- String-pattern findnext throws BoundsError outside its source-checked byte
range. This claim makes no error assertion about reverse-search starts. -/
def StringStartErrorsSpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu),
    DenseLaws cfg sv tv bv pv enc → ∀ s t i,
      (i.val < 1 ∨ endIndex sv s < i.val) →
        (denseNext cfg indexOps t s i).run = some (.error (cfg.source.boundsError s i.val))

/-- Byte-vector findnext returns the first matching sequence range at or after the start, or nothing if none exists, for arbitrary offset axes and mixed signed/unsigned byte element types. -/
def BytePatternForwardSpec : Prop :=
∀ (A T B C I E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) (ix : IntegerOps I E),
    BytePatternLaws cfg sv tv → IntegerLaws ix → ∀ a t start,
      sv.first a ≤ ix.value start → ix.value start ≤ sv.first a + Int.ofNat (sv.elements a).length →
      Returns (vectorNext cfg ix t a start) (FirstRange (byteRangeAt cfg sv tv a t) (ix.value start))

/-- Byte-vector findprev returns the last nonempty sequence range ending at or before the start, or nothing if none exists, for arbitrary offset axes. -/
def BytePatternReverseSpec : Prop :=
∀ (A T B C I E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C) (ix : IntegerOps I E),
    BytePatternLaws cfg sv tv → IntegerLaws ix → ∀ a t start,
      (tv.elements t).isEmpty = false →
      sv.first a - 1 ≤ ix.value start → ix.value start < sv.first a + Int.ofNat (sv.elements a).length →
      Returns (vectorPrev cfg ix t a start) (LastRange (byteRangeAt cfg sv tv a t) (ix.value start))

/-- Byte-vector findfirst and findlast return the earliest and latest complete
sequence occurrence ranges, including the empty-pattern range at lastindex. -/
def BytePatternFirstLastSpec : Prop :=
  ∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv → ∀ a t,
      Returns (vectorFirst cfg t a) (FirstRange (byteRangeAt cfg sv tv a t) (sv.first a)) ∧
      Returns (vectorLast cfg t a) (LastRange (byteRangeAt cfg sv tv a t)
        (sv.first a + Int.ofNat (sv.elements a).length - 1))

/-- Every returned nonempty byte-pattern range has the pattern length, independently of both vectors first indices. -/
def OffsetPatternRangeSpec : Prop :=
∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv →
    ∀ a t i r, (tv.elements t).isEmpty = false →
      ((vectorNext cfg indexOps t a i).run = some (.ok (some r)) ∨
       (vectorPrev cfg indexOps t a i).run = some (.ok (some r)) ∨
       (vectorFirst cfg t a).run = some (.ok (some r)) ∨
       (vectorLast cfg t a).run = some (.ok (some r))) →
      r.last.val - r.first.val + 1 = Int.ofNat (tv.elements t).length

/-- An empty byte-vector pattern matches the empty range at the requested haystack index, including on offset axes. -/
def ByteEmptyPatternSpec : Prop :=
∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv →
    ∀ a t i, tv.elements t = [] →
      sv.first a ≤ i.val → i.val ≤ sv.first a + Int.ofNat (sv.elements a).length →
      (vectorNext cfg indexOps t a i).run = some (.ok (some ⟨i, i - int 1⟩)) ∧
      (vectorPrev cfg indexOps t a i).run = some (.ok (some ⟨i, i - int 1⟩))

/-- The forward byte-pattern method rejects starts before the first element or
after its one-past-end index. Reverse search rejects starts below firstindex-1.
Its one-byte path compares the normalized start with lastindex. -/
def BytePatternStartErrorsSpec : Prop :=
  ∀ (A T B C E : Type) (cfg : BytePatternSearch A T B C E)
    (sv : ByteView A B) (tv : ByteView T C), BytePatternLaws cfg sv tv → ∀ a t i,
      ((i.val < sv.first a ∨ sv.first a + Int.ofNat (sv.elements a).length < i.val) →
        (vectorNext cfg indexOps t a i).run = some (.error (cfg.source.boundsError a i.val))) ∧
      (i.val < sv.first a - 1 →
        (vectorPrev cfg indexOps t a i).run = some (.error (cfg.source.boundsError a i.val))) ∧
      ((tv.elements t).length = 1 ∧
        i.val - (sv.first a - 1) >
          sv.first a + Int.ofNat (sv.elements a).length - 1) →
        (vectorPrev cfg indexOps t a i).run =
          some (.error (cfg.source.boundsError a (i.val - (sv.first a - 1))))

/-- String occursin and its fixed-haystack function are true exactly when a complete match exists, agreeing with findfirst returning a match. -/
def OccursinSpec : Prop :=
  ∀ (S T A D E : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu),
    DenseLaws cfg sv tv bv pv enc → ∀ s t,
      ((denseOccursin cfg t s).run = some (.ok true) ↔
        ∃ r, (denseFirst cfg t s).run = some (.ok (some r))) ∧
      ((denseOccursin cfg t s).run = some (.ok true) ↔
        ∃ r, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r) ∧
      ((applyFix2 (denseOccursinFix cfg s) t).run = some (.ok true) ↔
        ∃ r, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r)
/-- String-pattern findall returns valid matching ranges in increasing order, disjoint ranges when overlap is false, and every match when overlap is true. -/
def FindallRangeSpec : Prop :=
∀ (S T A D E H : Type) (cfg : DenseStringSearch S T A D E)
    (sv : TextView S JChar) (tv : TextView T JChar) (bv : ByteView A UInt8)
    (pv : ByteView D UInt8) (ncu : JChar → Index) (enc : CharEncoding ncu)
    (vec : VectorStore MatchRange E H),
    DenseLaws cfg sv tv bv pv enc → VectorStoreLaws vec → ∀ s t overlap ranges h,
      VectorResult vec (denseAll cfg vec t s overlap) h ranges →
      (∀ r ∈ ranges, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r) ∧
      ranges.Pairwise (fun a b => a.first.val < b.first.val) ∧
      (overlap = false → ranges.Pairwise (fun a b => a.last.val < b.first.val)) ∧
      (overlap = true → ∀ r, textSequenceAt sv (fun t => (tv.characters t).map (·.2)) s t r → r ∈ ranges)

/-- String findall's match ranges equal the sequence of repeated findnext
results returned by regex eachmatch when its documented iteration contract holds. -/
def FindallRangesOfEachmatch : Prop :=
  ∀ (S P E H : Type) [AbstractPattern P] (string : SearchStringOps S JChar E)
    (v : TextView S JChar) (regex : RegexInterface S P E) (vec : VectorStore MatchRange E H),
    TextLaws string v → RegexInterfaceLaws regex string v → VectorStoreLaws vec → ∀ re s h,
      let run := findallRanges vec (fun re s i => liftExcept (regex.findnext re s i))
        JuliaLean.base.strings.basic.firstindexString (fun s => liftExcept (string.lastindex s))
        (fun s i => liftExcept (string.nextind s i)) false re s
      match regex.eachmatchRanges re s with
      | .ok rs => VectorResult vec run h rs
      | .error e => ∃ h', run h = some (.error e, h')

/-- The iszero specializations search the entire documented Integer-start domain,
including conversion errors and both out-of-axis directions. Both signed and
unsigned implementations call their installed memchr and memrchr methods. -/
def ZeroByteSpec : Prop :=
  (∀ (A I E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8)
    (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix →
    (∀ b, ops.value b = Int.ofNat b.toNat) → ops.zero = 0 →
    ∀ a start, match ix.toInt start with
      | .error e =>
          findnextZero ops ix (memchrUInt8 ops) a start = .error e ∧
          findprevZero ops ix (memrchrUInt8 ops) a start = .error e
      | .ok i =>
          (if i.val < v.first a then
            findnextZero ops ix (memchrUInt8 ops) a start = .error (ops.boundsError a i.val)
          else FirstIndex (byteMatches v (fun b => b == 0) a) i.val
            (findnextZero ops ix (memchrUInt8 ops) a start)) ∧
          (if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
            findprevZero ops ix (memrchrUInt8 ops) a start = .error (ops.boundsError a i.val)
          else LastIndex (byteMatches v (fun b => b == 0) a) i.val
            (findprevZero ops ix (memrchrUInt8 ops) a start))) ∧
  (∀ (A I E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8))
    (ix : IntegerOps I E),
    CMemoryLaws ops v → IntegerLaws ix →
    (∀ b, ops.value b = b.val) → ops.zero.val = 0 →
    ∀ a start, match ix.toInt start with
      | .error e =>
          findnextZero ops ix (memchrInt8 ops) a start = .error e ∧
          findprevZero ops ix (memrchrInt8 ops) a start = .error e
      | .ok i =>
          (if i.val < v.first a then
            findnextZero ops ix (memchrInt8 ops) a start = .error (ops.boundsError a i.val)
          else FirstIndex (byteMatches v (fun b => b.val == 0) a) i.val
            (findnextZero ops ix (memchrInt8 ops) a start)) ∧
          (if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
            findprevZero ops ix (memrchrInt8 ops) a start = .error (ops.boundsError a i.val)
          else LastIndex (byteMatches v (fun b => b.val == 0) a) i.val
            (findprevZero ops ix (memrchrInt8 ops) a start)))
namespace Round5

open JuliaLean.Proofs.base.strings.search

/-- The approved round-3 primitive protocol, unchanged. Iteration is constrained
only at valid character starts; invalid and out-of-bounds states are unrestricted. -/
structure PrimitiveTextLaws {S R C CU CT E : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (v : TextView S C) : Prop where
  sizeFits : ∀ s, Int.ofNat (v.bytes s).length ≤ IntTy.max .i64
  ncodeunits : ∀ s, (ops.ncodeunits s).val = Int.ofNat (v.bytes s).length
  iterationBound : ∀ s, (v.bytes s).length ≤ ops.iterationBound s
  sorted : ∀ s, (v.characters s).Pairwise (fun a b => a.1.val < b.1.val)
  indices : ∀ s p, p ∈ v.characters s → 1 ≤ p.1.val ∧ p.1.val < endIndex v s
  nonempty : ∀ s, (v.characters s).isEmpty = (v.bytes s).isEmpty
  first : ∀ s p, (v.characters s).head? = some p → p.1 = int 1
  isvalid : ∀ s i, ops.isvalid s i = .ok ((v.characters s).any (fun p => p.1 == i))
  iterate : ∀ s i c, (i, c) ∈ v.characters s →
    ops.iterateAt s i = .ok (some (c, nextPosition v s i))

/-- The constructor selected by Julia for an Integer-valued codepoint.
Every BitInteger width is passed to the installed dispatch adapter, including
Int8/UInt8's specialized constructor. Bool and raw UInt32 use their installed
routes. Other Integer types may provide UInt32 conversion or their own Char
constructor; these are external methods, with no assumed successful answer. -/
inductive IntegerCharConstructor (N : Type) where
  | bitInteger (t : IntTy) (carrier : N = JInt t)
  | uint8 (carrier : N = UInt8)
  | int8 (carrier : N = Int8)
  | uint32 (carrier : N = JChar)
  | boolean (carrier : N = Bool)
  | defaultInteger (toUInt32 : N → JuliaLean.base.char.CharResult JChar)
  | extensionMethod (construct : N → JuliaLean.base.char.CharResult JChar)

def charOfCodepoint {N : Type} (constructor : IntegerCharConstructor N)
    (number : N) : JuliaLean.base.char.CharResult JChar :=
  match constructor with
  | .bitInteger t carrier =>
      JuliaLean.Proofs.base.char.charOfIntegerDispatch t (Eq.mp carrier number)
  | .uint8 carrier =>
      JuliaLean.Proofs.base.char.charOfIntegerDispatch .u8
        (JInt.lit .u8 (Int.ofNat (Eq.mp carrier number).toNat))
  | .int8 carrier =>
      JuliaLean.Proofs.base.char.charOfIntegerDispatch .i8
        (JInt.lit .i8 (Eq.mp carrier number).toInt)
  | .uint32 carrier => JuliaLean.base.char.char_UInt32 (Eq.mp carrier number)
  | .boolean carrier =>
      JuliaLean.base.char.constructor_Number_AbstractChar
        JuliaLean.Proofs.base.char.uint32OfBool JuliaLean.base.char.char_UInt32
        (Eq.mp carrier number)
  | .defaultInteger toUInt32 =>
      JuliaLean.base.char.constructor_Number_AbstractChar
        toUInt32 JuliaLean.base.char.char_UInt32 number
  | .extensionMethod construct => construct number

/-- Native Char identity, the generic codepoint constructor over any Integer
return type, or an external Char(::C) extension method. Julia's selected method
is supplied as dispatch data; no conversion-success law is assumed. -/
inductive CharConversion (C : Type) where
  | native (carrier : C = JChar)
  | codepoint (N : Type) (operation : C → JuliaLean.base.char.CharResult N)
      (constructor : IntegerCharConstructor N)
  | extensionMethod (construct : C → JuliaLean.base.char.CharResult JChar)

def convertChar {C : Type} (conversion : CharConversion C)
    (c : C) : JuliaLean.base.char.CharResult JChar :=
  match conversion with
  | .native carrier =>
      .ok (JuliaLean.base.char.constructor_Same_AbstractChar (Eq.mp carrier c))
  | .codepoint _ operation constructor =>
      JuliaLean.base.char.constructor_AbstractChar_AbstractChar
        operation (charOfCodepoint constructor) c
  | .extensionMethod construct => construct c

/-- Builtin equality, the default AbstractChar fallback, or an external equality
method added for extension types. Only the external method is a callback, and
its result is never assumed: matching and first-error observations inspect the
actual return value. The native/default cases bind installed equality models. -/
inductive CharEqualityDispatch (C D E : Type) where
  | native (left : C = JChar) (right : D = JChar)
  | defaultAbstract (left : CharConversion C) (right : CharConversion D)
      (encodeError : JuliaLean.base.char.CharError → E)
  | extensionMethod (operation : C → D → Except E Bool)

def charEquality {C D E : Type} (dispatch : CharEqualityDispatch C D E)
    (c : C) (d : D) : Except E Bool :=
  match dispatch with
  | .native left right =>
      .ok (JuliaLean.base.char.eq_Char (Eq.mp left c) (Eq.mp right d))
  | .defaultAbstract left right encodeError =>
      (JuliaLean.base.char.eq_AbstractChar (convertChar left) (convertChar right)
        JuliaLean.base.char.eq_Char c d).mapError encodeError
  | .extensionMethod operation => operation c d

/-- An independent ordered-search observation. A true predicate result or an
exception is returned exactly at the first non-false test; an all-false sequence
returns nothing. This is a specification of the search, not a law imposed on
its equality callee. It includes conversion exceptions without assuming totality. -/
def FirstTestOutcome {C E : Type} (characters : List (Index × C))
    (test : C → Except E Bool) (result : Except E (Option Index)) : Prop :=
  (∀ i, result = .ok (some i) ↔
    ∃ before c after, characters = before ++ (i, c) :: after ∧
      (∀ p ∈ before, test p.2 = .ok false) ∧ test c = .ok true) ∧
  (result = .ok none ↔ ∀ p ∈ characters, test p.2 = .ok false) ∧
  (∀ e, result = .error e ↔
    ∃ before i c after, characters = before ++ (i, c) :: after ∧
      (∀ p ∈ before, test p.2 = .ok false) ∧ test c = .error e)

/-- Character search wrappers return the directional first equal character,
absence, or the first equality/conversion exception. All native codepoint widths and default
constructors call installed models; custom conversion/equality methods are
unrestricted external callees. No equality correctness hypothesis is supplied. All accepted starts, including reverse one-past-end, are retained. -/
def CharWrapperSpec : Prop :=
  ∀ (S R C CU CT D E : Type)
    (primitive : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (intString : Index → String) (v : TextView S C)
    (equality : CharEqualityDispatch C D E),
    PrimitiveTextLaws primitive v → ∀ s target start,
      (((validAt v s start ∨ start.val = endIndex v s) →
        Returns
          (findnextCharWrapper (charEquality equality)
            (findnextPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              indexOps) target s start)
          (FirstTestOutcome ((v.characters s).filter (fun p => start.val ≤ p.1.val))
            (fun c => charEquality equality c target))) ∧
       ((validAt v s start ∨ start.val = 0 ∨ start.val = endIndex v s) →
        if start.val = endIndex v s then
          (findprevCharWrapper (charEquality equality)
            (findprevPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              indexOps) target s start).run = some (.ok none)
        else Returns
          (findprevCharWrapper (charEquality equality)
            (findprevPredicate
              (fromBasic (JuliaLean.base.strings.basic.modelStringOps primitive intString))
              indexOps) target s start)
          (FirstTestOutcome
            (((v.characters s).filter (fun p => p.1.val ≤ start.val)).reverse)
            (fun c => charEquality equality c target))))

end Round5

/-- Character findfirst and findlast return exactly the first and last equal character index or nothing if the character is absent. -/
def CharFirstLastSpec : Prop :=
∀ (S C D E : Type) (ops : SearchStringOps S C E) (v : TextView S C)
    (equal : C → D → Except E Bool) (accepts : C → D → Bool)
    (first last : (C → Except E Bool) → S → Except E (Option Index)),
    TextLaws ops v → (∀ c d, equal c d = .ok (accepts c d)) →
    (∀ (test : C → Except E Bool) (accept : C → Bool) (s : S), (∀ c, test c = .ok (accept c)) →
      FirstIndex (charMatches v (fun c => accept c = true) s) 1 (first test s)) →
    (∀ (test : C → Except E Bool) (accept : C → Bool) (s : S), (∀ c, test c = .ok (accept c)) →
      LastIndex (charMatches v (fun c => accept c = true) s) (lastIndex v s).val (last test s)) →
    ∀ target s,
      FirstIndex (charMatches v (fun c => accepts c target = true) s) 1
        (findfirstChar equal first target s) ∧
      LastIndex (charMatches v (fun c => accepts c target = true) s) (lastIndex v s).val
        (findlastChar equal last target s)

/-- Character occursin and dense character membership are true exactly when the decoded character occurs in the string, including malformed input bytes. -/
def CharOccursinSpec : Prop :=
∀ (S A E : Type) (ops : SearchStringOps S JChar E) (v : TextView S JChar)
    (bytes : DenseOps A UInt8 E) (bv : ByteView A UInt8) (codeunits : S → A)
    (ncodeunitsChar : JChar → Index) (enc : CharEncoding ncodeunitsChar) (chars : CharOps JChar E),
    Utf8TextLaws ops v ncodeunitsChar enc → CharOpsLaws chars ncodeunitsChar →
    (∀ c, chars.toChar c = .ok c) → CodeunitLaws codeunits bytes v bv → ∀ s c,
      ((charOccurrence ops bytes codeunits chars c s).run = some (.ok true)
        ↔ ∃ p ∈ v.characters s, p.2 = c) ∧
      (inCharDense ops bytes codeunits chars c s = .ok true
        ↔ ∃ p ∈ v.characters s, p.2 = c)

/-- Character and byte membership agree with element occurrence; string-in-string rejects the call and directs the caller to occursin. -/
def MembershipSpec : Prop :=
(∀ (S R C CU CT D E H : Type) (st : StringType S R C CU CT E) (v : TextView S C)
    (equal : C → D → Except E JuliaLean.base.operators.Truth) (accepts : C → D → Bool)
    (assertion : E),
    TextLaws (searchOpsOf st) v →
    (∀ c d, equal c d = .ok (if accepts c d then .true else .false)) →
    ∀ s c (h : H), (∃ h', inChar st (SourceKind.generic (A := Unit)) equal assertion c s h =
      some (.ok true, h')) ↔ ∃ p ∈ v.characters s, accepts p.2 c = true) ∧
  (∀ (S R CU CT A D E H : Type) (st : StringType S R JChar CU CT E) (v : TextView S JChar)
    (u : Utf8Source S A D E) (bv : ByteView A UInt8) (ncu : JChar → Index)
    (enc : CharEncoding ncu) (equal : JChar → D → Except E JuliaLean.base.operators.Truth)
    (assertion : E),
    Utf8TextLaws u.search v ncu enc → CharOpsLaws u.chars ncu →
    CodeunitLaws u.codeunits u.bytes v bv →
    ∀ s c cc (h : H), u.chars.toChar c = .ok cc →
      ((∃ h', inChar st (SourceKind.utf8 u) equal assertion c s h = some (.ok true, h')) ↔
        ∃ p ∈ v.characters s, p.2 = cc)) ∧
  (∀ (A E : Type) (ops : DenseOps A UInt8 E) (v : ByteView A UInt8),
    CMemoryLaws ops v → (∀ b, ops.value b = Int.ofNat b.toNat) →
    ∀ a b, inUInt8 ops b a = .ok true ↔ b ∈ v.elements a) ∧
  (∀ (A E : Type) (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8)),
    CMemoryLaws ops v → (∀ b, ops.value b = b.val) →
    ∀ a b, inInt8 ops b a = .ok true ↔ b ∈ v.elements a) ∧
  (∀ (S T E : Type) (error : String → E) (needle : T) (haystack : S),
    inString error needle haystack = .error (error "use occursin(needle, haystack) for string containment"))

/-- Byte-pattern findall returns matching sequence ranges in order, excludes overlap when requested, and includes every match when overlap is enabled. -/
def ByteFindallSpec : Prop :=
∀ (A T E H : Type) (cfg : BytePatternSearch A T UInt8 UInt8 E)
    (sv : ByteView A UInt8) (tv : ByteView T UInt8) (vec : VectorStore MatchRange E H),
    BytePatternLaws cfg sv tv → VectorStoreLaws vec →
    ∀ a t overlap ranges h,
      VectorResult vec (findallRanges vec (fun t a i => liftSearch (vectorNext cfg indexOps t a i))
        cfg.source.firstindex (fun a => liftExcept (.ok (cfg.source.lastindex a)))
        (fun _ i => liftExcept (.ok (i + int 1))) overlap t a) h ranges →
      (∀ r ∈ ranges, byteRangeAt cfg sv tv a t r) ∧
      ranges.Pairwise (fun a b => a.first.val < b.first.val) ∧
      (overlap = false → ranges.Pairwise (fun a b => a.last.val < b.first.val)) ∧
      (overlap = true → ∀ r, byteRangeAt cfg sv tv a t r → r ∈ ranges)

@[simp] private theorem bind_ok_raw {E α β : Type} (a : α) (f : α → Except E β) :
    Bind.bind (Except.ok a) f = f a := rfl

private theorem bloom_shift_testBit :
    ∀ (a k : Fin 64),
      (UInt64.ofNat 1 <<< UInt64.ofNat a.val).toNat.testBit k.val = decide (k.val = a.val) := by
  decide

private theorem bitvec_and_63_toNat (z : Int) :
    (BitVec.ofInt 64 z &&& BitVec.ofInt 64 63).toNat = (z % 64).toNat := by
  have h1 : (BitVec.ofInt 64 z &&& BitVec.ofInt 64 63).toNat =
      (BitVec.ofInt 64 z).toNat &&& 63 := by
    rw [BitVec.toNat_and]
    rfl
  have h2 : (BitVec.ofInt 64 z).toNat &&& 63 = (BitVec.ofInt 64 z).toNat % 64 := by
    change (BitVec.ofInt 64 z).toNat &&& (2 ^ 6 - 1) = (BitVec.ofInt 64 z).toNat % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod _ 6
  have h3 : (BitVec.ofInt 64 z).toNat = (z % (2 ^ 64 : Int)).toNat := by
    simp [BitVec.ofInt]
  rw [h1, h2, h3]
  omega

theorem bloomBitSpec_proven : BloomBitSpec := by
  intro B E value b mask hmask k
  unfold byteBloom searchBloomMask at hmask
  simp only [bind_ok_raw, Except.ok.injEq] at hmask
  subst hmask
  have hmod : (BitVec.ofInt 64 (value b) &&& BitVec.ofInt 64 (int 63).val).toNat =
      (value b % 64).toNat := by
    have h63 : (int 63).val = 63 := by decide
    rw [h63]
    exact bitvec_and_63_toNat (value b)
  have hlt : (value b % 64).toNat < 64 := by omega
  have h1 : (JInt.lit .u64 1).val.toNat = 1 := by decide
  rw [h1, hmod]
  exact bloom_shift_testBit ⟨(value b % 64).toNat, hlt⟩ k

private theorem int_val_self (i : Index) : int i.val = i := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 i.val i.property

private theorem flatMap_getElem? {α β : Type} (f : α → List β) :
    ∀ (xs : List α) (k : Nat) (b : β),
      (xs.flatMap f)[k]? = some b →
      ∃ (m : Nat) (p : α) (r : Nat),
        xs[m]? = some p ∧ (f p)[r]? = some b ∧ k = ((xs.take m).flatMap f).length + r := by
  intro xs
  induction xs with
  | nil =>
      intro k b h
      simp at h
  | cons x xs ih =>
      intro k b h
      simp only [List.flatMap_cons] at h
      by_cases hk : k < (f x).length
      · rw [List.getElem?_append_left hk] at h
        exact ⟨0, x, k, rfl, h, by simp⟩
      · have hle : (f x).length ≤ k := Nat.le_of_not_lt hk
        rw [List.getElem?_append_right hle] at h
        obtain ⟨m, p, r, hm, hr, hkeq⟩ := ih (k - (f x).length) b h
        refine ⟨m + 1, p, r, ?_, hr, ?_⟩
        · simpa using hm
        · simp only [List.take_succ_cons, List.flatMap_cons, List.length_append]
          omega

theorem standalonePositionsSpec_proven : StandalonePositionsSpec := by
  intro S E ops v ncodeunitsChar enc hLaws s b k hstand hbyte
  rw [← hLaws.concatenation s] at hbyte
  obtain ⟨m, p, r, hm, hr, hkeq⟩ :=
    flatMap_getElem? (fun p => enc.bytes p.2) (v.characters s) k b hbyte
  have hp_mem : p ∈ v.characters s := List.mem_of_getElem? hm
  have hb_mem : b ∈ enc.bytes p.2 := List.mem_of_getElem? hr
  have hstand_range : b.toNat < 128 ∨ 247 < b.toNat := by
    simp only [isStandaloneByte, Bool.or_eq_true, decide_eq_true_eq] at hstand
    rcases hstand with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  have henc : enc.bytes p.2 = [b] := hLaws.standalone s p b hp_mem hb_mem hstand_range
  rw [henc] at hr
  have hr0 : r = 0 := by
    cases r with
    | zero => rfl
    | succ r' => simp at hr
  have hoff := hLaws.offsets s m p hm
  rw [hr0, Nat.add_zero] at hkeq
  have hp1_val : p.1.val = Int.ofNat k + 1 := by
    rw [hkeq, hoff]
    omega
  have hp1 : int (Int.ofNat k + 1) = p.1 := by
    rw [← hp1_val, int_val_self]
  refine ⟨p.2, ?_, henc⟩
  rw [hp1]
  exact hp_mem

@[simp] private theorem liftE_ok_bind {E α β : Type} (a : α) (f : α → SearchM E β) :
    (liftE (.ok a) >>= f) = f a := rfl

theorem denseReverseEmptySpec_proven : DenseReverseEmptySpec := by
  intro S T A D E cfg sv tv bv pv ncu enc hLaws s t i hbytes
  have hchars_empty : (tv.characters t).isEmpty = true := by
    rw [hLaws.pattern.nonempty t, hbytes]
    rfl
  have hchars : tv.characters t = [] := List.isEmpty_iff.mp hchars_empty
  have hlast : cfg.pattern.lastindex t = .ok (int 0) := by
    rw [hLaws.pattern.lastindex t]
    simp [lastIndex, hchars]
  have hncu : (cfg.pattern.ncodeunits t).val = 0 := by
    rw [hLaws.pattern.ncodeunits t, hbytes]
    rfl
  have hsz_nonneg : 0 ≤ (JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val := by
    rw [hLaws.sizeof s]
    exact Int.natCast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · intro hgt
    simp [densePrev, findprevString, indexOps, denseRRange, rsearchRange,
      liftE_ok_bind, denseRIndex, rsearchindexDense, hlast, hncu, hgt]
    rfl
  · intro hi0
    have hnotgt : ¬ ((JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val < 0) := by omega
    simp [densePrev, findprevString, indexOps, denseRRange, rsearchRange,
      liftE_ok_bind, denseRIndex, rsearchindexDense, hlast, hncu, hi0, hnotgt]
    rfl
  · intro hle hne
    have hnotgt : ¬ (i.val > (JuliaLean.base.strings.basic.sizeofString cfg.sourceBasic s).val) := by omega
    have hzero : (int 0).val = 0 := by decide
    have hone : (int 1).val = 1 := by decide
    simp [densePrev, findprevString, indexOps, denseRRange, rsearchRange,
      liftE_ok_bind, denseRIndex, rsearchindexDense, hlast, hncu, hnotgt, hne, hzero, hone, int_val_self]

private theorem uint32_shr_toUInt8 (c : JChar) (s : Nat) (hs : s < 32) :
    ((c >>> UInt32.ofNat s).toUInt8).toNat = (c.toNat / 2 ^ s) % 256 := by
  have h1 : (c >>> UInt32.ofNat s).toNat = c.toNat >>> s := by
    simp [UInt32.toNat_shiftRight, Nat.mod_eq_of_lt hs]
  have h2 : ((c >>> UInt32.ofNat s).toUInt8).toNat = (c >>> UInt32.ofNat s).toNat % 256 := rfl
  rw [h2, h1, Nat.shiftRight_eq_div_pow]

private theorem uint8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

private theorem packedCharBytes {ncodeunits : JChar → Index}
    (encoding : CharEncoding ncodeunits) (c : JChar) (bytes : List UInt8)
    (hbytes : encoding.bytes c = bytes) :
    c.toNat = bytes.zipIdx.foldl (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 := by
  exact (encoding.packed c).trans (congrArg (fun bs : List UInt8 =>
    bs.zipIdx.foldl (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0) hbytes)
/-- The byte `lastUtf8Byte` returns for a character whose length `ncodeunits` gives. -/
private def lastByteOf (ncodeunits : JChar → Index) (c : JChar) : UInt8 :=
  match lastUtf8Byte (E := Empty) (fun c => .ok (ncodeunits c)) c with
  | .ok b => b
  | .error e => nomatch e

private theorem lastUtf8Byte_ok {E : Type} (ncodeunits : JChar → Index) (c : JChar) :
    lastUtf8Byte (E := E) (fun c => .ok (ncodeunits c)) c = .ok (lastByteOf ncodeunits c) := rfl

private theorem lastByteOf_eq (ncodeunits : JChar → Index) (c : JChar) :
    lastByteOf ncodeunits c = (c >>> UInt32.ofNat
      ((BitVec.ofInt 64 ((int 4 - ncodeunits c) * int 8).val &&& BitVec.ofNat 64 31).toNat)).toUInt8 :=
  rfl

private theorem lastUtf8ByteCase1 (ncodeunits : JChar → Index)
    (encoding : CharEncoding ncodeunits) (c : JChar) (b0 : UInt8)
    (hbytes : encoding.bytes c = [b0]) :
    (encoding.bytes c).getLast? = some (lastByteOf ncodeunits c) := by
  have hpack := packedCharBytes encoding c [b0] hbytes
  have hncu_eq : ncodeunits c = int 1 := by
    apply Subtype.ext
    change (ncodeunits c).val = 1
    simpa [hbytes] using encoding.ncodeunits_eq c
  rw [hbytes]
  simp only [List.getLast?, List.getLast, lastByteOf_eq, hncu_eq, Option.some.injEq]
  have hsh : ((BitVec.ofInt 64 ((int 4 - int 1) * int 8).val &&& BitVec.ofNat 64 31).toNat) = 24 := by
    decide
  rw [hsh]
  apply uint8_eq_of_toNat
  rw [uint32_shr_toUInt8 c 24 (by decide)]
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hfold : [b0].zipIdx.foldl
      (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 = b0.toNat * 2 ^ 24 := by
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      Nat.reduceSub, Nat.reduceMul, Nat.zero_add]
  have hpack' : c.toNat = b0.toNat * 2 ^ 24 := hpack.trans hfold
  rw [hpack']
  rw [Nat.mul_div_cancel _ (by decide), Nat.mod_eq_of_lt hb0]

private theorem lastUtf8ByteCase2 (ncodeunits : JChar → Index)
    (encoding : CharEncoding ncodeunits) (c : JChar) (b0 b1 : UInt8)
    (hbytes : encoding.bytes c = [b0, b1]) :
    (encoding.bytes c).getLast? = some (lastByteOf ncodeunits c) := by
  have hpack := packedCharBytes encoding c [b0, b1] hbytes
  have hncu_eq : ncodeunits c = int 2 := by
    apply Subtype.ext
    change (ncodeunits c).val = 2
    simpa [hbytes] using encoding.ncodeunits_eq c
  rw [hbytes]
  simp only [List.getLast?, List.getLast, lastByteOf_eq, hncu_eq]
  have hsh : ((BitVec.ofInt 64 ((int 4 - int 2) * int 8).val &&& BitVec.ofNat 64 31).toNat) = 16 := by
    decide
  rw [hsh]
  congr 1
  apply uint8_eq_of_toNat
  rw [uint32_shr_toUInt8 c 16 (by decide)]
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
  have hfold : [b0, b1].zipIdx.foldl
      (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 =
      b0.toNat * 16777216 + b1.toNat * 65536 := by
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.zero_add]
  have hpacked : c.toNat = b0.toNat * 16777216 + b1.toNat * 65536 :=
    hpack.trans hfold
  have hpack' : c.toNat = (b0.toNat * 256 + b1.toNat) * 65536 := by
    calc
      c.toNat = b0.toNat * 16777216 + b1.toNat * 65536 := hpacked
      _ = (b0.toNat * 256 + b1.toNat) * 65536 := by
        rw [show 16777216 = 256 * 65536 by decide]
        omega
  rw [hpack']
  change b1.toNat = ((b0.toNat * 256 + b1.toNat) * 65536 / 65536) % 256
  rw [Nat.mul_div_cancel _ (by decide)]
  simp [Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt hb1]

private theorem lastUtf8ByteCase3 (ncodeunits : JChar → Index)
    (encoding : CharEncoding ncodeunits) (c : JChar) (b0 b1 b2 : UInt8)
    (hbytes : encoding.bytes c = [b0, b1, b2]) :
    (encoding.bytes c).getLast? = some (lastByteOf ncodeunits c) := by
  have hpack := packedCharBytes encoding c [b0, b1, b2] hbytes
  have hncu_eq : ncodeunits c = int 3 := by
    apply Subtype.ext
    change (ncodeunits c).val = 3
    simpa [hbytes] using encoding.ncodeunits_eq c
  rw [hbytes]
  simp only [List.getLast?, List.getLast, lastByteOf_eq, hncu_eq]
  have hsh : ((BitVec.ofInt 64 ((int 4 - int 3) * int 8).val &&& BitVec.ofNat 64 31).toNat) = 8 := by
    decide
  rw [hsh]
  congr 1
  apply uint8_eq_of_toNat
  rw [uint32_shr_toUInt8 c 8 (by decide)]
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
  have hb2 : b2.toNat < 256 := b2.toBitVec.isLt
  have hfold : [b0, b1, b2].zipIdx.foldl
      (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 =
      b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 := by
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.zero_add]
  have hpacked : c.toNat =
      b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 :=
    hpack.trans hfold
  have hpack' : c.toNat =
      (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) * 256 := by
    calc
      c.toNat = b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 := hpacked
      _ = (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) * 256 := by
        rw [show 16777216 = 65536 * 256 by decide,
          show 65536 = 256 * 256 by decide]
        omega
  rw [hpack']
  change b2.toNat =
    ((b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) * 256 / 256) % 256
  rw [Nat.mul_div_cancel _ (by decide)]
  have hzero0 : (b0.toNat * 65536) % 256 = 0 := by
    rw [show 65536 = 256 * 256 by decide, ← Nat.mul_assoc, Nat.mul_mod_left]
  simp [Nat.add_mod, hzero0, Nat.mul_mod_left, Nat.mod_eq_of_lt hb2]

private theorem lastUtf8ByteCase4 (ncodeunits : JChar → Index)
    (encoding : CharEncoding ncodeunits) (c : JChar) (b0 b1 b2 b3 : UInt8)
    (hbytes : encoding.bytes c = [b0, b1, b2, b3]) :
    (encoding.bytes c).getLast? = some (lastByteOf ncodeunits c) := by
  have hpack := packedCharBytes encoding c [b0, b1, b2, b3] hbytes
  have hncu_eq : ncodeunits c = int 4 := by
    apply Subtype.ext
    change (ncodeunits c).val = 4
    simpa [hbytes] using encoding.ncodeunits_eq c
  rw [hbytes]
  simp only [List.getLast?, List.getLast, lastByteOf_eq, hncu_eq]
  have hsh : ((BitVec.ofInt 64 ((int 4 - int 4) * int 8).val &&& BitVec.ofNat 64 31).toNat) = 0 := by
    decide
  rw [hsh]
  congr 1
  apply uint8_eq_of_toNat
  rw [uint32_shr_toUInt8 c 0 (by decide)]
  have hb0 : b0.toNat < 256 := b0.toBitVec.isLt
  have hb1 : b1.toNat < 256 := b1.toBitVec.isLt
  have hb2 : b2.toNat < 256 := b2.toBitVec.isLt
  have hb3 : b3.toNat < 256 := b3.toBitVec.isLt
  simp only [Nat.pow_zero, Nat.div_one]
  have hfold : [b0, b1, b2, b3].zipIdx.foldl
      (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 =
      b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat := by
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.zero_add, Nat.mul_one]
  have hpacked : c.toNat =
      b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat :=
    hpack.trans hfold
  have hpack' : c.toNat =
      (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) * 256 + b3.toNat := by
    calc
      c.toNat = b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat := hpacked
      _ = (b0.toNat * 65536 + b1.toNat * 256 + b2.toNat) * 256 + b3.toNat := by
        rw [show 16777216 = 65536 * 256 by decide,
          show 65536 = 256 * 256 by decide]
        omega
  rw [hpack']
  have hzero0 : (b0.toNat * 65536) % 256 = 0 := by
    rw [show 65536 = 256 * 256 by decide, ← Nat.mul_assoc, Nat.mul_mod_left]
  simp [Nat.add_mod, hzero0, Nat.mul_mod_left, Nat.mod_eq_of_lt hb3]

theorem lastUtf8ByteSpec_proven : LastUtf8ByteSpec := by
  intro E ncodeunits encoding c
  rw [lastUtf8Byte_ok]
  suffices h : (encoding.bytes c).getLast? = some (lastByteOf ncodeunits c) by rw [h]; rfl
  have hne := encoding.nonempty c
  have hlen := encoding.length c
  cases hbytes : encoding.bytes c with
  | nil =>
      rw [hbytes] at hne
      contradiction
  | cons b0 rest =>
      cases rest with
      | nil => simpa [hbytes] using lastUtf8ByteCase1 ncodeunits encoding c b0 hbytes
      | cons b1 rest =>
          cases rest with
          | nil => simpa [hbytes] using lastUtf8ByteCase2 ncodeunits encoding c b0 b1 hbytes
          | cons b2 rest =>
              cases rest with
              | nil => simpa [hbytes] using lastUtf8ByteCase3 ncodeunits encoding c b0 b1 b2 hbytes
              | cons b3 rest =>
                  cases rest with
                  | nil =>
                      simpa [hbytes] using lastUtf8ByteCase4 ncodeunits encoding c b0 b1 b2 b3 hbytes
                  | cons _ _ =>
                      rw [hbytes] at hlen
                      simp at hlen

private def emptyTextView : TextView Unit JChar := ⟨fun _ => [], fun _ => []⟩
private def emptyByteView : ByteView Unit UInt8 := ⟨fun _ => int 1, fun _ => []⟩

private def emptyStringOps : SearchStringOps Unit JChar Unit where
  ncodeunits := fun _ => int 0
  iterationBound := fun _ => 0
  lastindex := fun _ => .ok (int 0)
  nextind := fun _ _ => .ok (int 1)
  prevind := fun _ _ => .ok (int 0)
  isvalid := fun _ _ => .ok false
  getindex := fun _ _ => .error ()
  iterate := fun _ _ => .ok none
  boundsError := fun _ _ => ()
  stringIndexError := fun _ _ => ()
  somethingError := ()

private def emptyByteOps : ByteOps Unit UInt8 Unit where
  firstindex := fun _ => int 1
  lastindex := fun _ => int 0
  length := fun _ => int 0
  getindex := fun _ _ => .error ()
  value := fun b => Int.ofNat b.toNat
  zero := 0
  boundsError := fun _ _ => ()

private def emptyDenseOps : DenseOps Unit UInt8 Unit where
  toByteOps := emptyByteOps
  pointer := fun _ => JInt.lit .u64 1
  memchrCall := fun _ _ _ _ => .ok (JInt.wrap .u64 0)
  memrchrCall := fun _ _ _ _ => .ok (JInt.wrap .u64 0)

private theorem intVal (z : Int)
    (h : IntTy.min .i64 ≤ z ∧ z ≤ IntTy.max .i64) : (int z).val = z := by
  change wrapInt .i64 z = z
  exact wrapInt_of_inRange .i64 z h

private theorem intVal0 : (int 0).val = 0 := intVal 0 (by decide)
private theorem intVal1 : (int 1).val = 1 := intVal 1 (by decide)
private theorem intVal4 : (int 4).val = 4 := intVal 4 (by decide)
private theorem intValNeg1 : (int (-1)).val = -1 := intVal (-1) (by decide)
private theorem intZeroSubOne : int 0 - int 1 = int (-1) := by decide

private def emptyPackedCharBytes (c : JChar) : List UInt8 :=
  [UInt8.ofNat (c.toNat / 2 ^ 24), UInt8.ofNat (c.toNat / 2 ^ 16),
    UInt8.ofNat (c.toNat / 2 ^ 8), UInt8.ofNat c.toNat]

private theorem emptyPackedCharBytes_fold (c : JChar) :
    (emptyPackedCharBytes c).zipIdx.foldl
      (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 = c.toNat := by
  have hlt : c.toNat < 2 ^ 32 := c.toBitVec.isLt
  simp [emptyPackedCharBytes, List.zipIdx, List.foldl, UInt8.toNat_ofNat]
  omega

private def emptyNcodeunitsChar : JChar → Index := fun _ => int 4

private def emptyCharEncoding : CharEncoding emptyNcodeunitsChar where
  bytes := emptyPackedCharBytes
  nonempty := by intro c; simp [emptyPackedCharBytes]
  length := by intro c; simp [emptyPackedCharBytes]
  ncodeunits_eq := by intro c; simp [emptyNcodeunitsChar, emptyPackedCharBytes, intVal4]
  packed := by intro c; exact (emptyPackedCharBytes_fold c).symm

private theorem emptyTextLaws : TextLaws emptyStringOps emptyTextView := by
  refine {
    sizeFits := ?_
    ncodeunits := ?_
    iterationBound := ?_
    sorted := ?_
    indices := ?_
    nonempty := ?_
    first := ?_
    lastindex := ?_
    isvalid := ?_
    getindex := ?_
    nextind := ?_
    prevind := ?_
    iterate := ?_
  }
  · intro s
    simp [emptyTextView]
    decide
  · intro s
    simp [emptyStringOps, emptyTextView, intVal0]
  · intro s
    simp [emptyStringOps, emptyTextView]
  · intro s
    simp [emptyTextView]
  · intro s p hp
    simp [emptyTextView] at hp
  · intro s
    rfl
  · intro s p hp
    simp [emptyTextView] at hp
  · intro s
    simp [emptyStringOps, emptyTextView, lastIndex, intVal0]
  · intro s i
    simp [emptyStringOps, emptyTextView, intVal0]
  · intro s i c hp
    simp [emptyTextView] at hp
  · intro s i hi
    simp [emptyStringOps, emptyTextView, validAt, nextPosition, endIndex,
      intVal0, intVal1]
  · intro s i hi
    simp [emptyStringOps, emptyTextView, validAt, prevPosition, endIndex, intVal0]
  · intro s i c hp
    simp [emptyTextView] at hp

private theorem emptyUtf8TextLaws :
    Utf8TextLaws emptyStringOps emptyTextView emptyNcodeunitsChar emptyCharEncoding := by
  exact {
    toTextLaws := emptyTextLaws
    concatenation := by intro s; rfl
    offsets := by intro s k p hp; simp [emptyTextView] at hp
    standalone := by intro s p b hp; simp [emptyTextView] at hp
  }

private theorem emptyByteLaws : ByteLaws emptyByteOps emptyByteView := by
  refine {
    firstindex := by intro a; exact intVal1
    lastindex := by intro a; exact intVal0
    length := by intro a; exact intVal0
    getindex := ?_
    getindexOutside := by intro a i hi; rfl
    byteValue := ?_
  }
  · intro a k b h
    simp [emptyByteView] at h
  · intro b
    have hb : b.toNat < 256 := b.toBitVec.isLt
    constructor <;> simp [emptyByteOps] <;> omega

private theorem emptyCMemoryLaws : CMemoryLaws emptyDenseOps emptyByteView := by
  refine {
    bytes := emptyByteLaws
    nonnull := by
      intro a
      change wrapInt .u64 1 ≠ 0
      rw [wrapInt_of_inRange .u64 1 (by decide)]
      decide
    addressRange := by
      intro a
      change wrapInt .u64 1 + 0 < 2 ^ 64
      rw [wrapInt_of_inRange .u64 1 (by decide)]
      decide
    memchr := ?_
    memrchr := ?_
  }
  · intro a start count needle hstart hcount hbound
    simp [emptyDenseOps, emptyByteView, emptyByteOps]
  · intro a count needle hcount hbound
    simp [emptyDenseOps, emptyByteView, emptyByteOps]

private def emptyBasic : JuliaLean.base.strings.basic.StringOps Unit Unit JChar UInt8 Unit Unit where
  ncodeunits := fun _ => int 0
  codeunitType := fun _ => ()
  codeunitSize := fun _ => int 1
  codeunit := fun _ _ => .error ()
  isvalid := fun _ _ => .ok false
  iterateFirst := fun _ => .ok none
  iterateAt := fun _ _ => .ok none
  iterationBound := fun _ => 0
  thisind := fun _ i => .ok i
  prevind := fun _ i _ => .ok i
  nextind := fun _ i _ => .ok i
  lastindex := fun _ => .ok (int 0)
  getindexSlice := fun _ _ _ => .ok ()
  checkbounds := fun _ _ => .error ()
  checkboundsBool := fun _ _ => .ok false
  boundsError := fun _ _ => ()
  stringIndexError := fun _ _ => ()
  methodError := fun _ => ()
  argumentError := fun _ => ()
  tupleTypeError := ()
  isBoundsError := fun _ => true
  characters := fun _ => .ok []
  sameReference := fun _ _ => true
  equalChar := fun a b => decide (a = b)
  lessChar := fun a b => decide (a < b)

private def emptyCfg : DenseStringSearch Unit Unit Unit Unit Unit where
  source := emptyStringOps
  pattern := emptyStringOps
  sourceBytes := emptyDenseOps
  patternBytes := emptyByteOps
  codeunitsSource := fun _ => ()
  codeunitsPattern := fun _ => ()
  chars := ⟨fun c => .ok c, fun c => .ok (emptyNcodeunitsChar c)⟩
  sourceBasic := emptyBasic

private theorem emptyDenseLaws :
    DenseLaws emptyCfg emptyTextView emptyTextView emptyByteView emptyByteView emptyCharEncoding := by
  refine {
    source := emptyUtf8TextLaws
    pattern := emptyUtf8TextLaws
    codeunits := ?_
    chars := by intro c; rfl
    toChar := by intro c; rfl
    patternBytes := emptyByteLaws
    patternFirst := by intro t; rfl
    patternContents := by intro t; rfl
    patternValues := by intro b; rfl
    sizeof := by intro s; simp only [emptyCfg, emptyBasic, emptyTextView, JuliaLean.base.strings.basic.sizeofString]; decide
  }
  exact ⟨emptyCMemoryLaws, ⟨by intro s; rfl, ⟨by intro s; rfl, by intro b; rfl⟩⟩⟩

private def emptyRange : MatchRange := ⟨int 0, int (-1)⟩

private theorem emptyDensePrevOne :
    (densePrev emptyCfg indexOps () () (int 1)).run = some (.ok (some emptyRange)) := by
  simp [densePrev, findprevString, denseRRange, rsearchRange, denseRIndex,
    liftE, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
    rsearchindexDense, emptyCfg, emptyStringOps, emptyTextView, emptyByteOps,
    emptyDenseOps, emptyByteView, emptyNcodeunitsChar, emptyRange, indexOps,
    intVal0, intVal1, intValNeg1, intZeroSubOne]
  rfl

theorem findprevLatest_refuted : ¬ FindprevLatest := by
  intro h
  have hresult := h Unit Unit Unit Unit Unit emptyCfg emptyTextView emptyTextView
    emptyByteView emptyByteView emptyNcodeunitsChar emptyCharEncoding emptyDenseLaws () () (int 1) emptyRange
    (by decide) (by decide) emptyDensePrevOne
  have hfalse : ¬ textSequenceAt emptyTextView
      (fun t => (emptyTextView.characters t).map (·.2)) () () emptyRange := by
    simp [textSequenceAt, emptyTextView, emptyRange, intVal0, intValNeg1] <;> omega
  exact hfalse hresult.1

theorem emptyPatternStartSpec_refuted : ¬ EmptyPatternStartSpec := by
  intro h
  have hstart := h Unit Unit Unit Unit Unit emptyCfg emptyTextView emptyTextView
    emptyByteView emptyByteView emptyNcodeunitsChar emptyCharEncoding emptyDenseLaws () () (int 1) rfl
    (by decide) (by decide) (Or.inr (by decide))
  have hsize : (JuliaLean.base.strings.basic.sizeofString emptyCfg.sourceBasic ()).val = 0 := by simp only [emptyCfg, emptyBasic, JuliaLean.base.strings.basic.sizeofString]; decide
  have hreverse := denseReverseEmptySpec_proven Unit Unit Unit Unit Unit emptyCfg
    emptyTextView emptyTextView emptyByteView emptyByteView emptyNcodeunitsChar emptyCharEncoding emptyDenseLaws
    () () (int 1) rfl
  have hgt : (int 1).val > (JuliaLean.base.strings.basic.sizeofString emptyCfg.sourceBasic ()).val := by
    rw [intVal1, hsize]
    decide
  have hOneSubOne : int 1 - int 1 = int 0 := by decide
  have hrequested : (densePrev emptyCfg indexOps () () (int 1)).run =
      some (.ok (some (⟨int 1, int 0⟩ : MatchRange))) := by
    simpa [hOneSubOne] using hstart.2
  have hactual := hreverse.1 hgt
  have hboth : (some (Except.ok (some (⟨int 1, int 0⟩ : MatchRange))) :
      Option (Except Unit (Option MatchRange))) = some (Except.ok (some emptyRange)) :=
    hrequested.symm.trans hactual
  have hrange : (⟨int 1, int 0⟩ : MatchRange) = emptyRange := by
    injection hboth with hexc
    injection hexc with hoption
    injection hoption
  have hfirst : int 1 = int 0 := congrArg MatchRange.first hrange
  have hval : (int 1).val = (int 0).val :=
    congrArg (fun x : Index => x.val) hfirst
  rw [intVal1, intVal0] at hval
  omega

theorem charFirstLastSpec_proven : CharFirstLastSpec := by
  intro S C D E ops v equal accepts first last _ heq hfirst hlast target s
  exact ⟨hfirst (fun c => equal c target) (fun c => accepts c target) s
      (fun c => heq c target),
    hlast (fun c => equal c target) (fun c => accepts c target) s
      (fun c => heq c target)⟩

private def offsetEmptySourceOps : ByteOps Unit UInt8 Unit where
  firstindex := fun _ => int 0
  lastindex := fun _ => int (-1)
  length := fun _ => int 0
  getindex := fun _ _ => .error ()
  value := fun b => Int.ofNat b.toNat
  zero := 0
  boundsError := fun _ _ => ()

private def offsetEmptyPatternOps : ByteOps Unit UInt8 Unit where
  firstindex := fun _ => int 1
  lastindex := fun _ => int 0
  length := fun _ => int 0
  getindex := fun _ _ => .error ()
  value := fun b => Int.ofNat b.toNat
  zero := 0
  boundsError := fun _ _ => ()

private def offsetEmptyCfg : BytePatternSearch Unit Unit UInt8 UInt8 Unit where
  source := offsetEmptySourceOps
  pattern := offsetEmptyPatternOps
  findnext := fun _ _ _ => .ok none
  findprev := fun _ a i =>
    if (offsetEmptySourceOps.lastindex a).val < i.val then
      .error (offsetEmptySourceOps.boundsError a i.val)
    else .ok none

private def offsetEmptySv : ByteView Unit UInt8 := ⟨fun _ => 0, fun _ => []⟩
private def offsetEmptyTv : ByteView Unit UInt8 := ⟨fun _ => 1, fun _ => []⟩

private theorem intZeroVal : (int 0).val = 0 := by
  change wrapInt .i64 0 = 0
  exact wrapInt_of_inRange .i64 0 (by decide)

private theorem intOneVal : (int 1).val = 1 := by
  change wrapInt .i64 1 = 1
  exact wrapInt_of_inRange .i64 1 (by decide)
private theorem intNegOneVal : (int (-1)).val = -1 := by
  change wrapInt .i64 (-1) = -1
  exact wrapInt_of_inRange .i64 (-1) (by decide)

private theorem intZeroSubNegOne : int 0 - int (-1) = int 1 := by decide
private theorem intZeroAddOne : int 0 + int 1 = int 1 := by decide
private theorem intOneSubOne : int 1 - int 1 = int 0 := by decide

private theorem offsetEmptySourceByteLaws :
    ByteLaws offsetEmptySourceOps offsetEmptySv := by
  refine {
    firstindex := by intro a; change (int 0).val = 0; exact intZeroVal
    lastindex := by
      intro a
      change (int (-1)).val = 0 + Int.ofNat ([] : List UInt8).length - 1
      rw [intNegOneVal]
      decide
    length := by intro a; change (int 0).val = 0; exact intZeroVal
    getindex := fun _ _ _ h => nomatch h
    getindexOutside := by intro _ _ _; rfl
    byteValue := fun b => by
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hNat : b.toNat ≤ 255 := Nat.le_of_lt_succ (by simpa using hb)
      constructor
      · exact Int.le_trans (by decide : (-128 : Int) ≤ 0) (Int.natCast_nonneg _)
      · exact Int.ofNat_le.mpr hNat
  }

private theorem offsetEmptyPatternByteLaws :
    ByteLaws offsetEmptyPatternOps offsetEmptyTv := by
  refine {
    firstindex := by intro a; change (int 1).val = 1; exact intOneVal
    lastindex := by
      intro a
      change (int 0).val = 1 + Int.ofNat ([] : List UInt8).length - 1
      rw [intZeroVal]
      decide
    length := by intro a; change (int 0).val = 0; exact intZeroVal
    getindex := fun _ _ _ h => nomatch h
    getindexOutside := by intro _ _ _; rfl
    byteValue := fun b => by
      have hb : b.toNat < 256 := b.toBitVec.isLt
      have hNat : b.toNat ≤ 255 := Nat.le_of_lt_succ (by simpa using hb)
      constructor
      · exact Int.le_trans (by decide : (-128 : Int) ≤ 0) (Int.natCast_nonneg _)
      · exact Int.ofNat_le.mpr hNat
  }

private theorem offsetEmptyByteLaws :
    BytePatternLaws offsetEmptyCfg offsetEmptySv offsetEmptyTv := by
  refine {
    source := offsetEmptySourceByteLaws
    pattern := offsetEmptyPatternByteLaws
    findnext := ?_
    findprev := ?_
    findprevAboveLast := ?_
  }
  · intro a c i hi
    change FirstIndex
      (byteMatches offsetEmptySv (fun b => offsetEmptySourceOps.value b ==
        offsetEmptyPatternOps.value c) a) i.val (Except.ok none)
    simp [FirstIndex, byteMatches, byteAt, offsetEmptySv]
  · intro a c i hi
    have hnot : ¬ (-1 : Int) < i.val := by
      simp [offsetEmptySv] at hi
      omega
    have hlast : (offsetEmptySourceOps.lastindex a).val = -1 := by
      simp [offsetEmptySourceOps, intNegOneVal]
    change LastIndex
      (byteMatches offsetEmptySv (fun b => offsetEmptySourceOps.value b ==
        offsetEmptyPatternOps.value c) a) i.val
      (if (offsetEmptySourceOps.lastindex a).val < i.val then
        Except.error (offsetEmptySourceOps.boundsError a i.val) else Except.ok none)
    rw [hlast, if_neg hnot]
    simp [LastIndex, byteMatches, byteAt, offsetEmptySv]
  · intro a c i hi
    have hcond : -1 < i.val := by
      simpa [offsetEmptyCfg, offsetEmptySourceOps, intNegOneVal] using hi
    simp [offsetEmptyCfg, offsetEmptySourceOps, intNegOneVal, hcond]
set_option maxRecDepth 4096 in
theorem byteEmptyPatternSpec_refuted : ¬ ByteEmptyPatternSpec := by
  intro h
  have hrange := h Unit Unit UInt8 UInt8 Unit offsetEmptyCfg offsetEmptySv offsetEmptyTv
    offsetEmptyByteLaws () () (int 0) rfl (by decide) (by decide)
  have hactual : (vectorNext offsetEmptyCfg indexOps () () (int 0)).run =
      some (.ok (some ⟨int 1, int 0⟩)) := by
    classical
    simp [vectorNext, findnextVector, vectorRange, searchRange, searchindexBytes,
      liftE, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure,
      vectorNth, offsetEmptyCfg, offsetEmptySv, offsetEmptyTv, indexOps, imax,
      intZeroVal, intOneVal, intNegOneVal, intZeroSubOne, intZeroSubNegOne,
      intZeroAddOne, intOneSubOne, offsetEmptySourceOps, offsetEmptyPatternOps]
    rfl
  rw [hactual] at hrange
  have hneq : (some ⟨int 1, int 0⟩ : Option MatchRange) ≠ some ⟨int 0, int (-1)⟩ := by
    decide
  have heq : (some ⟨int 1, int 0⟩ : Option MatchRange) = some ⟨int 0, int (-1)⟩ := by
    have h1 := hrange.1
    injection h1 with h2
    injection h2
  exact hneq heq

private def hugeLength : Nat := (IntTy.max .i64).toNat
private theorem hugeBytesExists : ∃ xs : List UInt8, xs.length = hugeLength := by
  exact ⟨List.replicate hugeLength (0 : UInt8), by simp⟩

private noncomputable def hugeBytes : List UInt8 :=
  Classical.choose hugeBytesExists

private theorem hugeBytesLength : hugeBytes.length = hugeLength :=
  Classical.choose_spec hugeBytesExists

private noncomputable def hugeView : TextView Unit Unit where
  bytes _ := hugeBytes
  characters _ := [(int 1, ())]

private theorem maxNonnegative : 0 ≤ IntTy.max .i64 := by decide

private theorem hugeLengthValue : Int.ofNat hugeLength = IntTy.max .i64 := by
  simpa [hugeLength] using Int.toNat_of_nonneg maxNonnegative
private theorem hugeEndLarge : 1 < endIndex hugeView () := by
  unfold endIndex
  change 1 < Int.ofNat hugeBytes.length + 1
  rw [hugeBytesLength, hugeLengthValue]
  have hpos : 0 < IntTy.max .i64 := by decide
  omega
private theorem hugeLengthNeZero : hugeLength ≠ 0 := by
  intro hzero
  have h := hugeLengthValue
  simp [hzero] at h
  have hmax : IntTy.max .i64 ≠ 0 := by decide
  exact hmax h.symm

private theorem intValue (z : Int) (h : IntTy.min .i64 ≤ z ∧ z ≤ IntTy.max .i64) :
    (int z).val = z := by
  change wrapInt .i64 z = z
  exact wrapInt_of_inRange .i64 z h

private theorem intOneValue : (int 1).val = 1 := by
  change wrapInt .i64 1 = 1
  exact wrapInt_of_inRange .i64 1 (by decide)

private theorem maxPlusOneWraps :
    (int (IntTy.max .i64) + int 1).val = IntTy.min .i64 := by
  decide
private theorem intReconstruct (i : Index) : int i.val = i := by
  apply Subtype.ext
  exact intValue i.val i.property


private noncomputable def hugeOps : JuliaLean.base.strings.basic.StringOps Unit Unit Unit Unit Unit JlError where
  ncodeunits _ := int (IntTy.max .i64)
  codeunitType _ := ()
  codeunitSize _ := int 1
  codeunit _ _ := .ok ()
  isvalid s i := .ok ((hugeView.characters s).any (fun p => p.1 == i))
  iterateFirst _ := .ok (some ((), int 1))
  iterateAt s i := .ok (some ((), nextPosition hugeView s i))
  iterationBound _ := hugeLength
  thisind _ i := .ok i
  prevind _ i _ := .ok i
  nextind _ i n := .ok (i + n)
  lastindex _ := .ok (int 1)
  getindexSlice _ _ _ := .ok ()
  checkbounds _ _ := .ok ()
  checkboundsBool _ _ := .ok true
  boundsError _ _ := .boundsError
  stringIndexError _ _ := .boundsError
  methodError _ := .methodError ""
  argumentError _ := .argumentError ""
  tupleTypeError := .boundsError
  isBoundsError _ := true
  characters _ := .ok [()]
  sameReference _ _ := true
  equalChar _ _ := true
  lessChar _ _ := false

private theorem hugeTextLaws : Round3.PrimitiveTextLaws hugeOps hugeView := by
  refine {
    sizeFits := ?_
    ncodeunits := ?_
    iterationBound := ?_
    sorted := ?_
    indices := ?_
    nonempty := ?_
    first := ?_
    isvalid := ?_
    iterate := ?_
  }
  · intro s
    change Int.ofNat hugeBytes.length ≤ IntTy.max .i64
    rw [hugeBytesLength, hugeLengthValue]
    omega
  · intro s
    change (int (IntTy.max .i64)).val = Int.ofNat hugeBytes.length
    have hmax : (int (IntTy.max .i64)).val = IntTy.max .i64 :=
      intValue (IntTy.max .i64) ⟨by decide, by decide⟩
    rw [hmax, hugeBytesLength, hugeLengthValue]
  · intro s
    change hugeBytes.length ≤ hugeLength
    rw [hugeBytesLength]
    omega
  · intro s
    simp [hugeView]
  · intro s p hp
    simp [hugeView] at hp
    rcases hp with rfl
    constructor
    · rw [intOneValue]
      decide
    · change 1 < Int.ofNat hugeBytes.length + 1
      rw [hugeBytesLength, hugeLengthValue]
      have hpos : 0 < IntTy.max .i64 := by decide
      omega
  · intro s
    have hbytes : hugeBytes ≠ [] := by
      intro hnil
      have hlen := hugeBytesLength
      simp [hnil] at hlen
      exact hugeLengthNeZero hlen.symm
    cases hbytesEq : hugeBytes with
    | nil => exact (hbytes hbytesEq).elim
    | cons b bs => simp [hugeView, hbytesEq]
  · intro s p hp
    simp [hugeView] at hp
    rcases hp with rfl
    rfl
  · intro s i
    rfl
  · intro s p c hp
    simp [hugeView] at hp
    rcases hp with rfl
    rfl

private def hugeTest : Unit → SearchM JlError Bool := fun _ => pure true
private def alwaysTrue : Unit → Bool := fun _ => true

private theorem indexIntegerLaws : IntegerLaws (indexOps (E := JlError)) := by
  constructor
  · intro i _ _
    simp only [indexOps]
    rw [intReconstruct i]
  · intro i j h
    simp [indexOps] at h
    cases h
    rfl

private theorem hugeTestLaw : ∀ c, (hugeTest c).run = some (.ok (alwaysTrue c)) := by
  intro c
  rfl

theorem predicateForwardSpec_refuted : ¬ Round3.PredicateForwardSpec := by
  intro hspec
  let start := int 1
  have hstartValue : (indexOps (E := JlError)).value start = 1 := by
    simp [start, indexOps, intOneValue]
  have hend : (indexOps (E := JlError)).value start ≤ endIndex hugeView () := by
    have hLarge : 1 < endIndex hugeView () := hugeEndLarge
    rw [hstartValue]
    omega
  have hvalid : validAt hugeView () start := by
    exact ⟨(), by simp [hugeView, start]⟩
  have hvalidSpec : validAt hugeView ()
      (int ((indexOps (E := JlError)).value start)) := by
    rw [hstartValue]
    simpa [start] using hvalid
  have hspecApp := hspec Unit Unit Unit Unit Unit Index JlError hugeOps
    (fun _ => "") hugeView (indexOps (E := JlError)) hugeTest alwaysTrue
    hugeTextLaws indexIntegerLaws hugeTestLaw () start (by omega) hend (Or.inl hvalidSpec)
  have hactual :
      (findnextPredicate
        (fromBasic (JuliaLean.base.strings.basic.modelStringOps hugeOps (fun _ => "")))
        (indexOps (E := JlError)) hugeTest () start).run = some (.error JlError.boundsError) := by
    have hmin : IntTy.min .i64 < 1 := by decide
    unfold findnextPredicate
    simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure,
      fromBasic, JuliaLean.base.strings.basic.modelStringOps, hugeOps,
      indexOps, start, intOneValue, maxPlusOneWraps, IntTy.min, IntTy.signed, IntTy.bits, hmin]
  rcases hspecApp with ⟨result, hrun, hfirst⟩
  rw [hactual] at hrun
  have hresult : result = .error JlError.boundsError := by
    injection hrun with hEq
    exact hEq.symm
  subst result
  unfold FirstIndex at hfirst
  have hstartVal : start.val = 1 := by simp [start, intOneValue]
  have hmatch :
      charMatches hugeView (fun c : Unit => alwaysTrue c = true) () start.val := by
    unfold charMatches
    refine ⟨start, (), ?_, rfl, rfl⟩
    simp [hugeView, start]
  have hright :
      (indexOps (E := JlError)).value start ≤ start.val ∧
        charMatches hugeView (fun c : Unit => alwaysTrue c = true) () start.val ∧
        ∀ j, (indexOps (E := JlError)).value start ≤ j →
          charMatches hugeView (fun c : Unit => alwaysTrue c = true) () j →
          start.val ≤ j := by
    constructor
    · rw [hstartValue, hstartVal]
      omega
    · constructor
      · exact hmatch
      · intro j hj _
        rw [hstartVal]
        rw [hstartValue] at hj
        exact hj
  have hsome := (hfirst.1 start).2 hright
  cases hsome
theorem predicateReverseSpec_refuted : ¬ Round3.PredicateReverseSpec := by
  intro hspec
  let start := int 1
  have hstartValue : (indexOps (E := JlError)).value start = 1 := by
    simp [start, indexOps, intOneValue]
  have hEndLarge : 1 < endIndex hugeView () := hugeEndLarge
  have hend : (indexOps (E := JlError)).value start ≤ endIndex hugeView () := by
    rw [hstartValue]
    omega
  have hnotEnd : (indexOps (E := JlError)).value start ≠ endIndex hugeView () := by
    rw [hstartValue]
    omega
  have hvalid : validAt hugeView () start := by
    exact ⟨(), by simp [hugeView, start]⟩
  have hvalidSpec : validAt hugeView ()
      (int ((indexOps (E := JlError)).value start)) := by
    rw [hstartValue]
    simpa [start] using hvalid
  have hcontract := hspec Unit Unit Unit Unit Unit Index JlError hugeOps
    (fun _ => "") hugeView (indexOps (E := JlError)) hugeTest alwaysTrue
    hugeTextLaws indexIntegerLaws hugeTestLaw () start (by omega) hend (Or.inl hvalidSpec)
  have hreturns : Returns
      (findprevPredicate
        (fromBasic (JuliaLean.base.strings.basic.modelStringOps hugeOps (fun _ => "")))
        (indexOps (E := JlError)) hugeTest () start)
      (LastIndex (charMatches hugeView (fun c => alwaysTrue c = true) ())
        ((indexOps (E := JlError)).value start)) := by
    simpa [hnotEnd] using hcontract
  have hactual :
      (findprevPredicate
        (fromBasic (JuliaLean.base.strings.basic.modelStringOps hugeOps (fun _ => "")))
        (indexOps (E := JlError)) hugeTest () start).run = some (.error JlError.boundsError) := by
    have hmin : IntTy.min .i64 < 1 := by decide
    unfold findprevPredicate
    simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure,
      fromBasic, JuliaLean.base.strings.basic.modelStringOps, hugeOps,
      indexOps, start, intOneValue, maxPlusOneWraps, IntTy.min, IntTy.signed, IntTy.bits, hmin]
  rcases hreturns with ⟨result, hrun, hlast⟩
  rw [hactual] at hrun
  have hresult : result = .error JlError.boundsError := by
    injection hrun with hEq
    exact hEq.symm
  subst result
  unfold LastIndex at hlast
  have hstartVal : start.val = 1 := by simp [start, intOneValue]
  have hmatch :
      charMatches hugeView (fun c : Unit => alwaysTrue c = true) () start.val := by
    unfold charMatches
    refine ⟨start, (), ?_, rfl, rfl⟩
    simp [hugeView, start]
  have hright :
      start.val ≤ (indexOps (E := JlError)).value start ∧
        charMatches hugeView (fun c : Unit => alwaysTrue c = true) () start.val ∧
        ∀ j, j ≤ (indexOps (E := JlError)).value start →
          charMatches hugeView (fun c : Unit => alwaysTrue c = true) () j →
          j ≤ start.val := by
    constructor
    · rw [hstartVal, hstartValue]
      omega
    · constructor
      · exact hmatch
      · intro j hj _
        exact hj
  have hsome := (hlast.1 start).2 hright
  cases hsome

private theorem findnextZero_interiorUInt8 (A I E : Type)
    (ops : DenseOps A UInt8 E) (v : ByteView A UInt8) (ix : IntegerOps I E)
    (hmem : CMemoryLaws ops v)
    (hvalue : ∀ b, ops.value b = Int.ofNat b.toNat) (hzero : ops.zero = 0)
    (a : A) (start : I) (i : Index) (hconvert : ix.toInt start = .ok i)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    FirstIndex (byteMatches v (fun b => b == 0) a) i.val
      (findnextZero ops ix (memchrUInt8 ops) a start) := by
  have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
  have hlast : (ops.lastindex a).val =
      v.first a + Int.ofNat (v.elements a).length - 1 := hmem.bytes.lastindex a
  have hle : i.val ≤ (ops.lastindex a).val := by
    rw [hlast]
    omega
  have hsearch :=
    (memchrFirstSpec_proven.1 A E ops v hmem hvalue a ops.zero i hstart hstop)
  rw [hzero] at hsearch
  have hnotBelow : ¬ i.val < (ops.firstindex a).val := by
    rw [hfirst]
    omega
  have hnotAbove : ¬ (ops.lastindex a).val < i.val := by omega
  have hrun : findnextZero ops ix (memchrUInt8 ops) a start =
      memchrUInt8 ops a 0 i := by
    simp [findnextZero, hconvert, hnotBelow, hnotAbove, hzero]
  rw [hrun]
  exact hsearch

private theorem findprevZero_interiorUInt8 (A I E : Type)
    (ops : DenseOps A UInt8 E) (v : ByteView A UInt8) (ix : IntegerOps I E)
    (hmem : CMemoryLaws ops v)
    (hvalue : ∀ b, ops.value b = Int.ofNat b.toNat) (hzero : ops.zero = 0)
    (a : A) (start : I) (i : Index) (hconvert : ix.toInt start = .ok i)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    LastIndex (byteMatches v (fun b => b == 0) a) i.val
      (findprevZero ops ix (memrchrUInt8 ops) a start) := by
  have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
  have hlast : (ops.lastindex a).val =
      v.first a + Int.ofNat (v.elements a).length - 1 := hmem.bytes.lastindex a
  have hle : i.val ≤ (ops.lastindex a).val := by
    rw [hlast]
    omega
  have hsearch :=
    (memrchrLastSpec_proven.1 A E ops v hmem hvalue a ops.zero i hstart hstop)
  rw [hzero] at hsearch
  have hnotAbove : ¬ (ops.lastindex a).val < i.val := by omega
  have hnotBelow : ¬ i.val < (ops.firstindex a).val := by
    rw [hfirst]
    omega
  have hrun : findprevZero ops ix (memrchrUInt8 ops) a start =
      memrchrUInt8 ops a 0 i := by
    simp [findprevZero, hconvert, hnotAbove, hnotBelow, hzero]
  rw [hrun]
  exact hsearch

private theorem findnextZero_interiorInt8 (A I E : Type)
    (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8))
    (ix : IntegerOps I E) (hmem : CMemoryLaws ops v)
    (hvalue : ∀ b, ops.value b = b.val) (hzero : ops.zero.val = 0)
    (a : A) (start : I) (i : Index) (hconvert : ix.toInt start = .ok i)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    FirstIndex (byteMatches v (fun b => b.val == 0) a) i.val
      (findnextZero ops ix (memchrInt8 ops) a start) := by
  have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
  have hlast : (ops.lastindex a).val =
      v.first a + Int.ofNat (v.elements a).length - 1 := hmem.bytes.lastindex a
  have hle : i.val ≤ (ops.lastindex a).val := by
    rw [hlast]
    omega
  have hsearch :=
    (memchrFirstSpec_proven.2 A E ops v hmem hvalue a ops.zero i hstart hstop)
  rw [hzero] at hsearch
  have hnotBelow : ¬ i.val < (ops.firstindex a).val := by
    rw [hfirst]
    omega
  have hnotAbove : ¬ (ops.lastindex a).val < i.val := by omega
  have hrun : findnextZero ops ix (memchrInt8 ops) a start =
      memchrInt8 ops a ops.zero i := by
    simp [findnextZero, hconvert, hnotBelow, hnotAbove]
  rw [hrun]
  exact hsearch

private theorem findprevZero_interiorInt8 (A I E : Type)
    (ops : DenseOps A (JInt .i8) E) (v : ByteView A (JInt .i8))
    (ix : IntegerOps I E) (hmem : CMemoryLaws ops v)
    (hvalue : ∀ b, ops.value b = b.val) (hzero : ops.zero.val = 0)
    (a : A) (start : I) (i : Index) (hconvert : ix.toInt start = .ok i)
    (hstart : v.first a ≤ i.val)
    (hstop : i.val < v.first a + Int.ofNat (v.elements a).length) :
    LastIndex (byteMatches v (fun b => b.val == 0) a) i.val
      (findprevZero ops ix (memrchrInt8 ops) a start) := by
  have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
  have hlast : (ops.lastindex a).val =
      v.first a + Int.ofNat (v.elements a).length - 1 := hmem.bytes.lastindex a
  have hle : i.val ≤ (ops.lastindex a).val := by
    rw [hlast]
    omega
  have hsearch :=
    (memrchrLastSpec_proven.2 A E ops v hmem hvalue a ops.zero i hstart hstop)
  rw [hzero] at hsearch
  have hnotAbove : ¬ (ops.lastindex a).val < i.val := by omega
  have hnotBelow : ¬ i.val < (ops.firstindex a).val := by
    rw [hfirst]
    omega
  have hrun : findprevZero ops ix (memrchrInt8 ops) a start =
      memrchrInt8 ops a ops.zero i := by
    simp [findprevZero, hconvert, hnotAbove, hnotBelow]
  rw [hrun]
  exact hsearch

private theorem listGetNoneZeroByte (B : Type) (xs : List B) (n : Nat)
    (h : xs.length ≤ n) : xs[n]? = none := by
  cases hget : xs[n]? with
  | none => rfl
  | some b =>
      have hlt : n < xs.length := (List.getElem?_eq_some_iff.mp hget).1
      omega

private theorem byteAtNoneAfterZeroByte (A B : Type) (v : ByteView A B)
    (a : A) (i : Int)
    (h : v.first a + Int.ofNat (v.elements a).length ≤ i) :
    byteAt v a i = none := by
  unfold byteAt
  have hlen : 0 ≤ Int.ofNat (v.elements a).length := by simp
  have hnonneg : 0 ≤ i - v.first a := by omega
  have hoffset : Int.ofNat (v.elements a).length ≤ i - v.first a := by omega
  have hcast : Int.ofNat ((i - v.first a).toNat) = i - v.first a :=
    Int.toNat_of_nonneg hnonneg
  have hindex : (v.elements a).length ≤ (i - v.first a).toNat := by
    apply Int.ofNat_le.mp
    calc
      Int.ofNat (v.elements a).length ≤ i - v.first a := hoffset
      _ = Int.ofNat ((i - v.first a).toNat) := hcast.symm
  exact listGetNoneZeroByte B (v.elements a) (i - v.first a).toNat hindex

private theorem firstIndexNoneAfterZeroByte (A B E : Type) (v : ByteView A B)
    (equal : B → Bool) (a : A) (i : Int)
    (h : v.first a + Int.ofNat (v.elements a).length ≤ i) :
    FirstIndex (byteMatches v equal a) i (.ok none : Except E (Option Index)) := by
  unfold FirstIndex
  constructor
  · intro k
    constructor
    · intro hSome
      cases hSome
    · intro hMatch
      rcases hMatch with ⟨hstart, hAccept, _⟩
      rcases hAccept with ⟨_, b, hget, _⟩
      have hnone := byteAtNoneAfterZeroByte A B v a k.val (by omega)
      rw [hnone] at hget
      cases hget
  · constructor
    · intro _ j hj hAccept
      rcases hAccept with ⟨_, b, hget, _⟩
      have hnone := byteAtNoneAfterZeroByte A B v a j (by omega)
      rw [hnone] at hget
      cases hget
    · intro _
      rfl

private theorem lastIndexNoneBeforeFirstZeroByte (A B E : Type)
    (v : ByteView A B) (equal : B → Bool) (a : A) (i : Int)
    (h : i < v.first a) :
    LastIndex (byteMatches v equal a) i (.ok none : Except E (Option Index)) := by
  unfold LastIndex
  constructor
  · intro j
    constructor
    · intro hSome
      cases hSome
    · intro hMatch
      rcases hMatch with ⟨hle, hAccept, _⟩
      rcases hAccept with ⟨hfirst, _⟩
      omega
  · constructor
    · intro _ j hle hAccept
      rcases hAccept with ⟨hfirst, _⟩
      omega
    · intro _
      rfl

private theorem findnextZeroConversionError {A B I E : Type} (ops : DenseOps A B E)
    (ix : IntegerOps I E) (memchr : A → B → Index → Except E (Option Index))
    (a : A) (start : I) (e : E) (hconv : ix.toInt start = .error e) :
    findnextZero ops ix memchr a start = .error e := by
  unfold findnextZero
  rw [hconv]
  rfl

private theorem findprevZeroConversionError {A B I E : Type} (ops : DenseOps A B E)
    (ix : IntegerOps I E) (memrchr : A → B → Index → Except E (Option Index))
    (a : A) (start : I) (e : E) (hconv : ix.toInt start = .error e) :
    findprevZero ops ix memrchr a start = .error e := by
  unfold findprevZero
  rw [hconv]
  rfl

private theorem findnextZeroBelowFirst {A B I E : Type} (ops : DenseOps A B E)
    (ix : IntegerOps I E) (memchr : A → B → Index → Except E (Option Index))
    (a : A) (start : I) (i : Index) (first : Int)
    (hconv : ix.toInt start = .ok i)
    (hfirst : (ops.firstindex a).val = first) (hbelow : i.val < first) :
    findnextZero ops ix memchr a start = .error (ops.boundsError a i.val) := by
  unfold findnextZero
  rw [hconv, hfirst]
  simp [Bind.bind, Except.bind, hbelow]
  have hthrow : (throw (ops.boundsError a i.val) : Except E Unit) =
      .error (ops.boundsError a i.val) := rfl
  rw [hthrow]

private theorem findnextZeroAfterLast {A B I E : Type} (ops : DenseOps A B E)
    (ix : IntegerOps I E) (memchr : A → B → Index → Except E (Option Index))
    (a : A) (start : I) (i : Index) (first last : Int)
    (hconv : ix.toInt start = .ok i)
    (hfirst : (ops.firstindex a).val = first)
    (hlast : (ops.lastindex a).val = last)
    (hnotBelow : ¬ i.val < first) (hlastlt : last < i.val) :
    findnextZero ops ix memchr a start = .ok none := by
  unfold findnextZero
  rw [hconv, hfirst, hlast]
  simp [Bind.bind, Except.bind, Except.pure, hnotBelow, hlastlt]
  rfl

private theorem findprevZeroAboveLast {A B I E : Type} (ops : DenseOps A B E)
    (ix : IntegerOps I E) (memrchr : A → B → Index → Except E (Option Index))
    (a : A) (start : I) (i : Index)
    (hconv : ix.toInt start = .ok i)
    (hlastlt : (ops.lastindex a).val < i.val) :
    findprevZero ops ix memrchr a start = .error (ops.boundsError a i.val) := by
  unfold findprevZero
  rw [hconv]
  have hhigh : i.val > (ops.lastindex a).val := by omega
  simp [Bind.bind, Except.bind, hhigh]
  have hthrow : (throw (ops.boundsError a i.val) : Except E Unit) =
      .error (ops.boundsError a i.val) := rfl
  rw [hthrow]

private theorem findprevZeroBeforeFirst {A B I E : Type} (ops : DenseOps A B E)
    (ix : IntegerOps I E) (memrchr : A → B → Index → Except E (Option Index))
    (a : A) (start : I) (i : Index) (first : Int)
    (hconv : ix.toInt start = .ok i)
    (hfirst : (ops.firstindex a).val = first)
    (hnotAbove : ¬ (ops.lastindex a).val < i.val) (hbelow : i.val < first) :
    findprevZero ops ix memrchr a start = .ok none := by
  unfold findprevZero
  rw [hconv, hfirst]
  simp [Bind.bind, Except.bind, Except.pure, hnotAbove, hbelow]
  rfl

theorem zeroByteSpec_proven : ZeroByteSpec := by
  constructor
  · intro A I E ops v ix hmem _hix hvalue hzero a start
    cases hconvert : ix.toInt start with
    | error e =>
        constructor
        · exact findnextZeroConversionError ops ix (memchrUInt8 ops) a start e hconvert
        · exact findprevZeroConversionError ops ix (memrchrUInt8 ops) a start e hconvert
    | ok i =>
        have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
        have hlast : (ops.lastindex a).val =
            v.first a + Int.ofNat (v.elements a).length - 1 :=
          hmem.bytes.lastindex a
        constructor
        · by_cases hbelow : i.val < v.first a
          · rw [if_pos hbelow]
            exact findnextZeroBelowFirst ops ix (memchrUInt8 ops) a start i
              (v.first a) hconvert hfirst hbelow
          · rw [if_neg hbelow]
            by_cases hafter : v.first a + Int.ofNat (v.elements a).length ≤ i.val
            · have hlastlt : (ops.lastindex a).val < i.val := by
                rw [hlast]
                omega
              have hnone := findnextZeroAfterLast ops ix (memchrUInt8 ops)
                a start i (v.first a) (ops.lastindex a).val
                hconvert hfirst rfl (by omega) hlastlt
              rw [hnone]
              exact firstIndexNoneAfterZeroByte A UInt8 E v (fun b => b == 0) a i.val hafter
            · have hstart : v.first a ≤ i.val := by omega
              have hstop : i.val < v.first a + Int.ofNat (v.elements a).length := by omega
              exact findnextZero_interiorUInt8 A I E ops v ix hmem hvalue hzero
                a start i hconvert hstart hstop
        · by_cases hafter : v.first a + Int.ofNat (v.elements a).length ≤ i.val
          · rw [if_pos hafter]
            have hlastlt : (ops.lastindex a).val < i.val := by
              rw [hlast]
              omega
            exact findprevZeroAboveLast ops ix (memrchrUInt8 ops) a start i hconvert hlastlt
          · rw [if_neg hafter]
            by_cases hbelow : i.val < v.first a
            · have hlen : 0 ≤ Int.ofNat (v.elements a).length := by simp
              have hnotAbove : ¬ (ops.lastindex a).val < i.val := by
                rw [hlast]
                omega
              have hnone := findprevZeroBeforeFirst ops ix (memrchrUInt8 ops) a start i
                (v.first a) hconvert hfirst hnotAbove hbelow
              rw [hnone]
              exact lastIndexNoneBeforeFirstZeroByte A UInt8 E v (fun b => b == 0) a i.val hbelow
            · have hstart : v.first a ≤ i.val := by omega
              have hstop : i.val < v.first a + Int.ofNat (v.elements a).length := by omega
              exact findprevZero_interiorUInt8 A I E ops v ix hmem hvalue hzero
                a start i hconvert hstart hstop
  · intro A I E ops v ix hmem _hix hvalue hzero a start
    cases hconvert : ix.toInt start with
    | error e =>
        constructor
        · exact findnextZeroConversionError ops ix (memchrInt8 ops) a start e hconvert
        · exact findprevZeroConversionError ops ix (memrchrInt8 ops) a start e hconvert
    | ok i =>
        have hfirst : (ops.firstindex a).val = v.first a := hmem.bytes.firstindex a
        have hlast : (ops.lastindex a).val =
            v.first a + Int.ofNat (v.elements a).length - 1 :=
          hmem.bytes.lastindex a
        constructor
        · by_cases hbelow : i.val < v.first a
          · rw [if_pos hbelow]
            exact findnextZeroBelowFirst ops ix (memchrInt8 ops) a start i
              (v.first a) hconvert hfirst hbelow
          · rw [if_neg hbelow]
            by_cases hafter : v.first a + Int.ofNat (v.elements a).length ≤ i.val
            · have hlastlt : (ops.lastindex a).val < i.val := by
                rw [hlast]
                omega
              have hnone := findnextZeroAfterLast ops ix (memchrInt8 ops)
                a start i (v.first a) (ops.lastindex a).val
                hconvert hfirst rfl (by omega) hlastlt
              rw [hnone]
              exact firstIndexNoneAfterZeroByte A (JInt .i8) E v
                (fun b => b.val == 0) a i.val hafter
            · have hstart : v.first a ≤ i.val := by omega
              have hstop : i.val < v.first a + Int.ofNat (v.elements a).length := by omega
              exact findnextZero_interiorInt8 A I E ops v ix hmem hvalue hzero
                a start i hconvert hstart hstop
        · by_cases hafter : v.first a + Int.ofNat (v.elements a).length ≤ i.val
          · rw [if_pos hafter]
            have hlastlt : (ops.lastindex a).val < i.val := by
              rw [hlast]
              omega
            exact findprevZeroAboveLast ops ix (memrchrInt8 ops) a start i hconvert hlastlt
          · rw [if_neg hafter]
            by_cases hbelow : i.val < v.first a
            · have hlen : 0 ≤ Int.ofNat (v.elements a).length := by simp
              have hnotAbove : ¬ (ops.lastindex a).val < i.val := by
                rw [hlast]
                omega
              have hnone := findprevZeroBeforeFirst ops ix (memrchrInt8 ops) a start i
                (v.first a) hconvert hfirst hnotAbove hbelow
              rw [hnone]
              exact lastIndexNoneBeforeFirstZeroByte A (JInt .i8) E v
                (fun b => b.val == 0) a i.val hbelow
            · have hstart : v.first a ≤ i.val := by omega
              have hstop : i.val < v.first a + Int.ofNat (v.elements a).length := by omega
              exact findprevZero_interiorInt8 A I E ops v ix hmem hvalue hzero
                a start i hconvert hstart hstop
private def predicateErrorTest : Unit → SearchM JlError Bool :=
  fun _ => liftE (.error (.methodError "predicate"))

theorem predicateErrorSpec_refuted : ¬ Round3.PredicateErrorSpec := by
  intro hspec
  let start := int 1
  let exception := JlError.methodError "predicate"
  have hstartVal : start.val = 1 := by simp [start, intOneValue]
  have hmember : (start, ()) ∈ hugeView.characters () := by
    simp [hugeView, start]
  have hvalid : validAt hugeView () start := ⟨(), hmember⟩
  have htest : (predicateErrorTest ()).run = some (.error exception) := by rfl
  have hprefix :
      start.val ≤ start.val ∧
        ∀ j d, (j, d) ∈ hugeView.characters () →
          start.val ≤ j.val → j.val < start.val →
          (predicateErrorTest d).run = some (.ok false) := by
    constructor
    · omega
    · intro j d _ hj hlt
      omega
  have hcontract := hspec Unit Unit Unit Unit Unit JlError hugeOps
    (fun _ => "") hugeView predicateErrorTest hugeTextLaws () start start () exception
    hvalid hmember htest
  have hclaimed := hcontract.1 hprefix
  have hactual :
      (findnextPredicate
        (fromBasic (JuliaLean.base.strings.basic.modelStringOps hugeOps (fun _ => "")))
        (indexOps (E := JlError)) predicateErrorTest () start).run =
        some (.error JlError.boundsError) := by
    have hmin : IntTy.min .i64 < 1 := by decide
    unfold findnextPredicate
    simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure,
      fromBasic, JuliaLean.base.strings.basic.modelStringOps, hugeOps,
      indexOps, start, intOneValue, maxPlusOneWraps, IntTy.min, IntTy.signed, IntTy.bits, hmin]
  have hsame :
      (some (.error JlError.boundsError) : Option (Except JlError (Option Index))) =
        some (.error exception) :=
    hactual.symm.trans hclaimed
  have herr : JlError.boundsError = exception := by
    injection hsame with herror
    injection herror with herr
  have hneq : JlError.boundsError ≠ exception := by decide
  exact hneq herr

private theorem hugeCharTextLaws : Round5.PrimitiveTextLaws hugeOps hugeView := by
  exact {
    sizeFits := hugeTextLaws.sizeFits
    ncodeunits := hugeTextLaws.ncodeunits
    iterationBound := hugeTextLaws.iterationBound
    sorted := hugeTextLaws.sorted
    indices := hugeTextLaws.indices
    nonempty := hugeTextLaws.nonempty
    first := hugeTextLaws.first
    isvalid := hugeTextLaws.isvalid
    iterate := hugeTextLaws.iterate
  }

theorem charWrapperSpec_refuted : ¬ Round5.CharWrapperSpec := by
  intro hspec
  let start := int 1
  let target : Unit := ()
  let equality : Round5.CharEqualityDispatch Unit Unit JlError :=
    .extensionMethod (fun _ _ => .ok true)
  have hvalid : validAt hugeView () start := by
    exact ⟨(), by simp [hugeView, start]⟩
  have hcontract := hspec Unit Unit Unit Unit Unit Unit JlError hugeOps
    (fun _ => "") hugeView equality hugeCharTextLaws () target start
  have hclaimed := hcontract.1 (Or.inl hvalid)
  have hactual :
      (findnextCharWrapper (Round5.charEquality equality)
        (findnextPredicate
          (fromBasic (JuliaLean.base.strings.basic.modelStringOps hugeOps (fun _ => "")))
          (indexOps (E := JlError)))
        target () start).run = some (.error JlError.boundsError) := by
    have hmin : IntTy.min .i64 < 1 := by decide
    unfold findnextCharWrapper findnextPredicate
    simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure,
      Round5.charEquality, equality, fromBasic,
      JuliaLean.base.strings.basic.modelStringOps, hugeOps, indexOps,
      start, intOneValue, maxPlusOneWraps, IntTy.min, IntTy.signed, IntTy.bits, hmin]
  have hnotOutcome :
      ¬ Round5.FirstTestOutcome
        ((hugeView.characters ()).filter (fun p => start.val ≤ p.1.val))
        (fun c => Round5.charEquality equality c target)
        (.error JlError.boundsError) := by
    intro houtcome
    have hfirstError := (houtcome.2.2 JlError.boundsError).mp rfl
    rcases hfirstError with ⟨before, i, c, after, hchars, hfalse, herror⟩
    simp [Round5.charEquality, equality, target] at herror
  rcases hclaimed with ⟨result, hrun, houtcome⟩
  rw [hactual] at hrun
  have hresult : result = .error JlError.boundsError := by
    injection hrun with hresult
    exact hresult.symm
  subst result
  exact hnotOutcome houtcome

private theorem nextConversionError {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I) (e : E)
    (h : ix.toInt start = .error e) :
    (findnextPredicate ops ix testf s start).run = some (.error e) := by
  unfold findnextPredicate
  simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure, h]

private theorem prevConversionError {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I) (e : E)
    (h : ix.toInt start = .error e) :
    (findprevPredicate ops ix testf s start).run = some (.error e) := by
  unfold findprevPredicate
  simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure, h]

private theorem nextDomainError {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I)
    (i : Index) (hconv : ix.toInt start = .ok i)
    (h : i.val < 1 ∨ (ops.ncodeunits s + int 1).val < i.val) :
    ∃ e, (findnextPredicate ops ix testf s start).run = some (.error e) := by
  refine ⟨ops.boundsError s i.val, ?_⟩
  unfold findnextPredicate
  simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure, hconv, h]

private theorem prevDomainError {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I)
    (i : Index) (hconv : ix.toInt start = .ok i)
    (h : i.val < 0 ∨ (ops.ncodeunits s + int 1).val < i.val) :
    ∃ e, (findprevPredicate ops ix testf s start).run = some (.error e) := by
  refine ⟨ops.boundsError s i.val, ?_⟩
  unfold findprevPredicate
  simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure, hconv, h]

private theorem nextInteriorError {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I)
    (i : Index) (hconv : ix.toInt start = .ok i)
    (hvalid : ops.isvalid s i = .ok false)
    (hfirst : 1 ≤ i.val) (hbefore : i.val < (ops.ncodeunits s + int 1).val) :
    ∃ e, (findnextPredicate ops ix testf s start).run = some (.error e) := by
  let z := ops.ncodeunits s + int 1
  have hneval : i.val ≠ z.val := by
    change i.val ≠ (ops.ncodeunits s + int 1).val
    omega
  have hgood : ¬ (i.val < 1 ∨ (ops.ncodeunits s + int 1).val < i.val) := by omega
  have hne : i ≠ ops.ncodeunits s + int 1 := by
    intro he
    exact hneval (congrArg Subtype.val he)
  refine ⟨ops.stringIndexError s i, ?_⟩
  unfold findnextPredicate
  simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure,
    hconv, hvalid, hne, hgood, bne_iff_ne]

private theorem prevInteriorError {S C I E : Type} (ops : SearchStringOps S C E)
    (ix : IntegerOps I E) (testf : C → SearchM E Bool) (s : S) (start : I)
    (i : Index) (hconv : ix.toInt start = .ok i)
    (hvalid : ops.isvalid s i = .ok false)
    (hfirst : 1 ≤ i.val) (hbefore : i.val < (ops.ncodeunits s + int 1).val) :
    ∃ e, (findprevPredicate ops ix testf s start).run = some (.error e) := by
  have hneq : i.val ≠ (ops.ncodeunits s + int 1).val := by omega
  have hgood : ¬ (i.val < 0 ∨ (ops.ncodeunits s + int 1).val < i.val) := by omega
  have hnezero : i.val ≠ 0 := by omega
  refine ⟨ops.stringIndexError s i, ?_⟩
  unfold findprevPredicate
  simp [liftE, ExceptT.run_bind, ExceptT.run_throw, ExceptT.run_pure,
    hconv, hvalid, hneq, hgood, hnezero]

theorem predicateStartErrorsAnyErrorSpec_proven :
    Round7.PredicateStartErrorsAnyErrorSpec := by
  intro S R C CU CT I E primitive intString v ix testf htext hix s start
  let ops := fromBasic
    (JuliaLean.base.strings.basic.modelStringOps primitive intString)
  constructor
  · intro e herror
    constructor
    · exact ⟨e, nextConversionError ops ix testf s start e herror⟩
    · exact ⟨e, prevConversionError ops ix testf s start e herror⟩
  · intro i hconv
    let n := Int.ofNat (v.bytes s).length
    have hncode : (ops.ncodeunits s).val = n := by
      simpa [ops, fromBasic, JuliaLean.base.strings.basic.modelStringOps, n] using
        htext.ncodeunits s
    have hnle : n ≤ IntTy.max .i64 := by
      simpa [n] using htext.sizeFits s
    by_cases hmax : n = IntTy.max .i64
    · have hmaxRange : IntTy.min .i64 ≤ IntTy.max .i64 := by
        have hpow : 0 < (2 ^ 63 : Int) := by exact_mod_cast Nat.two_pow_pos 63
        change -(2 ^ 63 : Int) ≤ (2 ^ 63 : Int) - 1
        omega
      have hmaxLit : (int (IntTy.max .i64)).val = IntTy.max .i64 :=
        intValue _ ⟨hmaxRange, by omega⟩
      have hni : ops.ncodeunits s = int (IntTy.max .i64) := by
        apply Subtype.ext
        rw [hncode, hmax, hmaxLit]
      have hzmax : (ops.ncodeunits s + int 1).val = IntTy.min .i64 := by
        rw [hni]
        exact maxPlusOneWraps
      have hend : endIndex v s = IntTy.max .i64 + 1 := by
        unfold endIndex
        dsimp [n] at hmax ⊢
        omega
      have hminOne : IntTy.min .i64 < 1 := by
        have hpow : 0 < (2 ^ 63 : Int) := by exact_mod_cast Nat.two_pow_pos 63
        change -(2 ^ 63 : Int) < 1
        omega
      constructor
      · intro hnext
        rcases hnext with hlo | hhi
        · exact nextDomainError ops ix testf s start i hconv (Or.inl hlo)
        · have : False := by rw [hend] at hhi; have hi := i.property.2; omega
          exact False.elim this
      constructor
      · intro hprev
        rcases hprev with hlo | hhi
        · exact prevDomainError ops ix testf s start i hconv (Or.inl hlo)
        · have : False := by rw [hend] at hhi; have hi := i.property.2; omega
          exact False.elim this
      · intro hinvalid
        rcases hinvalid with ⟨hfirst, _, _⟩
        have hzlt : (ops.ncodeunits s + int 1).val < i.val := by
          rw [hzmax]
          omega
        exact ⟨nextDomainError ops ix testf s start i hconv (Or.inr hzlt),
          prevDomainError ops ix testf s start i hconv (Or.inr hzlt)⟩
    · have hnlt : n < IntTy.max .i64 := by omega
      have hminZero : IntTy.min .i64 ≤ 0 := by
        have hpow : 0 < (2 ^ 63 : Int) := by exact_mod_cast Nat.two_pow_pos 63
        change -(2 ^ 63 : Int) ≤ 0
        omega
      have hnnonneg : 0 ≤ n := by simp [n]
      have hzval : (ops.ncodeunits s + int 1).val = n + 1 := by
        change wrapInt .i64 ((ops.ncodeunits s).val + (int 1).val) = n + 1
        rw [hncode, intOneValue]
        apply wrapInt_of_inRange
        constructor
        · calc
            IntTy.min .i64 ≤ 0 := hminZero
            _ ≤ n + 1 := by omega
        · omega
      have hz : (ops.ncodeunits s + int 1).val = endIndex v s := by
        rw [hzval]
        rfl
      constructor
      · intro hnext
        rcases hnext with hlo | hhi
        · exact nextDomainError ops ix testf s start i hconv (Or.inl hlo)
        · have hzlt : (ops.ncodeunits s + int 1).val < i.val := by
            rw [hz]
            exact hhi
          exact nextDomainError ops ix testf s start i hconv (Or.inr hzlt)
      constructor
      · intro hprev
        rcases hprev with hlo | hhi
        · exact prevDomainError ops ix testf s start i hconv (Or.inl hlo)
        · have hzlt : (ops.ncodeunits s + int 1).val < i.val := by
            rw [hz]
            exact hhi
          exact prevDomainError ops ix testf s start i hconv (Or.inr hzlt)
      · intro hinvalid
        rcases hinvalid with ⟨hfirst, hbefore, hnotvalid⟩
        have hmodel : (v.characters s).any (fun p => p.1.val == i.val) = false := by
          cases hany : (v.characters s).any (fun p => p.1.val == i.val) with
          | false => rfl
          | true =>
            obtain ⟨p, hp, hbeq⟩ := List.any_eq_true.mp hany
            cases p with
            | mk j c =>
              have hji : j.val = i.val := by simpa only [beq_iff_eq] using hbeq
              have hj : j = i := Subtype.ext hji
              subst j
              exact False.elim (hnotvalid ⟨c, hp⟩)
        have hvalid : ops.isvalid s i = .ok false := by
          simpa [ops, fromBasic, JuliaLean.base.strings.basic.modelStringOps, hmodel] using
            htext.isvalid s i
        have hbeforez : i.val < (ops.ncodeunits s + int 1).val := by
          rw [hz]
          exact hbefore
        exact ⟨nextInteriorError ops ix testf s start i hconv hvalid hfirst hbeforez,
          prevInteriorError ops ix testf s start i hconv hvalid hfirst hbeforez⟩

end JuliaLean.Proofs.base.strings.search

namespace JuliaLean.ChatGPT.Batch6.Group2
open JuliaLean.Proofs.base.strings.search

theorem listGetNone_local {B : Type} (xs : List B) (n : Nat)
    (h : xs.length ≤ n) : xs[n]? = none := by
  cases hget : xs[n]? with
  | none => rfl
  | some b =>
      have hlt : n < xs.length := (List.getElem?_eq_some_iff.mp hget).1
      omega

theorem byteAtNoneAfter_local {A B : Type}
    (v : JuliaLean.Proofs.base.strings.search.ByteView A B) (a : A) (i : Int)
    (h : v.first a + Int.ofNat (v.elements a).length ≤ i) :
    JuliaLean.Proofs.base.strings.search.byteAt v a i = none := by
  unfold JuliaLean.Proofs.base.strings.search.byteAt
  have hlen : 0 ≤ Int.ofNat (v.elements a).length := by simp
  have hnonneg : 0 ≤ i - v.first a := by omega
  have hoffset : Int.ofNat (v.elements a).length ≤ i - v.first a := by omega
  have hcast : Int.ofNat ((i - v.first a).toNat) = i - v.first a :=
    Int.toNat_of_nonneg hnonneg
  apply listGetNone_local
  apply Int.ofNat_le.mp
  calc
    Int.ofNat (v.elements a).length ≤ i - v.first a := hoffset
    _ = Int.ofNat ((i - v.first a).toNat) := hcast.symm

theorem firstIndexNoneAfter_local {A B E : Type}
    (v : JuliaLean.Proofs.base.strings.search.ByteView A B)
    (equal : B → Bool) (a : A) (i : Int)
    (h : v.first a + Int.ofNat (v.elements a).length ≤ i) :
    JuliaLean.Proofs.base.strings.search.FirstIndex
      (JuliaLean.Proofs.base.strings.search.byteMatches v equal a) i
      (.ok none : Except E (Option JuliaLean.base.strings.search.Index)) := by
  unfold JuliaLean.Proofs.base.strings.search.FirstIndex
  constructor
  · intro k
    constructor
    · intro hSome
      cases hSome
    · rintro ⟨hstart, ⟨_, b, hget, _⟩, _⟩
      rw [byteAtNoneAfter_local v a k.val (by omega)] at hget
      cases hget
  · constructor
    · intro _ j hj
      rintro ⟨_, b, hget, _⟩
      rw [byteAtNoneAfter_local v a j (by omega)] at hget
      cases hget
    · intro _
      rfl

theorem lastIndexNoneBefore_local {A B E : Type}
    (v : JuliaLean.Proofs.base.strings.search.ByteView A B)
    (equal : B → Bool) (a : A) (i : Int) (h : i < v.first a) :
    JuliaLean.Proofs.base.strings.search.LastIndex
      (JuliaLean.Proofs.base.strings.search.byteMatches v equal a) i
      (.ok none : Except E (Option JuliaLean.base.strings.search.Index)) := by
  unfold JuliaLean.Proofs.base.strings.search.LastIndex
  constructor
  · intro j
    constructor
    · intro hSome
      cases hSome
    · rintro ⟨_, ⟨hfirst, _⟩, _⟩
      omega
  · constructor
    · intro _ j hj
      rintro ⟨hfirst, _⟩
      omega
    · intro _
      rfl

theorem denseByteForwardUInt8_local :
    ∀ (A I E : Type) (ops : JuliaLean.base.strings.search.DenseOps A UInt8 E)
      (v : JuliaLean.Proofs.base.strings.search.ByteView A UInt8)
      (ix : JuliaLean.base.strings.search.IntegerOps I E),
      JuliaLean.Proofs.base.strings.search.CMemoryLaws ops v →
      JuliaLean.Proofs.base.strings.search.IntegerLaws ix →
      (∀ b, ops.value b = Int.ofNat b.toNat) →
      ∀ a b start, match ix.toInt start with
        | .error e => JuliaLean.base.strings.search.findnextUInt8 ops ix b a start = .error e
        | .ok i => if i.val < v.first a then
            JuliaLean.base.strings.search.findnextUInt8 ops ix b a start =
              .error (ops.boundsError a i.val)
          else JuliaLean.Proofs.base.strings.search.FirstIndex
            (JuliaLean.Proofs.base.strings.search.byteMatches v (fun x => x == b) a)
            i.val (JuliaLean.base.strings.search.findnextUInt8 ops ix b a start) := by
  intro A I E ops v ix hmem _ hvalue a b start
  cases hconvert : ix.toInt start with
  | error e =>
      simp only [hconvert]
      simp [JuliaLean.base.strings.search.findnextUInt8, hconvert, Bind.bind, Except.bind]
  | ok i =>
      simp only [hconvert]
      have hfirst := hmem.bytes.firstindex a
      have hlast := hmem.bytes.lastindex a
      by_cases hbelow : i.val < v.first a
      · rw [if_pos hbelow]
        have hfirstLt : i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
        simp [JuliaLean.base.strings.search.findnextUInt8, hconvert, hfirstLt,
          Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · rw [if_neg hbelow]
        by_cases hafter : v.first a + Int.ofNat (v.elements a).length ≤ i.val
        · have hlastBefore : v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by
            omega
          have hrun : JuliaLean.base.strings.search.findnextUInt8 ops ix b a start = .ok none := by
            have hfirstGe : ¬ i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
            have hlastLt : (ops.lastindex a).val < i.val := by simpa [hlast] using hlastBefore
            simp [JuliaLean.base.strings.search.findnextUInt8, hconvert, hfirstGe, hlastLt,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [hrun]
          exact firstIndexNoneAfter_local v (fun x => x == b) a i.val hafter
        · have hnotLastBefore :
              ¬ v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by omega
          have hspec := JuliaLean.Proofs.base.strings.search.memchrFirstSpec_proven.1
            A E ops v hmem hvalue a b i (by omega) (by omega)
          have hfirstGe : ¬ i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
          have hlastGe : ¬ (ops.lastindex a).val < i.val := by simpa [hlast] using hnotLastBefore
          simpa [JuliaLean.base.strings.search.findnextUInt8, hconvert, hfirstGe, hlastGe,
            Bind.bind, Except.bind] using hspec

theorem denseByteForwardInt8_local :
    ∀ (A I E : Type) (ops : JuliaLean.base.strings.search.DenseOps A (JuliaLean.JInt .i8) E)
      (v : JuliaLean.Proofs.base.strings.search.ByteView A (JuliaLean.JInt .i8))
      (ix : JuliaLean.base.strings.search.IntegerOps I E),
      JuliaLean.Proofs.base.strings.search.CMemoryLaws ops v →
      JuliaLean.Proofs.base.strings.search.IntegerLaws ix →
      (∀ b, ops.value b = b.val) →
      ∀ a b start, match ix.toInt start with
        | .error e => JuliaLean.base.strings.search.findnextInt8 ops ix b a start = .error e
        | .ok i => if i.val < v.first a then
            JuliaLean.base.strings.search.findnextInt8 ops ix b a start =
              .error (ops.boundsError a i.val)
          else JuliaLean.Proofs.base.strings.search.FirstIndex
            (JuliaLean.Proofs.base.strings.search.byteMatches v (fun x => x.val == b.val) a)
            i.val (JuliaLean.base.strings.search.findnextInt8 ops ix b a start) := by
  intro A I E ops v ix hmem _ hvalue a b start
  cases hconvert : ix.toInt start with
  | error e =>
      simp only [hconvert]
      simp [JuliaLean.base.strings.search.findnextInt8, hconvert, Bind.bind, Except.bind]
  | ok i =>
      simp only [hconvert]
      have hfirst := hmem.bytes.firstindex a
      have hlast := hmem.bytes.lastindex a
      by_cases hbelow : i.val < v.first a
      · rw [if_pos hbelow]
        have hfirstLt : i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
        simp [JuliaLean.base.strings.search.findnextInt8, hconvert, hfirstLt,
          Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · rw [if_neg hbelow]
        by_cases hafter : v.first a + Int.ofNat (v.elements a).length ≤ i.val
        · have hlastBefore : v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by
            omega
          have hrun : JuliaLean.base.strings.search.findnextInt8 ops ix b a start = .ok none := by
            have hfirstGe : ¬ i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
            have hlastLt : (ops.lastindex a).val < i.val := by simpa [hlast] using hlastBefore
            simp [JuliaLean.base.strings.search.findnextInt8, hconvert, hfirstGe, hlastLt,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [hrun]
          exact firstIndexNoneAfter_local v (fun x => x.val == b.val) a i.val hafter
        · have hnotLastBefore :
              ¬ v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by omega
          have hspec := JuliaLean.Proofs.base.strings.search.memchrFirstSpec_proven.2
            A E ops v hmem hvalue a b i (by omega) (by omega)
          have hfirstGe : ¬ i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
          have hlastGe : ¬ (ops.lastindex a).val < i.val := by simpa [hlast] using hnotLastBefore
          simpa [JuliaLean.base.strings.search.findnextInt8, hconvert, hfirstGe, hlastGe,
            Bind.bind, Except.bind] using hspec

theorem denseByteReverseUInt8_local :
    ∀ (A I E : Type) (ops : JuliaLean.base.strings.search.DenseOps A UInt8 E)
      (v : JuliaLean.Proofs.base.strings.search.ByteView A UInt8)
      (ix : JuliaLean.base.strings.search.IntegerOps I E),
      JuliaLean.Proofs.base.strings.search.CMemoryLaws ops v →
      JuliaLean.Proofs.base.strings.search.IntegerLaws ix →
      (∀ b, ops.value b = Int.ofNat b.toNat) →
      ∀ a b start, match ix.toInt start with
        | .error e => JuliaLean.base.strings.search.findprevUInt8 ops ix b a start = .error e
        | .ok i => if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
            JuliaLean.base.strings.search.findprevUInt8 ops ix b a start =
              .error (ops.boundsError a i.val)
          else JuliaLean.Proofs.base.strings.search.LastIndex
            (JuliaLean.Proofs.base.strings.search.byteMatches v (fun x => x == b) a)
            i.val (JuliaLean.base.strings.search.findprevUInt8 ops ix b a start) := by
  intro A I E ops v ix hmem _ hvalue a b start
  cases hconvert : ix.toInt start with
  | error e =>
      simp only [hconvert]
      simp [JuliaLean.base.strings.search.findprevUInt8, hconvert, Bind.bind, Except.bind]
  | ok i =>
      simp only [hconvert]
      have hfirst := hmem.bytes.firstindex a
      have hlast := hmem.bytes.lastindex a
      by_cases habove : v.first a + Int.ofNat (v.elements a).length ≤ i.val
      · rw [if_pos habove]
        have hlastBefore : v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by
          omega
        have hlastLt : (ops.lastindex a).val < i.val := by simpa [hlast] using hlastBefore
        simp [JuliaLean.base.strings.search.findprevUInt8, hconvert, hlastLt,
          Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · rw [if_neg habove]
        by_cases hbelow : i.val < v.first a
        · have hnotLastBefore :
              ¬ v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by omega
          have hrun : JuliaLean.base.strings.search.findprevUInt8 ops ix b a start = .ok none := by
            have hlastGe : ¬ (ops.lastindex a).val < i.val := by simpa [hlast] using hnotLastBefore
            have hfirstLt : i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
            simp [JuliaLean.base.strings.search.findprevUInt8, hconvert, hlastGe, hfirstLt,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [hrun]
          exact lastIndexNoneBefore_local v (fun x => x == b) a i.val hbelow
        · have hnotLastBefore :
              ¬ v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by omega
          have hspec := JuliaLean.Proofs.base.strings.search.memrchrLastSpec_proven.1
            A E ops v hmem hvalue a b i (by omega) (by omega)
          have hlastGe : ¬ (ops.lastindex a).val < i.val := by simpa [hlast] using hnotLastBefore
          have hfirstGe : ¬ i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
          simpa [JuliaLean.base.strings.search.findprevUInt8, hconvert, hlastGe, hfirstGe,
            Bind.bind, Except.bind] using hspec

theorem denseByteReverseInt8_local :
    ∀ (A I E : Type) (ops : JuliaLean.base.strings.search.DenseOps A (JuliaLean.JInt .i8) E)
      (v : JuliaLean.Proofs.base.strings.search.ByteView A (JuliaLean.JInt .i8))
      (ix : JuliaLean.base.strings.search.IntegerOps I E),
      JuliaLean.Proofs.base.strings.search.CMemoryLaws ops v →
      JuliaLean.Proofs.base.strings.search.IntegerLaws ix →
      (∀ b, ops.value b = b.val) →
      ∀ a b start, match ix.toInt start with
        | .error e => JuliaLean.base.strings.search.findprevInt8 ops ix b a start = .error e
        | .ok i => if v.first a + Int.ofNat (v.elements a).length ≤ i.val then
            JuliaLean.base.strings.search.findprevInt8 ops ix b a start =
              .error (ops.boundsError a i.val)
          else JuliaLean.Proofs.base.strings.search.LastIndex
            (JuliaLean.Proofs.base.strings.search.byteMatches v (fun x => x.val == b.val) a)
            i.val (JuliaLean.base.strings.search.findprevInt8 ops ix b a start) := by
  intro A I E ops v ix hmem _ hvalue a b start
  cases hconvert : ix.toInt start with
  | error e =>
      simp only [hconvert]
      simp [JuliaLean.base.strings.search.findprevInt8, hconvert, Bind.bind, Except.bind]
  | ok i =>
      simp only [hconvert]
      have hfirst := hmem.bytes.firstindex a
      have hlast := hmem.bytes.lastindex a
      by_cases habove : v.first a + Int.ofNat (v.elements a).length ≤ i.val
      · rw [if_pos habove]
        have hlastBefore : v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by
          omega
        have hlastLt : (ops.lastindex a).val < i.val := by simpa [hlast] using hlastBefore
        simp [JuliaLean.base.strings.search.findprevInt8, hconvert, hlastLt,
          Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
      · rw [if_neg habove]
        by_cases hbelow : i.val < v.first a
        · have hnotLastBefore :
              ¬ v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by omega
          have hrun : JuliaLean.base.strings.search.findprevInt8 ops ix b a start = .ok none := by
            have hlastGe : ¬ (ops.lastindex a).val < i.val := by simpa [hlast] using hnotLastBefore
            have hfirstLt : i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
            simp [JuliaLean.base.strings.search.findprevInt8, hconvert, hlastGe, hfirstLt,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [hrun]
          exact lastIndexNoneBefore_local v (fun x => x.val == b.val) a i.val hbelow
        · have hnotLastBefore :
              ¬ v.first a + Int.ofNat (v.elements a).length - 1 < i.val := by omega
          have hspec := JuliaLean.Proofs.base.strings.search.memrchrLastSpec_proven.2
            A E ops v hmem hvalue a b i (by omega) (by omega)
          have hlastGe : ¬ (ops.lastindex a).val < i.val := by simpa [hlast] using hnotLastBefore
          have hfirstGe : ¬ i.val < (ops.firstindex a).val := by simpa [hfirst] using hbelow
          simpa [JuliaLean.base.strings.search.findprevInt8, hconvert, hlastGe, hfirstGe,
            Bind.bind, Except.bind] using hspec

/-- strings-search-dense-byte-forward: Dense signed and unsigned byte findnext returns the first match at or after the start, rejects a start below the array, and preserves Int conversion errors. -/
theorem StringsSearchDenseByteForward_proven : JuliaLean.Proofs.base.strings.search.DenseByteForwardSpec :=
  ⟨denseByteForwardUInt8_local, denseByteForwardInt8_local⟩

/-- strings-search-dense-byte-reverse: Dense signed and unsigned byte findprev returns the last match at or before the start, rejects a start above the array, and preserves Int conversion errors. -/
theorem StringsSearchDenseByteReverse_proven : JuliaLean.Proofs.base.strings.search.DenseByteReverseSpec :=
  ⟨denseByteReverseUInt8_local, denseByteReverseInt8_local⟩

end JuliaLean.ChatGPT.Batch6.Group2

section

set_option maxRecDepth 8192

namespace JuliaLean.ChatGPT.Batch9.Group15

open JuliaLean JuliaLean.base.strings.search JuliaLean.Proofs.base.strings.search
open JuliaLean.src.genericmemory_c

def denseMemoryView : ByteView JString UInt8 := ⟨fun _ => 1, fun s => s.bytes⟩

def denseMemoryOps : DenseOps JString UInt8 Unit where
  firstindex := fun _ => int 1
  lastindex := fun s => int (Int.ofNat s.bytes.length)
  length := fun s => int (Int.ofNat s.bytes.length)
  getindex := fun s i =>
    if i.val < 1 then .error ()
    else match s.bytes[(i.val - 1).toNat]? with
      | none => .error ()
      | some b => .ok b
  value := fun b => Int.ofNat b.toNat
  zero := 0
  boundsError := fun _ _ => ()
  pointer := fun _ => JInt.wrap .u64 1
  memchrCall := fun s p needle count => .ok (
    match ((s.bytes.drop (p.val - 1).toNat).take count.val.toNat).findIdx?
        (fun b => Int.ofNat b.toNat % 256 == needle.val % 256) with
      | none => JInt.wrap .u64 0
      | some offset => JInt.wrap .u64 (p.val + Int.ofNat offset))
  memrchrCall := fun s _ needle count => .ok (
    match ((s.bytes.take count.val.toNat).reverse).findIdx?
        (fun b => Int.ofNat b.toNat % 256 == needle.val % 256) with
      | none => JInt.wrap .u64 0
      | some offset => JInt.wrap .u64 (1 + count.val - 1 - Int.ofNat offset))

theorem denseMemoryLengthBounds (s : JString) :
    0 ≤ Int.ofNat s.bytes.length ∧ Int.ofNat s.bytes.length < 2 ^ 62 := by
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr s.small⟩

theorem denseMemoryLengthVal (s : JString) :
    (int (Int.ofNat s.bytes.length)).val = Int.ofNat s.bytes.length := by
  change wrapInt .i64 (Int.ofNat s.bytes.length) = _
  apply wrapInt_of_inRange
  have hl := denseMemoryLengthBounds s
  constructor
  · exact Int.le_trans (by decide) hl.1
  · have hbound : (2 ^ 62 : Int) ≤ IntTy.max .i64 := by decide
    exact Int.le_trans (Int.le_of_lt hl.2) hbound

theorem denseMemoryByteLaws : ByteLaws denseMemoryOps.toByteOps denseMemoryView := by
  refine {
    firstindex := fun _ => by change (int 1).val = 1; decide
    lastindex := ?_
    length := denseMemoryLengthVal
    getindex := ?_
    getindexOutside := ?_
    byteValue := ?_ }
  · intro s
    change (int (Int.ofNat s.bytes.length)).val = 1 + Int.ofNat s.bytes.length - 1
    rw [denseMemoryLengthVal]
    omega
  · intro s k b hb
    change s.bytes[k]? = some b at hb
    have hk : k < s.bytes.length := (List.getElem?_eq_some_iff.mp hb).1
    have hk0 : 0 ≤ Int.ofNat k := Int.natCast_nonneg _
    have hklen : Int.ofNat k < Int.ofNat s.bytes.length := Int.ofNat_lt.mpr hk
    have hlen := denseMemoryLengthBounds s
    have hv : (int (1 + Int.ofNat k)).val = 1 + Int.ofNat k := by
      change wrapInt .i64 (1 + Int.ofNat k) = _
      apply wrapInt_of_inRange
      have hlo : IntTy.min .i64 ≤ 0 := by decide
      have hhi : (2 ^ 62 : Int) ≤ IntTy.max .i64 := by decide
      omega
    dsimp only [denseMemoryOps, denseMemoryView]
    rw [hv]
    have hnot : ¬ 1 + Int.ofNat k < 1 := by omega
    rw [ite_eq_right hnot]
    have hd : 1 + Int.ofNat k - 1 = Int.ofNat k := by omega
    rw [hd]
    change (match s.bytes[k]? with | none => Except.error () | some b => Except.ok b) = _
    rw [hb]
  · intro s i hi
    change i.val < 1 ∨ 1 + Int.ofNat s.bytes.length ≤ i.val at hi
    change (if i.val < 1 then Except.error ()
      else match s.bytes[(i.val - 1).toNat]? with
        | none => Except.error ()
        | some b => Except.ok b) = Except.error ()
    by_cases hlo : i.val < 1
    · rw [ite_eq_left hlo]
    · rw [ite_eq_right hlo]
      have hge : s.bytes.length ≤ (i.val - 1).toNat := by
        have hlen := denseMemoryLengthBounds s
        have hcast : Int.ofNat (i.val - 1).toNat = i.val - 1 :=
          Int.toNat_of_nonneg (by omega)
        apply Int.ofNat_le.mp
        change Int.ofNat s.bytes.length ≤ Int.ofNat (i.val - 1).toNat
        rw [hcast]
        omega
      have hnone : s.bytes[(i.val - 1).toNat]? = none :=
        List.getElem?_eq_none_iff.mpr hge
      rw [hnone]
  · intro b
    change -128 ≤ Int.ofNat b.toNat ∧ Int.ofNat b.toNat ≤ 255
    have hb : b.toNat ≤ 255 := Nat.le_of_lt_succ b.toNat_lt
    exact ⟨Int.le_trans (by decide) (Int.natCast_nonneg _), Int.ofNat_le.mpr hb⟩

theorem denseMemoryU64Val (z : Int) (hlo : 0 ≤ z) (hhi : z < 2 ^ 64) :
    (JInt.wrap .u64 z).val = z := by
  change wrapInt .u64 z = z
  apply wrapInt_of_inRange
  constructor
  · exact hlo
  · change z ≤ 2 ^ 64 - 1
    omega

theorem denseMemoryLaws : CMemoryLaws denseMemoryOps denseMemoryView := by
  refine {
    bytes := denseMemoryByteLaws
    nonnull := fun _ => by change (JInt.wrap .u64 1).val ≠ 0; decide
    addressRange := ?_
    memchr := ?_
    memrchr := ?_ }
  · intro s
    change (JInt.wrap .u64 1).val + Int.ofNat s.bytes.length < 2 ^ 64
    have hptr : (JInt.wrap .u64 1).val = 1 := by decide
    rw [hptr]
    have hlen := denseMemoryLengthBounds s
    have hlimit : (1 : Int) + 2 ^ 62 < 2 ^ 64 := by decide
    omega
  · intro s start count needle hs hc htotal
    change start + count ≤ Int.ofNat s.bytes.length at htotal
    have hlen := denseMemoryLengthBounds s
    have hptr : (JInt.wrap .u64 1).val = 1 := by decide
    have hlimit : (1 : Int) + 2 ^ 62 < 2 ^ 64 := by decide
    have hstart : (JInt.wrap .u64 (1 + start)).val = 1 + start :=
      denseMemoryU64Val _ (by omega) (by omega)
    have hcount : (JInt.wrap .u64 count).val = count :=
      denseMemoryU64Val _ hc (by omega)
    simp only [denseMemoryOps, denseMemoryView, hptr, hstart, hcount]
    have hsub : 1 + start - 1 = start := by omega
    rw [hsub]
  · intro s count needle hc htotal
    change count ≤ Int.ofNat s.bytes.length at htotal
    have hlen := denseMemoryLengthBounds s
    have hptr : (JInt.wrap .u64 1).val = 1 := by decide
    have hlimit : (2 ^ 62 : Int) < 2 ^ 64 := by decide
    have hcount : (JInt.wrap .u64 count).val = count :=
      denseMemoryU64Val _ hc (by omega)
    simp only [denseMemoryOps, denseMemoryView, hptr, hcount]

private theorem denseIntVal (z : Int)
    (h : IntTy.min .i64 ≤ z ∧ z ≤ IntTy.max .i64) : (int z).val = z :=
  wrapInt_of_inRange .i64 z h

private theorem denseInt0 : (int 0).val = 0 := by decide

private theorem denseInt1 : (int 1).val = 1 := by decide

private theorem denseInt2 : (int 2).val = 2 := by decide

private theorem denseInt3 : (int 3).val = 3 := by decide

private theorem denseInt4 : (int 4).val = 4 := by decide

private def denseStoredBytes (c : JChar) : List UInt8 :=
  (JuliaLean.Proofs.base.char.storedBytes c).map UInt8.ofNat

private def denseNcu (c : JChar) : Index := int (denseStoredBytes c).length

private theorem denseStoredLength (c : JChar) :
    1 ≤ (denseStoredBytes c).length ∧ (denseStoredBytes c).length ≤ 4 := by
  rcases JuliaLean.Proofs.base.char.storedBytes_cases c with h | h | h | h <;>
    simp only [denseStoredBytes, h.1, List.map_cons, List.map_nil, List.length_cons,
      List.length_nil] <;> decide

private theorem denseStoredPack (c : JChar) :
    c.toNat = (denseStoredBytes c).zipIdx.foldl
      (fun n p => n + p.1.toNat * 2 ^ (8 * (3 - p.2))) 0 := by
  have hpack := JuliaLean.Proofs.base.char.toNat_bytes c
  rcases JuliaLean.Proofs.base.char.storedBytes_cases c with h | h | h | h
  · simpa only [denseStoredBytes, h.1, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat, UInt8.toNat_ofNat', List.map_cons, List.map_nil, Nat.mod_mod, Nat.zero_add, Nat.add_zero, Nat.mul_one, Nat.mul_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow] using hpack
  · simpa only [denseStoredBytes, h.1, h.2.1, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat, UInt8.toNat_ofNat', List.map_cons, List.map_nil, Nat.mod_mod, Nat.zero_add, Nat.add_zero, Nat.mul_one, Nat.mul_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow] using hpack
  · simpa only [denseStoredBytes, h.1, h.2.1, h.2.2.1, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat, UInt8.toNat_ofNat', List.map_cons, List.map_nil, Nat.mod_mod, Nat.zero_add, Nat.add_zero, Nat.mul_one, Nat.mul_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow] using hpack
  · simpa only [denseStoredBytes, h.1, h.2.1, h.2.2.1, h.2.2.2, List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat, UInt8.toNat_ofNat', List.map_cons, List.map_nil, Nat.mod_mod, Nat.zero_add, Nat.add_zero, Nat.mul_one, Nat.mul_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow] using hpack

private def denseEncoding : CharEncoding denseNcu where
  bytes := denseStoredBytes
  nonempty := by
    intro c
    have h := (denseStoredLength c).1
    cases hd : denseStoredBytes c with
    | nil => simp only [hd, List.length_nil] at h; omega
    | cons b rest => rfl
  length := fun c => (denseStoredLength c).2
  ncodeunits_eq := by
    intro c
    apply denseIntVal
    have h := denseStoredLength c
    constructor <;> simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] <;> omega
  packed := denseStoredPack

private def denseSourceView : TextView Unit JChar :=
  ⟨fun _ => [0xc2, 0x80, 0x61], fun _ => [(int 1, 0xc2800000), (int 3, 0x61000000)]⟩

private def densePatternView : TextView Unit JChar :=
  ⟨fun _ => [0x80, 0x61], fun _ => [(int 1, 0x80000000), (int 2, 0x61000000)]⟩

private def denseTextOps (v : TextView Unit JChar) (n : Index) :
    SearchStringOps Unit JChar Unit where
  ncodeunits := fun _ => n
  iterationBound := fun s => (v.bytes s).length
  lastindex := fun s => .ok (lastIndex v s)
  nextind := fun s i => .ok (nextPosition v s i)
  prevind := fun s i => .ok (prevPosition v s i)
  isvalid := fun s i => .ok ((v.characters s).any (fun p => p.1 == i))
  getindex := fun s i => match (v.characters s).find? (fun p => p.1 == i) with
    | none => .error ()
    | some p => .ok p.2
  iterate := fun s i => match (v.characters s).find? (fun p => p.1 == i) with
    | none => .ok none
    | some p => .ok (some (p.2, nextPosition v s i))
  boundsError := fun _ _ => ()
  stringIndexError := fun _ _ => ()
  somethingError := ()

private def denseSourceOps := denseTextOps denseSourceView (int 3)

private def densePatternOps := denseTextOps densePatternView (int 2)

private theorem denseSourceLaws :
    Utf8TextLaws denseSourceOps denseSourceView denseNcu denseEncoding := by
  refine {
    sizeFits := ?_
    ncodeunits := ?_
    iterationBound := ?_
    sorted := ?_
    indices := ?_
    nonempty := ?_
    first := ?_
    lastindex := ?_
    isvalid := ?_
    getindex := ?_
    nextind := ?_
    prevind := ?_
    iterate := ?_
    concatenation := ?_
    offsets := ?_
    standalone := ?_ }
  · intro s; cases s; decide
  · intro s; exact denseInt3
  · intro s; exact Nat.le_refl _
  · intro s; cases s; decide
  · intro s p hp
    simp only [denseSourceView, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> cases s <;> decide
  · intro s; rfl
  · intro s p hp
    have hp' : (int 1, (0xc2800000 : JChar)) = p := Option.some.inj hp
    rw [← hp']
  · intro s; rfl
  · intro s i; rfl
  · intro s i c hi
    simp only [denseSourceView, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  · intro s i hi; rfl
  · intro s i hi; rfl
  · intro s i c hi
    simp only [denseSourceView, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  · intro s; cases s; decide
  · intro s k p hp
    cases k with
    | zero =>
      have hp' : (int 1, (0xc2800000 : JChar)) = p := Option.some.inj hp
      rw [← hp']; cases s; decide
    | succ k =>
      cases k with
      | zero =>
        have hp' : (int 3, (0x61000000 : JChar)) = p := Option.some.inj hp
        rw [← hp']; cases s; decide
      | succ k => cases hp
  · intro s p b hp hb hs
    simp only [denseSourceView, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · change b ∈ ([0xc2, 0x80] : List UInt8) at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · change 194 < 128 ∨ 247 < 194 at hs
        omega
      · change 128 < 128 ∨ 247 < 128 at hs
        omega
    · have hb' : b = 0x61 := by change b ∈ ([0x61] : List UInt8) at hb; exact List.mem_singleton.mp hb
      subst b
      rfl

private theorem densePatternLaws :
    Utf8TextLaws densePatternOps densePatternView denseNcu denseEncoding := by
  refine {
    sizeFits := ?_
    ncodeunits := ?_
    iterationBound := ?_
    sorted := ?_
    indices := ?_
    nonempty := ?_
    first := ?_
    lastindex := ?_
    isvalid := ?_
    getindex := ?_
    nextind := ?_
    prevind := ?_
    iterate := ?_
    concatenation := ?_
    offsets := ?_
    standalone := ?_ }
  · intro s; cases s; decide
  · intro s; exact denseInt2
  · intro s; exact Nat.le_refl _
  · intro s; cases s; decide
  · intro s p hp
    simp only [densePatternView, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> cases s <;> decide
  · intro s; rfl
  · intro s p hp
    have hp' : (int 1, (0x80000000 : JChar)) = p := Option.some.inj hp
    rw [← hp']
  · intro s; rfl
  · intro s i; rfl
  · intro s i c hi
    simp only [densePatternView, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  · intro s i hi; rfl
  · intro s i hi; rfl
  · intro s i c hi
    simp only [densePatternView, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hi
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  · intro s; cases s; decide
  · intro s k p hp
    cases k with
    | zero =>
      have hp' : (int 1, (0x80000000 : JChar)) = p := Option.some.inj hp
      rw [← hp']; cases s; decide
    | succ k =>
      cases k with
      | zero =>
        have hp' : (int 2, (0x61000000 : JChar)) = p := Option.some.inj hp
        rw [← hp']; cases s; decide
      | succ k => cases hp
  · intro s p b hp hb hs
    simp only [densePatternView, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · change b ∈ ([0x80] : List UInt8) at hb
      have hb' : b = 0x80 := List.mem_singleton.mp hb
      subst b
      change 128 < 128 ∨ 247 < 128 at hs
      omega
    · have hb' : b = 0x61 := by change b ∈ ([0x61] : List UInt8) at hb; exact List.mem_singleton.mp hb
      subst b
      rfl

private def denseHay : JString := ⟨[0xc2, 0x80, 0x61], by decide⟩

private def denseNeedle : JString := ⟨[0x80, 0x61], by decide⟩

private def denseBasic : JuliaLean.base.strings.basic.StringOps Unit Unit JChar UInt8 Unit Unit where
  ncodeunits := fun _ => int 3
  codeunitType := fun _ => ()
  codeunitSize := fun _ => int 1
  codeunit := fun _ _ => .error ()
  isvalid := denseSourceOps.isvalid
  iterateFirst := fun _ => .ok (some (0xc2800000, int 3))
  iterateAt := denseSourceOps.iterate
  iterationBound := fun _ => 3
  thisind := fun _ i => .ok i
  prevind := fun s i _ => denseSourceOps.prevind s i
  nextind := fun s i _ => denseSourceOps.nextind s i
  lastindex := denseSourceOps.lastindex
  getindexSlice := fun _ _ _ => .ok ()
  checkbounds := fun _ _ => .error ()
  checkboundsBool := fun _ _ => .ok false
  boundsError := fun _ _ => ()
  stringIndexError := fun _ _ => ()
  methodError := fun _ => ()
  argumentError := fun _ => ()
  tupleTypeError := ()
  isBoundsError := fun _ => true
  characters := fun _ => .ok [0xc2800000, 0x61000000]
  sameReference := fun _ _ => true
  equalChar := fun a b => decide (a = b)
  lessChar := fun a b => decide (a < b)

private def denseCfg : DenseStringSearch Unit Unit JString JString Unit where
  source := denseSourceOps
  pattern := densePatternOps
  sourceBytes := denseMemoryOps
  patternBytes := denseMemoryOps.toByteOps
  codeunitsSource := fun _ => denseHay
  codeunitsPattern := fun _ => denseNeedle
  chars := ⟨fun c => .ok c, fun c => .ok (denseNcu c)⟩
  sourceBasic := denseBasic

private theorem denseCfgLaws :
    DenseLaws denseCfg denseSourceView densePatternView
      denseMemoryView denseMemoryView denseEncoding := by
  refine {
    source := denseSourceLaws
    pattern := densePatternLaws
    chars := fun _ => rfl
    toChar := fun _ => rfl
    codeunits := ?_
    patternBytes := denseMemoryByteLaws
    patternFirst := fun _ => rfl
    patternContents := fun _ => rfl
    patternValues := fun _ => rfl
    sizeof := ?_ }
  · exact ⟨denseMemoryLaws, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl)⟩
  · intro s; cases s; decide

private abbrev denseByteOps := denseMemoryOps.toByteOps

private def denseRange23 : MatchRange := ⟨int 2, int 3⟩

private theorem denseForwardCompare :
    forwardCompare denseByteOps denseByteOps denseHay denseNeedle
      (int 1) (int 2) (int 0) = pure (int 1) := by
  rw [forwardCompare.eq_def]
  change forwardCompare denseByteOps denseByteOps denseHay denseNeedle
      (int 1) (int 2) (int 1) = pure (int 1)
  rw [forwardCompare.eq_def]
  rfl

private theorem denseForwardLoopOne (mask : UInt64) (skip : Index) :
    searchBytesLoop denseByteOps denseByteOps denseHay denseNeedle
      (int 2) (int 1) mask skip (0x61 : UInt8) (int 0) (int 1) = pure (int 2) := by
  rw [searchBytesLoop.eq_def, denseForwardCompare]
  rfl

private def denseMask : UInt64 := 8589934593

private theorem denseForwardLoop :
    searchBytesLoop denseByteOps denseByteOps denseHay denseNeedle
      (int 2) (int 1) denseMask (int 1) (0x61 : UInt8) (int 0) (int 0) = pure (int 2) := by
  rw [searchBytesLoop.eq_def]
  change searchBytesLoop denseByteOps denseByteOps denseHay denseNeedle
      (int 2) (int 1) denseMask (int 1) (0x61 : UInt8) (int 0) (int 1) = pure (int 2)
  exact denseForwardLoopOne _ _

private theorem denseMaskComputed :
    forwardMask denseByteOps denseNeedle (int 2) (0x61 : UInt8) =
      .ok (denseMask, int 1) := by
  decide

private theorem denseBindLiftOk {E α β : Type} (x : α) (f : α → SearchM E β) :
    (do let y ← liftE (.ok x); f y) = f x := rfl

private theorem denseIndexOne : denseIndex denseCfg indexOps () () (int 1) = pure (int 2) := by
  unfold denseIndex searchindexDense
  have hp : denseCfg.pattern.lastindex () = .ok (int 2) := rfl
  rw [hp]
  simp only [denseBindLiftOk]
  change searchindexBytes denseByteOps denseByteOps
    (fun b a i => findnextUInt8 denseMemoryOps indexOps b a i) indexOps
    denseHay denseNeedle (int 1) = pure (int 2)
  have hfirst : denseByteOps.firstindex denseHay = int 1 := rfl
  have hslen : denseByteOps.length denseHay = int 3 := rfl
  have htlen : denseByteOps.length denseNeedle = int 2 := rfl
  have hsentinel : int 1 - int 1 = int 0 := by decide
  have hstart : int 1 - int 0 = int 1 := by decide
  have hend : int 3 + int 1 = int 4 := by decide
  have hwidth : int 3 - int 2 = int 1 := by decide
  have hlast : vectorNth denseByteOps denseNeedle (int 2) = .ok (0x61 : UInt8) := by decide
  unfold searchindexBytes
  simp only [hfirst, hslen, htlen, hsentinel, hstart, hend, hwidth, indexOps,
    denseBindLiftOk, denseInt0, denseInt1, denseInt2, denseInt4, hlast]
  rw [denseMaskComputed]
  exact denseForwardLoop

private theorem denseNextOne :
    (denseNext denseCfg indexOps () () (int 1)).run = some (.ok (some denseRange23)) := by
  change (denseRange denseCfg () () (int 1)).run = _
  unfold denseRange searchRange
  rw [denseIndexOne]
  rfl

private theorem denseNoMatch (r : MatchRange) :
    ¬ textSequenceAt denseSourceView
      (fun t => (densePatternView.characters t).map (·.2)) () () r := by
  intro hm
  change (∃ k,
    (([(int 1, (0xc2800000 : JChar)), (int 3, 0x61000000)])[k]?.map (·.1)) = some r.first ∧
    ((([(int 1, (0xc2800000 : JChar)), (int 3, 0x61000000)]).drop k).take 2).map (·.2) =
      [0x80000000, 0x61000000] ∧
    (([(int 1, (0xc2800000 : JChar)), (int 3, 0x61000000)])[k + 2 - 1]?.map (·.1)) = some r.last) at hm
  obtain ⟨k, hf, hm, hl⟩ := hm
  cases k with
  | zero =>
    have heq : (0xc2800000 : JChar) = 0x80000000 := by
      exact List.cons.inj hm |>.1
    have hne : (0xc2800000 : JChar) ≠ 0x80000000 := by decide
    exact hne heq
  | succ k =>
    cases k with
    | zero =>
      have hlen := congrArg List.length hm
      change 1 = 2 at hlen
      omega
    | succ k => cases hf

private theorem denseIndexLaws : IntegerLaws (indexOps : IntegerOps Index Unit) := by
  constructor
  · intro i hlo hhi
    change Except.ok i = Except.ok (int i.val)
    congr 1
    apply Subtype.ext
    exact (wrapInt_of_inRange .i64 i.val i.property).symm
  · intro i j h
    have h' : i = j := Except.ok.inj h
    rw [← h']
    rfl

theorem StringsSearchForwardFirstRange_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.DenseForwardSpec := by
  intro h
  obtain ⟨result, hr, hspec⟩ := h Unit Unit JString JString Index Unit denseCfg
    denseSourceView densePatternView denseMemoryView denseMemoryView denseNcu denseEncoding
    indexOps denseCfgLaws denseIndexLaws () () (int 1) (by decide) (by decide)
      (Or.inl ⟨0xc2800000, by decide⟩)
  rw [denseNextOne] at hr
  have heq : Except.ok (some denseRange23) = result := Option.some.inj hr
  subst result
  exact denseNoMatch denseRange23 ((hspec.1 denseRange23).mp rfl).1

theorem StringsSearchFirstLastString_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.DenseFirstLastSpec := by
  intro h
  obtain ⟨result, hr, hspec⟩ := (h Unit Unit JString JString Unit denseCfg
    denseSourceView densePatternView denseMemoryView denseMemoryView denseNcu denseEncoding
    denseCfgLaws () ()).1
  have hfirst : (denseFirst denseCfg () ()).run = some (.ok (some denseRange23)) := denseNextOne
  rw [hfirst] at hr
  have heq : Except.ok (some denseRange23) = result := Option.some.inj hr
  subst result
  exact denseNoMatch denseRange23 ((hspec.1 denseRange23).mp rfl).1

private theorem denseOccursTrue : (denseOccursin denseCfg () ()).run = some (.ok true) := by
  unfold denseOccursin JuliaLean.base.strings.search.occursin
  change (do let i ← denseIndex denseCfg indexOps () () (int 1)
             pure (i.val != 0)).run = _
  rw [denseIndexOne]
  rfl

theorem StringsSearchOccursinFirstMatch_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.OccursinSpec := by
  intro h
  have hs := h Unit Unit JString JString Unit denseCfg denseSourceView densePatternView
    denseMemoryView denseMemoryView denseNcu denseEncoding denseCfgLaws () ()
  obtain ⟨r, hr⟩ := hs.2.1.mp denseOccursTrue
  exact denseNoMatch r hr

private theorem byteInt0 : (int 0).val = 0 := by decide

private theorem byteInt1 : (int 1).val = 1 := by decide

private def byteOneSource : ByteOps Unit UInt8 Unit where
  firstindex := fun _ => int 0
  lastindex := fun _ => int 0
  length := fun _ => int 1
  getindex := fun _ i => if i.val = 0 then .ok 65 else .error ()
  value := fun b => Int.ofNat b.toNat
  zero := 0
  boundsError := fun _ _ => ()

private def byteOnePattern : ByteOps Unit UInt8 Unit where
  firstindex := fun _ => int 1
  lastindex := fun _ => int 1
  length := fun _ => int 1
  getindex := fun _ i => if i.val = 1 then .ok 65 else .error ()
  value := fun b => Int.ofNat b.toNat
  zero := 0
  boundsError := fun _ _ => ()

private def byteOneSv : ByteView Unit UInt8 := ⟨fun _ => 0, fun _ => [65]⟩

private def byteOneTv : ByteView Unit UInt8 := ⟨fun _ => 1, fun _ => [65]⟩

private def byteOneCfg : BytePatternSearch Unit Unit UInt8 UInt8 Unit where
  source := byteOneSource
  pattern := byteOnePattern
  findnext := fun c _ i =>
    if i.val < 0 then .error ()
    else if i.val = 0 ∧ c = 65 then .ok (some (int 0)) else .ok none
  findprev := fun c _ i =>
    if 0 < i.val then .error ()
    else if i.val = 0 ∧ c = 65 then .ok (some (int 0)) else .ok none

private theorem byteOneSourceLaws : ByteLaws byteOneSource byteOneSv := by
  refine {
    firstindex := ?_
    lastindex := ?_
    length := ?_
    getindex := ?_
    getindexOutside := ?_
    byteValue := ?_ }
  · intro a; exact byteInt0
  · intro a; change (int 0).val = 0 + Int.ofNat ([65] : List UInt8).length - 1
    rw [byteInt0]; decide
  · intro a; exact byteInt1
  · intro a k b h
    cases k with
    | zero =>
        have hb : (65 : UInt8) = b := Option.some.inj h
        subst b
        rfl
    | succ k => cases h
  · intro a i h
    have hi : i.val ≠ 0 := by
      change i.val < 0 ∨ 1 ≤ i.val at h
      omega
    simp only [byteOneSource, hi, ↓reduceIte]
  · intro b
    change -128 ≤ Int.ofNat b.toNat ∧ Int.ofNat b.toNat ≤ 255
    have hb : b.toNat ≤ 255 := Nat.le_of_lt_succ b.toNat_lt
    exact ⟨Int.le_trans (by decide) (Int.natCast_nonneg _), Int.ofNat_le.mpr hb⟩

private theorem byteOnePatternLaws : ByteLaws byteOnePattern byteOneTv := by
  refine {
    firstindex := ?_
    lastindex := ?_
    length := ?_
    getindex := ?_
    getindexOutside := ?_
    byteValue := ?_ }
  · intro a; exact byteInt1
  · intro a; change (int 1).val = 1 + Int.ofNat ([65] : List UInt8).length - 1
    rw [byteInt1]; decide
  · intro a; exact byteInt1
  · intro a k b h
    cases k with
    | zero =>
        have hb : (65 : UInt8) = b := Option.some.inj h
        subst b
        rfl
    | succ k => cases h
  · intro a i h
    have hi : i.val ≠ 1 := by
      change i.val < 1 ∨ 2 ≤ i.val at h
      omega
    simp only [byteOnePattern, hi, ↓reduceIte]
  · intro b
    change -128 ≤ Int.ofNat b.toNat ∧ Int.ofNat b.toNat ≤ 255
    have hb : b.toNat ≤ 255 := Nat.le_of_lt_succ b.toNat_lt
    exact ⟨Int.le_trans (by decide) (Int.natCast_nonneg _), Int.ofNat_le.mpr hb⟩

private theorem byteOneMatch (c : UInt8) (a : Unit) (j : Int) :
    byteMatches byteOneSv
      (fun b => byteOneSource.value b == byteOnePattern.value c) a j ↔
      j = 0 ∧ c = 65 := by
  simp only [byteMatches, byteAt, byteOneSv, byteOneSource, byteOnePattern,
    Int.sub_zero]
  constructor
  · rintro ⟨hj, b, hget, heq⟩
    have hlen := (List.getElem?_eq_some_iff.mp hget).1
    have hj0 : j = 0 := by simp only [List.length_cons, List.length_nil] at hlen; omega
    subst j
    have hb : (65 : UInt8) = b := Option.some.inj hget
    subst b
    have hc : Int.ofNat (65 : UInt8).toNat = Int.ofNat c.toNat := by
      exact beq_iff_eq.mp heq
    have hc' : (65 : UInt8).toNat = c.toNat := Int.ofNat_inj.mp hc
    exact ⟨rfl, (UInt8.toNat.inj hc').symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨by decide, 65, rfl, by decide⟩

private theorem byteOneLaws : BytePatternLaws byteOneCfg byteOneSv byteOneTv := by
  refine {
    source := byteOneSourceLaws
    pattern := byteOnePatternLaws
    findnext := ?_
    findprev := ?_
    findprevAboveLast := ?_ }
  · intro a c i hi
    have hi' : 0 ≤ i.val := hi
    have hn : ¬ i.val < 0 := by omega
    change FirstIndex
      (byteMatches byteOneSv (fun b => byteOneSource.value b == byteOnePattern.value c) a)
      i.val (if i.val < 0 then .error () else
        if i.val = 0 ∧ c = 65 then .ok (some (int 0)) else .ok none)
    rw [ite_eq_right hn]
    simp only [FirstIndex, byteOneMatch]
    by_cases h : i.val = 0 ∧ c = 65
    · rw [ite_eq_left h]
      constructor
      · intro j
        constructor
        · intro hj
          have hj' : int 0 = j := Option.some.inj (Except.ok.inj hj)
          subst j
          exact ⟨by rw [byteInt0, h.1]; decide, ⟨byteInt0, h.2⟩,
            fun k _ hk => by rw [byteInt0, hk.1]; decide⟩
        · rintro ⟨_, ⟨hj, _⟩, _⟩
          have heq : int 0 = j := Subtype.ext (by rw [byteInt0, hj])
          rw [heq]
      · constructor
        · intro hf; cases hf
        · intro hn
          exact (hn 0 (by omega) ⟨rfl, h.2⟩).elim
    · rw [ite_eq_right h]
      constructor
      · intro j
        constructor
        · intro hf; cases hf
        · rintro ⟨hj, ⟨hz, hc⟩, _⟩
          exact (h ⟨by omega, hc⟩).elim
      · constructor
        · intro _ j hj hm
          exact h ⟨by omega, hm.2⟩
        · intro _; rfl
  · intro a c i hi
    have hi' : i.val < 1 := hi
    have hn : ¬ 0 < i.val := by omega
    change LastIndex
      (byteMatches byteOneSv (fun b => byteOneSource.value b == byteOnePattern.value c) a)
      i.val (if 0 < i.val then .error () else
        if i.val = 0 ∧ c = 65 then .ok (some (int 0)) else .ok none)
    rw [ite_eq_right hn]
    simp only [LastIndex, byteOneMatch]
    by_cases h : i.val = 0 ∧ c = 65
    · rw [ite_eq_left h]
      constructor
      · intro j
        constructor
        · intro hj
          have hj' : int 0 = j := Option.some.inj (Except.ok.inj hj)
          subst j
          exact ⟨by rw [byteInt0, h.1]; decide, ⟨byteInt0, h.2⟩,
            fun k _ hk => by rw [byteInt0, hk.1]; decide⟩
        · rintro ⟨_, ⟨hj, _⟩, _⟩
          have heq : int 0 = j := Subtype.ext (by rw [byteInt0, hj])
          rw [heq]
      · constructor
        · intro hf; cases hf
        · intro hn
          exact (hn 0 (by omega) ⟨rfl, h.2⟩).elim
    · rw [ite_eq_right h]
      constructor
      · intro j
        constructor
        · intro hf; cases hf
        · rintro ⟨hj, ⟨hz, hc⟩, _⟩
          exact (h ⟨by omega, hc⟩).elim
      · constructor
        · intro _ j hj hm
          exact h ⟨by omega, hm.2⟩
        · intro _; rfl
  · intro a c i hi
    change 0 < i.val at hi
    simp only [byteOneCfg, hi, ↓reduceIte, byteOneSource]

private theorem byteIndexLaws : IntegerLaws (indexOps (E := Unit)) := by
  constructor
  · intro i _ _
    apply congrArg Except.ok
    apply Subtype.ext
    change i.val = wrapInt .i64 i.val
    exact (wrapInt_of_inRange .i64 i.val i.property).symm
  · intro i j h
    exact congrArg Subtype.val (Except.ok.inj h).symm

private theorem byteOneNext :
    (vectorNext byteOneCfg indexOps () () (int 0)).run = some (.ok none) := by
  decide

private theorem byteOnePrev :
    (vectorPrev byteOneCfg indexOps () () (int 0)).run = some (.error ()) := by
  decide

private theorem byteOneRange :
    byteRangeAt byteOneCfg byteOneSv byteOneTv () () ⟨int 0, int 0⟩ := by
  constructor
  · refine ⟨by decide, by decide, ?_⟩
    intro k b hb
    cases k with
    | zero =>
        have h : (65 : UInt8) = b := Option.some.inj hb
        subst b
        exact ⟨65, by decide, rfl⟩
    | succ k => cases hb
  · decide

private theorem byteOneOnlyRange (r : MatchRange)
    (hr : byteRangeAt byteOneCfg byteOneSv byteOneTv () () r) : r.first.val = 0 := by
  have h1 := hr.1.1
  have h2 := hr.1.2.1
  change 0 ≤ r.first.val at h1
  change r.first.val + 1 ≤ 0 + 1 at h2
  omega

theorem StringsSearchBytePatternFirst_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.BytePatternForwardSpec := by
  intro h
  obtain ⟨x, hx, hs⟩ := h Unit Unit UInt8 UInt8 Index Unit byteOneCfg
    byteOneSv byteOneTv indexOps byteOneLaws byteIndexLaws () () (int 0)
      (by decide) (by decide)
  rw [byteOneNext] at hx
  have hx' : Except.ok none = x := Option.some.inj hx
  subst x
  have hn := hs.2.mp rfl ⟨int 0, int 0⟩ (by decide)
  exact hn byteOneRange

theorem StringsSearchBytePatternLast_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.BytePatternReverseSpec := by
  intro h
  obtain ⟨x, hx, hs⟩ := h Unit Unit UInt8 UInt8 Index Unit byteOneCfg
    byteOneSv byteOneTv indexOps byteOneLaws byteIndexLaws () () (int 0)
      (by decide) (by decide) (by decide)
  rw [byteOnePrev] at hx
  have hx' : Except.error () = x := Option.some.inj hx
  subst x
  have bad := (hs.1 ⟨int 0, int 0⟩).mpr
    ⟨byteOneRange, by decide, fun q hq _ => by
      rw [byteOneOnlyRange q hq, byteInt0]
      decide⟩
  cases bad

theorem StringsSearchFirstLastBytePattern_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.BytePatternFirstLastSpec := by
  intro h
  obtain ⟨x, hx, hs⟩ := (h Unit Unit UInt8 UInt8 Unit byteOneCfg
    byteOneSv byteOneTv byteOneLaws () ()).1
  have hactual : (vectorFirst byteOneCfg () ()).run = some (.ok none) := byteOneNext
  rw [hactual] at hx
  have hx' : Except.ok none = x := Option.some.inj hx
  subst x
  have hn := hs.2.mp rfl ⟨int 0, int 0⟩ (by decide)
  exact hn byteOneRange

private def byteRangeElementLayout : JuliaLean.base.runtime_internals.DataTypeLayout :=
  nativeLayout 16 0 0 (-1) 8 128

private def byteRangeMetadata : Metadata :=
  { runtimeType :=
      { identity := 15
        layout := genericMemoryHeader 16 8 0 (-1)
        elementType := .datatype ⟨byteRangeElementLayout, byteRangeElementLayout, fun _ => 0⟩
        elementTag := .bitInteger .i128
        kind := .notAtomic }
    typeofBottom := none
    owner := 0
    mutexBytes := 0 }

private def byteRangeRuntimeLayout : DictLayout where
  metadata := byteRangeMetadata
  nonAtomicKind := rfl
  nonAtomicFlag := rfl
  unlocked := rfl
  inlineDatatype := by
    intro _ _ _
    exact ⟨⟨byteRangeElementLayout, byteRangeElementLayout, fun _ => 0⟩, rfl⟩

private def byteRangeStore :
    VectorStore MatchRange Unit (JuliaLean.base.array.MutableMemory MatchRange) where
  layout := JuliaLean.base.array.MemoryLayoutMetadata.ofRuntime byteRangeRuntimeLayout
  memory := id
  setMemory := fun _ m => m
  error := fun _ => ()

private def byteEmptyHeap : JuliaLean.base.array.MutableMemory MatchRange := ⟨[], []⟩

private def byteAllocatedHeap : JuliaLean.base.array.MutableMemory MatchRange :=
  ⟨[[]], [⟨(0, int 1), int 0⟩]⟩

private def byteAllRun :=
  findallRanges byteRangeStore
    (fun t a i => liftSearch (vectorNext byteOneCfg indexOps t a i))
    byteOneCfg.source.firstindex
    (fun a => liftExcept (.ok (byteOneCfg.source.lastindex a)))
    (fun _ i => liftExcept (.ok (i + int 1))) true () ()

private theorem byteAllResult : VectorResult byteRangeStore byteAllRun byteEmptyHeap [] := by
  refine ⟨0, byteAllocatedHeap, ?_, rfl⟩
  unfold byteAllRun findallRanges
  change (findallRangesLoop byteRangeStore
    (fun t a i => liftSearch (vectorNext byteOneCfg indexOps t a i))
    (fun _ i => liftExcept (.ok (i + int 1))) true () () (int 0) 0 (int 0))
      byteAllocatedHeap = some (.ok 0, byteAllocatedHeap)
  rw [findallRangesLoop.eq_def]
  simp only [Bind.bind, JuliaLean.base.iterators.bind, liftSearch, byteOneNext,
    Pure.pure, JuliaLean.base.iterators.ret]

theorem StringsSearchBytePatternAll_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.ByteFindallSpec := by
  intro h
  have hs := h Unit Unit Unit (JuliaLean.base.array.MutableMemory MatchRange)
    byteOneCfg byteOneSv byteOneTv byteRangeStore byteOneLaws
    (fun _ _ => rfl) () () true [] byteEmptyHeap byteAllResult
  have bad := hs.2.2.2 rfl ⟨int 0, int 0⟩ byteOneRange
  cases bad

private theorem denseReverseCompare :
    reverseCompare denseByteOps denseByteOps denseHay denseNeedle
      (int 2) (int 2) (int 1) = pure (int 2) := by
  rw [reverseCompare.eq_def]
  change reverseCompare denseByteOps denseByteOps denseHay denseNeedle
      (int 2) (int 2) (int 2) = pure (int 2)
  rw [reverseCompare.eq_def]
  rfl

private theorem denseReverseLoop :
    rsearchBytesLoop denseByteOps denseByteOps denseHay denseNeedle
      (int 2) denseMask (int 1) (0x80 : UInt8) (int 0) (int 2) = pure (int 2) := by
  rw [rsearchBytesLoop.eq_def, denseReverseCompare]
  rfl

private theorem denseReverseMaskComputed :
    reverseMask denseByteOps denseNeedle (int 2) (0x80 : UInt8) =
      .ok (denseMask, int 1) := by
  decide

private theorem denseReverseByteIndex :
    rsearchindexBytes denseByteOps denseByteOps
      (fun b a i => findprevUInt8 denseMemoryOps indexOps b a i) indexOps
      denseHay denseNeedle (int 3) = pure (int 2) := by
  have hfirst : denseByteOps.firstindex denseHay = int 1 := rfl
  have hslen : denseByteOps.length denseHay = int 3 := rfl
  have htlen : denseByteOps.length denseNeedle = int 2 := rfl
  have hsentinel : int 1 - int 1 = int 0 := by decide
  have hstart : int 3 - int 0 = int 3 := by decide
  have hwidth : int 3 - int 2 = int 1 := by decide
  have htfirst : vectorNth denseByteOps denseNeedle (int 1) = .ok (0x80 : UInt8) := by decide
  unfold rsearchindexBytes
  simp only [hfirst, hslen, htlen, hsentinel, hstart, hwidth, indexOps,
    denseBindLiftOk, denseInt1, denseInt2, denseInt3, htfirst]
  rw [denseReverseMaskComputed]
  exact denseReverseLoop

private theorem denseTailBindPure {E α β : Type} (x : α) (f : α → SearchM E β) :
    (do let y ← pure x; f y) = f x := rfl

private theorem denseReverseIndexThree :
    denseRIndex denseCfg indexOps () () (int 3) = pure (int 2) := by
  have hr : rsearchindexDense denseCfg indexOps () () (int 3) =
      pure (DenseSearchIndex.juliaInt (int 2)) := by
    have hp : denseCfg.pattern.lastindex () = .ok (int 2) := rfl
    have hs : denseCfg.source.ncodeunits () = int 3 := rfl
    have hn : denseCfg.source.nextind () (int 3) = .ok (int 4) := rfl
    have heq : ((int 2).val == 1) = false := by decide
    have hne : ((int 2).val != 0) = true := by decide
    have hsub : int 4 - int 1 = int 3 := by decide
    unfold rsearchindexDense
    simp only [hp, denseBindLiftOk, heq, hne, Bool.false_eq_true,
      ↓reduceIte, indexOps, hs, Int.le_refl, hn, hsub, denseTailBindPure]
    dsimp only [denseCfg]
    have hbr := denseReverseByteIndex
    simp only [indexOps] at hbr
    rw [hbr]
    rfl
  unfold denseRIndex
  rw [hr]
  rfl

private theorem densePrevThree :
    (densePrev denseCfg indexOps () () (int 3)).run = some (.ok (some denseRange23)) := by
  change (denseRRange denseCfg () () (int 3)).run = _
  unfold denseRRange rsearchRange
  rw [denseReverseIndexThree]
  rfl

theorem StringsSearchReverseLastRange_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.DenseReverseSpec := by
  intro h
  obtain ⟨result, hr, hspec⟩ := h Unit Unit JString JString Index Unit denseCfg
    denseSourceView densePatternView denseMemoryView denseMemoryView denseNcu denseEncoding
    indexOps denseCfgLaws denseIndexLaws () () (int 3)
      (by decide) (by decide) (by decide) (Or.inl ⟨0x61000000, by decide⟩)
  rw [densePrevThree] at hr
  have heq : Except.ok (some denseRange23) = result := Option.some.inj hr
  subst result
  exact denseNoMatch denseRange23 ((hspec.1 denseRange23).mp rfl).1

private theorem denseIndexFour : denseIndex denseCfg indexOps () () (int 4) = pure (int 0) := by
  unfold denseIndex searchindexDense
  have hp : denseCfg.pattern.lastindex () = .ok (int 2) := rfl
  rw [hp]
  simp only [denseBindLiftOk]
  change searchindexBytes denseByteOps denseByteOps
    (fun b a i => findnextUInt8 denseMemoryOps indexOps b a i) indexOps
    denseHay denseNeedle (int 4) = pure (int 0)
  rfl

private theorem denseNextFour :
    (denseNext denseCfg indexOps () () (int 4)).run = some (.ok none) := by
  change (denseRange denseCfg () () (int 4)).run = _
  unfold denseRange searchRange
  rw [denseIndexFour]
  rfl

private def densePushedHeap : JuliaLean.base.array.MutableMemory MatchRange :=
  (Id.run ((ExceptT.run (vectorPush byteRangeStore.layout 0 denseRange23)).run
    byteAllocatedHeap)).2

private theorem densePushComputed :
    liftMutation byteRangeStore (vectorPush byteRangeStore.layout 0 denseRange23)
      byteAllocatedHeap = some (.ok 0, densePushedHeap) := by
  rfl

private theorem densePushedContents :
    (byteRangeStore.memory densePushedHeap).contents 0 = [some denseRange23] := by
  decide

private def denseAllConcrete := denseAll denseCfg byteRangeStore () () false

private theorem denseAllResult :
    VectorResult byteRangeStore denseAllConcrete byteEmptyHeap [denseRange23] := by
  refine ⟨0, densePushedHeap, ?_, densePushedContents⟩
  unfold denseAllConcrete denseAll findallRanges
  change (findallRangesLoop byteRangeStore
    (fun t s i => liftSearch (denseNext denseCfg indexOps t s i))
    (fun s i => liftExcept (denseCfg.source.nextind s i)) false () ()
    (int 3) 0 (int 1)) byteAllocatedHeap = some (.ok 0, densePushedHeap)
  rw [findallRangesLoop.eq_def]
  simp only [Bind.bind, JuliaLean.base.iterators.bind, liftSearch, denseNextOne,
    densePushComputed]
  change (findallRangesLoop byteRangeStore
    (fun t s i => liftSearch (denseNext denseCfg indexOps t s i))
    (fun s i => liftExcept (denseCfg.source.nextind s i)) false () ()
    (int 3) 0 (int 4)) densePushedHeap = some (.ok 0, densePushedHeap)
  rw [findallRangesLoop.eq_def]
  simp only [Bind.bind, JuliaLean.base.iterators.bind, liftSearch, denseNextFour,
    Pure.pure, JuliaLean.base.iterators.ret]

theorem StringsSearchAllPatternRanges_refuted :
    ¬ JuliaLean.Proofs.base.strings.search.FindallRangeSpec := by
  intro h
  have hs := h Unit Unit JString JString Unit (JuliaLean.base.array.MutableMemory MatchRange)
    denseCfg denseSourceView densePatternView denseMemoryView denseMemoryView denseNcu denseEncoding
    byteRangeStore denseCfgLaws (fun _ _ => rfl) () () false [denseRange23]
    byteEmptyHeap denseAllResult
  exact denseNoMatch denseRange23 (hs.1 denseRange23 (by simp only [List.mem_singleton]))

def sliceByteChar (b : UInt8) : JChar := UInt32.ofNat (b.toNat * 16777216)

theorem sliceByteChar_bytes_table : ∀ n : Fin 256,
    denseEncoding.bytes (UInt32.ofNat (n.val * 16777216)) = [UInt8.ofNat n.val] := by
  decide

theorem sliceByteChar_bytes (b : UInt8) : denseEncoding.bytes (sliceByteChar b) = [b] := by
  have h := sliceByteChar_bytes_table ⟨b.toNat, b.toNat_lt⟩
  simpa only [sliceByteChar, UInt8.ofNat_toNat] using h

def sliceIndex (n : Nat) : Index := int (Int.ofNat n + 1)

theorem sliceIndex_val (n : Nat) (h : n ≤ 2 ^ 62) :
    (sliceIndex n).val = Int.ofNat n + 1 := by
  apply denseIntVal
  have hn : 0 ≤ Int.ofNat n := Int.natCast_nonneg n
  have hcast : Int.ofNat n ≤ 4611686018427387904 := Int.ofNat_le.mpr h
  change -9223372036854775808 ≤ Int.ofNat n + 1 ∧
    Int.ofNat n + 1 ≤ 9223372036854775807
  omega

def sliceByteCharacters (start : Nat) : List UInt8 → List (Index × JChar)
  | [] => []
  | b :: bs => (sliceIndex start, sliceByteChar b) :: sliceByteCharacters (start + 1) bs

theorem sliceByteCharacters_bounds (bs : List UInt8) (start : Nat)
    (hbound : start + bs.length < 2 ^ 62) (p : Index × JChar)
    (hp : p ∈ sliceByteCharacters start bs) :
    Int.ofNat start + 1 ≤ p.1.val ∧ p.1.val ≤ Int.ofNat start + Int.ofNat bs.length := by
  induction bs generalizing start p with
  | nil => cases hp
  | cons b bs ih =>
    simp only [sliceByteCharacters, List.mem_cons] at hp
    have hlen : (b :: bs).length = bs.length + 1 := rfl
    rw [hlen] at hbound ⊢
    rcases hp with rfl | hp
    · rw [sliceIndex_val start (by omega)]
      have hbs := Int.natCast_nonneg bs.length
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
      omega
    · have h := ih (start + 1) (by omega) p hp
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one] at h ⊢
      omega

theorem sliceByteCharacters_sorted (bs : List UInt8) (start : Nat)
    (hbound : start + bs.length < 2 ^ 62) :
    (sliceByteCharacters start bs).Pairwise (fun p q => p.1.val < q.1.val) := by
  induction bs generalizing start with
  | nil => exact List.Pairwise.nil
  | cons b bs ih =>
    have htail : start + 1 + bs.length < 2 ^ 62 := by
      simp only [List.length_cons] at hbound
      omega
    apply List.Pairwise.cons
    · intro p hp
      have h := sliceByteCharacters_bounds bs (start + 1) htail p hp
      rw [sliceIndex_val start (by omega)]
      simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one] at h ⊢
      omega
    · exact ih (start + 1) htail

theorem sliceByteCharacters_concat (bs : List UInt8) (start : Nat) :
    (sliceByteCharacters start bs).flatMap (fun p => denseEncoding.bytes p.2) = bs := by
  induction bs generalizing start with
  | nil => rfl
  | cons b bs ih =>
    simp only [sliceByteCharacters, List.flatMap_cons, sliceByteChar_bytes, List.singleton_append]
    rw [ih]

theorem sliceByteCharacters_offsets (bs : List UInt8) (start : Nat)
    (hbound : start + bs.length < 2 ^ 62) (k : Nat) (p : Index × JChar)
    (hp : (sliceByteCharacters start bs)[k]? = some p) :
    p.1.val = Int.ofNat start + 1 +
      Int.ofNat (((sliceByteCharacters start bs).take k).flatMap
        (fun q => denseEncoding.bytes q.2)).length := by
  induction bs generalizing start k p with
  | nil => cases hp
  | cons b bs ih =>
    have htail : start + 1 + bs.length < 2 ^ 62 := by
      simp only [List.length_cons] at hbound
      omega
    cases k with
    | zero =>
      have he : (sliceIndex start, sliceByteChar b) = p := Option.some.inj hp
      rw [← he]
      simp only [List.take_zero, List.flatMap_nil, List.length_nil, Int.ofNat_eq_natCast, Int.ofNat_zero, Int.add_zero]
      exact sliceIndex_val start (by omega)
    | succ k =>
      have h := ih (start + 1) htail k p hp
      simp only [sliceByteCharacters, List.take_succ_cons, List.flatMap_cons,
        sliceByteChar_bytes, List.singleton_append, List.length_cons, Int.ofNat_eq_natCast, Int.natCast_add,
        Int.natCast_one] at h ⊢
      omega

theorem sliceByteCharacters_singleton (bs : List UInt8) (start : Nat)
    (p : Index × JChar) (hp : p ∈ sliceByteCharacters start bs) :
    ∃ b, denseEncoding.bytes p.2 = [b] := by
  induction bs generalizing start p with
  | nil => cases hp
  | cons b bs ih =>
    simp only [sliceByteCharacters, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨b, sliceByteChar_bytes b⟩
    · exact ih (start + 1) p hp

def sliceSource : JString := ⟨[0xc2, 0x80, 0x61], by decide⟩

def sliceNeedle : JString := ⟨[0x80, 0x61], by decide⟩

def sliceView : TextView JString JChar where
  bytes := fun s => s.bytes
  characters := fun s => if s = sliceSource then
    [(int 1, 0xc2800000), (int 3, 0x61000000)]
    else sliceByteCharacters 0 s.bytes

theorem sliceView_sorted (s : JString) :
    (sliceView.characters s).Pairwise (fun p q => p.1.val < q.1.val) := by
  by_cases hs : s = sliceSource
  · subst s
    change [(int 1, (0xc2800000 : JChar)), (int 3, 0x61000000)].Pairwise
      (fun p q => p.1.val < q.1.val)
    decide
  · simp only [sliceView, hs, ite_false]
    exact sliceByteCharacters_sorted s.bytes 0 (by simpa only [Nat.zero_add] using s.small)

theorem sliceFindExact (xs : List (Index × JChar))
    (hs : xs.Pairwise (fun p q => p.1.val < q.1.val))
    (i : Index) (c : JChar) (hi : (i, c) ∈ xs) :
    xs.find? (fun p => p.1 == i) = some (i, c) := by
  induction xs with
  | nil => cases hi
  | cons p ps ih =>
    rcases List.mem_cons.mp hi with he | hi
    · subst p
      exact List.find?_cons_of_pos (by simp only [beq_self_eq_true])
    · have hlt := (List.pairwise_cons.mp hs).1 (i, c) hi
      have hne : ¬ (p.1 == i) = true := by
        intro he
        have he' : p.1 = i := eq_of_beq he
        rw [he'] at hlt
        exact Int.lt_irrefl _ hlt
      rw [List.find?_cons_of_neg (p := fun q : Index × JChar => q.1 == i) (a := p) (l := ps) hne]
      exact ih (List.pairwise_cons.mp hs).2 hi

def sliceText : SearchStringOps JString JChar Unit where
  ncodeunits := fun s => int (Int.ofNat s.bytes.length)
  iterationBound := fun s => s.bytes.length
  lastindex := fun s => .ok (lastIndex sliceView s)
  nextind := fun s i => .ok (nextPosition sliceView s i)
  prevind := fun s i => .ok (prevPosition sliceView s i)
  isvalid := fun s i => .ok ((sliceView.characters s).any (fun p => p.1 == i))
  getindex := fun s i => match (sliceView.characters s).find? (fun p => p.1 == i) with
    | none => .error ()
    | some p => .ok p.2
  iterate := fun s i => match (sliceView.characters s).find? (fun p => p.1 == i) with
    | none => .ok none
    | some p => .ok (some (p.2, nextPosition sliceView s i))
  boundsError := fun _ _ => ()
  stringIndexError := fun _ _ => ()
  somethingError := ()

theorem sliceText_laws : Utf8TextLaws sliceText sliceView denseNcu denseEncoding := by
  refine {
    sizeFits := ?_
    ncodeunits := denseMemoryLengthVal
    iterationBound := fun _ => Nat.le_refl _
    sorted := sliceView_sorted
    indices := ?_
    nonempty := ?_
    first := ?_
    lastindex := fun _ => rfl
    isvalid := fun _ _ => rfl
    getindex := ?_
    nextind := fun _ _ _ => rfl
    prevind := fun _ _ _ => rfl
    iterate := ?_
    concatenation := ?_
    offsets := ?_
    standalone := ?_ }
  · intro s
    have h := denseMemoryLengthBounds s
    have hmax : (2 : Int) ^ 62 ≤ IntTy.max .i64 := by decide
    exact Int.le_trans (Int.le_of_lt h.2) hmax
  · intro s p hp
    by_cases hs : s = sliceSource
    · subst s
      change p ∈ [(int 1, (0xc2800000 : JChar)), (int 3, 0x61000000)] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> decide
    · simp only [sliceView, hs, ite_false] at hp
      have h := sliceByteCharacters_bounds s.bytes 0
        (by simpa only [Nat.zero_add] using s.small) p hp
      change 1 ≤ p.1.val ∧ p.1.val < Int.ofNat s.bytes.length + 1
      simp only [Int.ofNat_eq_natCast, Int.ofNat_zero, Int.zero_add] at h ⊢
      omega
  · intro s
    by_cases hs : s = sliceSource
    · subst s; rfl
    · simp only [sliceView, hs, ite_false]
      cases s.bytes <;> rfl
  · intro s p hp
    by_cases hs : s = sliceSource
    · subst s
      have he : (int 1, (0xc2800000 : JChar)) = p := Option.some.inj hp
      rw [← he]
    · simp only [sliceView, hs, ite_false] at hp
      cases hb : s.bytes with
      | nil => simp only [hb, sliceByteCharacters, List.head?_nil] at hp; cases hp
      | cons b bs =>
        rw [hb] at hp
        have he : (sliceIndex 0, sliceByteChar b) = p := Option.some.inj hp
        rw [← he]
        rfl
  · intro s i c hi
    change (match (sliceView.characters s).find? (fun p => p.1 == i) with
      | none => Except.error () | some p => Except.ok p.2) = .ok c
    rw [sliceFindExact _ (sliceView_sorted s) i c hi]
  · intro s i c hi
    change (match (sliceView.characters s).find? (fun p => p.1 == i) with
      | none => Except.ok none
      | some p => Except.ok (some (p.2, nextPosition sliceView s i))) = _
    rw [sliceFindExact _ (sliceView_sorted s) i c hi]
  · intro s
    by_cases hs : s = sliceSource
    · subst s; decide
    · simp only [sliceView, hs, ite_false]
      exact sliceByteCharacters_concat s.bytes 0
  · intro s k p hp
    by_cases hs : s = sliceSource
    · subst s
      cases k with
      | zero =>
        have he : (int 1, (0xc2800000 : JChar)) = p := Option.some.inj hp
        rw [← he]; decide
      | succ k =>
        cases k with
        | zero =>
          have he : (int 3, (0x61000000 : JChar)) = p := Option.some.inj hp
          rw [← he]; decide
        | succ k => cases hp
    · simp only [sliceView, hs, ite_false] at hp ⊢
      have h := sliceByteCharacters_offsets s.bytes 0
        (by simpa only [Nat.zero_add] using s.small) k p hp
      simpa only [Int.ofNat_eq_natCast, Int.ofNat_zero, Int.zero_add] using h
  · intro s p b hp hb hstandalone
    by_cases hs : s = sliceSource
    · subst s
      change p ∈ [(int 1, (0xc2800000 : JChar)), (int 3, 0x61000000)] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · change b ∈ ([0xc2, 0x80] : List UInt8) at hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · change 194 < 128 ∨ 247 < 194 at hstandalone
          omega
        · change 128 < 128 ∨ 247 < 128 at hstandalone
          omega
      · have he : b = 0x61 := by
          change b ∈ ([0x61] : List UInt8) at hb
          exact List.mem_singleton.mp hb
        subst b
        rfl
    · simp only [sliceView, hs, ite_false] at hp
      obtain ⟨byte, hbyte⟩ := sliceByteCharacters_singleton s.bytes 0 p hp
      rw [hbyte] at hb ⊢
      have he := List.mem_singleton.mp hb
      rw [he]

def sliceValid (s : JString) (i : Index) : Bool :=
  (sliceView.characters s).any (fun p => p.1 == i)

theorem sliceValid_iff (s : JString) (i : Index) :
    sliceValid s i = true ↔ validAt sliceView s i := by
  constructor
  · intro h
    obtain ⟨p, hp, hi⟩ := List.any_eq_true.mp h
    have he : p.1 = i := eq_of_beq hi
    refine ⟨p.2, ?_⟩
    rw [← he]
    exact hp
  · rintro ⟨c, hc⟩
    exact List.any_eq_true.mpr ⟨(i, c), hc, by simp only [beq_self_eq_true]⟩

theorem sliceString_eq_bytes (s t : JString) : s = t ↔ s.bytes = t.bytes := by
  constructor
  · intro h; cases h; rfl
  · intro h
    cases s with
    | mk sb hs =>
      cases t with
      | mk tb ht =>
        cases h
        rfl

def sliceResult (s : JString) (i j : Index) : JString :=
  s.slice (i.val - 1).toNat ((nextPosition sliceView s j).val - i.val).toNat

def sliceString (s : JString) (i j : Index) : Except Unit JString :=
  if j.val < i.val then
    if 1 ≤ i.val ∧ i.val ≤ endIndex sliceView s then .ok JuliaLean.Strings.JStr.empty
    else .error ()
  else
    if sliceValid s i = true ∧ sliceValid s j = true then .ok (sliceResult s i j)
    else .error ()

theorem sliceString_laws : SliceLaws sliceView sliceString := by
  refine ⟨fun _ => rfl, ?_⟩
  intro s i j t
  by_cases hempty : j.val < i.val
  · unfold sliceString
    rw [ite_eq_left hempty]
    by_cases hvalid : 1 ≤ i.val ∧ i.val ≤ endIndex sliceView s
    · rw [ite_eq_left hvalid]
      constructor
      · intro h
        have ht := congrArg (fun s : JString => s.bytes) (Except.ok.inj h)
        exact Or.inl ⟨hempty, hvalid.1, hvalid.2, ht.symm⟩
      · intro h
        rcases h with ⟨_, _, _, ht⟩ | ⟨hnonempty, _⟩
        · apply congrArg Except.ok
          exact (sliceString_eq_bytes _ _).mpr ht.symm
        · omega
    · rw [ite_eq_right hvalid]
      constructor
      · intro h; cases h
      · intro h
        rcases h with ⟨_, hlo, hhi, _⟩ | ⟨hnonempty, _⟩
        · exact False.elim (hvalid ⟨hlo, hhi⟩)
        · omega
  · unfold sliceString
    rw [ite_eq_right hempty]
    by_cases hvalid : sliceValid s i = true ∧ sliceValid s j = true
    · rw [ite_eq_left hvalid]
      constructor
      · intro h
        have ht := congrArg (fun s : JString => s.bytes) (Except.ok.inj h)
        exact Or.inr ⟨by omega, (sliceValid_iff s i).mp hvalid.1,
          (sliceValid_iff s j).mp hvalid.2, ht.symm⟩
      · intro h
        rcases h with ⟨hempty', _⟩ | ⟨_, hi, hj, ht⟩
        · exact False.elim (hempty hempty')
        · apply congrArg Except.ok
          exact (sliceString_eq_bytes _ _).mpr ht.symm
    · rw [ite_eq_right hvalid]
      constructor
      · intro h; cases h
      · intro h
        rcases h with ⟨hempty', _⟩ | ⟨_, hi, hj, _⟩
        · exact False.elim (hempty hempty')
        · exact False.elim (hvalid ⟨(sliceValid_iff s i).mpr hi, (sliceValid_iff s j).mpr hj⟩)

def sliceBasic : JuliaLean.base.strings.basic.StringOps
    JString JString JChar UInt8 Unit Unit where
  ncodeunits := sliceText.ncodeunits
  codeunitType := fun _ => ()
  codeunitSize := fun _ => int 1
  codeunit := denseMemoryOps.getindex
  isvalid := sliceText.isvalid
  iterateFirst := fun s => sliceText.iterate s (int 1)
  iterateAt := sliceText.iterate
  iterationBound := sliceText.iterationBound
  thisind := fun _ i => .ok i
  prevind := fun s i _ => sliceText.prevind s i
  nextind := fun s i _ => sliceText.nextind s i
  lastindex := sliceText.lastindex
  getindexSlice := sliceString
  checkbounds := fun _ _ => .error ()
  checkboundsBool := fun _ _ => .ok false
  boundsError := fun _ _ => ()
  stringIndexError := fun _ _ => ()
  methodError := fun _ => ()
  argumentError := fun _ => ()
  tupleTypeError := ()
  isBoundsError := fun _ => true
  characters := fun s => .ok ((sliceView.characters s).map (·.2))
  sameReference := fun s t => decide (s = t)
  equalChar := fun c d => decide (c = d)
  lessChar := fun c d => decide (c < d)

def sliceCfg : DenseStringSearch JString JString JString JString Unit where
  source := sliceText
  pattern := sliceText
  sourceBytes := denseMemoryOps
  patternBytes := denseMemoryOps.toByteOps
  codeunitsSource := id
  codeunitsPattern := id
  chars := ⟨fun c => .ok c, fun c => .ok (denseNcu c)⟩
  sourceBasic := sliceBasic

theorem sliceCfg_laws : DenseLaws sliceCfg sliceView sliceView
    denseMemoryView denseMemoryView denseEncoding := by
  refine {
    source := sliceText_laws
    pattern := sliceText_laws
    chars := fun _ => rfl
    toChar := fun _ => rfl
    codeunits := ⟨denseMemoryLaws, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl)⟩
    patternBytes := denseMemoryByteLaws
    patternFirst := fun _ => rfl
    patternContents := fun _ => rfl
    patternValues := fun _ => rfl
    sizeof := ?_ }
  intro s
  change wrapInt .i64
    ((int (Int.ofNat s.bytes.length)).val * (int 1).val) = Int.ofNat s.bytes.length
  rw [denseMemoryLengthVal, denseInt1, Int.mul_one]
  exact denseMemoryLengthVal s

theorem sliceIndexOne :
    denseIndex sliceCfg indexOps sliceSource sliceNeedle (int 1) = pure (int 2) := by
  unfold denseIndex searchindexDense
  have hp : sliceCfg.pattern.lastindex sliceNeedle = .ok (int 2) := rfl
  rw [hp]
  simp only [denseBindLiftOk]
  change searchindexBytes denseByteOps denseByteOps
    (fun b a i => findnextUInt8 denseMemoryOps indexOps b a i) indexOps
    denseHay denseNeedle (int 1) = pure (int 2)
  have hfirst : denseByteOps.firstindex denseHay = int 1 := rfl
  have hslen : denseByteOps.length denseHay = int 3 := rfl
  have htlen : denseByteOps.length denseNeedle = int 2 := rfl
  have hsentinel : int 1 - int 1 = int 0 := by decide
  have hstart : int 1 - int 0 = int 1 := by decide
  have hend : int 3 + int 1 = int 4 := by decide
  have hwidth : int 3 - int 2 = int 1 := by decide
  have hlast : vectorNth denseByteOps denseNeedle (int 2) = .ok (0x61 : UInt8) := by decide
  unfold searchindexBytes
  simp only [hfirst, hslen, htlen, hsentinel, hstart, hend, hwidth, indexOps,
    denseBindLiftOk, denseInt0, denseInt1, denseInt2, denseInt4, hlast]
  rw [denseMaskComputed]
  exact denseForwardLoop

theorem sliceNextOne :
    (denseNext sliceCfg indexOps sliceNeedle sliceSource (int 1)).run =
      some (.ok (some denseRange23)) := by
  change (denseRange sliceCfg sliceSource sliceNeedle (int 1)).run = _
  unfold denseRange searchRange
  rw [sliceIndexOne]
  rfl

theorem sliceAtInteriorError :
    sliceString sliceSource (int 2) (int 3) = .error () := by
  decide

theorem StringsFindnextInsideChar_refuted : ¬ JuliaLean.Proofs.base.strings.search.FindnextMatches := by
  intro h
  have result := h JString JString Unit sliceCfg sliceView sliceView denseMemoryView
    denseMemoryView denseNcu denseEncoding sliceString sliceCfg_laws sliceString_laws
    (fun _ => rfl) sliceNeedle sliceSource (int 1) denseRange23 sliceNextOne
  change sliceString sliceSource (int 2) (int 3) = .ok sliceNeedle at result
  rw [sliceAtInteriorError] at result
  cases result

end JuliaLean.ChatGPT.Batch9.Group15

end

namespace JuliaLean.Proofs.base.strings.search

open JuliaLean.Registry

def entries : List Entry := [
  { id := "strings-search-dense-byte-forward", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},Int8},::DenseInt8,::Integer)", "findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},UInt8},::DenseUInt8,::Integer)"],
    statement := "Dense signed and unsigned byte findnext returns the first match at or after the start, rejects a start below the array, and preserves Int conversion errors.",
    source := "findnext contract and byte-array indexing invariant; base/strings/search.jl:168-180",
    status := .proven, prop := ``DenseByteForwardSpec,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group2.StringsSearchDenseByteForward_proven },
  { id := "strings-search-dense-byte-reverse", juliaFile := "base/strings/search.jl",
    juliaFns := ["findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},Int8},::DenseInt8,::Integer)", "findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},UInt8},::DenseUInt8,::Integer)"],
    statement := "Dense signed and unsigned byte findprev returns the last match at or before the start, rejects a start above the array, and preserves Int conversion errors.",
    source := "findprev contract and byte-array indexing invariant; base/strings/search.jl:232-244",
    status := .proven, prop := ``DenseByteReverseSpec,
    thm := some ``JuliaLean.ChatGPT.Batch6.Group2.StringsSearchDenseByteReverse_proven },
  { id := "strings-search-predicate-forward", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Function,::AbstractString,::Integer)"],
    statement := "Predicate findnext returns exactly the least accepted character index at or after a valid start, or nothing when no character is accepted. Primitive iteration is constrained only at valid character starts, leaving invalid/out-of-bounds iteration unrestricted. The actual basic.jl indexing models remain the callees.",
    source := "findnext contract; base/strings/search.jl:343-354", status := .refuted,
    prop := ``Round3.PredicateForwardSpec, thm := some ``predicateForwardSpec_refuted,
    issue := "#54584 (related); no exact duplicate found. Queries: site:github.com/JuliaLang/julia/issues typemax(Int) findnext AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/pull ncodeunits findnext StringIndexError overflow; site:github.com/JuliaLang/julia/issues ncodeunits findnext StringIndexError",
    notes := "Julia repro: repro/strings-search-predicate-forward.jl. ncodeunits(s)+1 wraps when ncodeunits(s) is typemax(Int)." },
  { id := "strings-search-predicate-reverse", juliaFile := "base/strings/search.jl",
    juliaFns := ["findprev(::Function,::AbstractString,::Integer)"],
    statement := "Predicate findprev returns exactly the greatest accepted character index at or before a valid start, or nothing when no character is accepted. Primitive iteration is constrained only at valid character starts, leaving invalid/out-of-bounds iteration unrestricted. The actual basic.jl indexing models remain the callees. Accepted one-past-end start explicitly returns .ok none.",
    source := "findprev contract; base/strings/search.jl:668-679", status := .refuted,
    prop := ``Round3.PredicateReverseSpec, thm := some ``predicateReverseSpec_refuted,
    issue := "#54584 (related); PR #35742 (related); no exact duplicate found. Queries: site:github.com/JuliaLang/julia/issues typemax(Int) findprev AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/pull typemax(Int) findprev AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/issues ncodeunits findprev StringIndexError",
    notes := "Julia repro: repro/strings-search-predicate-reverse.jl. ncodeunits(s)+1 wraps when ncodeunits(s) is typemax(Int)." },
  { id := "strings-search-predicate-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Function,::AbstractString,::Integer)", "findprev(::Function,::AbstractString,::Integer)"],
    statement := "Predicate search returns an error when `Int(i)` conversion fails, when the converted start lies outside the directional domain, or when it lies inside a character's byte sequence. No specific error type is required, and the maximum virtual-string length remains covered.",
    source := "base/array.jl:2441-2451,2629-2639; base/strings/search.jl:343-354,668-679; Strings manual, Unicode and UTF-8", status := .proven, prop := ``Round7.PredicateStartErrorsAnyErrorSpec, thm := some ``predicateStartErrorsAnyErrorSpec_proven },
  { id := "strings-search-predicate-error-propagation", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Function,::AbstractString,::Integer)", "findprev(::Function,::AbstractString,::Integer)"],
    statement := "A predicate exception at the first tested position after a false-only prefix is returned unchanged in either search direction. Primitive iteration is constrained only at valid character starts, leaving invalid/out-of-bounds iteration unrestricted. The actual basic.jl indexing models remain the callees.",
    source := "generic Function call semantics; base/strings/search.jl:350,675", status := .refuted,
    prop := ``Round3.PredicateErrorSpec, thm := some ``predicateErrorSpec_refuted,
    issue := "#54584 (related); PR #35742 (related); no exact duplicate found. Queries: site:github.com/JuliaLang/julia/issues typemax(Int) findprev AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/pull typemax(Int) findprev AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/issues ncodeunits findprev StringIndexError",
    notes := "Julia repro: repro/strings-search-predicate-error-propagation.jl. ncodeunits(s)+1 wraps when ncodeunits(s) is typemax(Int), so valid start 1 is rejected before the predicate runs." },
  { id := "strings-search-forward-character-iterator", juliaFile := "base/strings/search.jl",
    juliaFns := ["FwCharPosIter(::UTF8String,::AbstractChar)", "iterate(::FwCharPosIter,::Int)", "try_next"],
    statement := "Forward character-position iteration yields the least complete matching character from a valid start and returns nothing exactly when no such character remains.",
    source := "character-position iterator invariant; base/strings/search.jl:54-93,138-141", status := .todo, prop := ``ForwardIteratorSpec, thm := none,
    notes := "The supplied counterexample uses reinterpret(Char, UInt32(0xc2410000)), an artificially constructed malformed character outside ordinary public input. No Julia bug is claimed; the property remains open for ordinary character inputs." },
  { id := "strings-search-reverse-character-iterator", juliaFile := "base/strings/search.jl",
    juliaFns := ["RvCharPosIter(::UTF8String,::AbstractChar)", "iterate(::RvCharPosIter,::Int)", "try_next"],
    statement := "Reverse character-position iteration yields the greatest complete matching character at or before a valid start and returns nothing exactly when none remains.",
    source := "character-position iterator invariant; base/strings/search.jl:105-141", status := .todo, prop := ``ReverseIteratorSpec, thm := none,
    notes := "The supplied counterexample uses reinterpret(Char, UInt32(0xc2410000)), an artificially constructed malformed character outside ordinary public input. No Julia bug is claimed; the property remains open for ordinary character inputs." },
  { id := "strings-search-character-extrema", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)", "findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)"],
    statement := "Character findnext and findprev return the first or last matching decoded character at valid string indices, including for malformed input bytes.",
    source := "findnext/findprev character docstrings; base/strings/search.jl:143-166,209-230,510-512,824-826", status := .todo, prop := ``CharSearchSpec, thm := none,
    notes := "The supplied counterexample uses reinterpret(Char, UInt32(0xc2410000)), an artificially constructed malformed character outside ordinary public input. No Julia bug is claimed; the property remains open for ordinary character inputs." },
  { id := "strings-search-character-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)", "findprev(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String,::Integer)"],
    statement := "Forward Char search rejects a start inside a character; both Char directions throw BoundsError only at starts outside their source-checked bounds.",
    source := "explicit BoundsError and StringIndexError sites; base/strings/search.jl:148-160,214-220", status := .todo, prop := ``CharStartErrorsSpec, thm := none,
    notes := "Statement defect: TextLaws allows ncodeunits(s) = typemax(Int), so ncodeunits(s)+1 wraps and the early sentinel branch returns nothing at typemin(Int). A strict length bound is needed. This maximum-length model witness is not a constructible-string Julia bug." },
  { id := "strings-search-all-character-matches", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar},::UTF8String)"],
    statement := "Character findall returns all and only the matching character indices in increasing order, including in malformed UTF-8 strings.",
    source := "findall contract and character-index invariant; base/strings/search.jl:272-284", status := .todo, prop := ``FindallCharSpec, thm := none,
    notes := "The supplied counterexample uses reinterpret(Char, UInt32(0xc2410000)), an artificially constructed malformed character outside ordinary public input. No Julia bug is claimed; the property remains open for ordinary character inputs." },
  { id := "strings-search-forward-first-range", juliaFile := "base/strings/search.jl",
    juliaFns := ["_searchindex(::DenseUTF8String,::DenseUTF8String,::Integer)", "_search", "findnext(::AbstractString,::AbstractString,::Integer)"],
    statement := "String findnext returns exactly the earliest complete match range at or after a valid start and returns nothing exactly when no matching range exists.",
    source := "findnext docstring base/strings/search.jl:481-507", status := .refuted, prop := ``DenseForwardSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchForwardFirstRange_refuted,
    issue := "No exact duplicate found; #25997 is related. Paced gh searches: issues/prs findfirst invalid UTF-8; issues _searchindex. Details: bugs/strings-findnext-inside-char.yaml.",
    notes := "Needle bytes [0x80,0x61] match haystack bytes [0xc2,0x80,0x61] at 2:3, beginning inside a decoded character. Existing bug record: bugs/strings-findnext-inside-char.yaml." },
  { id := "strings-findnext-inside-char", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractString,::AbstractString,::Integer)", "findfirst(::AbstractString,::AbstractString)"],
    statement := "Every range returned by string findnext indexes the complete needle: slicing the haystack by that range succeeds and equals the needle, including for invalid input bytes.",
    source := "findnext docstring base/strings/search.jl:489-493", status := .refuted, prop := ``FindnextMatches, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsFindnextInsideChar_refuted,
    issue := "No exact duplicate found; #25997 is related. Paced gh searches: issues/prs findfirst invalid UTF-8; issues _searchindex. Details: bugs/strings-findnext-inside-char.yaml.",
    notes := "Needle bytes [0x80,0x61] match haystack bytes [0xc2,0x80,0x61] at 2:3; slicing that range rejects its interior-character start. Existing bug record: bugs/strings-findnext-inside-char.yaml." },
  { id := "strings-search-first-last-string", juliaFile := "base/strings/search.jl",
    juliaFns := ["findfirst(::AbstractString,::AbstractString)", "findlast(::AbstractString,::AbstractString)"],
    statement := "String findfirst and findlast return the earliest and latest complete pattern ranges, including the empty-pattern range at lastindex for an empty string.",
    source := "findfirst/findlast docstrings base/strings/search.jl:286-302,553-569", status := .refuted, prop := ``DenseFirstLastSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchFirstLastString_refuted,
    issue := "No exact duplicate found; #25997 is related. Paced gh searches: issues/prs findfirst invalid UTF-8; issues _searchindex. Details: bugs/strings-findnext-inside-char.yaml.",
    notes := "The first-match conjunct fails for needle bytes [0x80,0x61] and haystack bytes [0xc2,0x80,0x61]: 2:3 is returned without a complete character-sequence occurrence. Existing bug record: bugs/strings-findnext-inside-char.yaml." },
  { id := "strings-findprev-empty-end", juliaFile := "base/strings/search.jl",
    juliaFns := ["findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "Every range returned by findprev matches the pattern and ends at or before the requested start.",
    source := "findprev docstring base/strings/search.jl:799-807", status := .refuted, prop := ``FindprevLatest,
    thm := some ``findprevLatest_refuted,
    issue := "#39940 (related), PR #40120 (related); queries: gh search issues --repo JuliaLang/julia findprev; gh search prs --repo JuliaLang/julia findprev",
    notes := "bug record: bugs/strings-findprev-empty-end.yaml; Julia repro: repro/strings-findprev-empty-end.jl." },
  { id := "strings-search-reverse-last-range", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::DenseUTF8String,::DenseUTF8String,::Integer)", "_rsearch", "findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "For nonempty needles, string findprev returns exactly the latest complete match whose inclusive end is at or before the start, or nothing if none exists.",
    source := "findprev docstring base/strings/search.jl:798-821", status := .refuted, prop := ``DenseReverseSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchReverseLastRange_refuted,
    issue := "No exact duplicate found; #25997 is related. Paced gh searches: issues/prs findfirst invalid UTF-8; issues _searchindex. Details: bugs/strings-findnext-inside-char.yaml.",
    notes := "Reverse search returns 2:3 for needle bytes [0x80,0x61] in haystack bytes [0xc2,0x80,0x61], beginning inside a decoded character. Existing bug record: bugs/strings-findnext-inside-char.yaml." },
  { id := "strings-search-dense-reverse-empty-integer", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::DenseUTF8String,::DenseUTF8String,::Integer)", "_rsearch", "findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "For an empty pattern, reverse search returns 0:-1 when i>sizeof(s), 1:0 when i=0, and i:i-1 otherwise.",
    source := "findprev docstring and empty-pattern contract; base/strings/search.jl:705-719,799-821", status := .proven, prop := ``DenseReverseEmptySpec, thm := some ``denseReverseEmptySpec_proven },
  { id := "strings-search-empty-pattern-start", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractString,::AbstractString,::Integer)", "findprev(::AbstractString,::AbstractString,::Integer)"],
    statement := "An empty string pattern matches the empty range at the requested valid start, including one past the final code unit.",
    source := "empty-pattern invariant and findnext/findprev docs; base/strings/search.jl:365-373,705-719", status := .refuted, prop := ``EmptyPatternStartSpec, thm := some ``emptyPatternStartSpec_refuted,
    issue := "#39940 (related), PR #40120 (related)",
    notes := "bug record: bugs/strings-findprev-empty-end.yaml; Julia repro: repro/strings-findprev-empty-end.jl." },
  { id := "strings-search-string-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractString,::AbstractString,::Integer)"],
    statement := "String-pattern findnext throws BoundsError outside [1,ncodeunits+1]; this entry makes no error claim about reverse starts or valid interior byte positions.",
    source := "byte-search bounds check; base/strings/search.jl:395-408", status := .todo, prop := ``StringStartErrorsSpec, thm := none,
    notes := "Statement/interface defect: the byte branch returns sourceBytes.boundsError on CodeUnits while the proposition requires source.boundsError on String; no carrier-coherence law equates them. Both are BoundsError in Julia. The character branch also needs a strict length bound. No runtime bug is claimed." },
  { id := "strings-search-byte-pattern-first", juliaFile := "base/strings/search.jl",
    juliaFns := ["_nthbyte(::AbstractVector,index)", "_searchindex(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "_search", "findnext(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "Byte-vector findnext returns the first matching sequence range at or after the start, or nothing if none exists, for arbitrary offset axes and mixed signed/unsigned byte element types.",
    source := "byte-vector findnext docstring base/strings/search.jl:529-551", status := .refuted, prop := ``BytePatternForwardSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchBytePatternFirst_refuted,
    issue := "No exact duplicate found; #37280 is related. Paced gh searches: issues/prs findnext offset; issues byte search offset; issues _searchindex; prs offset search. Details: bugs/strings-search-offset-zero-byte.yaml.",
    notes := "A one-byte UInt8 source indexed at 0:0 loses its only forward match for UInt8[0x41] searched from 0. Release and pinned-nightly evidence: bugs/strings-search-offset-zero-byte.yaml." },
  { id := "strings-search-byte-pattern-last", juliaFile := "base/strings/search.jl",
    juliaFns := ["_rsearchindex(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "_rsearch", "findprev(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "Byte-vector findprev returns the last nonempty sequence range ending at or before the start, or nothing if none exists, for arbitrary offset axes.",
    source := "byte-vector findprev docstring base/strings/search.jl:843-862", status := .refuted, prop := ``BytePatternReverseSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchBytePatternLast_refuted,
    issue := "No exact duplicate found; #37280 is related. Paced gh searches: issues/prs findnext offset; issues byte search offset; issues _searchindex; prs offset search. Details: bugs/strings-search-offset-zero-byte.yaml.",
    notes := "A one-byte UInt8 source indexed at 0:0 raises BoundsError for UInt8[0x41] searched backward from 0 because the normalized scalar start is 1. Release and pinned-nightly evidence: bugs/strings-search-offset-zero-byte.yaml." },
  { id := "strings-search-first-last-byte-pattern", juliaFile := "base/strings/search.jl",
    juliaFns := ["findfirst(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}})", "findlast(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}})"],
    statement := "Byte-vector findfirst and findlast return the earliest and latest complete pattern ranges, including the empty-pattern range selected from lastindex on an empty vector.",
    source := "findfirst/findlast byte-vector docstrings base/strings/search.jl:323-340,571-586", status := .refuted, prop := ``BytePatternFirstLastSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchFirstLastBytePattern_refuted,
    issue := "No exact duplicate found; #37280 is related. Paced gh searches: issues/prs findnext offset; issues byte search offset; issues _searchindex; prs offset search. Details: bugs/strings-search-offset-zero-byte.yaml.",
    notes := "The first-match conjunct fails for a one-byte UInt8 source indexed at 0:0: findfirst loses its only match for UInt8[0x41]. Release and pinned-nightly evidence: bugs/strings-search-offset-zero-byte.yaml." },
  { id := "stringscova-search-offset-pattern-range", juliaFile := "base/strings/search.jl",
    juliaFns := ["_search", "_rsearch", "findnext/findprev/findfirst/findlast byte-vector wrappers"],
    statement := "Every returned nonempty byte-pattern range has the pattern length, independently of both vectors first indices.",
    source := "documented match-range invariant; base/strings/search.jl:468-479,785-796", status := .todo, prop := ``OffsetPatternRangeSpec, thm := none,
    notes := "Model defect: MatchRange stores raw endpoints while Julia UnitRange normalizes the descending stop in the supplied typemin(Int)-axis witness. Repair range construction through the source-mirrored UnitRange constructor before settling this target. Existing bugs/stringscova-search-offset-pattern-range.yaml records a different offset-pattern witness." },
  { id := "strings-search-byte-empty-pattern-start", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "findprev(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "An empty byte-vector pattern matches the empty range at the requested haystack index, including on offset axes.",
    source := "empty-sequence matching invariant; base/strings/search.jl:401-416,721-734", status := .refuted, prop := ``ByteEmptyPatternSpec, thm := some ``byteEmptyPatternSpec_refuted,
    issue := "No exact duplicate found. Related: #64263 / PR #64279 (nonempty offset-pattern ranges), #39940 / PR #40120 (String empty-findprev at end). Queries: site:github.com/JuliaLang/julia/issues \"empty pattern\" byte vector offset axes findprev; site:github.com/JuliaLang/julia/pull \"empty pattern\" offset byte findprev search.",
    notes := "Julia repro: repro/strings-search-byte-empty-pattern-start.jl. The byte-vector docstrings say \"starting at position start\" (base/strings/search.jl:534, 848). With both arrays empty and haystack axes 0:-1, Julia returns 1:0 from findnext(..., 0) and -1:-2 from findprev(..., 0). The source accepts normalized forward indices through m+1 (1075-1076), but reverse only through m (1165-1166); maintainers may choose to clarify the docs."
  },
  { id := "strings-search-byte-pattern-start-errors", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)", "findprev(::AbstractVector{<:Union{Int8,UInt8}},::AbstractVector{<:Union{Int8,UInt8}},::Integer)"],
    statement := "Byte-pattern findnext throws BoundsError before firstindex or after its one-past-end index; findprev throws below firstindex-1, and its one-byte path also throws when the normalized start exceeds lastindex.",
    source := "byte-vector search checks; base/strings/search.jl:401-408,721-734", status := .todo, prop := ``BytePatternStartErrorsSpec, thm := none,
    notes := "Statement defect: the final implication scopes over the preceding conjunction, rather than forming an independent third clause. A one-byte pattern on an empty source at start 1 returns nothing before scalar bounds checks. Parentheses and the empty-source case require review; no documented Julia bug is claimed." },
  { id := "strings-search-occursin-first-match", juliaFile := "base/strings/search.jl",
    juliaFns := ["occursin(::Union{AbstractString,AbstractChar},::AbstractString)", "occursin(haystack)"],
    statement := "String occursin and its fixed-haystack function are true exactly when a complete match exists, agreeing with findfirst returning a match.",
    source := "occursin docstrings base/strings/search.jl:863-911", status := .refuted, prop := ``OccursinSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchOccursinFirstMatch_refuted,
    issue := "No exact duplicate found; #25997 is related. Paced gh searches: issues/prs findfirst invalid UTF-8; issues _searchindex. Details: bugs/strings-findnext-inside-char.yaml.",
    notes := "Byte occurrence is true for needle bytes [0x80,0x61] in haystack bytes [0xc2,0x80,0x61] although no complete character-sequence occurrence exists. Existing bug record: bugs/strings-findnext-inside-char.yaml." },
  { id := "strings-search-all-pattern-ranges", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}},::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}};overlap)"],
    statement := "String-pattern findall returns valid matching ranges in increasing order, disjoint ranges when overlap is false, and every match when overlap is true.",
    source := "findall docstring base/strings/search.jl:607-665", status := .refuted, prop := ``FindallRangeSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchAllPatternRanges_refuted,
    issue := "No exact duplicate found; #25997 is related. Paced gh searches: issues/prs findfirst invalid UTF-8; issues _searchindex. Details: bugs/strings-findnext-inside-char.yaml.",
    notes := "Findall returns [2:3] for needle bytes [0x80,0x61] in haystack bytes [0xc2,0x80,0x61], whose match starts inside a decoded character. Existing bug record: bugs/strings-findnext-inside-char.yaml." },
  { id := "regexunicode-findall-skips-nonempty", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Regex,::AbstractString)", "findall(t::Union{AbstractString, AbstractPattern, AbstractVector{UInt8}}, s::Union{AbstractString, AbstractPattern, AbstractVector{UInt8}}, ; overlap::Bool=false)", "eachmatch(::Regex,::AbstractString)"],
    statement := "Regex findall returns the same ranges as eachmatch; the interface law states eachmatch's ranges are repeated findnext results, including empty matches.",
    source := "findall docstring base/strings/search.jl:619-621; eachmatch contract base/regex.jl", status := .todo, prop := ``FindallRangesOfEachmatch, thm := none,
    notes := "Statement/interface defect: the supplied ASCII-mode regex witness refutes the extra eachmatch error-propagation clause, which the registry prose does not promise. The historical empty-alternative witness is excluded by eachmatchFindnext. The target remains open; no new runtime bug is claimed." },
  { id := "strings-search-zero-byte-extrema", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::typeof(iszero),::DenseUInt8OrInt8,::Integer)", "findprev(::typeof(iszero),::DenseUInt8OrInt8,::Integer)"],
    statement := "The iszero specializations search the full documented Integer-start domain, including conversion errors and out-of-axis bounds; both signed and unsigned implementations call installed memchr and memrchr.",
    source := "iszero byte-pattern invariant; base/strings/search.jl:200-207,264-270", status := .proven, prop := ``ZeroByteSpec, thm := some ``zeroByteSpec_proven },
  { id := "strings-search-abstract-character-wrappers", juliaFile := "base/strings/search.jl",
    juliaFns := ["findnext(::AbstractChar,::AbstractString,::Integer)", "findprev(::AbstractChar,::AbstractString,::Integer)"],
    statement := "AbstractChar wrappers return the first directional equality match, nothing when all tested characters differ, or the first equality/conversion exception, for native and extension AbstractChars, including every Integer codepoint width and user-defined conversion/equality methods; reverse zero and one-past-end starts return nothing.",
    source := "character findnext/findprev contracts; base/strings/search.jl:526-527,840-841; equality base/char.jl:263,270", status := .refuted,
    prop := ``Round5.CharWrapperSpec, thm := some ``charWrapperSpec_refuted,
    issue := "#54584 (related); PR #35742 (related); no exact duplicate found. Queries: site:github.com/JuliaLang/julia/issues typemax(Int) findprev AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/pull typemax(Int) findprev AbstractString ncodeunits overflow; site:github.com/JuliaLang/julia/issues ncodeunits findprev StringIndexError",
    notes := "Julia repro: repro/strings-search-abstract-character-wrappers.jl. ncodeunits(s)+1 wraps when ncodeunits(s) is typemax(Int), rejecting valid start 1 before character comparison." },
  { id := "strings-search-first-last-character", juliaFile := "base/strings/search.jl",
    juliaFns := ["findfirst(::AbstractChar,::AbstractString)", "findlast(::AbstractChar,::AbstractString)"],
    statement := "Character findfirst and findlast return exactly the first and last equal character index or nothing if the character is absent.",
    source := "character findfirst/findlast docstrings; base/strings/search.jl:304-321,588-605", status := .proven,
    prop := ``CharFirstLastSpec, thm := some ``charFirstLastSpec_proven },
  { id := "strings-search-character-occurrence", juliaFile := "base/strings/search.jl",
    juliaFns := ["_searchindex(::AbstractString,::AbstractChar,::Integer)", "occursin(::Union{AbstractString,AbstractChar},::AbstractString)", "in(::Char,::Union{String,SubString{String}})"],
    statement := "Character occursin and dense character membership are true exactly when the decoded character occurs in the string, including malformed input bytes.",
    source := "occursin and character-membership contract; base/strings/search.jl:360-363,386,886-887", status := .todo, prop := ``CharOccursinSpec, thm := none,
    notes := "The supplied counterexample uses reinterpret(Char, UInt32(0xc2410000)), an artificially constructed malformed character outside ordinary public input. No Julia bug is claimed; the property remains open for ordinary character inputs." },
  { id := "strings-search-membership", juliaFile := "base/strings/search.jl",
    juliaFns := ["in(::AbstractChar,::AbstractString)", "in(::UInt8,::DenseUInt8)", "in(::Int8,::DenseInt8)", "in(::AbstractString,::AbstractString)"],
    statement := "Character and byte membership agree with element occurrence; string-in-string rejects the call and directs the caller to occursin.",
    source := "membership invariant and string-containment guidance; base/strings/search.jl:356,913-916", status := .todo, prop := ``MembershipSpec, thm := none,
    notes := "The supplied counterexample uses reinterpret(Char, UInt32(0xc2410000)), an artificially constructed malformed character outside ordinary public input. No Julia bug is claimed; the property remains open for ordinary character inputs." },
  { id := "strings-search-byte-pattern-all", juliaFile := "base/strings/search.jl",
    juliaFns := ["findall(::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}},::Union{AbstractString,AbstractPattern,AbstractVector{UInt8}};overlap)"],
    statement := "Byte-pattern findall returns matching sequence ranges in order, excludes overlap when requested, and includes every match when overlap is enabled.",
    source := "findall byte-vector docstring base/strings/search.jl:607-665", status := .refuted, prop := ``ByteFindallSpec, thm := some ``JuliaLean.ChatGPT.Batch9.Group15.StringsSearchBytePatternAll_refuted,
    issue := "No exact duplicate found; #37280 is related. Paced gh searches: issues/prs findnext offset; issues byte search offset; issues _searchindex; prs offset search. Details: bugs/strings-search-offset-zero-byte.yaml.",
    notes := "Findall with overlap=true returns no ranges for UInt8[0x41] in a matching one-byte UInt8 source indexed at 0:0. Release and pinned-nightly evidence: bugs/strings-search-offset-zero-byte.yaml." }
]

/-! ## Nothing to promise

IteratorSize@102: returns fixed iterator metadata without selecting a search result.
eltype@103: returns the fixed index element type without searching any input.
_nthbyte@392: forwards the unchanged index to codeunit; storage and bounds are the string.jl callee's contract.

The constructors, try_next, vector _nthbyte, and public forwarding methods are
used by the iterator, sequence-search, membership, and public-search statements.
-/

end JuliaLean.Proofs.base.strings.search
