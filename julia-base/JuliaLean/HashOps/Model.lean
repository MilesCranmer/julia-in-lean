import JuliaLean.Core
import JuliaLean.Promotion.Hash

/-!
Models for `base/hashing.jl`, the collection hash methods, and the generic
fallbacks in `base/operators.jl` and `base/number.jl` at Julia master
`bbfa0ce4150`.

Hash bytes are opaque below: the contract needs only that identical byte
streams and seeds make the same primitive call. Integer hashing reuses the
source-level term model in `JuliaLean.Promotion.Hash`.
-/

namespace JuliaLean.HashOps

open JuliaLean JuliaLean.Promotion

/-! ## Hash mixing, `base/hashing.jl:48-77` -/

abbrev HashWord := JInt .u64

def hashXor (x y : HashWord) : HashWord :=
  JInt.wrap .u64 (Int.ofNat (Nat.xor x.val.toNat y.val.toNat))

def hashMixLinear (x h : HashWord) : HashWord := JInt.lit .u64 3 * h - x

def hashFinalizer (x : HashWord) : HashWord :=
  let x := hashXor x (JInt.wrap .u64 (Int.ofNat (x.val.toNat / 2^32)))
  let x := x * JInt.lit .u64 0x63652a4cd374b267
  hashXor x (JInt.wrap .u64 (Int.ofNat (x.val.toNat / 2^33)))

/-! ## Generic `hash(::Real)`, `base/hashing.jl:198-245` -/

abbrev Decomposition := Int × Int × Int

/-- The generic source method, with the integer storage type supplied by the
caller's `decompose` implementation. -/
def hashDecomposed (numTy : IntTy) (d : Decomposition) (h : HTerm) : HTerm :=
  hashReal numTy d h

/-! ## Strings, `base/hashing.jl:101-145,649-654` -/

def utf8 (c : Nat) : List UInt8 :=
  if c < 0x80 then [UInt8.ofNat c]
  else if c < 0x800 then
    [UInt8.ofNat (0xc0 + c / 64), UInt8.ofNat (0x80 + c % 64)]
  else if c < 0x10000 then
    [UInt8.ofNat (0xe0 + c / 4096), UInt8.ofNat (0x80 + (c / 64) % 64),
      UInt8.ofNat (0x80 + c % 64)]
  else
    [UInt8.ofNat (0xf0 + c / 262144), UInt8.ofNat (0x80 + (c / 4096) % 64),
      UInt8.ofNat (0x80 + (c / 64) % 64), UInt8.ofNat (0x80 + c % 64)]

structure Text where
  chars : List Nat
  raw : List UInt8
  byteBacked : Bool
  deriving DecidableEq, Repr

def Text.canonicalBytes (s : Text) : List UInt8 := s.chars.flatMap utf8

/-- `utf8units`: byte-backed strings use `codeunits`; other strings encode the
characters yielded by iteration. -/
def Text.utf8units (s : Text) : List UInt8 :=
  if s.byteBacked then s.raw else s.canonicalBytes

def Text.Valid (s : Text) : Prop := s.byteBacked = true → s.raw = s.canonicalBytes

inductive ByteHash where
  | call (bytes : List UInt8) (seed : Nat)
  deriving DecidableEq, Repr

def hashText (s : Text) (h : Nat) : ByteHash := .call s.utf8units h

/-! ## Annotated strings, `base/strings/annotated.jl:64-67,224-249` -/

structure Annotation where
  label : Nat
  value : Nat
  deriving DecidableEq, Repr

structure AnnotatedText where
  chars : List Nat
  annotations : List Annotation
  deriving DecidableEq, Repr

def annotatedIsequal (a b : AnnotatedText) : Bool :=
  a.chars == b.chars && a.annotations == b.annotations

def cmpChars : List Nat → List Nat → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a < b then -1 else if b < a then 1 else cmpChars as bs

/-- AnnotatedString's `cmp` methods discard annotations. -/
def annotatedCmp (a b : AnnotatedText) : Int := cmpChars a.chars b.chars
def annotatedIsless (a b : AnnotatedText) : Bool := annotatedCmp a b < 0

/-- `UTF8Units` calls `reinterpret(UInt32, char)`. Plain `Char` is isbits; an
`AnnotatedChar` contains a vector and raises `ArgumentError`. -/
def hashNonByteUnderlying (chars : List Nat) (h : Nat) : Except JlError ByteHash :=
  .ok (.call (chars.flatMap utf8) h)

def hashNonByteAnnotated (_ : AnnotatedText) (_ : Nat) : Except JlError ByteHash :=
  .error (.argumentError "Source type for reinterpret must be isbits")

/-! ## Abstract arrays, `base/multidimensional.jl:1995-2123` -/

structure CanonArray where
  axes : List (Int × Int)
  values : List Nat
  deriving DecidableEq, Repr

def mixNat (x h : Nat) : Nat := Nat.xor (3 * h) x
def finalNat (h : Nat) : Nat := Nat.xor h (h / 2^33)

def hashNatList (xs : List Nat) (h : Nat) : Nat := xs.foldl (fun h x => mixNat x h) h

def arrayInitial (a : CanonArray) (h : Nat) : Nat :=
  let h := hashNatList (a.axes.map (fun x => x.1.natAbs)) (Nat.xor h 0x7e2d6fb6448beb77)
  hashNatList (a.axes.map (fun x => x.2.natAbs)) h

def setStream (p : List Nat) (i value : Nat) : List Nat := p.set i value

def mediumStreams (xs : List Nat) (h : Nat) : List Nat :=
  (List.range xs.length).foldl (fun p i =>
    let j := i % 8
    setStream p j (mixNat (xs.getD i 0) (p.getD j h))) (List.replicate 8 h)

def foldStreams (p : List Nat) (h : Nat) : Nat := finalNat (p.foldl (fun h x => mixNat x h) h)

def findPrevDifferent (xs : List Nat) (i value : Nat) : Option Nat :=
  (List.range (i + 1)).reverse.find? (fun j => xs.getD j value != value)

/-- The Fibonacci sampler works backwards, increases the skip every 4096
samples, and after each skip finds the previous value distinct from the last
hashed element (`base/multidimensional.jl:2026-2054`). -/
def fibSamples (xs : List Nat) : Nat → Nat → Nat → Nat → Nat → List (Nat × Nat)
  | 0, _, _, _, _ => []
  | fuel + 1, i, skip, prev, n =>
      match xs[i]? with
      | none => []
      | some value =>
          let sample := (i, value)
          if i < skip then [sample]
          else
            let candidate := i - skip
            let n' := n + 1
            let (skip', prev') := if n' % 4096 = 0 then (skip + prev, skip) else (skip, prev)
            match findPrevDifferent xs candidate value with
            | none => [sample]
            | some j => sample :: fibSamples xs fuel j skip' prev' n'

def longStreams (xs : List Nat) (h : Nat) : List Nat :=
  let samples := if xs.isEmpty then [] else fibSamples xs xs.length (xs.length - 1) 1 1 0
  (List.range samples.length).foldl (fun p i =>
    let sample := samples.getD i (0, 0)
    let j := i % 4
    let old := p.getD j h
    setStream p j (mixNat (mixNat sample.1 old) (mixNat sample.2 old))) (List.replicate 4 h)

/-- `hash_shaped`, including its short, eight-stream, and Fibonacci branches. -/
def hashArray (a : CanonArray) (h : Nat) : Nat :=
  let h := arrayInitial a h
  if a.values.length < 8 then hashNatList a.values h
  else if a.values.length < 32768 then foldStreams (mediumStreams a.values h) h
  else foldStreams (longStreams a.values h) h

/-! ## Tuple, Dict and Set hash shapes -/

def pairContribution (p : Nat × Nat) : Nat := mixNat p.1 (mixNat p.2 0)
def dictHash (pairs : List (Nat × Nat)) (h : Nat) : Nat :=
  mixNat (pairs.foldl (fun acc p => Nat.xor acc (pairContribution p)) 0x6d35bb51952d5539) h

def setHash (values : List Nat) (h : Nat) : Nat :=
  mixNat (values.foldl (fun acc x => Nat.xor acc (mixNat x 0)) 0x852ada37cfe8e0ce) h

/-! ## Generic operator and number fallbacks -/

structure FallbackOps (α : Type) where
  eq : α → α → Bool
  lt : α → α → Bool
  zero : α → α
  one : α → α
  neg : α → α
  add : α → α → α
  mul : α → α → α
  div : α → α → α
  castOne : α → α

def isequalFallback (o : FallbackOps α) (x y : α) : Bool := o.eq x y
def islessFallback (o : FallbackOps α) (x y : α) : Bool := o.lt x y
def cmpFallback (o : FallbackOps α) (x y : α) : Int :=
  if islessFallback o x y then -1 else if islessFallback o y x then 1 else 0
def neFallback (o : FallbackOps α) (x y : α) : Bool := !o.eq x y
def leFallback (o : FallbackOps α) (x y : α) : Bool := o.lt x y || o.eq x y
def geFallback (o : FallbackOps α) (x y : α) : Bool := leFallback o y x
def iszeroFallback (o : FallbackOps α) (x : α) : Bool := o.eq x (o.zero x)
def isoneFallback (o : FallbackOps α) (x : α) : Bool := o.eq x (o.one x)
def signbitFallback (o : FallbackOps α) (x : α) : Bool := o.lt x (o.zero x)
def absFallback (o : FallbackOps α) (x : α) : α := if signbitFallback o x then o.neg x else x
def signFallback (o : FallbackOps α) (x : α) : α :=
  if o.lt x (o.zero x) then o.neg (o.one x)
  else if o.lt (o.zero x) x then o.one x else x
def zeroFallback (o : FallbackOps α) (x : α) : α := o.zero x
def oneFallback (o : FallbackOps α) (x : α) : α := o.one x
def oneunitFallback (o : FallbackOps α) (x : α) : α := o.castOne (o.one x)
def muladdFallback (o : FallbackOps α) (x y z : α) : α := o.add (o.mul x y) z
def invFallback (o : FallbackOps α) (x : α) : α := o.div (o.one x) x

inductive FmaResult (α : Type) where
  | ok (value : α)
  | noOperation
  deriving DecidableEq, Repr

/-- `fma(::T,::T,::T)` catch-all (`base/promotion.jl:657`) and its Integer
specialization at line 658. -/
def fmaNumberFallback (_ _ _ : α) : FmaResult α := .noOperation
def fmaIntegerFallback (o : FallbackOps α) (x y z : α) : FmaResult α :=
  .ok (o.add (o.mul x y) z)

/-- `literal_pow`, `base/intfuncs.jl:470-489`. -/
def literalPowFallback (o : FallbackOps α) (pow : α → Int → α) (x : α) (p : Int) : α :=
  if p < 0 then pow (invFallback o x) (-p) else pow x p

def literalPowHW (o : FallbackOps α) (pow : α → Int → α) (x : α) (p : Int) : α :=
  if p = 0 then oneFallback o x
  else if p = 1 then x
  else if p = 2 then o.mul x x
  else if p = 3 then o.mul (o.mul x x) x
  else if p = -1 then invFallback o x
  else if p = -2 then let i := invFallback o x; o.mul i i
  else literalPowFallback o pow x p

/-! ## `widen`, `base/operators.jl:955-977`, `base/int.jl:911-918` -/

def widenTarget : IntTy → Option IntTy
  | .i8 => some .i16 | .i16 => some .i32 | .i32 => some .i64 | .i64 => some .i128
  | .u8 => some .u16 | .u16 => some .u32 | .u32 => some .u64 | .u64 => some .u128
  | .i128 | .u128 => none

def widenAdd (t : IntTy) (x y : JInt t) : Int :=
  match widenTarget t with
  | some s => wrapInt s (x.val + y.val)
  | none => x.val + y.val

def widenSub (t : IntTy) (x y : JInt t) : Int :=
  match widenTarget t with
  | some s => wrapInt s (x.val - y.val)
  | none => x.val - y.val

end JuliaLean.HashOps
