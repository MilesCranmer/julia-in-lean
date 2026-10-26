import JuliaLean.HashOps.Proofs
import JuliaLean.Promotion.Hash
import JuliaLean.MissingChar.Char
import JuliaLean.ParsePrint.Bits

/-!
Executable models for `base/hashing.jl` at master `bbfa0ce4150`. The byte
hash uses the array method's exact branches and 48-byte loop. Pointer and iterator
overloads are stated against the same byte sequence, which is their documented
value-level invariant.
-/

namespace JuliaLean.IntFuncsCov.Hashing

open JuliaLean
open JuliaLean.ParsePrint

abbrev Word := JInt .u64

def wxor (a b : Word) : Word := bxor a b
def wor (a b : Word) : Word := bor a b

def mulParts (a b : Word) : Word × Word :=
  let p : Int := a.val * b.val
  (JInt.lit .u64 (p / 2 ^ 64), JInt.lit .u64 p)

def hashMix (a b : Word) : Word :=
  let p := mulParts a b
  wxor p.1 p.2

def hashMixLinear (x h : Word) : Word := JInt.lit .u64 3 * h - x

def hashFinalizer (x : Word) : Word :=
  let x := wxor x (shr x 32)
  let x := x * JInt.lit .u64 0x63652a4cd374b267
  wxor x (shr x 33)

def HashPrimitiveBehavior : Prop :=
  (∀ a b : Word, mulParts a b =
    (JInt.lit .u64 (a.val * b.val / 2 ^ 64), JInt.lit .u64 (a.val * b.val))) ∧
  (∀ a b : Word, hashMix a b = wxor (mulParts a b).1 (mulParts a b).2) ∧
  (∀ x h : Word, hashMixLinear x h = JInt.lit .u64 3 * h - x) ∧
  (∀ x : Word, hashFinalizer x =
    let x := wxor x (shr x 32)
    let x := x * JInt.lit .u64 0x63652a4cd374b267
    wxor x (shr x 33))

theorem hashPrimitiveBehavior : HashPrimitiveBehavior := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

structure IntegerCodeUnits where
  value : Int
  numBytes : Nat
  deriving DecidableEq

def integerCodeUnits (x : Int) : IntegerCodeUnits :=
  let u := x.natAbs
  ⟨u, max (((u.log2 + if u = 0 then 0 else 1) + 7) / 8) 1⟩

def integerCodeUnit (u : IntegerCodeUnits) (i : Nat) : UInt8 :=
  UInt8.ofNat ((u.value.natAbs / 2 ^ (8 * (i - 1))) % 256)

def integerBytes (x : Int) : List UInt8 :=
  let u := integerCodeUnits x
  (List.range u.numBytes).map fun i => integerCodeUnit u (i + 1)

def HashIntegerUnitsBehavior : Prop :=
  (∀ x : Int, (integerCodeUnits x).numBytes =
    max (((x.natAbs.log2 + if x.natAbs = 0 then 0 else 1) + 7) / 8) 1) ∧
  (∀ (x : Int) (i : Nat), integerCodeUnit (integerCodeUnits x) (i + 1) =
    UInt8.ofNat ((x.natAbs / 2 ^ (8 * i)) % 256)) ∧
  (∀ x : Int, (integerBytes x).length = (integerCodeUnits x).numBytes)

theorem hashIntegerUnitsBehavior : HashIntegerUnitsBehavior := by
  refine ⟨fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro x
  simp [integerBytes]

def loadLE (bytes : List UInt8) (idx n : Nat) : Word :=
  JInt.lit .u64 ((List.range n).foldl
    (fun acc k => acc + (bytes.getD (idx + k) 0).toNat * 2 ^ (8 * k)) 0)

def process48 (secret : Word × Word × Word × Word) :
    List UInt8 → Nat → Nat → Word → Word → Word → Word × Word × Word × Nat × Nat
  | bytes, pos, remaining, seed, see1, see2 =>
    if h : 48 < remaining then
      process48 secret bytes (pos + 48) (remaining - 48)
        (hashMix (wxor (loadLE bytes pos 8) secret.1)
          (wxor (loadLE bytes (pos + 8) 8) seed))
        (hashMix (wxor (loadLE bytes (pos + 16) 8) secret.2.1)
          (wxor (loadLE bytes (pos + 24) 8) see1))
        (hashMix (wxor (loadLE bytes (pos + 32) 8) secret.2.2.1)
          (wxor (loadLE bytes (pos + 40) 8) see2))
    else (seed, see1, see2, pos, remaining)
termination_by bytes pos remaining seed see1 see2 => remaining
decreasing_by omega

def hashBytes (bytes : List UInt8) (seed : Word)
    (secret : Word × Word × Word × Word) : Word :=
  let n := bytes.length
  let seed := wxor seed (hashMix (wxor seed secret.2.2.1) secret.2.1)
  let init : Word := JInt.lit .u64 0
  let result := process48 secret bytes 0 n seed seed seed
  let seed := if 48 < n then wxor (wxor result.1 result.2.1) result.2.2.1 else result.1
  let pos := result.2.2.2.1
  let remaining := result.2.2.2.2
  let (seed, a, b) :=
    if n ≤ 16 then
      if 4 ≤ n then
        let seed := wxor seed (JInt.lit .u64 n)
        if 8 ≤ n then (seed, loadLE bytes 0 8, loadLE bytes (n - 8) 8)
        else (seed, loadLE bytes 0 4, loadLE bytes (n - 4) 4)
      else if 0 < n then
        (seed,
          wor (shl (JInt.lit .u64 (bytes.getD 0 0).toNat) 45)
            (JInt.lit .u64 (bytes.getD (n - 1) 0).toNat),
          JInt.lit .u64 (bytes.getD (n / 2) 0).toNat)
      else (seed, init, init)
    else
      let seed := if 16 < remaining then
        let seed := hashMix (wxor (loadLE bytes pos 8) secret.2.2.1)
          (wxor (loadLE bytes (pos + 8) 8) seed)
        if 32 < remaining then hashMix (wxor (loadLE bytes (pos + 16) 8) secret.2.2.1)
          (wxor (loadLE bytes (pos + 24) 8) seed) else seed
        else seed
      (seed, wxor (loadLE bytes (n - 16) 8) (JInt.lit .u64 remaining),
        loadLE bytes (n - 8) 8)
  let a := wxor a secret.2.1
  let b := wxor b seed
  let p := mulParts a b
  hashMix (wxor p.2 secret.2.2.2) (wxor (wxor p.1 secret.2.1) (JInt.lit .u64 remaining))

def hashBytesArray := hashBytes
def hashBytesPointer := hashBytes
def hashBytesIterator := hashBytes

def concatShift (low high : Word) (shiftBytes : UInt8) : Word :=
  let shift := shiftBytes.toNat * 8 % 64
  wor (shr low shift) (shl high (64 - shift))

def readWord (bytes : List UInt8) : Word × List UInt8 × Nat :=
  let n := min 8 bytes.length
  (loadLE bytes 0 n, bytes.drop n, n)

def HashBytesBehavior : Prop :=
  (∀ (bytes : List UInt8) (seed : Word) (secret : Word × Word × Word × Word),
    hashBytesArray bytes seed secret = hashBytes bytes seed secret ∧
    hashBytesPointer bytes seed secret = hashBytes bytes seed secret ∧
    hashBytesIterator bytes seed secret = hashBytes bytes seed secret) ∧
  (∀ low high : Word, ∀ shift : UInt8, concatShift low high shift =
    let bits := shift.toNat * 8 % 64
    wor (shr low bits) (shl high (64 - bits))) ∧
  (∀ bytes : List UInt8, (readWord bytes).2.2 = min 8 bytes.length ∧
    (readWord bytes).2.1 = bytes.drop (min 8 bytes.length))

theorem hashBytesBehavior : HashBytesBehavior := by
  refine ⟨fun _ _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ _ => rfl, ?_⟩
  intro bytes
  simp [readWord]

def hashQuote {α : Type} (hash : α → Word → Word) (value : α) (h : Word) : Word :=
  hash value (wxor h (JInt.lit .u64 0x2c97bf8b3de87020))

def hashPhi {α β : Type} (hashA : α → Word → Word) (hashB : β → Word → Word)
    (edges : α) (values : β) (h : Word) : Word :=
  hashA edges (hashB values (wxor h (JInt.lit .u64 0x2c97bf8b3de87020)))

def hashFields {α : Type} (hash : α → Word → Word) (fields : List α) (h : Word) : Word :=
  fields.foldl (fun h x => hash x h) (wxor h (JInt.lit .u64 0x2c97bf8b3de87020))

def hashGlobalRef {M N : Type} (hashM : M → Word → Word) (hashN : N → Word → Word)
    (mod : M) (name : N) (h : Word) : Word :=
  hashN name (hashM mod (wxor h (JInt.lit .u64 0xe19bede84d316c06)))

def HashStructuralBehavior : Prop :=
  (∀ (α : Type) (hash : α → Word → Word) (x : α) (h : Word),
    hashQuote hash x h = hash x (wxor h (JInt.lit .u64 0x2c97bf8b3de87020))) ∧
  (∀ (α : Type) (hash : α → Word → Word) (xs : List α) (h : Word),
    hashFields hash xs h = xs.foldl (fun h x => hash x h)
      (wxor h (JInt.lit .u64 0x2c97bf8b3de87020))) ∧
  (∀ (M N : Type) (hm : M → Word → Word) (hn : N → Word → Word)
      (m : M) (n : N) (h : Word),
    hashGlobalRef hm hn m n h = hn n (hm m (wxor h (JInt.lit .u64 0xe19bede84d316c06))))

theorem hashStructuralBehavior : HashStructuralBehavior := by
  exact ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

end JuliaLean.IntFuncsCov.Hashing
