import JuliaLean.base.hashing

/-!
Executable models for `base/hashing.jl` at master `bbfa0ce4150`. The byte
hash uses the array method's exact branches and 48-byte loop. Pointer and iterator
overloads are stated against the same byte sequence, which is their documented
value-level invariant.
-/

namespace JuliaLean.IntFuncsCov.Hashing

open JuliaLean
open JuliaLean.ParsePrint

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
