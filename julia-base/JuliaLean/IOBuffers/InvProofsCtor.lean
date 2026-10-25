import JuliaLean.IOBuffers.InvProofsBase

/-!
Every constructor call with in-range arguments yields a buffer satisfying `SInv _ (2 ^ 60)`.
-/

namespace JuliaLean.IOBuffers.InvP

open JuliaLean JuliaLean.IOBuffers

theorem except_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl
theorem except_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := rfl
theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem toI_eq (x : Int) (h1 : -2 ^ 63 ≤ x) (h2 : x ≤ 2 ^ 63 - 1) :
    ∃ v : I, toI x = .ok v ∧ v.val = x := by
  unfold toI JInt.convert
  have hc : IntTy.min .i64 ≤ x ∧ x ≤ IntTy.max .i64 := by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ↓reduceIte]; omega
  rw [dif_pos hc]
  exact ⟨_, rfl, rfl⟩

theorem generic_sinv {d : DataArg} {r w sk a t : Bool} {m : Int} {io0 : IOBuf}
    (hd : d.ok) (hm0 : 0 ≤ m) (hm1 : m < 2 ^ 63)
    (hb : genericIOBuffer d r w sk a m t = .ok io0) : SInv io0 (2 ^ 60) := by
  obtain ⟨mz, hmz, hmv⟩ := toI_eq m (by omega) (by omega)
  cases d with
  | vec v =>
    simp only [DataArg.ok, bound] at hd
    simp only [genericIOBuffer, hmz, except_bind_ok] at hb
    split at hb
    · rw [except_bind_error] at hb; cases hb
    · next hc =>
      simp only [except_pure, except_bind_ok] at hb
      cases hb
      cases t
      · have hc' : ¬ mz.val < ↑v.len := fun h' => hc ⟨rfl, h'⟩
        unfold newBuf
        sinv_auto
      · unfold newBuf
        sinv_auto
  | mem d' =>
    simp only [DataArg.ok, bound] at hd
    simp only [genericIOBuffer, hmz, except_bind_ok] at hb
    split at hb
    · rw [except_bind_error] at hb; cases hb
    · next hc =>
      simp only [except_pure, except_bind_ok] at hb
      cases hb
      cases t
      · have hc' : ¬ mz.val < ↑d'.length := fun h' => hc ⟨rfl, h'⟩
        rw [if_neg Bool.false_ne_true]
        unfold newBuf
        sinv_auto
      · unfold newBuf
        sinv_auto
  | other d' =>
    simp only [DataArg.ok, bound] at hd
    simp only [genericIOBuffer, hmz, except_bind_ok] at hb
    split at hb
    · rw [except_bind_error] at hb; cases hb
    · next hc =>
      simp only [except_pure, except_bind_ok] at hb
      cases hb
      cases t
      · have hc' : ¬ mz.val < ↑d'.length := fun h' => hc ⟨rfl, h'⟩
        rw [if_neg Bool.false_ne_true]
        unfold newBuf
        sinv_auto
      · unfold newBuf
        sinv_auto

theorem empty_sinv {r w a t : Option Bool} {m : Int} {sh : Option Int} {io0 : IOBuf}
    (hc : Ctor.ok (.empty r w a t m sh)) (hb : iobufferEmpty r w a t m sh = .ok io0) :
    SInv io0 (2 ^ 60) := by
  obtain ⟨hm0, hm1, hsh⟩ := hc
  obtain ⟨mz, hmz, hmv⟩ := toI_eq m (by omega) (by omega)
  simp only [iobufferEmpty, hmz, except_bind_ok] at hb
  split at hb
  · rw [except_bind_error] at hb; cases hb
  · simp only [except_pure, except_bind_ok] at hb
    cases sh with
    | none =>
      simp only [except_pure, except_bind_ok] at hb
      have hz : 0 ≤ (imin mz (i 32)).val := by vo
      simp only [stringMemory, if_neg (show ¬ (imin mz (i 32)).val < 0 by omega), except_pure,
        except_bind_ok] at hb
      cases hb
      unfold newBuf
      sinv_auto
    | some h0 =>
      obtain ⟨hi, hbd⟩ := hsh h0 rfl
      simp only [isInt, bound] at hi hbd
      obtain ⟨v, hv, hvv⟩ := toI_eq h0 (by omega) (by omega)
      simp only [hv, except_bind_ok, except_pure] at hb
      have hz : 0 ≤ (imin mz (imax (i 0) v)).val := by vo
      simp only [stringMemory, if_neg (show ¬ (imin mz (imax (i 0) v)).val < 0 by omega),
        except_pure, except_bind_ok] at hb
      cases hb
      unfold newBuf
      sinv_auto

theorem pipeN_sinv {m : Int} {io0 : IOBuf} (hc : Ctor.ok (.pipeN m))
    (hb : Ctor.build (.pipeN m) = .ok io0) : SInv io0 (2 ^ 60) := by
  obtain ⟨hm0, hm1⟩ := hc
  simp only [bound] at hm1
  obtain ⟨mz, hmz, hmv⟩ := toI_eq m (by omega) (by omega)
  simp only [Ctor.build, pipeBufferN, if_neg (show ¬ m < 0 by omega), except_pure,
    except_bind_ok, pipeBuffer] at hb
  rw [if_neg (show ¬ (IntTy.i64 ≠ IntTy.i64) from fun h => h rfl)] at hb
  simp only [genericIOBuffer, hmz, except_bind_ok] at hb
  split at hb
  · rw [except_bind_error] at hb; cases hb
  · simp only [except_pure, except_bind_ok] at hb
    cases hb
    unfold newBuf
    sinv_auto

theorem ctor_sinv {c : Ctor} {io0 : IOBuf} (hc : c.ok) (hb : c.build = .ok io0) :
    SInv io0 (2 ^ 60) := by
  cases c with
  | empty r w a t m sh => exact empty_sinv hc hb
  | data d r w a t m =>
    obtain ⟨hd, hm0, hm1⟩ := hc
    exact generic_sinv hd hm0 hm1 hb
  | str s =>
    exact generic_sinv (d := .vec ⟨s, 0, s.length⟩) ⟨by simp, hc⟩ (by omega) (by omega) hb
  | pipe d m =>
    obtain ⟨hd, hm0, hm1⟩ := hc
    simp only [Ctor.build, pipeBuffer] at hb
    rw [if_neg (show ¬ (IntTy.i64 ≠ IntTy.i64) from fun h => h rfl)] at hb
    exact generic_sinv hd hm0 hm1 hb
  | pipeN m => exact pipeN_sinv hc hb

end JuliaLean.IOBuffers.InvP
