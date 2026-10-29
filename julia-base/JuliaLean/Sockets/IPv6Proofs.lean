import JuliaLean.Sockets.IPv4Proofs
import JuliaLean.Sockets.IPv6Print

namespace JuliaLean.Sockets

open JuliaLean

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

@[simp] theorem hexStr_no_dot (n : Nat) :
    (hexStr n).any (fun c => c == '.') = false := by
  simp only [List.any_eq_false]
  intro c hc
  intro he
  have he : c = '.' := beq_iff_eq.mp he
  subst c
  exact dot_not_hex n hc

theorem pv6go_hex (num k : Nat) (cf : Int) (ret n : Nat) (fs : List JStr)
    (hn : n < 65536) :
    pv6go num k cf ret (hexStr n :: fs) =
      pv6go num k (cf - 1) (ret ||| shift128 n (cf * 16)) fs := by
  simp [pv6go, hexStr_nonempty, parseJInt_hex hn,
    show ¬((n : Int) < 0) from by omega]

theorem pv6go_empty (num k : Nat) (cf : Int) (ret : Nat) (fs : List JStr) :
    pv6go num k cf ret ([] :: fs) =
      pv6go num k ((if cf ≠ 7 ∧ cf ≠ 0 then cf - (num - k) else cf) - 1) ret fs := by
  rfl

theorem pv6go_hex_prefix (num k : Nat) (cf : Int) (ret : Nat)
    (vs : List Nat) (fs : List JStr) (bounds : ∀ v ∈ vs, v < 65536) :
    pv6go num k cf ret (vs.map hexStr ++ fs) =
      let state := vs.foldl (fun state v =>
        (state.1 - 1, state.2 ||| shift128 v (state.1 * 16))) (cf, ret)
      pv6go num k state.1 state.2 fs := by
  induction vs generalizing cf ret with
  | nil => rfl
  | cons v vs ih =>
    have hv : v < 65536 := bounds v (by simp)
    have hvs : ∀ w ∈ vs, w < 65536 := by
      intro w hw
      exact bounds w (by simp [hw])
    simp only [List.map_cons, List.cons_append, List.foldl_cons]
    rw [pv6go_hex num k cf ret v _ hv]
    exact ih (cf - 1) (ret ||| shift128 v (cf * 16)) hvs


@[simp] theorem shift_slot0 {v : Nat} (hv : v < 65536) : shift128 v 0 = v := by
  simp [shift128, Nat.mod_eq_of_lt (show v < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot1 {v : Nat} (hv : v < 65536) : shift128 v 16 = v * 2 ^ 16 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 16 < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot2 {v : Nat} (hv : v < 65536) : shift128 v 32 = v * 2 ^ 32 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 32 < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot3 {v : Nat} (hv : v < 65536) : shift128 v 48 = v * 2 ^ 48 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 48 < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot4 {v : Nat} (hv : v < 65536) : shift128 v 64 = v * 2 ^ 64 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 64 < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot5 {v : Nat} (hv : v < 65536) : shift128 v 80 = v * 2 ^ 80 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 80 < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot6 {v : Nat} (hv : v < 65536) : shift128 v 96 = v * 2 ^ 96 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 96 < 2 ^ 128 from by omega)]
@[simp] theorem shift_slot7 {v : Nat} (hv : v < 65536) : shift128 v 112 = v * 2 ^ 112 := by
  simp [shift128, Nat.mod_eq_of_lt (show v * 2 ^ 112 < 2 ^ 128 from by omega)]

theorem ipv6EightGroups_proven : IPv6EightGroups := by
  intro vs hl hb
  cases vs with
  | nil => simp at hl
  | cons a vs =>
    cases vs with
    | nil => simp at hl
    | cons b vs =>
      cases vs with
      | nil => simp at hl
      | cons c vs =>
        cases vs with
        | nil => simp at hl
        | cons d vs =>
          cases vs with
          | nil => simp at hl
          | cons e vs =>
            cases vs with
            | nil => simp at hl
            | cons f vs =>
              cases vs with
              | nil => simp at hl
              | cons g vs =>
                cases vs with
                | nil => simp at hl
                | cons h vs =>
                  cases vs with
                  | cons i vs => simp at hl
                  | nil =>
                    simp only [List.mem_cons, List.mem_singleton] at hb
                    have ba : a < 65536 := by have := hb a (by simp); omega
                    have bb : b < 65536 := by have := hb b (by simp); omega
                    have bc : c < 65536 := by have := hb c (by simp); omega
                    have bd : d < 65536 := by have := hb d (by simp); omega
                    have be : e < 65536 := by have := hb e (by simp); omega
                    have bf : f < 65536 := by have := hb f (by simp); omega
                    have bg : g < 65536 := by have := hb g (by simp); omega
                    have bh : h < 65536 := by have := hb h (by simp); omega
                    simp (disch := omega) [List.intercalate, List.append_assoc, List.cons_append,
                      parseIPv6, parseipv6fields, pv6go, hostOf, parseJInt_hex,
                      shift_slot0, shift_slot1, shift_slot2, shift_slot3,
                      shift_slot4, shift_slot5, shift_slot6, shift_slot7,
                      or_slot0, or_slot1, or_slot2, or_slot3, or_slot4, or_slot5, or_slot6, or_slot7,
                      Int.natCast_nonneg]
                    simp only [show ¬((a : Int) < 0) from by omega, show ¬((b : Int) < 0) from by omega,
                      show ¬((c : Int) < 0) from by omega, show ¬((d : Int) < 0) from by omega,
                      show ¬((e : Int) < 0) from by omega, show ¬((f : Int) < 0) from by omega,
                      show ¬((g : Int) < 0) from by omega, show ¬((h : Int) < 0) from by omega, ite_false]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096) (b * 79228162514264337593543950336) 112 (by omega) (by omega)]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096 + b * 79228162514264337593543950336) (c * 1208925819614629174706176) 96 (by omega) (by omega)]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096 + b * 79228162514264337593543950336 + c * 1208925819614629174706176) (d * 18446744073709551616) 80 (by omega) (by omega)]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096 + b * 79228162514264337593543950336 + c * 1208925819614629174706176 + d * 18446744073709551616) (e * 281474976710656) 64 (by omega) (by omega)]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096 + b * 79228162514264337593543950336 + c * 1208925819614629174706176 + d * 18446744073709551616 + e * 281474976710656) (f * 4294967296) 48 (by omega) (by omega)]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096 + b * 79228162514264337593543950336 + c * 1208925819614629174706176 + d * 18446744073709551616 + e * 281474976710656 + f * 4294967296) (g * 65536) 32 (by omega) (by omega)]
                    rw [lor_add_disjoint (a * 5192296858534827628530496329220096 + b * 79228162514264337593543950336 + c * 1208925819614629174706176 + d * 18446744073709551616 + e * 281474976710656 + f * 4294967296 + g * 65536) h 16 (by omega) (by omega)]
                    simp [Nat.add_assoc]


end JuliaLean.Sockets
