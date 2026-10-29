import JuliaLean.Sockets.Props
import JuliaLean.Sockets.Words
import JuliaLean.Sockets.Interface

namespace JuliaLean.Sockets

open JuliaLean

theorem bareNum_of_digits {base : Nat} {cs : JStr} (hn : cs ≠ [])
    (hd : ∀ c ∈ cs, 0 ≤ digitVal c ∧ digitVal c < base) : bareNum base cs = true := by
  cases cs with
  | nil => contradiction
  | cons c cs => simpa [bareNum, List.all_eq_true] using hd

@[simp] theorem bareNum_dec (n : Nat) : bareNum 10 (decStr n) = true :=
  bareNum_of_digits (decStr_nonempty n) (decStr_mem n)

@[simp] theorem bareNum_hex (n : Nat) : bareNum 16 (hexStr n) = true :=
  bareNum_of_digits (hexStr_nonempty n) (hexStr_mem n)

theorem splitIPv4 (h : Nat) : splitOn '.' (ipv4Str h) =
    [decStr (ipv4Byte h 3), decStr (ipv4Byte h 2), decStr (ipv4Byte h 1), decStr (ipv4Byte h 0)] := by
  simp only [ipv4Str, List.append_assoc, List.cons_append, List.nil_append,
    splitOn_dec_prefix, splitOn_dec]

theorem decStr_first (n : Nat) : decStr n = ['0'] ∨ (decStr n).head? ≠ some '0' := by
  by_cases hz : n = 0
  · exact Or.inl (by simp [hz])
  · exact Or.inr (decStr_head n (by omega))

theorem decStr_properties (n : Nat) (hn : n < 256) :
    bareNum 10 (decStr n) ∧ (decStr n = ['0'] ∨ (decStr n).head? ≠ some '0') ∧
      numVal 10 (decStr n) ≤ 255 := by
  exact ⟨bareNum_dec n, decStr_first n, by rw [decStr_value]; omega⟩

theorem ipv4PrintBare_proven : IPv4PrintBare := by
  intro h hh f hf
  rw [splitIPv4] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  all_goals exact decStr_properties _ (ipv4Byte_bound h _)

theorem parseIPv4_quad (a b c d : Nat) (ha : a < 256) (hb : b < 256)
    (hc : c < 256) (hd : d < 256) :
    parseIPv4 (decStr a ++ ['.'] ++ decStr b ++ ['.'] ++ decStr c ++ ['.'] ++ decStr d) =
      .ok (a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d) := by
  have hna : ¬((a : Int) < 0 ∨ (a : Int) > 255) := by omega
  have hnb : ¬((b : Int) < 0 ∨ (b : Int) > 255) := by omega
  have hnc : ¬((c : Int) < 0 ∨ (c : Int) > 255) := by omega
  have hnd : ¬((d : Int) < 0 ∨ (d : Int) > 255) := by omega
  simp (disch := omega) only [parseIPv4, pv4go, List.append_assoc, List.cons_append, List.nil_append,
    splitOn_dec_prefix, splitOn_dec, decStr_nonempty, decStr_leading,
    parseJInt_dec, hna, hnb, hnc, hnd, ite_false, List.length_cons, List.length_nil,
    Int.toNat_natCast, Nat.add_zero, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
    Nat.one_mul, Nat.mul_one, Nat.zero_or]
  rw [lor_add_disjoint (a * 16777216) (b * 65536) 24 (by omega) (by omega)]
  rw [lor_add_disjoint (a * 16777216 + b * 65536) (c * 256) 16 (by omega) (by omega)]
  rw [lor_add_disjoint (a * 16777216 + b * 65536 + c * 256) d 8 (by omega) (by omega)]
  simp

theorem ipv6EmbeddedValue_proven : IPv6EmbeddedValue := by
  intro a b c d ha hb hc hd
  let tail := decStr a ++ ['.'] ++ decStr b ++ ['.'] ++ decStr c ++ ['.'] ++ decStr d
  have noColon : ':' ∉ tail := by
    simp [tail]
  have hasDot : tail.any (fun c => c == '.') = true := by
    simp [tail, List.any_append]
  have splitTail : splitOn ':' tail = [tail] := splitOn_noSep noColon
  have parsed : parseIPv4 tail =
      .ok (a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d) :=
    parseIPv4_quad a b c d (by omega) (by omega) (by omega) (by omega)
  change parseIPv6 ([':', ':'] ++ tail) = _
  simp [parseIPv6, splitOn_colon_prefix, splitTail, hasDot,
    parseipv6fields, pv6go, parsed]

theorem ipv4Roundtrip_proven : IPv4Roundtrip := by
  intro h hh
  have ha := ipv4Byte_bound h 3
  have hb := ipv4Byte_bound h 2
  have hc := ipv4Byte_bound h 1
  have hd := ipv4Byte_bound h 0
  unfold ipv4Str
  rw [parseIPv4_quad _ _ _ _ ha hb hc hd, ipv4_decomposition h hh]

/-- Parsing a printed IPv4 address through `IPAddr` recovers its address and type. -/
def IPv4IPAddrRoundtrip : Prop :=
  ∀ h : Nat, h < 2 ^ 32 →
    parseIPAddr (ipv4Str h) = .ok (.v4 (JInt.wrap .u32 h))

theorem ipv4IPAddrRoundtrip_proven : IPv4IPAddrRoundtrip := by
  intro h hh
  have noColon : ':' ∉ ipv4Str h := by simp [ipv4Str]
  simp [parseIPAddr, noColon, ipv4Roundtrip_proven h hh]

theorem islessStrictOrder_proven : IslessStrictOrder := by
  intro a b c
  simp [islessIP]
  omega

theorem inet4ShowText_proven : Inet4ShowText := by
  intro h hh p hp
  simp [inet4Show, ipv4Show, List.append_assoc]

end JuliaLean.Sockets
