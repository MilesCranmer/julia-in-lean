import JuliaLean.IOBuffers.WriteProofsBasic

/-! List lemmas about the bytes a write stores. -/

namespace JuliaLean.IOBuffers
open JuliaLean
namespace WriteP

theorem slice_drop (d : List UInt8) (a b z : Int) (h1 : 1 ≤ a) (h2 : a ≤ b) (h3 : b ≤ z + 1) :
    slice d b z = (slice d a z).drop (b - a).toNat := by
  simp only [slice, List.drop_take, List.drop_drop]
  rw [show (z - a + 1).toNat - (b - a).toNat = (z - b + 1).toNat by omega,
    show (a - 1).toNat + (b - a).toNat = (b - 1).toNat by omega]

theorem take_end (d wk : List UInt8) (q z K : Nat) (h1 : q ≤ z) (h2 : z ≤ d.length) (hk : wk.length = K) :
    ((d.take z ++ wk ++ d.drop (z + K)).drop q).take (z - q + K) = (d.drop q).take (z - q) ++ wk := by
  have hA : (d.take z).length = z := by simp; omega
  rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.drop_take, List.take_append,
    List.take_take]
  have hB : ((d.drop q).take (z - q)).length = z - q := by simp; omega
  rw [hB, show min (z - q + K) (z - q) = z - q by omega, show z - q + K - (z - q) = K by omega,
    List.take_left' hk]

theorem take_mid (d wk : List UInt8) (o p z K : Nat) (h1 : o + p ≤ z) (h2 : z ≤ d.length)
    (h3 : o + p + K ≤ d.length) (hk : wk.length = K) :
    ((d.take (o + p) ++ wk ++ d.drop (o + p + K)).drop o).take (max z (o + p + K) - o) =
      ((d.drop o).take (z - o)).take p ++ wk ++ ((d.drop o).take (z - o)).drop (p + K) := by
  have hA : (d.take (o + p)).length = o + p := by simp; omega
  rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.drop_take,
    Nat.add_sub_cancel_left, List.take_append]
  have hB : ((d.drop o).take p).length = p := by simp; omega
  rw [hB, List.take_append, hk, List.take_of_length_le (l := wk) (by omega)]
  simp only [List.take_take, List.drop_take, List.drop_drop, List.append_assoc]
  rw [show min (max z (o + p + K) - o) p = p by omega, show min p (z - o) = p by omega,
    show max z (o + p + K) - o - p - K = z - o - (p + K) by omega, show o + p + K = o + (p + K) by omega]

end WriteP
end JuliaLean.IOBuffers
