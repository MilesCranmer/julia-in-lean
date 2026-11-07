import JuliaLean.Proofs.stdlib.Sockets.src.IPAddr.Props

namespace JuliaLean.Sockets

open JuliaLean


/-- Both documented Integer constructors accept every in-range BigInt host. -/
def BigIntConstructors : Prop := ∀ n : Int, 0 ≤ n → n ≤ IntTy.u32.max →
  bigCtor .u32 n = .ok (JInt.lit .u32 n) ∧ bigCtor .u128 n = .ok (JInt.lit .u128 n)

def IPv6BoundaryElision : Prop := ∀ a b c d e f g : Nat,
  a < 65536 → b < 65536 → c < 65536 → d < 65536 → e < 65536 → f < 65536 → g < 65536 →
  parseIPv6 ([':', ':'] ++ List.intercalate [':'] ([a,b,c,d,e,f,g].map hexStr)) =
    .ok (hostOf [a,b,c,d,e,f,g])

def WordConstructorInRange : Prop := ∀ target t : IntTy, ∀ n : JInt t,
  ∀ (_hn : 0 ≤ n.val) (hmin : target.min ≤ n.val) (hmax : n.val ≤ target.max),
    wordCtor target t n = .ok ⟨n.val, ⟨hmin, hmax⟩⟩

def WordConstructorRejects : Prop := ∀ target t : IntTy, ∀ n : JInt t,
  (n.val < 0 ∨ target.max < n.val) →
    ∃ m, wordCtor target t n = .error (.argumentError m)

def FieldsRejectOutOfRange : Prop := ∀ target : IntTy, ∀ bits : Nat, ∀ fields : List Int,
  (∃ x ∈ fields, x < 0 ∨ (2 ^ bits : Int) - 1 < x) →
    fieldsCtor target bits fields = .error (.argumentError "address field out of range")

def IPAddrRoundtrip : Prop := ∀ a : Address, parseIPAddr (addressString a) = .ok a

def AddressHashCongruent : Prop :=
  ∀ objectId : Address → JInt .u64, ∀ hashUInt : JInt .u64 → JInt .u64 → JInt .u64,
    ∀ a b : Address, ∀ seed : JInt .u64, addressIsequal a b = true →
      addressHash objectId hashUInt a seed = addressHash objectId hashUInt b seed

def Inet6ShowText : Prop := ∀ h port : Nat, h < 2 ^ 128 → port < 65536 →
  inet6Show h port = "Sockets.InetAddr{IPv6}".toList ++ ['('] ++ ['i','p','"'] ++
    ipv6Str h ++ ['"'] ++ ", ".toList ++ decStr port ++ [')']

theorem bigIntConstructors_refuted : ¬ BigIntConstructors := by
  intro h
  have he := (h 1 (by decide) (by decide)).1
  cases he

theorem ipv6BoundaryElision_refuted : ¬ IPv6BoundaryElision := by
  intro h
  have he := h 1 2 3 4 5 6 7 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact absurd he (by decide)

theorem wordConstructorInRange_proven : WordConstructorInRange := by
  intro target t n hn hmin hmax
  simp [wordCtor, integerCtor, JInt.convert, show ¬n.val < 0 from by omega,
    show ¬(t.max > target.max ∧ n.val > target.max) from by omega, hmin, hmax]

theorem wordConstructorRejects_proven : WordConstructorRejects := by
  intro target t n h
  by_cases hn : n.val < 0
  · exact ⟨"address must be positive", by simp [wordCtor, integerCtor, hn]⟩
  · have hmax : target.max < n.val := by omega
    have ht := n.property.2
    exact ⟨"address must fit within word", by simp [wordCtor, integerCtor, hn, hmax,
      show target.max < t.max from by omega]⟩

theorem fieldsRejectOutOfRange_proven : FieldsRejectOutOfRange := by
  intro target bits fields h
  have he : ¬fields.all (fun x => 0 ≤ x ∧ x ≤ (2 ^ bits : Int) - 1) := by
    intro ha
    obtain ⟨x, hx, hv⟩ := h
    have hh := List.all_eq_true.mp ha x hx
    simp only [decide_eq_true_eq] at hh
    omega
  simp only [fieldsCtor, ite_eq_right he]

theorem addressHashCongruent_proven : AddressHashCongruent := by
  intro objectId hashUInt a b seed he
  have hab : a = b := by simpa [addressIsequal] using he
  subst b
  rfl

theorem inet6ShowText_proven : Inet6ShowText := by
  intro h p hh hp
  simp [inet6Show, ipv6Show, List.append_assoc]

end JuliaLean.Sockets
