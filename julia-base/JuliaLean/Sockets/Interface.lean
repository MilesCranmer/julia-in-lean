import JuliaLean.Sockets.Props

namespace JuliaLean.Sockets

open JuliaLean

/-- Integer-host constructor, stdlib/Sockets/src/IPAddr.jl:42-50,105-115.
`none` represents BigInt, for which the source's typemax call has no method. -/
def integerCtor (target : IntTy) (sourceMax : Option Int) (host : Int) : Jl (JInt target) :=
  if host < 0 then .error (.argumentError "address must be positive")
  else match sourceMax with
    | none => .error (.methodError "typemax(BigInt)")
    | some m =>
      if m > target.max ∧ host > target.max then
        .error (.argumentError "address must fit within word")
      else JInt.convert target host

/-- Fixed-width Integer input to the single-host constructor. -/
def wordCtor (target t : IntTy) (host : JInt t) : Jl (JInt target) :=
  integerCtor target (some t.max) host.val

/-- BigInt input to the same constructor. -/
def bigCtor (target : IntTy) (host : Int) : Jl (JInt target) := integerCtor target none host

/-- The UInt8/UInt16 field assembly of the four/eight-argument constructors,
stdlib/Sockets/src/IPAddr.jl:19-28,74-91. Values are checked before conversion. -/
def packFields (fieldBits : Nat) : List Int → Nat
  | [] => 0
  | x :: xs => (x.toNat * 2 ^ (fieldBits * xs.length)) ||| packFields fieldBits xs

def fieldsCtor (target : IntTy) (fieldBits : Nat) (fields : List Int) : Jl (JInt target) :=
  if fields.all (fun x => 0 ≤ x ∧ x ≤ (2 ^ fieldBits : Int) - 1) then
    .ok (JInt.wrap target (packFields fieldBits fields))
  else .error (.argumentError "address field out of range")

/-- The address type tag and its fixed-width host; stdlib/Sockets/src/IPAddr.jl:16-18,71-73. -/
inductive Address where
  | v4 (host : JInt .u32)
  | v6 (host : JInt .u128)
  deriving DecidableEq

/-- `parse(IPAddr, str)`, stdlib/Sockets/src/IPAddr.jl:263-269. Wrapping records
that ret is a UInt32/UInt128 word in the underlying parsers. -/
def parseIPAddr (cs : JStr) : Jl Address :=
  if ':' ∈ cs then
    match parseIPv6 cs with
    | .error e => .error e
    | .ok v => .ok (.v6 (JInt.wrap .u128 v))
  else
    match parseIPv4 cs with
    | .error e => .error e
    | .ok v => .ok (.v4 (JInt.wrap .u32 v))

def addressString : Address → JStr
  | .v4 host => ipv4Str host.val.toNat
  | .v6 host => ipv6Str host.val.toNat

/-- The default equality of an isbits address is type-and-field identity. -/
def addressIsequal (a b : Address) : Bool := decide (a = b)

/-- Default hash dispatch, base/hashing.jl:40,46. The C runtime's objectid
and the UInt hash remain parameters; no collision-freedom is assumed. -/
def addressHash (objectId : Address → JInt .u64)
    (hashUInt : JInt .u64 → JInt .u64 → JInt .u64) (a : Address) (seed : JInt .u64) : JInt .u64 :=
  hashUInt (objectId a) seed

/-- IPv6 instance of InetAddr.show, stdlib/Sockets/src/IPAddr.jl:324-329. -/
def inet6Show (h port : Nat) : JStr :=
  "Sockets.InetAddr{IPv6}".toList ++ ['('] ++ ipv6Show h ++ ", ".toList ++ decStr port ++ [')']

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
