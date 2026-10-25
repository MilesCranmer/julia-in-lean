import JuliaLean.Sockets.Model

/-!
Properties of `stdlib/Sockets/src/IPAddr.jl` promised by docstrings, the RFC
4291/5952 grammars, or obvious invariants.
-/

namespace JuliaLean.Sockets

open JuliaLean

/-- Whether a `Jl` computation returned normally. -/
def isOk {α : Type} (x : Jl α) : Bool :=
  match x with | .ok _ => true | .error _ => false

/-- A nonempty field of digits valid in `base` (no sign, no whitespace). -/
def bareNum (base : Nat) (f : JStr) : Bool :=
  match f with
  | [] => false
  | _ => f.all (fun c => 0 ≤ digitVal c ∧ digitVal c < base)

/-- A leading or trailing colon belongs to a `::` pair. Interior single
colons are the ordinary group separators of valid IPv6 text. -/
def ColonPaired (cs : JStr) : Bool :=
  (if cs.head? = some ':' then cs[1]? == some ':' else true) &&
  (if cs.getLast? = some ':' then cs.reverse[1]? == some ':' else true)

/-- Number of maximal runs of two or more consecutive ':' (`::` elisions). -/
def elisionRuns (run : Nat) : JStr → Nat
  | [] => 0
  | c :: cs =>
    if c == ':' then (if run == 1 then 1 else 0) + elisionRuns (run + 1) cs
    else elisionRuns 0 cs

/-- Host value of a list of group values, first group most significant. -/
def hostOf : List Nat → Nat
  | [] => 0
  | v :: vs => v * 2 ^ (16 * vs.length) + hostOf vs


/-- `decide` on parse results: `Except JlError Nat` has no core `DecidableEq`. -/
instance : DecidableEq (Except JlError Nat) :=
  fun a b =>
    match a, b with
    | .error e, .error e' =>
      match decEq e e' with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (fun he => by cases he; exact absurd rfl h)
    | .ok n, .ok n' =>
      match decEq n n' with
      | isTrue h => isTrue (by cases h; rfl)
      | isFalse h => isFalse (fun he => by cases he; exact absurd rfl h)
    | .error _, .ok _ => isFalse (fun he => by cases he)
    | .ok _, .error _ => isFalse (fun he => by cases he)

/-- parse(IPv6, s) never accepts the empty string. -/
def IPv6Nonempty : Prop := ∀ cs : JStr, (parseIPv6 cs).isOk → cs ≠ []

/-- Leading and trailing colons in accepted IPv6 text occur in pairs. -/
def IPv6ColonPaired : Prop :=
  ∀ cs : JStr, (parseIPv6 cs).isOk → ColonPaired cs = true

/-- A string parse(IPv6, ..) accepts contains at most one '::' elision. -/
def IPv6OneElision : Prop :=
  ∀ cs : JStr, (parseIPv6 cs).isOk → elisionRuns 0 cs ≤ 1

/-- Every error of a `Jl` computation is an `ArgumentError`. -/
def isArgError : JlError → Bool
  | .argumentError _ => true
  | _ => false

/-- parse(IPv6, s) either returns or throws ArgumentError. -/
def IPv6ErrorIsArgument : Prop :=
  ∀ cs : JStr, ∀ e : JlError, parseIPv6 cs = .error e → isArgError e = true

/-- Every nonempty field of a string parse(IPv6, ..) accepts is a bare
hexadecimal numeral of value at most 0xFFFF. -/
def IPv6FieldRange : Prop :=
  ∀ cs : JStr, (parseIPv6 cs).isOk →
    ∀ f ∈ splitOn ':' cs, f ≠ [] → '.' ∉ f → bareNum 16 f ∧ numVal 16 f ≤ 65535

/-- Every field of a string parse(IPv6, ..) accepts is a bare hexadecimal
numeral (no sign, no whitespace). -/
def IPv6FieldBare : Prop :=
  ∀ cs : JStr, (parseIPv6 cs).isOk →
    ∀ f ∈ splitOn ':' cs, f ≠ [] → '.' ∉ f → bareNum 16 f

/-- Every field of a string parse(IPv4, ..) accepts is a bare decimal numeral
(no sign, no whitespace). -/
def IPv4FieldBare : Prop :=
  ∀ cs : JStr, (parseIPv4 cs).isOk → ∀ f ∈ splitOn '.' cs, bareNum 10 f

/-- parse(IPv4, s) either returns or throws ArgumentError. -/
def IPv4ErrorIsArgument : Prop :=
  ∀ cs : JStr, ∀ e : JlError, parseIPv4 cs = .error e → isArgError e = true

/-- parse(IPv6, "..") accepts the valid RFC 4291 form of five groups plus an
embedded IPv4 part around one elided group. -/
def IPv6AcceptsFiveGroupsV4 : Prop :=
  ∀ g1 g2 g3 g4 g5 a b c d : Nat,
    g1 ≤ 65535 → g2 ≤ 65535 → g3 ≤ 65535 → g4 ≤ 65535 → g5 ≤ 65535 →
    a ≤ 255 → b ≤ 255 → c ≤ 255 → d ≤ 255 →
    parseIPv6 ([':', ':'] ++ hexStr g1 ++ [':'] ++ hexStr g2 ++ [':'] ++ hexStr g3 ++ [':'] ++
        hexStr g4 ++ [':'] ++ hexStr g5 ++ [':'] ++
        decStr a ++ ['.'] ++ decStr b ++ ['.'] ++ decStr c ++ ['.'] ++ decStr d)
      = .ok (g1 * 2 ^ 96 + g2 * 2 ^ 80 + g3 * 2 ^ 64 + g4 * 2 ^ 48 + g5 * 2 ^ 32
        + a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d)

/-! ### Proven -/

/-- Every field of `string(ip::IPv4)` is a bare decimal of value 0-255 with no
leading zero. -/
def IPv4PrintBare : Prop :=
  ∀ h : Nat, h < 2 ^ 32 →
    ∀ f ∈ splitOn '.' (ipv4Str h),
      bareNum 10 f ∧ (f = "0".toList ∨ f.head? ≠ some '0') ∧ numVal 10 f ≤ 255

/-- parse(IPv4, string(ip)) recovers the host. -/
def IPv4Roundtrip : Prop := ∀ h : Nat, h < 2 ^ 32 → parseIPv4 (ipv4Str h) = .ok h

/-- `string(ip::IPv6)` is the RFC 5952 section 4 form of the address. -/
def IPv6Rfc5952 : Prop := ∀ h : Nat, ipv6Str h = rfc5952 h

/-- parse(IPv6, string(ip)) recovers the host. -/
def IPv6Roundtrip : Prop := ∀ h : Nat, h < 2 ^ 128 → parseIPv6 (ipv6Str h) = .ok h

/-- Eight explicit groups parse to their field-wise value. -/
def IPv6EightGroups : Prop :=
  ∀ vs : List Nat, vs.length = 8 → (∀ v ∈ vs, v ≤ 65535) →
    parseIPv6 (List.intercalate [':'] (vs.map hexStr)) = .ok (hostOf vs)

/-- `::a.b.c.d` embeds the IPv4 value in the low 32 bits. -/
def IPv6EmbeddedValue : Prop :=
  ∀ a b c d : Nat, a ≤ 255 → b ≤ 255 → c ≤ 255 → d ≤ 255 →
    parseIPv6 ([':', ':'] ++ decStr a ++ ['.'] ++ decStr b ++ ['.'] ++ decStr c ++ ['.'] ++ decStr d)
      = .ok (a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d)

/-- `isless` on IP addresses is the strict order of the host values. -/
def IslessStrictOrder : Prop :=
  ∀ a b c : Nat,
    islessIP a a = false ∧
    (islessIP a b = true → islessIP b a = false) ∧
    (islessIP a b = true → islessIP b c = true → islessIP a c = true) ∧
    (a = b ∨ islessIP a b = true ∨ islessIP b a = true)

/-- `show(::InetAddr)` prints the documented format with the canonical address
text and the decimal port. -/
def Inet4ShowText : Prop :=
  ∀ h : Nat, h < 2 ^ 32 → ∀ p : Nat, p ≤ 65535 →
    inet4Show h p =
      "Sockets.InetAddr{IPv4}".toList ++ ['('] ++ ['i', 'p', '"'] ++ ipv4Str h ++ ['"'] ++
        ", ".toList ++ decStr p ++ [')']

end JuliaLean.Sockets
