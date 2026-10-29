import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.ParsePrint.IntParse

/-!
Model of the pure address code of `stdlib/Sockets/src/IPAddr.jl` at Julia
master `f755f49a9e41380d7da126b3c1db9fe7f83dd027`: `IPv4`/`IPv6` parse and print, `InetAddr` show, `isless`.

Strings are well-formed Unicode strings represented as `List Char`.
Integer fields use the grammar and overflow precedence of
`base/parse.jl:49-51,99-171`, including Unicode whitespace from the existing
`IntParse` model. Exact magnitudes are used until the Int64 range check;
Julia detects that overflow rather than wrapping. Group counters are exact
because at most eight tokens are processed. Hosts store word magnitudes,
with explicit modulo 2^128 at UInt128 shifts; constructors in `Interface`
use the shared `JInt` types. Malformed UTF-8 byte strings are outside this
character-list model.
-/

namespace JuliaLean.Sockets

open JuliaLean

abbrev JStr := List Char

/-- `skipspace`/`skipspace_back`, base/parse.jl:53-97, with the Unicode
whitespace categories shared with the integer parser. -/
def isWs (c : Char) : Bool :=
  (c.toNat == 32) || (9 ≤ c.toNat && c.toNat ≤ 13) || (c.toNat == 0x85) ||
    JuliaLean.ParsePrint.IntParse.isZsZlZp c.toNat

/-- `Parsers.digitvalue`, valid when the result is `< base`. -/
def digitVal (c : Char) : Int :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then (c.toNat - 48 : Int)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then (c.toNat - 97 + 10 : Int)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then (c.toNat - 65 + 10 : Int)
  else -1

/-- Leading-whitespace skip, base/parse.jl:70-82. -/
def dropWs : JStr → JStr
  | [] => []
  | c :: cs => if isWs c then dropWs cs else c :: cs

/-- Trailing-whitespace skip, `skipspace_back`, base/parse.jl:84-97. -/
def dropLastWs (cs : JStr) : JStr := (dropWs cs.reverse).reverse

/-- Longest prefix of digits valid in `base`. -/
def takeDigits (base : Nat) : JStr → JStr
  | [] => []
  | c :: cs => if 0 ≤ digitVal c ∧ digitVal c < base then c :: takeDigits base cs else []

/-- Value of a digit list, most significant digit first. -/
def numValGo (base : Nat) (acc : Nat) : JStr → Nat
  | [] => acc
  | c :: cs => numValGo base (acc * base + (digitVal c).toNat) cs

def numVal (base : Nat) (cs : JStr) : Nat := numValGo base 0 cs

/-- `parse(Int, s; base)` on master: value, `ArgumentError`, or `OverflowError`
(the digit run's overflow takes precedence over trailing junk,
base/parse.jl:153-171). -/
def parseJInt (base : Nat) (cs : JStr) : Jl Int :=
  let cs1 := dropWs cs
  let cs2 : JStr :=
    match cs1 with
    | [] => []
    | c :: rest => if c == '+' ∨ c == '-' then dropWs rest else cs1
  let sgn : Int :=
    match cs1 with
    | [] => 1
    | c :: _ => if c == '-' then -1 else 1
  match cs2 with
  | [] => .error (.argumentError "input string is empty or only contains whitespace")
  | _ =>
    let body := dropLastWs cs2
    let run := takeDigits base body
    if run == [] then .error (.argumentError "invalid digit")
    else
      let v := sgn * (numVal base run : Int)
      if v < -9223372036854775808 ∨ v > 9223372036854775807 then
        .error (.overflowError "overflow parsing")
      else if run.length < body.length then .error (.argumentError "invalid digit")
      else .ok v

/-! ### Field splitting -/

/-- `split(str, c)`, keeping empty fields. -/
def splitGo (sep : Char) : JStr → JStr → List JStr
  | [], rev => [rev.reverse]
  | c :: cs, rev =>
    if c == sep then rev.reverse :: splitGo sep cs [] else splitGo sep cs (c :: rev)

def splitOn (sep : Char) (cs : JStr) : List JStr := splitGo sep cs []

/-! ### Numeric text -/

def decCh (d : Nat) : Char := Char.ofNat (48 + d)

def hexCh (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (97 + d - 10)

/-- `string(n, base = b)` for a fixed digit function (no padding, no leading
zeros). `repDigits base toCh fuel n acc` emits the digits of `n` in front of
acc, stopping early when `fuel` runs out; `repStr` passes `fuel = n`, and a
number never has more digits than itself for `base ≥ 2`. -/
def repDigits (base : Nat) (toCh : Nat → Char) : Nat → Nat → JStr → JStr
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    if n = 0 then acc else repDigits base toCh fuel (n / base) (toCh (n % base) :: acc)

def repStr {base : Nat} (_hb : 1 < base) (toCh : Nat → Char) (n : Nat) : JStr :=
  if n = 0 then [toCh 0] else repDigits base toCh n n []

def decStr (n : Nat) : JStr := @repStr 10 (by decide) decCh n

/-- `print_ipv6_field`, stdlib/Sockets/src/IPAddr.jl:130-131. -/
def hexStr (v : Nat) : JStr := @repStr 16 (by decide) hexCh v

/-! ### IPv4 -/

/-- Byte `k` (0 = lowest) of a host, `(host & 0xFF << 8k) >> 8k`. -/
def ipv4Byte (h k : Nat) : Nat := (h / 2 ^ (8 * k)) % 256

/-- `print(io, ip::IPv4)`, stdlib/Sockets/src/IPAddr.jl:66-69. -/
def ipv4Str (h : Nat) : JStr :=
  decStr (ipv4Byte h 3) ++ ['.'] ++ decStr (ipv4Byte h 2) ++ ['.'] ++
    decStr (ipv4Byte h 1) ++ ['.'] ++ decStr (ipv4Byte h 0)

/-- `parse(::Type{IPv4}, str)` on master, stdlib/Sockets/src/IPAddr.jl:196-219. -/
def pv4go (i : Nat) (ret : Nat) : List JStr → Jl Nat
  | [] => .ok ret
  | f :: fs =>
    if f = [] then .error (.argumentError "empty field in IPv4 address")
    else if f.length > 1 ∧ f.head? = some '0' then
      .error (.argumentError "leading zeros in IPv4 addresses are disallowed")
    else
      match parseJInt 10 f with
      | .error e => .error e
      | .ok r =>
        if r < 0 ∨ r > 255 then .error (.argumentError "IPv4 field out of range (must be 0-255)")
        else pv4go (i + 1) (ret ||| r.toNat * 2 ^ ((4 - i) * 8)) fs

def parseIPv4 (cs : JStr) : Jl Nat :=
  let fs := splitOn '.' cs
  if fs.length ≠ 4 then .error (.argumentError "IPv4 addresses must be specified as a dotted quad")
  else pv4go 1 0 fs

/-- `show(io, ip::IPv4)`, stdlib/Sockets/src/IPAddr.jl:65. -/
def ipv4Show (h : Nat) : JStr := ['i', 'p', '"'] ++ ipv4Str h ++ ['"']

/-! ### IPv6 -/

/-- `ipv6_field(ip, i)` for `i` in 0..7 (0 = lowest group),
stdlib/Sockets/src/IPAddr.jl:134-139. -/
def ipv6Field (h i : Nat) : Nat := (h / 2 ^ (16 * i)) % 65536

/-- `parseipv6fields` shift: `UInt128(v) << sh` wraps mod 2^128, and a negative
`sh` shifts the other way (`base/int.jl` shift semantics). -/
def shift128 (v : Nat) (sh : Int) : Nat :=
  if 0 ≤ sh then (v * 2 ^ sh.toNat) % 2 ^ 128 else v / 2 ^ sh.natAbs

/-- `parseipv6fields(fields, num_fields)`, stdlib/Sockets/src/IPAddr.jl:221-241.
`num` is `num_fields`, `k` the (constant) number of fields. -/
def pv6go (num k : Nat) (cf : Int) (ret : Nat) : List JStr → Jl Nat
  | [] => .ok ret
  | f :: fs =>
    if f = [] then
      pv6go num k ((if cf ≠ 7 ∧ cf ≠ 0 then cf - (num - k) else cf) - 1) ret fs
    else
      match parseJInt 16 f with
      | .error e => .error e
      | .ok r =>
        if r < 0 then .error (.inexactError "UInt128")
        else pv6go num k (cf - 1) (ret ||| shift128 r.toNat (cf * 16)) fs

def parseipv6fields (num : Nat) (fs : List JStr) : Jl Nat :=
  if fs.length > num then .error (.argumentError "too many fields in IPv6 address")
  else pv6go num fs.length 7 0 fs

/-- `parse(::Type{IPv6}, str)`, stdlib/Sockets/src/IPAddr.jl:243-255. -/
def parseIPv6 (cs : JStr) : Jl Nat :=
  let fs := splitOn ':' cs
  if fs.length > 8 then .error (.argumentError "too many fields in IPv6 address")
  else if fs.length = 8 then parseipv6fields 8 fs
  else
    let last := (fs.getLast?).getD []
    if last.any (fun c => c == '.') then
      match parseipv6fields 6 fs.dropLast, parseIPv4 last with
      | .ok a, .ok b => .ok (a ||| b)
      | .error e, _ => .error e
      | _, .error e => .error e
    else parseipv6fields 8 fs

/-! ### IPv6 printing -/

/-- The nested longest-zero-run scan of `print(io, ip::IPv6)`,
stdlib/Sockets/src/IPAddr.jl:153-171: starting from the topmost zero group,
returns `(longest_sub_i, m)` for the best run seen. -/
def scanGo (h : Nat) : Nat → Int → Nat → Nat → Int × Nat
  | 0, lsi, m, _ => (lsi, m)
  | j + 1, lsi, m, c =>
    let c' := if ipv6Field h j = 0 then c + 1 else 0
    if c' > m then
      scanGo h j (if (j : Int) + c' != lsi + 1 then (j : Int) + c' - 1 else lsi) c' c'
    else scanGo h j lsi m c'
  termination_by j _ _ _ => j


/-- The outer loop of `print(io, ip::IPv6)`, stdlib/Sockets/src/IPAddr.jl:144-187.
`iprintGo h n lsi m acc` has `n` = Julia's `i` at the top of the loop, `acc`
the characters printed so far. The `m == 1` guard sets `longest_sub_i = 9`
(line 169-171), which no `i` in 0..7 equals, so the compression branch always
has `m ≥ 2`; the `m = 1` fallback below is therefore unreachable on scan-derived
states (Julia itself would loop forever there). -/
def iprintGo (h : Nat) : Nat → Int → Nat → JStr → JStr
  | 0, _, _, acc => acc
  | n + 1, lsi, m, acc =>
    let i := n
    let field := ipv6Field h i
    let p :=
      if field = 0 ∧ lsi = -1 then
        let (l2, m2) := scanGo h i i 1 1
        (if m2 = 1 then 9 else l2, m2)
      else (lsi, m)
    if (i : Int) = p.1 then
      if hm : 2 ≤ p.2 then
        if i + 1 ≤ p.2 then iprintGo h 0 p.1 p.2 (acc ++ [':', ':'])
        else
          have hdec : i + 1 - p.2 < n + 1 := by omega
          iprintGo h (i + 1 - p.2) p.1 p.2 (acc ++ [':'])
      else iprintGo h 0 p.1 p.2 acc
    else
      let sep := if i = 7 then [] else [':']
      iprintGo h i p.1 p.2 (acc ++ sep ++ hexStr field)
  termination_by n _ _ _ => n
  decreasing_by all_goals omega

/-- `print(io, ip::IPv6)` / `string(ip::IPv6)`. -/
def ipv6Str (h : Nat) : JStr := iprintGo h 8 (-1) 0 []

/-- `show(io, ip::IPv6)`, stdlib/Sockets/src/IPAddr.jl:141. -/
def ipv6Show (h : Nat) : JStr := ['i', 'p', '"'] ++ ipv6Str h ++ ['"']

/-! ### RFC 5952 section 4 reference form -/

/-- Length of the run of zero groups ending at group `i`. -/
def zeroLen (h : Nat) : Nat → Nat
  | 0 => if ipv6Field h 0 = 0 then 1 else 0
  | i + 1 => if ipv6Field h (i + 1) = 0 then zeroLen h i + 1 else 0

/-- Maximal zero runs of `h` as `(top, len)`, tops descending. -/
def runTops (h : Nat) : Nat → List (Nat × Nat)
  | 0 => if ipv6Field h 0 = 0 then [(0, zeroLen h 0)] else []
  | i + 1 =>
    (if ipv6Field h (i + 1) == 0 ∧ (i + 1 == 7 ∨ ipv6Field h (i + 2) ≠ 0)
      then [(i + 1, zeroLen h (i + 1))] else []) ++ runTops h i

/-- Longest run wins; ties keep the first (leftmost / highest) run. -/
def bestOf : List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | r :: rest => match bestOf rest with
    | none => some r
    | some s => some (if s.2 > r.2 then s else r)

/-- The leftmost longest run of at least two zero groups, if any. -/
def bestRun (h : Nat) : Option (Nat × Nat) :=
  bestOf ((runTops h 7).filter (fun r => 2 ≤ r.2))

/-- RFC 5952 section 4 text of a host: lowercase hex groups, the leftmost
longest run of two or more zero groups compressed to `::`, a lone zero group
never compressed. -/
def rfc5952 (h : Nat) : JStr :=
  match bestRun h with
  | none => List.intercalate [':'] ((List.range 8).map (fun i => hexStr (ipv6Field h (7 - i))))
  | some (t, m) =>
    let upper := (List.range (7 - t)).map (fun k => hexStr (ipv6Field h (7 - k)))
    let lower := (List.range (t + 1 - m)).map (fun k => hexStr (ipv6Field h (t - m - k)))
    List.intercalate [':'] upper ++ [':', ':'] ++ List.intercalate [':'] lower

/-! ### InetAddr and isless -/

/-- `show(io, addr::InetAddr)`, stdlib/Sockets/src/IPAddr.jl:324-329. -/
def inet4Show (h : Nat) (port : Nat) : JStr :=
  "Sockets.InetAddr{IPv4}".toList ++ ['('] ++ ipv4Show h ++ ", ".toList ++ decStr port ++ [')']

/-- `isless(a::T, b::T) = isless(a.host, b.host)`,
stdlib/Sockets/src/IPAddr.jl:10. -/
def islessIP (a b : Nat) : Bool := decide (a < b)

end JuliaLean.Sockets
