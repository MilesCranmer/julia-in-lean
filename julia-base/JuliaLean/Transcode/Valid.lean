import JuliaLean.Transcode.Basic

/-!
# Well-formed UTF-8 and UTF-16

The Unicode definitions (Unicode 15, §3.9, Table 3-7 for UTF-8 and D91 for
UTF-16) that the properties of `transcode` refer to. A Julia `String` is
`isvalid` exactly when its bytes are well-formed UTF-8.
-/

namespace JuliaLean.Transcode

/-- A continuation byte `80..BF`. -/
def isC (b : UInt8) : Bool := 0x80 ≤ b && b ≤ 0xbf

/-- One well-formed UTF-8 byte sequence (one character), Table 3-7. -/
def wfChar : List UInt8 → Bool
  | [a] => a ≤ 0x7f
  | [a, b] => 0xc2 ≤ a && a ≤ 0xdf && isC b
  | [a, b, c] =>
    isC c &&
      (if a == 0xe0 then 0xa0 ≤ b && b ≤ 0xbf
       else if a == 0xed then 0x80 ≤ b && b ≤ 0x9f
       else 0xe1 ≤ a && a ≤ 0xef && isC b)
  | [a, b, c, d] =>
    isC c && isC d &&
      (if a == 0xf0 then 0x90 ≤ b && b ≤ 0xbf
       else if a == 0xf4 then 0x80 ≤ b && b ≤ 0x8f
       else 0xf1 ≤ a && a ≤ 0xf3 && isC b)
  | _ => false

/-- `bs` is well-formed UTF-8: a concatenation of well-formed characters. -/
def ValidUtf8 (bs : List UInt8) : Prop :=
  ∃ cs : List (List UInt8), (∀ c ∈ cs, wfChar c = true) ∧ bs = cs.flatten

/-- A high surrogate `D800..DBFF`. -/
def isHigh (u : UInt16) : Bool := (u &&& 0xfc00) == 0xd800

/-- A low surrogate `DC00..DFFF`. -/
def isLow (u : UInt16) : Bool := (u &&& 0xfc00) == 0xdc00

/-- Well-formed UTF-16 (D91): every high surrogate is immediately followed by a
low surrogate, and every low surrogate immediately follows a high surrogate. -/
def wf16 : List UInt16 → Bool
  | [] => true
  | [u] => !isHigh u && !isLow u
  | u :: v :: r =>
    if isHigh u then isLow v && wf16 r
    else !isLow u && wf16 (v :: r)

end JuliaLean.Transcode
