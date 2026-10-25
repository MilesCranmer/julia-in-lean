import JuliaLean.Strings.Ops

/-!
# Searching and splitting, `base/strings/search.jl` and `base/strings/util.jl`

Matches of a String needle are `start:stop` ranges, written `(start, stop)`.
-/

namespace JuliaLean.Strings

/-- `memchr`-based `findnext(==(b), codeunits(s), i)`, `base/search.jl:175-189`:
the first index `k ≥ i` holding `b`. Bound: `n + 1 - i`. -/
def memchrFrom (bs : List UInt8) (b : UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | k + 1, i => if bs.getD (i - 1) 0 == b then some i else memchrFrom bs b k (i + 1)

/-- `findnext(==(b), a::DenseUInt8, i)`, `base/strings/search.jl:175-180`. -/
def findnextByte (bs : List UInt8) (b : UInt8) (i : JInt64) : SJl (Option JInt64) :=
  if i.val < 1 then .error boundsErr
  else if i.val > bs.length then .ok none
  else .ok ((memchrFrom bs b (bs.length + 1 - i.val.toNat) i.val.toNat).map fun k => ix k)

/-- `memrchr`-based `findprev(==(b), a, i)`: the last index `k ≤ i` holding `b`. -/
def memrchrFrom (bs : List UInt8) (b : UInt8) : Nat → Option Nat
  | 0 => none
  | k + 1 => if bs.getD k 0 == b then some (k + 1) else memrchrFrom bs b k

/-- `findprev(==(b), a::DenseUInt8, i)`, `base/strings/search.jl:239-244`. -/
def findprevByte (bs : List UInt8) (b : UInt8) (i : JInt64) : SJl (Option JInt64) :=
  if i.val > bs.length then .error boundsErr
  else if i.val < 1 then .ok none
  else .ok ((memrchrFrom bs b i.val.toNat).map fun k => ix k)

/-- `last_utf8_byte(c)`, `base/strings/search.jl:34-38`. -/
def lastUtf8Byte (c : UInt32) : UInt8 :=
  let shift := ((4 - ncodeunitsChar c) * 8) % 32
  (c >>> shift.toUInt32).toUInt8

/-- `is_standalone_byte(x) = (x < 0x80) | (x > 0xf7)`, `base/strings/search.jl:42`. -/
def isStandalone (x : UInt8) : Bool := decide (x < 0x80) || decide (x > 0xf7)

/-- The loop of `iterate(s::FwCharPosIter, i)`, `base/strings/search.jl:73-91`.
Each pass increases `i`; bound `n + 1 - i`. -/
def fwLoop (s : JStr) (c : UInt32) (byte : UInt8) (ncu : Nat) : Nat → JInt64 → SJl (Option (JInt64 × JInt64))
  | 0, _ => .ok none
  | k + 1, i =>
    if i.val > (ncodeunits s).val then .ok none
    else
      match findnextByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) =>
        let i := i + ix 1
        let index := i - ix ncu
        if !isvalidAt s index then fwLoop s c byte ncu k i
        else
          match iterate s index with
          | none => .error .assertion
          | some (ch, _) => if ch == c then .ok (some (index, i)) else fwLoop s c byte ncu k i

/-- `iterate(s::FwCharPosIter, i)`, `base/strings/search.jl:62-93`. -/
def fwIterate (s : JStr) (c : UInt32) (i : JInt64) : SJl (Option (JInt64 × JInt64)) :=
  let byte := lastUtf8Byte c
  if isStandalone byte then
    if i.val > (ncodeunits s).val then .ok none
    else
      match findnextByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) => .ok (some (i, i + ix 1))
  else fwLoop s c byte (ncodeunitsChar c) (s.bytes.length + 2) i

/-- `findnext(==(c), s::String, i)` for `c::Char`, `base/strings/search.jl:143-166`. -/
def findnextChar (c : UInt32) (s : JStr) (i : JInt64) : SJl (Option JInt64) :=
  let scu := ncodeunits s
  if i.val = (scu + ix 1).val then .ok none
  else if decide (i.val < 1) || decide (i.val > (scu + ix 1).val) then .error boundsErr
  else
    let u := (c >>> 24).toUInt8
    if !isvalidAt s i then .error (.stringIndexError i.val)
    else if isStandalone u then findnextByte s.bytes u i
    else (fwIterate s c i).map (·.map (·.1))

/-- The loop of `iterate(s::RvCharPosIter, i)`, `base/strings/search.jl:125-134`.
Each pass decreases `i`; bound `i + 1`. -/
def rvLoop (s : JStr) (c : UInt32) (byte : UInt8) (ncu : Nat) : Nat → JInt64 → SJl (Option (JInt64 × JInt64))
  | 0, _ => .ok none
  | k + 1, i =>
    if i.val < ncu then .ok none
    else
      match findprevByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) =>
        let index := i - ix ncu + ix 1
        let i := i - ix 1
        if !isvalidAt s index then rvLoop s c byte ncu k i
        else
          match iterate s index with
          | none => .error .assertion
          | some (ch, _) => if ch == c then .ok (some (index, i)) else rvLoop s c byte ncu k i

/-- `iterate(s::RvCharPosIter, i)`, `base/strings/search.jl:117-136`. -/
def rvIterate (s : JStr) (c : UInt32) (i : JInt64) : SJl (Option (JInt64 × JInt64)) :=
  let ncu := ncodeunitsChar c
  let byte := lastUtf8Byte c
  if isStandalone byte then
    if i.val < ncu then .ok none
    else
      match findprevByte s.bytes byte i with
      | .error e => .error e
      | .ok none => .ok none
      | .ok (some i) => .ok (some (i, i - ix 1))
  else
    let i := imin (ncodeunits s) (i + ix ncu - ix 1)
    rvLoop s c byte ncu (s.bytes.length + 2) i

/-- `findprev(==(c), s::String, i)` for `c::Char`, `base/strings/search.jl:209-230`. -/
def findprevChar (c : UInt32) (s : JStr) (i : JInt64) : SJl (Option JInt64) :=
  if decide (i.val = (ncodeunits s + ix 1).val) || decide (i.val = 0) then .ok none
  else if decide (i.val < 1) || decide (i.val > (ncodeunits s + ix 1).val) then .error boundsErr
  else
    let u := (c >>> 24).toUInt8
    if isStandalone u then findprevByte s.bytes u i
    else (rvIterate s c i).map (·.map (·.1))

/-- `_search_bloom_mask(c) = UInt64(1) << (c & 63)`, `base/strings/search.jl:388-390`. -/
def bloomBit (b : UInt8) : UInt64 := (1 : UInt64) <<< (b &&& 63).toUInt64

/-- `_nthbyte`: one-based byte access. -/
abbrev nth (bs : List UInt8) (i : Int) : UInt8 := bs.getD (i - 1).toNat 0

/-- The inner comparison loop, `base/strings/search.jl:437-443`: the number of
leading bytes `t[1..j]` that match `s[i+1..i+j]`, up to `n - 1`. -/
def matchLen (s t : List UInt8) (i : Int) (n : Nat) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j =>
    if j < n - 1 then
      if nth s (i + j + 1) != nth t (j + 1) then j else matchLen s t i n k (j + 1)
    else j

/-- The main loop of the byte `_searchindex`, `base/strings/search.jl:434-463`.
Every pass increases `i`; bound `w - i + 1`. -/
def searchLoop (s t : List UInt8) (n : Nat) (w : Int) (mask : UInt64) (skip : Int) (tlast : UInt8) :
    Nat → Int → Int
  | 0, _ => 0
  | k + 1, i =>
    if i ≤ w then
      if nth s (i + n) == tlast then
        let j := matchLen s t i n n 0
        if j = n - 1 then i + 1
        else
          let i := if i < w && (mask &&& bloomBit (nth s (i + n + 1))) == 0 then i + n else i + skip
          searchLoop s t n w mask skip tlast k (i + 1)
      else
        let i := if i < w && (mask &&& bloomBit (nth s (i + n + 1))) == 0 then i + n else i
        searchLoop s t n w mask skip tlast k (i + 1)
    else 0

/-- `_searchindex(s::AbstractVector{UInt8}, t::AbstractVector{UInt8}, _i)`,
`base/strings/search.jl:401-466`. Index arithmetic stays far inside Int. -/
def searchindexBytes (s t : List UInt8) (i0 : JInt64) : SJl Int := do
  let n := t.length
  let m := s.length
  let i : Int := i0.val
  if i < 1 ∨ i > m + 1 then throw boundsErr
  if n = 0 then return (if 1 ≤ i ∧ i ≤ m + 1 then max 1 i else 0)
  if m = 0 then return 0
  if n = 1 then
    let r ← findnextByte s (nth t 1) i0
    return (r.map (·.val)).getD 0
  let w : Int := (m : Int) - n
  if w < 0 ∨ i - 1 > w then return 0
  let tlast := nth t n
  let (mask, skip) := (List.range n).foldl (fun (acc : UInt64 × Int) j0 =>
    let j : Nat := j0 + 1
    let mask := acc.1 ||| bloomBit (nth t j)
    let skip := if nth t j == tlast && j < n then (n : Int) - j - 1 else acc.2
    (mask, skip)) ((0 : UInt64), (n : Int) - 1)
  return searchLoop s t n w mask skip tlast (m + 2) (i - 1)

/-- `_searchindex(s::DenseUTF8String, t::DenseUTF8String, i)`, `base/strings/search.jl:395-399`. -/
def searchindexStr (s t : JStr) (i : JInt64) : SJl Int :=
  if (lastindex t).val = 1 then
    match getindex t (ix 1) with
    | .error e => .error e
    | .ok c => (findnextChar c s i).map fun r => (r.map (·.val)).getD 0
  else searchindexBytes s.bytes t.bytes i

/-- `findnext(t::AbstractString, s::AbstractString, i)` = `_search(s, t, Int(i))`,
`base/strings/search.jl:468-479,507` for two Strings. -/
def findnextStr (t s : JStr) (i : JInt64) : SJl (Option (Int × Int)) := do
  let idx ← searchindexStr s t i
  if t.bytes.length = 0 then return some (idx, idx - 1)
  else if idx ≥ 1 then return some (idx, idx + (lastindex t).val - 1)
  else return none

/-- The main loop of the byte `_rsearchindex`, `base/strings/search.jl:752-780`.
Every pass decreases `i`; bound `i`. -/
def rsearchLoop (s t : List UInt8) (n : Nat) (mask : UInt64) (skip : Int) (tfirst : UInt8) :
    Nat → Int → Int
  | 0, _ => 0
  | k + 1, i =>
    if i > 0 then
      if nth s i == tfirst then
        let j := (matchLen s t (i - 1) (n + 1) n 1)
        if j = n then i
        else
          let i := if i > 1 && (mask &&& bloomBit (nth s (i - 1))) == 0 then i - n else i - skip
          rsearchLoop s t n mask skip tfirst k (i - 1)
      else
        let i := if i > 1 && (mask &&& bloomBit (nth s (i - 1))) == 0 then i - n else i
        rsearchLoop s t n mask skip tfirst k (i - 1)
    else 0

/-- `_rsearchindex(s::AbstractVector{UInt8}, t::AbstractVector{UInt8}, _k)`,
`base/strings/search.jl:721-783`. -/
def rsearchindexBytes (s t : List UInt8) (k0 : Int) : SJl Int := do
  let n := t.length
  let m := s.length
  let k := k0
  if k < 0 then throw boundsErr
  if n = 0 then return (if 0 ≤ k ∧ k ≤ m then max k 1 else 0)
  if m = 0 then return 0
  if n = 1 then
    let r ← findprevByte s (nth t 1) (ix k)
    return (r.map (·.val)).getD 0
  let w : Int := (m : Int) - n
  if w < 0 ∨ k ≤ 0 then return 0
  let tfirst := nth t 1
  let (mask, skip) := ((List.range n).reverse).foldl (fun (acc : UInt64 × Int) j0 =>
    let j : Nat := j0 + 1
    let mask := acc.1 ||| bloomBit (nth t j)
    let skip := if nth t j == tfirst && j > 1 then (j : Int) - 2 else acc.2
    (mask, skip)) ((0 : UInt64), (n : Int) - 1)
  return rsearchLoop s t n mask skip tfirst (m + 2) (min (k - n + 1) (w + 1))

/-- `_rsearchindex(s::DenseUTF8String, t::DenseUTF8String, i)`, `base/strings/search.jl:705-719`. -/
def rsearchindexStr (s t : JStr) (i : JInt64) : SJl Int :=
  let lt := lastindex t
  if lt.val = 1 then
    match getindex t (ix 1) with
    | .error e => .error e
    | .ok c => (findprevChar c s i).map fun r => (r.map (·.val)).getD 0
  else if lt.val ≠ 0 then
    if i.val ≤ (ncodeunits s).val then
      match nextind s i with
      | .error e => .error e
      | .ok j => rsearchindexBytes s.bytes t.bytes (j - ix 1).val
    else rsearchindexBytes s.bytes t.bytes i.val
  else if i.val > s.bytes.length then .ok 0
  else if i.val = 0 then .ok 1
  else .ok i.val

/-- `findprev(t::AbstractString, s::AbstractString, i)` = `_rsearch(s, t, Int(i))`,
`base/strings/search.jl:785-796,821` for two Strings. -/
def findprevStr (t s : JStr) (i : JInt64) : SJl (Option (Int × Int)) := do
  let idx ← rsearchindexStr s t i
  if t.bytes.length = 0 then return some (idx, idx - 1)
  else if idx > 0 then return some (idx, idx + (lastindex t).val - 1)
  else return none

/-- `iterate(iter::SplitIterator, (i, k, n))`, `base/strings/util.jl:791-807`, for a
String and a `Char` splitter (`isequal(c)`, whose `findnext` is `findnextChar`).
The inner `while` loop is bounded by the remaining code units (`k` increases). -/
def splitInner (s : JStr) (c : UInt32) (limit : JInt64) (keepempty : Bool) :
    Nat → JInt64 → JInt64 → JInt64 → Option JInt64 → SJl (Option (JSub × (JInt64 × JInt64 × JInt64)))
  | fuel, i, k, n, r =>
    let tail : SJl (Option (JSub × (JInt64 × JInt64 × JInt64))) :=
      if !keepempty && !decide (i.val ≤ (ncodeunits s).val) then .ok none
      else (substring s i (lastindex s) false).map fun sub =>
        some (sub, (ncodeunits s + ix 2, k, n + ix 1))
    match fuel, r with
    | 0, _ => tail
    | _, none => tail
    | fuel + 1, some j =>
      if !(decide (n.val ≠ (limit - ix 1).val) && decide (j.val ≤ (ncodeunits s).val)) then tail
      else
        match nextind s j with
        | .error e => .error e
        | .ok k =>
          let k_ : SJl JInt64 := if k.val ≤ j.val then nextind s j else .ok k
          match k_ with
          | .error e => .error e
          | .ok k_ =>
            let cont (i : JInt64) : SJl (Option (JSub × (JInt64 × JInt64 × JInt64))) :=
              match findnextChar c s k_ with
              | .error e => .error e
              | .ok r => splitInner s c limit keepempty fuel i k_ n r
            if i.val < k.val then
              match prevind s j with
              | .error e => .error e
              | .ok pj =>
                match substring s i pj false with
                | .error e => .error e
                | .ok sub =>
                  if keepempty || decide (i.val < j.val) then .ok (some (sub, (k, k_, n + ix 1)))
                  else cont k
            else cont i

def splitIterate (s : JStr) (c : UInt32) (limit : JInt64) (keepempty : Bool)
    (st : JInt64 × JInt64 × JInt64) : SJl (Option (JSub × (JInt64 × JInt64 × JInt64))) :=
  let (i, k, n) := st
  if (i - ix 1).val > (ncodeunits s).val then .ok none
  else
    match findnextChar c s k with
    | .error e => .error e
    | .ok r => splitInner s c limit keepempty (s.bytes.length + 2) i k n r

/-- `split(s, c; limit, keepempty)` = `collect(eachsplit(...))`, `base/strings/util.jl:958-961`.
Every yielded piece advances the state; bound `n + 2` pieces. -/
def splitAll (s : JStr) (c : UInt32) (limit : JInt64) (keepempty : Bool) :
    Nat → JInt64 × JInt64 × JInt64 → SJl (List JSub)
  | 0, _ => .ok []
  | fuel + 1, st =>
    match splitIterate s c limit keepempty st with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (sub, st')) => (splitAll s c limit keepempty fuel st').map (sub :: ·)

def split (s : JStr) (c : UInt32) (limit : JInt64 := ix 0) (keepempty : Bool := true) : SJl (List JSub) :=
  splitAll s c limit keepempty (s.bytes.length + 2) (ix 1, ix 1, ix 0)

end JuliaLean.Strings
