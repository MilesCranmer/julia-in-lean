import JuliaLean.Strings.Char

/-!
# SubString and derived String operations

`base/strings/substring.jl`, `base/strings/basic.jl`, `base/strings/util.jl`,
`base/strings/stringview.jl` (master `bbfa0ce4150`).
-/

namespace JuliaLean.Strings

/-- `SubString{String}`, `base/strings/substring.jl:71-106`. -/
structure JSub where
  str : JStr
  offset : JInt64
  ncu : JInt64
  deriving DecidableEq, Repr

/-- The code units of a SubString: `codeunit(s::SubString, i) =
codeunit(s.string, s.offset + i)`, `base/strings/substring.jl:146-149`. -/
def JSub.view (ss : JSub) : JStr := ss.str.slice ss.offset.val.toNat ss.ncu.val.toNat

/-- `SubString{T}(s, i, j)`, `base/strings/substring.jl:76-84`. `checked = false`
models `@inbounds`. `checkbounds(s, i:j)` is `1 ≤ i && j ≤ ncodeunits(s)` for a
nonempty range (`base/strings/basic.jl:206-207`). -/
def substring (s : JStr) (i j : JInt64) (checked : Bool := true) : SJl JSub :=
  if !decide (i.val ≤ j.val) then .ok ⟨s, ix 0, ix 0⟩
  else
    let chk : SJl Unit :=
      if !checked then .ok ()
      else if !(decide (1 ≤ i.val) && decide (j.val ≤ (ncodeunits s).val)) then .error boundsErr
      else if !isvalidAt s i then .error (.stringIndexError i.val)
      else if !isvalidAt s j then .error (.stringIndexError j.val)
      else .ok ()
    match chk with
    | .error e => .error e
    | .ok () =>
      match nextind s j with
      | .error e => .error e
      | .ok j' => .ok ⟨s, i - ix 1, j' - i⟩

/-- `raw_substring(s, first_index, n_codeunits)`, `base/strings/substring.jl:86-91`. -/
def rawSubstring (s : JStr) (first n : JInt64) (checked : Bool := true) : SJl JSub :=
  if checked && (decide (n.val < 0) || decide (first.val < 1) ||
      decide (n.val > (ncodeunits s - first + ix 1).val)) then .error boundsErr
  else .ok ⟨s, first - ix 1, n⟩

/-- `SubString(s) = @inbounds raw_substring(s, 1, ncodeunits(s))`,
`base/strings/substring.jl:117`. -/
def wholeSub (s : JStr) : JSub := ⟨s, ix 0, ncodeunits s⟩

/-- `iterate(s::SubString, i)`, `base/strings/substring.jl:151-158`. -/
def subIterate (ss : JSub) (i : JInt64) : SJl (Option (UInt32 × JInt64)) :=
  if i.val = (ss.ncu + ix 1).val then .ok none
  else if !(decide (1 ≤ i.val) && decide (i.val ≤ ss.ncu.val)) then .error boundsErr
  else
    match iterate ss.str (ss.offset + i) with
    | none => .ok none
    | some (c, j) => .ok (some (c, j - ss.offset))

/-- `length(s::SubString{String})`, `base/strings/substring.jl:144`. -/
def subLength (ss : JSub) : SJl JInt64 :=
  lengthRange ss.str (ss.offset + ix 1) (ss.offset + ss.ncu)

/-- `isvalid(s::SubString, i)`, `base/strings/substring.jl:168-172`. -/
def subIsvalid (ss : JSub) (i : JInt64) : Bool :=
  decide (1 ≤ i.val ∧ i.val ≤ ss.ncu.val) && isvalidAt ss.str (ss.offset + i)

/-- `getindex(s::SubString, i)`, `base/strings/substring.jl:160-163`. -/
def subGetindex (ss : JSub) (i : JInt64) : SJl UInt32 :=
  if !(decide (1 ≤ i.val) && decide (i.val ≤ ss.ncu.val)) then .error boundsErr
  else getindex ss.str (ss.offset + i)

/-- Complete iteration traces of a SubString, including a thrown error. -/
inductive SubIterTrace (ss : JSub) : JInt64 → SJl (List (UInt32 × JInt64)) → Prop where
  | done {i} : subIterate ss i = .ok none → SubIterTrace ss i (.ok [])
  | error {i e} : subIterate ss i = .error e → SubIterTrace ss i (.error e)
  | step {i c j r} : subIterate ss i = .ok (some (c, j)) → SubIterTrace ss j r →
      SubIterTrace ss i ((fun xs => (c, i) :: xs) <$> r)

/-- `min(x, y)` on Int: `ifelse(y < x, y, x)`. -/
def imin (x y : JInt64) : JInt64 := if y.val < x.val then y else x
/-- `max(x, y)` on Int: `ifelse(y < x, x, y)`. -/
def imax (x y : JInt64) : JInt64 := if y.val < x.val then x else y

/-- `first(s::AbstractString, n::Integer) = @inbounds s[1:min(end, nextind(s, 0, n))]`,
`base/strings/basic.jl:700`. -/
def firstN (s : JStr) (n : JInt64) : SJl JStr :=
  match nextindN s (ix 0) n with
  | .error e => .error e
  | .ok k => getindexRange s (ix 1) (imin (lastindex s) k) false

/-- `last(s::AbstractString, n::Integer) = @inbounds s[max(1, prevind(s, ncodeunits(s)+1, n)):end]`,
`base/strings/basic.jl:719`. -/
def lastN (s : JStr) (n : JInt64) : SJl JStr :=
  match previndN s (ncodeunits s + ix 1) n with
  | .error e => .error e
  | .ok k => getindexRange s (imax (ix 1) k) (lastindex s) false

/-- `chop(s; head, tail)`, `base/strings/util.jl:236-241`. -/
def chop (s : JStr) (head tail : JInt64) : SJl JSub :=
  if s.bytes.length = 0 then .ok (wholeSub s)
  else
    match nextindN s (firstindex s) head with
    | .error e => .error e
    | .ok a =>
      match previndN s (lastindex s) tail with
      | .error e => .error e
      | .ok b => substring s a b

/-- `chomp(s::Union{String, SubString{String}})`, `base/strings/util.jl:379-391`, for a String. -/
def chomp (s : JStr) : SJl JSub :=
  let ncu := ncodeunits s
  let len :=
    if ncu.val = 0 then ix 0
    else
      let hasLf := s.bytes.getLast? == some 0x0a
      let two := decide (ncu.val > 1)
      let hasCr := hasLf && two && (cu s (ncu - bInt two) == 0x0d)
      ncu - (bInt hasLf + bInt hasCr)
  rawSubstring s (ix 1) len false

/-- The generic `chomp(s::AbstractString)`, `base/strings/util.jl:371-377`.
`'\n'` is `0x0a000000`, `'\r'` is `0x0d000000`. -/
def chompGeneric (s : JStr) : SJl JSub :=
  let i := lastindex s
  let test (k : JInt64) (c : UInt32) : SJl Bool :=
    if k.val < 1 then .ok true
    else match getindex s k with
      | .error e => .error e
      | .ok d => .ok (d != c)
  match test i 0x0a000000 with
  | .error e => .error e
  | .ok true => substring s (ix 1) i
  | .ok false =>
    match prevind s i with
    | .error e => .error e
    | .ok j =>
      match test j 0x0d000000 with
      | .error e => .error e
      | .ok true => substring s (ix 1) j
      | .ok false =>
        match prevind s j with
        | .error e => .error e
        | .ok k => substring s (ix 1) k

/-- `lstrip(f, s)`, `base/strings/util.jl:416-422`. `pairs(s)` zips `keys(s)`
(`EachStringIndex`, `base/strings/basic.jl:585`) with `iterate(s)`. The first
argument bounds the remaining steps by `n + 1 - i`. -/
def lstripLoop (f : UInt32 → Bool) (s : JStr) (e : JInt64) : Nat → JInt64 → JInt64 → SJl JSub
  | 0, _, _ => substring s (e + ix 1) e
  | k + 1, ki, si =>
    if ki.val > (ncodeunits s).val then substring s (e + ix 1) e
    else
      match nextind s ki with
      | .error err => .error err
      | .ok ki' =>
        match iterate s si with
        | none => substring s (e + ix 1) e
        | some (c, si') =>
          if !f c then substring s ki e false else lstripLoop f s e k ki' si'

def lstrip (f : UInt32 → Bool) (s : JStr) : SJl JSub :=
  lstripLoop f s (lastindex s) (s.bytes.length + 1) (ix 1) (ix 1)

/-- `rstrip(f, s)`, `base/strings/util.jl:451-456`: `Iterators.reverse(pairs(s))`
zips reversed `keys(s)` and reversed `s` (`base/strings/basic.jl:775-776`), both
starting at `lastindex(s)` and stepping with `prevind`. The first argument is
the remaining-step bound `i`. -/
def rstripLoop (f : UInt32 → Bool) (s : JStr) : Nat → JInt64 → SJl JSub
  | 0, _ => substring s (ix 1) (ix 0)
  | k + 1, i =>
    if i.val < 1 then substring s (ix 1) (ix 0)
    else
      match prevind s i with
      | .error e => .error e
      | .ok i' =>
        match getindex s i with
        | .error e => .error e
        | .ok c => if !f c then substring s (ix 1) i false else rstripLoop f s k i'

def rstrip (f : UInt32 → Bool) (s : JStr) : SJl JSub :=
  rstripLoop f s (s.bytes.length + 1) (lastindex s)

/-- `memcmp` sign over the first `len` bytes. -/
def memcmpSign : List UInt8 → List UInt8 → Nat → Int
  | _, _, 0 => 0
  | a :: as, b :: bs, k + 1 => if a < b then -1 else if b < a then 1 else memcmpSign as bs k
  | _, _, _ => 0

/-- `startswith(a::String, b::String)` via `DenseUTF8String`, `base/strings/util.jl:69-85`. -/
def startswith (a b : JStr) : SJl Bool :=
  let cub := ncodeunits b
  if (ncodeunits a).val < cub.val then .ok false
  else if memcmpSign a.bytes b.bytes b.bytes.length = 0 then
    match nextind a cub with
    | .error e => .error e
    | .ok k => .ok (decide (k.val = (cub + ix 1).val))
  else .ok false

/-- The generic `startswith(a::AbstractString, b::AbstractString)`,
`base/strings/util.jl:31-39`. The bound is the number of remaining `b` states. -/
def startswithLoop (a b : JStr) : Nat → Option (UInt32 × JInt64) → Option (UInt32 × JInt64) → Bool
  | _, _, none => true
  | _, none, some _ => false
  | 0, some _, some _ => false
  | k + 1, some (c, i), some (d, j) => if c != d then false
      else startswithLoop a b k (iterate a i) (iterate b j)

def startswithGeneric (a b : JStr) : Bool :=
  startswithLoop a b (b.bytes.length + 1) (iterate a (ix 1)) (iterate b (ix 1))

/-- `endswith(a::String, b::String)` via `DenseUTF8String`, `base/strings/util.jl:107-122`. -/
def endswith (a b : JStr) : SJl Bool :=
  let astart := ncodeunits a - ncodeunits b + ix 1
  if astart.val < 1 then .ok false
  else if memcmpSign (a.bytes.drop (astart.val - 1).toNat) b.bytes b.bytes.length = 0 then
    match thisind a astart with
    | .error e => .error e
    | .ok k => .ok (decide (k.val = astart.val))
  else .ok false

/-- `cmp(a::String, b::String)`, `base/strings/string.jl:232-236`. -/
def cmp (a b : JStr) : Int :=
  let c := memcmpSign a.bytes b.bytes (min a.bytes.length b.bytes.length)
  if c < 0 then -1 else if c > 0 then 1
  else if a.bytes.length < b.bytes.length then -1
  else if b.bytes.length < a.bytes.length then 1 else 0

/-- The loop of the generic `cmp(a::AbstractString, b::AbstractString)`,
`base/strings/basic.jl:308-317`; Char `<` compares bit patterns (`base/char.jl:264`). -/
def cmpLoop (a b : JStr) : Nat → Option (UInt32 × JInt64) → Option (UInt32 × JInt64) → Int
  | k + 1, some (c, i), some (d, j) =>
    if c != d then (if c < d then -1 else 1) else cmpLoop a b k (iterate a i) (iterate b j)
  | _, none, none => 0
  | _, none, some _ => -1
  | _, some _, _ => 1

def cmpGeneric (a b : JStr) : Int :=
  if a = b then 0
  else cmpLoop a b (a.bytes.length + 1) (iterate a (ix 1)) (iterate b (ix 1))

/-- `_string_n(n)`: a fresh String of `n` bytes (`jl_alloc_string`) filled by
the caller with the bytes `fill ()`. The model machine allocates any size below
`2^62` bytes and throws `OutOfMemoryError` otherwise. -/
def stringN (n : Nat) (fill : Unit → List UInt8) : SJl JStr :=
  if n < 2 ^ 62 then
    let bs := fill ()
    if h : bs.length < 2 ^ 62 then .ok ⟨bs, h⟩ else .error .outOfMemory
  else .error .outOfMemory

/-- `repeat(s::Union{String, SubString{String}}, r::Integer)`,
`base/strings/substring.jl:289-307`, for `r::Int`. `typemax(UInt) ÷ UInt(n)` and
`n*r` are UInt64 operations; the copy loop stores copy `i` at offset `i*n`. -/
def repeatStr (s : JStr) (r : JInt64) : SJl JStr :=
  if r.val < 0 then .error (.jl (.argumentError "can't repeat a string r times"))
  else
    let r := JInt.rem .u64 r
    if r.val = 0 then .ok JStr.empty
    else if r.val = 1 then .ok s
    else
      let n := s.bytes.length
      if n = 0 then .ok JStr.empty
      else if r.val > (JInt.typemax .u64).val / n then .error .outOfMemory
      else
        let size := (r * JInt.lit .u64 n).val.toNat
        stringN size fun _ => (List.replicate r.val.toNat s.bytes).flatten

/-- `repeat(c::AbstractChar, r::Integer)`, `base/strings/string.jl:682-715`,
for `c::Char`, `r::Int`. -/
def repeatChar (c : UInt32) (r : JInt64) : SJl JStr :=
  if r.val < 0 then .error (.jl (.argumentError "can't repeat a character r times"))
  else
    let r := JInt.rem .u64 r
    if r.val = 0 then .ok JStr.empty
    else
      let u := bswap32 c
      let n := 4 - clz32 (u ||| 0xff) / 8
      if r.val > (JInt.typemax .u64).val / n then .error .outOfMemory
      else
        let size := (r * JInt.lit .u64 n).val.toNat
        let unit := [u.toUInt8, (u >>> 8).toUInt8, (u >>> 16).toUInt8, (u >>> 24).toUInt8].take n
        stringN size fun _ => (List.replicate r.val.toNat unit).flatten

/-- Store `bs` at zero-based offset `p` of `buf`. -/
def writeAt (buf : List UInt8) (p : Nat) (bs : List UInt8) : List UInt8 :=
  buf.take p ++ bs ++ buf.drop (p + bs.length)

/-- `reverse(s::UTF8String)`, `base/strings/stringview.jl:67-83`: read chars
forwards and store each one ending at the current offset. -/
def reverse (s : JStr) : JStr :=
  let n := s.bytes.length
  let step : List UInt8 × Int → UInt32 → List UInt8 × Int := fun (buf, offs) c =>
    let offs := offs - ncodeunitsChar c
    (writeAt buf (offs - 1).toNat (charBytes c), offs)
  let out := ((chars s).foldl step (List.replicate n 0, n + 1)).1
  if h : out.length < 2 ^ 62 then ⟨out, h⟩ else JStr.empty

/-- `_isascii(cu, first, last)`, `base/strings/basic.jl:622-628`: OR the bytes. -/
def isasciiRange (bs : List UInt8) (a b : Int) : Bool :=
  let r := ((bs.drop (a - 1).toNat).take (b - a + 1).toNat).foldl (· ||| ·) 0
  decide (r < 0x80)

/-- `_isascii_chunks`, `base/strings/basic.jl:631-638`. Bound: `(last - n) / cs + 1`. -/
def isasciiChunksLoop (cs : Int) (bs : List UInt8) (last : Int) : Nat → Int → Bool
  | 0, _ => isasciiRange bs (last - cs + 1) last
  | k + 1, n =>
    if n ≤ last - cs then
      if !isasciiRange bs n (n + cs - 1) then false else isasciiChunksLoop cs bs last k (n + cs)
    else isasciiRange bs (last - cs + 1) last

/-- `isascii(s::String) = isascii(codeunits(s))`, `base/strings/string.jl:665`,
`base/strings/basic.jl:645-653`. -/
def isascii (s : JStr) : Bool :=
  let l : Int := s.bytes.length
  if l < 1536 then isasciiRange s.bytes 1 l
  else isasciiChunksLoop 1024 s.bytes l (s.bytes.length / 1024 + 1) 1

/-- `state_shifts`, `base/strings/string.jl:377`. -/
def dfaShifts : List Nat := [0, 4, 10, 14, 18, 24, 8, 20, 12, 26]

/-- `character_classes`, `base/strings/string.jl:379-394`, by byte value. -/
def dfaClass (b : UInt8) : Nat :=
  let x := b.toNat
  if x < 0x80 then 0 else if x < 0x90 then 1 else if x < 0xa0 then 9
  else if x < 0xc0 then 7 else if x < 0xc2 then 8 else if x < 0xe0 then 2
  else if x = 0xe0 then 10 else if x = 0xed then 4 else if x < 0xf0 then 3
  else if x = 0xf0 then 11 else if x < 0xf4 then 6 else if x = 0xf4 then 5 else 8

/-- `state_arrays`, `base/strings/string.jl:397-408`, row = class, column = state. -/
def dfaStates : List (List Nat) :=
  [[0, 1, 2, 2, 2, 2, 2, 2, 2, 2],
   [2, 2, 2, 1, 3, 2, 3, 2, 4, 4],
   [3, 3, 2, 2, 2, 2, 2, 2, 2, 2],
   [4, 4, 2, 2, 2, 2, 2, 2, 2, 2],
   [6, 6, 2, 2, 2, 2, 2, 2, 2, 2],
   [9, 9, 2, 2, 2, 2, 2, 2, 2, 2],
   [8, 8, 2, 2, 2, 2, 2, 2, 2, 2],
   [2, 2, 2, 1, 3, 3, 2, 4, 4, 2],
   [2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
   [2, 2, 2, 1, 3, 2, 3, 4, 4, 2],
   [5, 5, 2, 2, 2, 2, 2, 2, 2, 2],
   [7, 7, 2, 2, 2, 2, 2, 2, 2, 2]]

/-- `class_row[i]`, `base/strings/string.jl:411-422`: OR of
`UInt32(state_shifts[next+1]) << state_shifts[j]` over the ten states. -/
def dfaRow (cls : Nat) : UInt32 :=
  ((List.range 10).map fun j =>
    (UInt32.ofNat (dfaShifts.getD ((dfaStates.getD cls []).getD j 0) 0)) <<<
      (UInt32.ofNat (dfaShifts.getD j 0))).foldl (· ||| ·) 0

/-- `_utf_dfa_step(state, byte)`, `base/strings/string.jl:433`, with
`_UTF8_DFA_TABLE[byte+1] = class_row[class(byte)+1]` (`:424`). -/
def dfaStep (state : UInt32) (b : UInt8) : UInt32 := (dfaRow (dfaClass b) >>> state) &&& 0x1e

/-- `_isvalid_utf8_dfa(state, bytes, first, last)`, `base/strings/string.jl:435-440`. -/
def dfaRun (state : UInt32) (bs : List UInt8) (a b : Int) : UInt32 :=
  ((bs.drop (a - 1).toNat).take (b - a + 1).toNat).foldl dfaStep state

/-- `_find_nonascii_chunk`, `base/strings/string.jl:442-451`. Bound as for `isascii`. -/
def findNonasciiLoop (cs : Int) (bs : List UInt8) (last : Int) : Nat → Int → Option Int
  | 0, _ =>
    let n := last - cs + 1
    if !isasciiRange bs n last then some n else none
  | k + 1, n =>
    if n ≤ last - cs then
      if !isasciiRange bs n (n + cs - 1) then some n else findNonasciiLoop cs bs last k (n + cs)
    else
      let n := last - cs + 1
      if !isasciiRange bs n last then some n else none

/-- The inner ASCII-skipping loop of `_byte_string_classify_nonascii`,
`base/strings/string.jl:484-488`. Bound: remaining chunks. -/
def classifySkip (bs : List UInt8) (last : Int) (state : UInt32) : Nat → Int → Int → Int × Int
  | 0, start, stop => (start, stop)
  | k + 1, start, stop =>
    if state == 0x4 then
      if !isasciiRange bs start stop then (start, stop)
      else
        let start := start + 256
        if !(start ≤ last) then (start, stop)
        else classifySkip bs last state k start (min last (stop + 256))
    else (start, stop)

/-- `_byte_string_classify_nonascii(bytes, first, last)`, `base/strings/string.jl:476-497`.
Each outer iteration advances `start` by at least 256, bounding the loop. -/
def classifyLoop (bs : List UInt8) (last : Int) : Nat → Int → Int → UInt32 → Nat
  | 0, _, _, state => if state == 0x4 then 2 else 0
  | k + 1, start, stop, state =>
    if start ≤ last then
      let (start, stop) := classifySkip bs last state (bs.length / 256 + 2) start stop
      let state := dfaRun state bs start stop
      if state == 10 then 0
      else classifyLoop bs last k (start + 256) (min last (stop + 256)) state
    else if state == 0x4 then 2 else 0

def classifyNonascii (bs : List UInt8) (first last : Int) : Nat :=
  classifyLoop bs last (bs.length / 256 + 2) first (min last (first + 255)) 0x4

/-- `byte_string_classify(bytes)`, `base/strings/string.jl:462-474`. -/
def byteStringClassify (bs : List UInt8) : Nat :=
  let n : Int := bs.length
  if n > 1536 then
    match findNonasciiLoop 1024 bs n (bs.length / 1024 + 1) 1 with
    | none => 1
    | some start => classifyNonascii bs start n
  else if isasciiRange bs 1 n then 1
  else classifyNonascii bs 1 n

/-- `isvalid(s::String) = isvalid(String, codeunits(s))`, `base/strings/string.jl:499-502`. -/
def isvalidStr (s : JStr) : Bool := byteStringClassify s.bytes != 0

/-- `iterate(itr::PartitionIterator{<:AbstractString}, state)`,
`base/strings/util.jl:814-818`, for a String and `itr.n::Int`. -/
def partitionIterate (s : JStr) (n state : JInt64) : SJl (Option (JSub × JInt64)) :=
  if state.val > (ncodeunits s).val then .ok none
  else
    match nextindN s state (n - ix 1) with
    | .error e => .error e
    | .ok k =>
      let r := imin k (lastindex s)
      match substring s state r with
      | .error e => .error e
      | .ok sub =>
        match nextind s r with
        | .error e => .error e
        | .ok r' => .ok (some (sub, r'))

/-- `lpad(s, n, p=' ')`, `base/strings/util.jl:526-544`, for a String `s` with
`textwidth(s) = tw` and the default pad `' '` (`textwidth(' ') = 1`), which the
model treats as given values. `signed(n) - tw` is a wrapping Int subtraction. -/
def lpad (s : JStr) (tw n : JInt64) : SJl JStr :=
  let m := n - tw
  if m.val ≤ 0 then .ok s
  else
    let l := ix 1
    match JInt.div m l, JInt.remInt m l with
    | .ok q, .ok r =>
      match repeatChar 0x20000000 q with
      | .error e => .error e
      | .ok pad =>
        let tail := if r.val = 0 then s.bytes else charBytes 0x20000000 ++ s.bytes
        stringN (pad.bytes.length + tail.length) fun _ => pad.bytes ++ tail
    | _, _ => .error (.jl .divideError)

end JuliaLean.Strings
