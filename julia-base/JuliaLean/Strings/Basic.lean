import JuliaLean.Core

/-!
# Strings as UTF-8 code units

Model of `String` from `base/strings/string.jl` and the generic index
functions of `base/strings/basic.jl` (master `bbfa0ce4150`).

* A `String` is its byte sequence (`JStr.bytes`), with no validity
  requirement: overlong forms, surrogates, truncated sequences and stray
  continuation bytes are all representable, exactly as in Julia
  (`base/strings/string.jl:80-90`).
* A `Char` is its 32-bit encoded bit pattern (`base/char.jl:39-52`): the
  UTF-8 bytes of the character, left-aligned, padded with zero bytes.
  Bit patterns are Lean `UInt8`/`UInt32`, whose operators are the
  fixed-width wrapping operators Julia uses on those types.
* Indices and counts are `Int` (`JInt64`) and use the wrapping `JInt`
  operators, so overflow happens exactly where Julia overflows.
* Julia's `while` loops are written as structural recursion on an explicit
  bound on the number of remaining iterations (for example `n - i` when `i`
  increases towards `n`). Each docstring states the bound; when it reaches
  zero the loop condition is false, so the bound never truncates a run.
-/

namespace JuliaLean.Strings

/-- Exceptions thrown by the modelled string functions. `jl` wraps the shared
`JlError` (BoundsError, ArgumentError, ...); the others are
`StringIndexError` (`base/strings/string.jl:56`), `OutOfMemoryError`,
`InvalidCharError` and `CodePointError` (`base/char.jl:102-107`) and an
`@assert` failure. -/
inductive SErr where
  | jl (e : JlError)
  | stringIndexError (i : Int)
  | outOfMemory
  | invalidChar (bits : UInt32)
  | codePointError (u : UInt32)
  | assertion
  deriving Repr, DecidableEq, Inhabited

abbrev SJl (α : Type) := Except SErr α

abbrev boundsErr : SErr := .jl .boundsError

/-- A Julia `String`: its UTF-8 code units. Julia cannot allocate `2^62` bytes,
so every String is shorter; the bound keeps `ncodeunits(s) + 1`-style index
arithmetic exact, as it is in Julia. -/
structure JStr where
  bytes : List UInt8
  small : bytes.length < 2 ^ 62

instance : DecidableEq JStr := fun a b =>
  if h : a.bytes = b.bytes then isTrue (by cases a; cases b; simp_all)
  else isFalse (by intro e; cases e; exact h rfl)

instance : Repr JStr := ⟨fun s _ => repr s.bytes⟩

def JStr.empty : JStr := ⟨[], by decide⟩

/-- Integer literal of type `Int`. -/
abbrev ix (x : Int) : JInt64 := JInt.lit .i64 x

/-- `Int(b)` for a Bool, as used in `n -= isvalid(s, i)`. -/
abbrev bInt (b : Bool) : JInt64 := ix (if b then 1 else 0)

/-- `ncodeunits(s::String) = Core.sizeof(s)`, `base/strings/string.jl:209`. -/
def ncodeunits (s : JStr) : JInt64 := ix s.bytes.length

/-- `@inbounds codeunit(s, i)` (`base/strings/string.jl:213-217`): the byte at
one-based index `i`. Only called at indices the caller has checked. -/
def cu (s : JStr) (i : JInt64) : UInt8 := s.bytes.getD (i.val.toNat - 1) 0

/-- `codeunit(s::String, i::Int)` with its bounds check, `base/strings/string.jl:213-217`. -/
def codeunit (s : JStr) (i : JInt64) : SJl UInt8 :=
  if 1 ≤ i.val ∧ i.val ≤ (ncodeunits s).val then .ok (cu s i) else .error boundsErr

/-- `b & 0xc0 == 0x80`: `b` is a continuation byte. -/
abbrev isCont (b : UInt8) : Bool := (b &&& 0xc0) == 0x80

/-- `between(b, lo, hi) = (lo ≤ b) & (b ≤ hi)`, `base/strings/string.jl:78`. -/
abbrev between (b lo hi : UInt8) : Bool := decide (lo ≤ b) && decide (b ≤ hi)

/-- `between` on `Int` indices. -/
abbrev betweenI (i lo hi : JInt64) : Bool := decide (lo.val ≤ i.val) && decide (i.val ≤ hi.val)

/-- The slow path `_thisind_continued`, `base/strings/string.jl:259-270`.
Precondition (from the caller): `b(i)` is a continuation byte and `i > 1`. -/
def thisindContinued (s : JStr) (i : JInt64) : JInt64 :=
  let b := cu s (i - ix 1)
  if between b 0xc0 0xf7 then i - ix 1
  else if !(isCont b && decide ((i - ix 2).val > 0)) then i
  else
    let b := cu s (i - ix 2)
    if between b 0xe0 0xf7 then i - ix 2
    else if !(isCont b && decide ((i - ix 3).val > 0)) then i
    else
      let b := cu s (i - ix 3)
      if between b 0xf0 0xf7 then i - ix 3 else i

/-- `_thisind_str(s, i::Int)`, `base/strings/string.jl:252-271`; this is
`thisind(s::String, i::Int)` (`:245`). -/
def thisind (s : JStr) (i : JInt64) : SJl JInt64 :=
  if i.val = 0 then .ok (ix 0)
  else
    let n := ncodeunits s
    if i.val = (n + ix 1).val then .ok i
    else if !betweenI i (ix 1) n then .error boundsErr
    else
      let b := cu s i
      if !(isCont b && decide ((i - ix 1).val > 0)) then .ok i
      else .ok (thisindContinued s i)

/-- `isvalid(s::String, i::Int) = checkbounds(Bool, s, i) && thisind(s, i) == i`,
`base/strings/string.jl:662`, with `checkbounds(Bool, s, i) = 1 ≤ i ≤ ncodeunits(s)`
(`base/strings/basic.jl:204-205`). -/
def isvalidAt (s : JStr) (i : JInt64) : Bool :=
  decide (1 ≤ i.val ∧ i.val ≤ (ncodeunits s).val) &&
    (match thisind s i with
     | .ok j => decide (j.val = i.val)
     | .error _ => false)

/-- The lead-byte part of `_nextind_continued`, `base/strings/string.jl:293-304`:
skip up to three continuation bytes after the lead byte `l` at `i`. -/
def nextindFromLead (s : JStr) (i n : JInt64) (l : UInt8) : JInt64 :=
  let i := i + ix 1
  if i.val > n.val then i
  else if !isCont (cu s i) then i
  else
    let i := i + ix 1
    if decide (i.val > n.val) || decide (l < 0xe0) then i
    else if !isCont (cu s i) then i
    else
      let i := i + ix 1
      if decide (i.val > n.val) || decide (l < 0xf0) then i
      else if !isCont (cu s i) then i else i + ix 1

/-- `_nextind_continued(s, i, n, l)`, `base/strings/string.jl:282-305`. -/
def nextindContinued (s : JStr) (i n : JInt64) (l : UInt8) : SJl JInt64 :=
  if l < 0xc0 then
    match thisind s i with
    | .error e => .error e
    | .ok i' =>
      if i'.val ≥ i.val then .ok (i + ix 1)
      else
        let l := cu s i'
        if decide (l < 0x80) || decide (0xf8 ≤ l) then .ok (i' + ix 1)
        else if !decide (l ≥ 0xc0) then .error .assertion
        else .ok (nextindFromLead s i' n l)
  else .ok (nextindFromLead s i n l)

/-- `_nextind_str(s, i::Int)`, `base/strings/string.jl:276-306`; this is
`nextind(s::String, i::Int)` (`:273`). -/
def nextind (s : JStr) (i : JInt64) : SJl JInt64 :=
  if i.val = 0 then .ok (ix 1)
  else
    let n := ncodeunits s
    if !betweenI i (ix 1) n then .error boundsErr
    else
      let l := cu s i
      if !between l 0x80 0xf7 then .ok (i + ix 1)
      else nextindContinued s i n l

/-- The loop of `nextind(s, i, n)`, `base/strings/basic.jl:569-572`:
`while n > 0 && i < z; n -= isvalid(s, i += 1); end; return i + n`.
The first argument is `z - i`, so at `0` the condition `i < z` is false. -/
def nextindNLoop (s : JStr) (z : JInt64) : Nat → JInt64 → JInt64 → JInt64
  | 0, i, n => i + n
  | k + 1, i, n =>
    if decide (n.val > 0) && decide (i.val < z.val) then
      let i := i + ix 1
      nextindNLoop s z k i (n - bInt (isvalidAt s i))
    else i + n

/-- `nextind(s::AbstractString, i::Int, n::Int)`, `base/strings/basic.jl:564-573`. -/
def nextindN (s : JStr) (i n : JInt64) : SJl JInt64 :=
  if n.val < 0 then .error (.jl (.argumentError "n cannot be negative"))
  else
    let z := ncodeunits s
    if !betweenI i (ix 0) z then .error boundsErr
    else if n.val = 0 then
      match thisind s i with
      | .error e => .error e
      | .ok j => if j.val = i.val then .ok i else .error (.stringIndexError i.val)
    else .ok (nextindNLoop s z (z.val - i.val).toNat i n)

/-- The loop of `prevind(s, i, n)`, `base/strings/basic.jl:510-513`:
`while n > 0 && 1 < i; n -= isvalid(s, i -= 1); end; return i - n`.
The first argument is `i - 1`, so at `0` the condition `1 < i` is false. -/
def previndNLoop (s : JStr) : Nat → JInt64 → JInt64 → JInt64
  | 0, i, n => i - n
  | k + 1, i, n =>
    if decide (n.val > 0) && decide (1 < i.val) then
      let i := i - ix 1
      previndNLoop s k i (n - bInt (isvalidAt s i))
    else i - n

/-- `prevind(s::AbstractString, i::Int, n::Int)`, `base/strings/basic.jl:505-514`.
`prevind(s, i)` is `prevind(s, i, 1)` (`:503`). -/
def previndN (s : JStr) (i n : JInt64) : SJl JInt64 :=
  if n.val < 0 then .error (.jl (.argumentError "n cannot be negative"))
  else
    let z := ncodeunits s + ix 1
    if !(decide (0 < i.val) && decide (i.val ≤ z.val)) then .error boundsErr
    else if n.val = 0 then
      match thisind s i with
      | .error e => .error e
      | .ok j => if j.val = i.val then .ok i else .error (.stringIndexError i.val)
    else .ok (previndNLoop s (i.val - 1).toNat i n)

/-- `prevind(s, i) = prevind(s, i, 1)`, `base/strings/basic.jl:503`. -/
def prevind (s : JStr) (i : JInt64) : SJl JInt64 := previndN s i (ix 1)

/-- `lastindex(s::String) = thisind(s, ncodeunits(s))`, `base/strings/string.jl:249`.
It cannot throw: `thisind(s, n)` is in bounds or `n = 0`. -/
def lastindex (s : JStr) : JInt64 :=
  match thisind s (ncodeunits s) with
  | .ok j => j
  | .error _ => ix 0

/-- `firstindex(s::AbstractString) = 1`, `base/strings/basic.jl:179`. -/
def firstindex (_ : JStr) : JInt64 := ix 1

/-- `iterate_continued(s, i, u)`, `base/strings/string.jl:517-538`. -/
def iterateContinued (s : JStr) (i : JInt64) (u : UInt32) : UInt32 × JInt64 :=
  if u < 0xc0000000 then (u, i + ix 1)
  else
    let n := ncodeunits s
    let i := i + ix 1
    if i.val > n.val then (u, i)
    else
      let b := cu s i
      if !isCont b then (u, i)
      else
        let u := u ||| (b.toUInt32 <<< 16)
        let i := i + ix 1
        if decide (i.val > n.val) || decide (u < 0xe0000000) then (u, i)
        else
          let b := cu s i
          if !isCont b then (u, i)
          else
            let u := u ||| (b.toUInt32 <<< 8)
            let i := i + ix 1
            if decide (i.val > n.val) || decide (u < 0xf0000000) then (u, i)
            else
              let b := cu s i
              if !isCont b then (u, i)
              else (u ||| b.toUInt32, i + ix 1)

/-- `iterate(s::String, i::Int)`, `base/strings/string.jl:508-514`.
`(i % UInt) - 1 < ncodeunits(s)` is a wrapping UInt64 subtraction followed by
Julia's exact mixed signed/unsigned comparison. -/
def iterate (s : JStr) (i : JInt64) : Option (UInt32 × JInt64) :=
  if !decide ((JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits s).val) then none
  else
    let b := cu s i
    let u := b.toUInt32 <<< 24
    if !between b 0x80 0xf7 then some (u, i + ix 1)
    else some (iterateContinued s i u)

/-- `getindex_continued(s, i, u)`, `base/strings/string.jl:548-573`. -/
def getindexContinued (s : JStr) (i : JInt64) (u : UInt32) : SJl UInt32 :=
  if u < 0xc0000000 then
    if isvalidAt s i then .ok u else .error (.stringIndexError i.val)
  else .ok (iterateContinued s i u).1

/-- `getindex(s::String, i::Int)`, `base/strings/string.jl:540-545`. -/
def getindex (s : JStr) (i : JInt64) : SJl UInt32 := do
  let b ← codeunit s i
  let u := b.toUInt32 <<< 24
  if !between b 0x80 0xf7 then pure u else getindexContinued s i u

theorem slice_small (s : JStr) (a b : Nat) : ((s.bytes.drop a).take b).length < 2 ^ 62 := by
  have := s.small; simp only [List.length_take, List.length_drop]; omega

/-- The fresh String holding `len` code units of `s` starting after byte `a`
(`unsafe_copyto!` from `pointer(s, a + 1)`). -/
def JStr.slice (s : JStr) (a len : Nat) : JStr := ⟨(s.bytes.drop a).take len, slice_small s a len⟩

/-- `getindex(s::String, r::UnitRange{Int})`, `base/strings/string.jl:580-595`, for
`r = i:j`. `checked = false` models a call under `@inbounds`, which skips the
`@boundscheck` block. `isempty(r)` is `j < i`. -/
def getindexRange (s : JStr) (i j : JInt64) (checked : Bool := true) : SJl JStr :=
  if j.val < i.val then .ok JStr.empty
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
      | .ok j' =>
        let j := j' - ix 1
        let n := JInt.rem .u64 (j - i + ix 1)
        .ok (s.slice (i.val - 1).toNat n.val.toNat)

/-- The loops of `_length_continued`, `base/strings/string.jl:635-658`. The state
is the head of the inner `while` loop, before `(i += 1) ≤ n`; `b` is the byte
read last. The first argument is `n - i`; every path back to the head passes
through the increment, and at `0` the test `(i += 1) ≤ n` fails. -/
def lenLoop (s : JStr) (n : JInt64) : Nat → JInt64 → UInt8 → JInt64 → JInt64
  | 0, _, _, c => c
  | k + 1, i, b, c =>
    let i := i + ix 1
    if !(decide (0xc0 ≤ b) && decide (b ≤ 0xf7)) then lenLoop s n k i (cu s i) c
    else
      let l := b
      let b := cu s i
      let x := isCont b
      let c := c - bInt x
      if !(x && decide (l ≥ 0xe0)) then lenLoop s n k i b c
      else
        match k with
        | 0 => c
        | k + 1 =>
          let i := i + ix 1
          let b := cu s i
          let x := isCont b
          let c := c - bInt x
          if !(x && decide (l ≥ 0xf0)) then lenLoop s n k i b c
          else
            match k with
            | 0 => c
            | k + 1 =>
              let i := i + ix 1
              let b := cu s i
              let c := c - bInt (isCont b)
              lenLoop s n k i b c

/-- `_length_continued(s, i, n, c)`, `base/strings/string.jl:635-658`. -/
def lengthContinued (s : JStr) (i n c : JInt64) : JInt64 :=
  if !decide (i.val < n.val) then c
  else lenLoop s n (n.val - i.val).toNat i (cu s i) c

/-- `length(s::String)`, `base/strings/string.jl:598-600`. -/
def length (s : JStr) : JInt64 :=
  lengthContinued s (ix 1) (ncodeunits s) (ncodeunits s)

/-- `length(s::String, i::Int, j::Int)` = `_length(s, i, j)`,
`base/strings/string.jl:607-624`. -/
def lengthRange (s : JStr) (i j : JInt64) : SJl JInt64 :=
  let n := ncodeunits s
  if !(decide (0 < i.val) && decide (i.val ≤ (n + ix 1).val)) then .error boundsErr
  else if !(decide (0 ≤ j.val) && decide (j.val < (n + ix 1).val)) then .error boundsErr
  else if j.val < i.val then .ok (ix 0)
  else
    match thisind s i with
    | .error e => .error e
    | .ok i' =>
      let c := j - i' + bInt (decide (i'.val = i.val))
      .ok (lengthContinued s i' j c)

/-- Complete iteration traces: `xs` lists the `(char, index)` pairs produced by
iterating `s` from state `i` until `iterate` returns `nothing`. -/
inductive IterTrace (s : JStr) : JInt64 → List (UInt32 × JInt64) → Prop where
  | done {i} : iterate s i = none → IterTrace s i []
  | step {i c j xs} : iterate s i = some (c, j) → IterTrace s j xs →
      IterTrace s i ((c, i) :: xs)

/-- `collect(s)` by repeated `iterate`, starting at `firstindex(s) = 1`. The bound
is `n + 1`: every step increases the state by at least one and `iterate`
returns `nothing` once the state exceeds `n` (see `iterTrace_collect`). -/
def collectFrom (s : JStr) : Nat → JInt64 → List (UInt32 × JInt64)
  | 0, _ => []
  | k + 1, i =>
    match iterate s i with
    | none => []
    | some (c, j) => (c, i) :: collectFrom s k j

def collectPairs (s : JStr) : List (UInt32 × JInt64) :=
  collectFrom s (s.bytes.length + 1) (ix 1)

/-- `collect(s)`: the characters. -/
def chars (s : JStr) : List UInt32 := (collectPairs s).map (·.1)

/-- `[i for i in a:ncodeunits(s) if isvalid(s, i)]`; the first argument counts the
remaining positions. -/
def validFrom (s : JStr) : Nat → JInt64 → List Int
  | 0, _ => []
  | k + 1, i => if isvalidAt s i then i.val :: validFrom s k (i + ix 1) else validFrom s k (i + ix 1)

/-- The valid indices `1 ≤ i ≤ ncodeunits(s)` in increasing order. -/
def validIndices (s : JStr) : List Int := validFrom s s.bytes.length (ix 1)

end JuliaLean.Strings
