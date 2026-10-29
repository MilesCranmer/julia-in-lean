import JuliaLean.base.strings.basic
import JuliaLean.base.strings.substring
import JuliaLean.base.generator

/-!
# Model of base/strings/util.jl

The source methods are generic over AbstractString and take operations from other Julia files as typed parameters.
-/

namespace JuliaLean.base.strings.util

open JuliaLean.base.strings.basic

/-! ## Prefix, suffix, and containment -/

/--
Julia source: base/strings/util.jl:31-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function startswith(a::AbstractString, b::AbstractString)
    i, j = iterate(a), iterate(b)
    while true
        j === nothing && return true # ran out of prefix: success!
        i === nothing && return false # ran out of source: failure
        i[1] == j[1] || return false # mismatch: failure
        i, j = iterate(a, i[2]), iterate(b, j[2])
    end
end
```
-/
def startswith {S T RA RB C D CU1 CU2 CT1 CT2 E : Type}
    (opsA : StringOps S RA C CU1 CT1 E) (opsB : StringOps T RB D CU2 CT2 E)
    (equalChar : C → D → Bool) (a : S) (b : T) : Except E Bool := do
  let i ← opsA.iterateFirst a
  let j ← opsB.iterateFirst b
  let rec loop (fuel : Nat) (i : Option (C × Index)) (j : Option (D × Index)) : Except E Bool :=
    match fuel with
    | 0 => .ok false
    | n + 1 =>
      match j with
      | none => .ok true
      | some (d, nextB) =>
        match i with
        | none => .ok false
        | some (c, nextA) =>
          if equalChar c d then do
            let i ← opsA.iterateAt a nextA
            let j ← opsB.iterateAt b nextB
            loop n i j
          else .ok false
  loop (opsA.iterationBound a + opsB.iterationBound b + 1) i j

/--
Julia source: base/strings/util.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
startswith(str::AbstractString, chars::Chars) = !isempty(str) && first(str)::AbstractChar in chars
```
-/
def startswithChars {S Q C E : Type}
    (isempty : S → Bool) (first : S → Except E C) (member : C → Q → Bool)
    (str : S) (chars : Q) : Except E Bool := do
  if isempty str then return false
  return member (← first str) chars

/--
Julia source: base/strings/util.jl:57-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function endswith(a::AbstractString, b::AbstractString)
    a, b = Iterators.Reverse(a), Iterators.Reverse(b)
    i, j = iterate(a), iterate(b)
    while true
        j === nothing && return true # ran out of suffix: success!
        i === nothing && return false # ran out of source: failure
        i[1] == j[1] || return false # mismatch: failure
        i, j = iterate(a, i[2]), iterate(b, j[2])
    end
end
```
-/
def endswith {S T RA RB R1 R2 C D CU1 CU2 CT1 CT2 E : Type}
    (reverseA : S → RA) (reverseB : T → RB)
    (opsA : StringOps RA R1 C CU1 CT1 E)
    (opsB : StringOps RB R2 D CU2 CT2 E)
    (equalChar : C → D → Bool) (a : S) (b : T) : Except E Bool := do
  let a := reverseA a
  let b := reverseB b
  let i ← opsA.iterateFirst a
  let j ← opsB.iterateFirst b
  let rec loop (fuel : Nat) (i : Option (C × Index)) (j : Option (D × Index)) : Except E Bool :=
    match fuel with
    | 0 => .ok false
    | n + 1 =>
      match j with
      | none => .ok true
      | some (d, nextB) =>
        match i with
        | none => .ok false
        | some (c, nextA) =>
          if equalChar c d then do
            let i ← opsA.iterateAt a nextA
            let j ← opsB.iterateAt b nextB
            loop n i j
          else .ok false
  loop (opsA.iterationBound a + opsB.iterationBound b + 1) i j

/--
Julia source: base/strings/util.jl:67-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
endswith(str::AbstractString, chars::Chars) = !isempty(str) && last(str) in chars
```
-/
def endswithChars {S Q C E : Type}
    (isempty : S → Bool) (last : S → Except E C) (member : C → Q → Bool)
    (str : S) (chars : Q) : Except E Bool := do
  if isempty str then return false
  return member (← last str) chars

/--
Julia source: base/strings/util.jl:152-152 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
contains(haystack::AbstractString, needle) = occursin(needle, haystack)
```
-/
def contains {H N : Type} (occursin : N → H → Bool) (haystack : H) (needle : N) : Bool :=
  occursin needle haystack

/-! ## Chopping -/

/--
Julia source: base/strings/util.jl:236-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chop(s::AbstractString; head::Integer = 0, tail::Integer = 1)
    if isempty(s)
        return SubString(s)
    end
    SubString(s, nextind(s, firstindex(s), head), prevind(s, lastindex(s), tail))
end
```
-/
def chop {S R I N E : Type}
    (isempty : S → Bool) (whole : S → Except E R)
    (firstindex lastindex : S → I) (nextind : S → I → N → Except E I)
    (prevind : S → I → N → Except E I) (substring : S → I → I → Except E R)
    (s : S) (head tail : N) : Except E R := do
  if isempty s then return ← whole s
  let first ← nextind s (firstindex s) head
  let last ← prevind s (lastindex s) tail
  substring s first last

/-! ## Prefix and suffix removal -/

/--
Julia source: base/strings/util.jl:268-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chopprefix(s::AbstractString, prefix::AbstractString)
    k = firstindex(s)
    i, j = iterate(s), iterate(prefix)
    while true
        j === nothing && i === nothing && return SubString(s, 1, 0) # s == prefix: empty result
        j === nothing && return @inbounds SubString(s, k) # ran out of prefix: success!
        i === nothing && return SubString(s) # ran out of source: failure
        i[1] == j[1] || return SubString(s) # mismatch: failure
        k = i[2]
        i, j = iterate(s, k), iterate(prefix, j[2])
    end
end
```
-/
def chopprefix {S P R C D E : Type}
    (iterateFirstS : S → Except E (Option (C × Index)))
    (iterateFirstP : P → Except E (Option (D × Index)))
    (iterateS : S → Index → Except E (Option (C × Index)))
    (iterateP : P → Index → Except E (Option (D × Index)))
    (boundS : S → Nat) (boundP : P → Nat)
    (firstindex : S → Index) (empty : S → Except E R)
    (subFrom : S → Index → Except E R) (whole : S → Except E R)
    (equalChar : C → D → Bool) (s : S) (pre : P) : Except E R := do
  let k := firstindex s
  let i ← iterateFirstS s
  let j ← iterateFirstP pre
  let rec loop (fuel : Nat) (k : Index) (i : Option (C × Index))
      (j : Option (D × Index)) : Except E R :=
    match fuel with
    | 0 => whole s
    | n + 1 =>
      match j with
      | none =>
        match i with
        | none => empty s
        | some _ => subFrom s k
      | some (d, nextP) =>
        match i with
        | none => whole s
        | some (c, nextS) =>
          if equalChar c d then do
            let i ← iterateS s nextS
            let j ← iterateP pre nextP
            loop n nextS i j
          else whole s
  loop (boundS s + boundP pre + 1) k i j

/--
Julia source: base/strings/util.jl:290-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chopprefix(s::AbstractString, prefix::AbstractChar)
    if !isempty(s) && first(s) == prefix
        return SubString(s, nextind(s, firstindex(s)))
    else
        return SubString(s)
    end
end
```
-/
def chopprefixChar {S R C D E : Type}
    (isempty : S → Bool) (first : S → Except E C) (firstindex : S → Index)
    (nextind : S → Index → Except E Index) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (equalChar : C → D → Bool) (s : S) (pre : D) :
    Except E R := do
  if !isempty s then
    if equalChar (← first s) pre then
      return ← subFrom s (← nextind s (firstindex s))
  whole s
/--
Julia source: base/strings/util.jl:281-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chopprefix(s::Union{String, SubString{String}},
                    prefix::Union{String, SubString{String}})
    if startswith(s, prefix)
        SubString(s, 1 + ncodeunits(prefix))
    else
        SubString(s)
    end
end
```
-/
def chopprefixFast {S P R E : Type}
    (starts : S → P → Except E Bool) (ncodeunits : P → Index)
    (subFrom : S → Index → Except E R) (whole : S → Except E R)
    (s : S) (pre : P) : Except E R := do
  if ← starts s pre then subFrom s (int 1 + ncodeunits pre)
  else whole s

/--
Julia source: base/strings/util.jl:320-332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chopsuffix(s::AbstractString, suffix::AbstractString)
    a, b = Iterators.Reverse(s), Iterators.Reverse(suffix)
    k = lastindex(s)
    i, j = iterate(a), iterate(b)
    while true
        j === nothing && i === nothing && return SubString(s, 1, 0) # s == suffix: empty result
        j === nothing && return @inbounds SubString(s, firstindex(s), k) # ran out of suffix: success!
        i === nothing && return SubString(s) # ran out of source: failure
        i[1] == j[1] || return SubString(s) # mismatch: failure
        k = i[2]
        i, j = iterate(a, k), iterate(b, j[2])
    end
end
```
-/
def chopsuffix {S P RS RP R C D E : Type}
    (reverseS : S → RS) (reverseP : P → RP)
    (iterateFirstS : RS → Except E (Option (C × Index)))
    (iterateFirstP : RP → Except E (Option (D × Index)))
    (iterateS : RS → Index → Except E (Option (C × Index)))
    (iterateP : RP → Index → Except E (Option (D × Index)))
    (boundS : RS → Nat) (boundP : RP → Nat) (lastindex : S → Index)
    (firstindex : S → Index) (empty : S → Except E R)
    (through : S → Index → Index → Except E R) (whole : S → Except E R)
    (equalChar : C → D → Bool) (s : S) (suffix : P) : Except E R := do
  let a := reverseS s
  let b := reverseP suffix
  let k := lastindex s
  let i ← iterateFirstS a
  let j ← iterateFirstP b
  let rec loop (fuel : Nat) (k : Index) (i : Option (C × Index))
      (j : Option (D × Index)) : Except E R :=
    match fuel with
    | 0 => whole s
    | n + 1 =>
      match j with
      | none =>
        match i with
        | none => empty s
        | some _ => through s (firstindex s) k
      | some (d, nextP) =>
        match i with
        | none => whole s
        | some (c, nextS) =>
          if equalChar c d then do
            let i ← iterateS a nextS
            let j ← iterateP b nextP
            loop n nextS i j
          else whole s
  loop (boundS a + boundP b + 1) k i j

/--
Julia source: base/strings/util.jl:344-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chopsuffix(s::AbstractString, suffix::AbstractChar)
    if !isempty(s) && last(s) == suffix
        return SubString(s, firstindex(s), prevind(s, lastindex(s)))
    else
        return SubString(s)
    end
end
```
-/
def chopsuffixChar {S R C D E : Type}
    (isempty : S → Bool) (last : S → Except E C) (firstindex lastindex : S → Index)
    (prevind : S → Index → Except E Index) (through : S → Index → Index → Except E R)
    (whole : S → Except E R) (equalChar : C → D → Bool) (s : S) (suffix : D) :
    Except E R := do
  if !isempty s then
    if equalChar (← last s) suffix then
      return ← through s (firstindex s) (← prevind s (lastindex s))
  whole s
/--
Julia source: base/strings/util.jl:334-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chopsuffix(s::Union{String, SubString{String}},
                    suffix::Union{String, SubString{String}})
    if !isempty(suffix) && endswith(s, suffix)
        astart = ncodeunits(s) - ncodeunits(suffix) + 1
        @inbounds SubString(s, firstindex(s), prevind(s, astart))
    else
        SubString(s)
    end
end
```
-/
def chopsuffixFast {S P R E : Type}
    (isempty : P → Bool) (ends : S → P → Except E Bool)
    (ncodeunitsS : S → Index) (ncodeunitsP : P → Index) (firstindex : S → Index)
    (prevind : S → Index → Except E Index)
    (substring : S → Index → Index → Except E R) (whole : S → Except E R)
    (s : S) (suffix : P) : Except E R := do
  if isempty suffix then return ← whole s
  if ← ends s suffix then
    let astart := ncodeunitsS s - ncodeunitsP suffix + int 1
    let stop ← prevind s astart
    substring s (firstindex s) stop
  else whole s

/-! ## Newline removal -/

/--
Julia source: base/strings/util.jl:371-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function chomp(s::AbstractString)
    i = lastindex(s)
    (i < 1 || s[i] != '\n') && (return SubString(s, 1, i))
    j = prevind(s,i)
    (j < 1 || s[j] != '\r') && (return SubString(s, 1, j))
    return SubString(s, 1, prevind(s,j))
end

```
-/
def chomp {S R C E : Type}
    (lastindex : S → Index) (getindex : S → Index → Except E C)
    (prevind : S → Index → Except E Index) (substring : S → Index → Index → Except E R)
    (equalChar : C → C → Bool) (newline carriageReturn : C) (s : S) : Except E R := do
  let i := lastindex s
  if i.val < 1 then return ← substring s (int 1) i
  if !equalChar (← getindex s i) newline then return ← substring s (int 1) i
  let j ← prevind s i
  if j.val < 1 then return ← substring s (int 1) j
  if !equalChar (← getindex s j) carriageReturn then return ← substring s (int 1) j
  substring s (int 1) (← prevind s j)

/-! ## Whitespace and character stripping -/

structure StripOps (S R C FState BState E : Type) where
  lastindex : S → Index
  firstindex : S → Index
  addOne : Index → Index
  substring : S → Index → Index → Except E R
  pairsFirst : S → Except E (Option ((Index × C) × FState))
  pairsNext : S → FState → Except E (Option ((Index × C) × FState))
  pairsBound : S → Nat
  reversePairsFirst : S → Except E (Option ((Index × C) × BState))
  reversePairsNext : S → BState → Except E (Option ((Index × C) × BState))
  reversePairsBound : S → Nat

/--
Julia source: base/strings/util.jl:416-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lstrip(f, s::AbstractString)
    e = lastindex(s)
    for (i::Int, c::AbstractChar) in pairs(s)
        !f(c) && return @inbounds SubString(s, i, e)
    end
    SubString(s, e+1, e)
end
```
-/
def lstrip {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Bool) (s : S) : Except E R := do
  let e := ops.lastindex s
  let first ← ops.pairsFirst s
  let rec loop (fuel : Nat) (current : Option ((Index × C) × FS)) : Except E R :=
    match fuel with
    | 0 => ops.substring s (ops.addOne e) e
    | n + 1 =>
      match current with
      | none => ops.substring s (ops.addOne e) e
      | some ((i, c), state) =>
        if !f c then ops.substring s i e
        else do
          let next ← ops.pairsNext s state
          loop n next
  loop (ops.pairsBound s + 1) first

/--
Julia source: base/strings/util.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lstrip(s::AbstractString) = lstrip(isspace, s)
```
-/
def lstripDefault {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (isspace : C → Bool) (s : S) : Except E R :=
  lstrip ops isspace s

/--
Julia source: base/strings/util.jl:424-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lstrip(s::AbstractString, chars::Chars) = lstrip(in(chars), s)
```
-/
def lstripChars {S R C Q FS BS E : Type} (ops : StripOps S R C FS BS E)
    (member : C → Q → Bool) (chars : Q) (s : S) : Except E R :=
  lstrip ops (fun c => member c chars) s

/--
Julia source: base/strings/util.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lstrip(::AbstractString, ::AbstractString) = throw(ArgumentError("Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))
```
-/
def lstripStringError {S T R E : Type} (argumentError : String → E)
    (_s : S) (_chars : T) : Except E R :=
  .error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s")

/--
Julia source: base/strings/util.jl:451-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rstrip(f, s::AbstractString)
    for (i, c) in Iterators.reverse(pairs(s))
        f(c::AbstractChar) || return @inbounds SubString(s, 1, i::Int)
    end
    SubString(s, 1, 0)
end
```
-/
def rstrip {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Bool) (s : S) : Except E R := do
  let first ← ops.reversePairsFirst s
  let rec loop (fuel : Nat) (current : Option ((Index × C) × BS)) : Except E R :=
    match fuel with
    | 0 => ops.substring s (int 1) (int 0)
    | n + 1 =>
      match current with
      | none => ops.substring s (int 1) (int 0)
      | some ((i, c), state) =>
        if !f c then ops.substring s (int 1) i
        else do
          let next ← ops.reversePairsNext s state
          loop n next
  loop (ops.reversePairsBound s + 1) first

/--
Julia source: base/strings/util.jl:457-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rstrip(s::AbstractString) = rstrip(isspace, s)
```
-/
def rstripDefault {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (isspace : C → Bool) (s : S) : Except E R :=
  rstrip ops isspace s

/--
Julia source: base/strings/util.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rstrip(s::AbstractString, chars::Chars) = rstrip(in(chars), s)
```
-/
def rstripChars {S R C Q FS BS E : Type} (ops : StripOps S R C FS BS E)
    (member : C → Q → Bool) (chars : Q) (s : S) : Except E R :=
  rstrip ops (fun c => member c chars) s

/--
Julia source: base/strings/util.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rstrip(::AbstractString, ::AbstractString) = throw(ArgumentError("Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))
```
-/
def rstripStringError {S T R E : Type} (argumentError : String → E)
    (_s : S) (_chars : T) : Except E R :=
  .error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s")

/--
Julia source: base/strings/util.jl:486-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(s::AbstractString) = lstrip(rstrip(s))
```
-/
def stripDefault {S R T C FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (isspace : C → Bool) (s : S) : Except E T := do
  let right ← rstripDefault opsS isspace s
  lstripDefault opsR isspace right

/--
Julia source: base/strings/util.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(s::AbstractString, chars::Chars) = lstrip(rstrip(s, chars), chars)
```
-/
def stripChars {S R T C Q FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (member : C → Q → Bool) (chars : Q) (s : S) : Except E T := do
  let right ← rstripChars opsS member chars s
  lstripChars opsR member chars right

/--
Julia source: base/strings/util.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(::AbstractString, ::AbstractString) = throw(ArgumentError("Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))
```
-/
def stripStringError {S U R E : Type} (argumentError : String → E)
    (_s : S) (_chars : U) : Except E R :=
  .error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s")

/--
Julia source: base/strings/util.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(f, s::AbstractString) = lstrip(f, rstrip(f, s))
```
-/
def stripPredicate {S R T C FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (f : C → Bool) (s : S) : Except E T := do
  let right ← rstrip opsS f s
  lstrip opsR f right

/--
Julia source: base/strings/util.jl:379-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :removable :foldable function chomp(s::Union{String, SubString{String}})
    cu = codeunits(s)
    ncu = length(cu)
    len = if iszero(ncu)
        0
    else
        has_lf = @inbounds(cu[ncu]) == 0x0a
        two_bytes = ncu > 1
        has_cr = has_lf & two_bytes & (@inbounds(cu[ncu - two_bytes]) == 0x0d)
        ncu - (has_lf + has_cr)
    end
    @inbounds raw_substring(s, 1, len)
end
```
-/
def chompFast {S R E : Type} (codeunits : S → List UInt8)
    (rawSubstring : S → Index → Nat → Except E R) (s : S) : Except E R :=
  let cu := codeunits s
  let ncu := cu.length
  let len :=
    if ncu = 0 then 0
    else
      let hasLF := cu.getD (ncu - 1) 0 == 0x0a
      let twoBytes := ncu > 1
      let hasCR := hasLF && twoBytes &&
        (cu.getD (ncu - (if twoBytes then 1 else 0) - 1) 0 == 0x0d)
      ncu - (if hasLF then 1 else 0) - (if hasCR then 1 else 0)
  rawSubstring s (int 1) len
/-! ## Padding -/

inductive PadInput (S C : Type) where
  | string : S → PadInput S C
  | character : C → PadInput S C

inductive PadPart (S C R : Type) where
  | value : PadInput S C → PadPart S C R
  | view : R → PadPart S C R

structure PadRemainderOps (S C R FS E : Type) where
  textwidthChar : C → Except E Index
  pairsFirst : S → Except E (Option ((Index × C) × FS))
  pairsNext : S → FS → Except E (Option ((Index × C) × FS))
  pairsBound : S → Nat
  viewPrefix : S → Index → Except E R
  whole : S → Except E R

/--
Julia source: base/strings/util.jl:516-523 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pad_remainder(p::AbstractString, r::Int)
    width = 0
    for (i, c) in pairs(p)
        width += Int(textwidth(c))::Int
        width >= r && return @view p[begin:i]
    end
    return SubString(p) # unreachable: caller guarantees r < textwidth(p)
end
```
-/
def padRemainderString {S C R FS E : Type}
    (ops : PadRemainderOps S C R FS E) (p : S) (r : Index) : Except E R := do
  let first ← ops.pairsFirst p
  let rec loop (fuel : Nat) (current : Option ((Index × C) × FS))
      (width : Index) : Except E R :=
    match fuel with
    | 0 => ops.whole p
    | n + 1 =>
      match current with
      | none => ops.whole p
      | some ((i, c), state) => do
        let charWidth ← ops.textwidthChar c
        let width := width + charWidth
        if width.val ≥ r.val then ops.viewPrefix p i
        else
          let next ← ops.pairsNext p state
          loop n next width
  loop (ops.pairsBound p + 1) first (int 0)

/--
Julia source: base/strings/util.jl:524-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pad_remainder(p::AbstractChar, r::Int) = p
```
-/
def padRemainderChar {C : Type} (_r : Index) (p : C) : C := p

/-- Dispatch to the concrete pad-remainder method. -/
def padRemainder {S C R FS E : Type} (ops : PadRemainderOps S C R FS E)
    (p : PadInput S C) (r : Index) : Except E (PadPart S C R) := do
  match p with
  | .string str => return .view (← padRemainderString ops str r)
  | .character c => return .value (.character (padRemainderChar r c))

structure PadValueOps (S C R O N E : Type) where
  toInt : N → Except E Index
  signed : Index → Index
  textwidth : PadInput S C → Except E Index
  isAnnotated : PadInput S C → Bool
  repr : PadInput S C → String
  ncodeunits : PadInput S C → Nat
  isString : PadInput S C → Bool
  codeunitIsUInt8 : PadInput S C → Bool
  argumentError : String → E
  divrem : Index → Index → Except E (Index × Index)
  repeatPad : PadInput S C → Index → Except E (PadInput S C)
  assemble : Bool → List (PadPart S C R) → Except E O

/-- The zero-width pad error text of lpad. -/
def lpadZeroWidthMessage {S C R O N E : Type} (ops : PadValueOps S C R O N E)
    (s p : PadInput S C) : String :=
  ops.repr p ++ " has zero textwidth" ++
    (if ops.ncodeunits p != 1 then "" else
      "; maybe you want pad^max(0, npad - ncodeunits(str)) * str to pad by codeunits" ++
        (if ops.isString s && !ops.codeunitIsUInt8 s then "?" else " (bytes)?"))

/--
Julia source: base/strings/util.jl:526-544 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function lpad(
    s::Union{AbstractChar,AbstractString},
    n::Integer,
    p::Union{AbstractChar,AbstractString}=' ',
)
    stringfn = if _isannotated(s) || _isannotated(p)
        annotatedstring else string end
    n = Int(n)::Int
    m = signed(n) - Int(textwidth(s))::Int
    m ≤ 0 && return stringfn(s)
    l = Int(textwidth(p))::Int
    if l == 0
        throw(ArgumentError("$(repr(p)) has zero textwidth" * (ncodeunits(p) != 1 ? "" :
            "; maybe you want pad^max(0, npad - ncodeunits(str)) * str to pad by codeunits" *
            (s isa AbstractString && codeunit(s) != UInt8 ? "?" : " (bytes)?"))))
    end
    q, r = divrem(m, l)
    r == 0 ? stringfn(p^q, s) : stringfn(p^q, _pad_remainder(p, r), s)
end
```
-/
def lpad {S C R O N E FS : Type}
    (ops : PadValueOps S C R O N E) (remOps : PadRemainderOps S C R FS E)
    (s p : PadInput S C) (n : N) : Except E O := do
  let stringfn := ops.isAnnotated s || ops.isAnnotated p
  let n ← ops.toInt n
  let m := ops.signed n - (← ops.textwidth s)
  if m.val ≤ 0 then return ← ops.assemble stringfn [.value s]
  let l ← ops.textwidth p
  if l.val = 0 then throw (ops.argumentError (lpadZeroWidthMessage ops s p))
  let (q, r) ← ops.divrem m l
  let pq ← ops.repeatPad p q
  if r.val = 0 then ops.assemble stringfn [.value pq, .value s]
  else do
    let rem ← padRemainder remOps p r
    ops.assemble stringfn [.value pq, rem, .value s]

/--
Julia source: base/strings/util.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lpad(s, n::Integer, p::Union{AbstractChar,AbstractString}=' ') = lpad(string(s)::AbstractString, n, string(p))
```
-/
def lpadWrapper {A B S C R O N E FS : Type}
    (ops : PadValueOps S C R O N E) (remOps : PadRemainderOps S C R FS E)
    (stringifyA : A → Except E (PadInput S C))
    (stringifyB : B → Except E (PadInput S C)) (s : A) (n : N) (p : B) : Except E O := do
  let s ← stringifyA s
  let p ← stringifyB p
  lpad ops remOps s p n

/-- The zero-width pad error text of rpad. -/
def rpadZeroWidthMessage {S C R O N E : Type} (ops : PadValueOps S C R O N E)
    (s p : PadInput S C) : String :=
  ops.repr p ++ " has zero textwidth" ++
    (if ops.ncodeunits p != 1 then "" else
      "; maybe you want str * pad^max(0, npad - ncodeunits(str)) to pad by codeunits" ++
        (if ops.isString s && !ops.codeunitIsUInt8 s then "?" else " (bytes)?"))

/--
Julia source: base/strings/util.jl:566-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rpad(
    s::Union{AbstractChar,AbstractString},
    n::Integer,
    p::Union{AbstractChar,AbstractString}=' ',
)
    stringfn = if _isannotated(s) || _isannotated(p)
        annotatedstring else string end
    n = Int(n)::Int
    m = signed(n) - Int(textwidth(s))::Int
    m ≤ 0 && return stringfn(s)
    l = Int(textwidth(p))::Int
    if l == 0
        throw(ArgumentError("$(repr(p)) has zero textwidth" * (ncodeunits(p) != 1 ? "" :
            "; maybe you want str * pad^max(0, npad - ncodeunits(str)) to pad by codeunits" *
            (s isa AbstractString && codeunit(s) != UInt8 ? "?" : " (bytes)?"))))
    end
    q, r = divrem(m, l)
    r == 0 ? stringfn(s, p^q) : stringfn(s, p^q, _pad_remainder(p, r))
end
```
-/
def rpad {S C R O N E FS : Type}
    (ops : PadValueOps S C R O N E) (remOps : PadRemainderOps S C R FS E)
    (s p : PadInput S C) (n : N) : Except E O := do
  let stringfn := ops.isAnnotated s || ops.isAnnotated p
  let n ← ops.toInt n
  let m := ops.signed n - (← ops.textwidth s)
  if m.val ≤ 0 then return ← ops.assemble stringfn [.value s]
  let l ← ops.textwidth p
  if l.val = 0 then throw (ops.argumentError (rpadZeroWidthMessage ops s p))
  let (q, r) ← ops.divrem m l
  let pq ← ops.repeatPad p q
  if r.val = 0 then ops.assemble stringfn [.value s, .value pq]
  else do
    let rem ← padRemainder remOps p r
    ops.assemble stringfn [.value s, .value pq, rem]

/--
Julia source: base/strings/util.jl:564-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rpad(s, n::Integer, p::Union{AbstractChar,AbstractString}=' ') = rpad(string(s)::AbstractString, n, string(p))
```
-/
def rpadWrapper {A B S C R O N E FS : Type}
    (ops : PadValueOps S C R O N E) (remOps : PadRemainderOps S C R FS E)
    (stringifyA : A → Except E (PadInput S C))
    (stringifyB : B → Except E (PadInput S C)) (s : A) (n : N) (p : B) : Except E O := do
  let s ← stringifyA s
  let p ← stringifyB p
  rpad ops remOps s p n
/-! ## Width-aware truncation -/

inductive TruncMode where
  | left
  | right
  | center
  deriving DecidableEq

inductive TruncPiece (S V : Type) where
  | string : S → TruncPiece S V
  | view : V → TruncPiece S V

structure TruncateOps (S V R C E : Type) where
  iterate : S → IterSteps C Index E
  iterationBound : S → Nat
  textwidthChar : C → Index
  textwidthReplacement : R → Except E Index
  getindex : S → Index → Except E C
  firstindex : S → Index
  lastindex : S → Index
  prevind : S → Index → Except E Index
  nextind : S → Index → Except E Index
  substring : S → Index → Index → Except E V
  stringify : S → Except E S
  stringifyReplacement : R → Except E S
  concat : List (TruncPiece S V) → Except E S
  argumentError : String → E

/-- Incremental character-width check stopping as soon as the accumulated width exceeds `maxwidth`. -/
def checkTextwidthLoop {C E : Type} (textwidthChar : C → Index) (maxwidth : Index) :
    IterSteps C Index E → Index → Except E Bool
  | .done, _ => .ok true
  | .fail err, _ => .error err
  | .yield c state next, total =>
    let total := total + textwidthChar c
    if total.val > maxwidth.val then .ok false
    else checkTextwidthLoop textwidthChar maxwidth (next state) total

/--
Julia source: base/strings/util.jl:687-695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function check_textwidth(str::AbstractString, maxwidth::Integer)
    # check efficiently for early return if str is wider than maxwidth
    total_width = 0
    for c in str
        total_width += textwidth(c)
        total_width > maxwidth && return false
    end
    return true
end
```
-/
def checkTextwidth {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (maxwidth : Index) : Except E Bool :=
  checkTextwidthLoop ops.textwidthChar maxwidth (ops.iterate str) (int 0)

/-- The width of the character at one valid string index. -/
def textwidthAt {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (i : Index) : Except E Index := do
  return ops.textwidthChar (← ops.getindex str i)

/-- The character-removal loop shared by the truncation modes. -/
def truncateLoop {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (maxwidth : Index) (mode : TruncMode) (preferLeft : Bool) :
    Nat → Index → Index → Index → Index → Index → Bool → Except E (Index × Index)
  | 0, left, right, _, _, _, _ => .ok (left, right)
  | fuel + 1, left, right, width, removedLeft, removedRight, forceOther => do
    let removeRight := mode == .left || (mode == .center && (!preferLeft || left.val > (ops.firstindex str).val))
    let firstStep ←
      if removeRight then do
        let removed ← textwidthAt ops str right
        if mode == .left || removedRight.val ≤ removedLeft.val || forceOther then
          if (width + removed).val ≤ maxwidth.val then do
            let right ← ops.prevind str right
            pure (some (right, width + removed, removedRight + removed, false))
          else pure none
        else pure (some (right, width, removedRight, true))
      else pure (some (right, width, removedRight, forceOther))
    match firstStep with
    | none => .ok (left, right)
    | some (right, width, removedRight, forceOther) =>
      if mode == .right || mode == .center then do
        let removed ← textwidthAt ops str left
        if mode == .left || removedLeft.val ≤ removedRight.val || forceOther then
          if (width + removed).val ≤ maxwidth.val then do
            let left ← ops.nextind str left
            return ← truncateLoop ops str maxwidth mode preferLeft fuel left right (width + removed)
              (removedLeft + removed) removedRight false
          else return (left, right)
        else
          return ← truncateLoop ops str maxwidth mode preferLeft fuel left right width
            removedLeft removedRight true
      else
        truncateLoop ops str maxwidth mode preferLeft fuel left right width
          removedLeft removedRight forceOther

/--
Julia source: base/strings/util.jl:697-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string_truncate_boundaries(
            str::AbstractString,
            maxwidth::Integer,
            replacement::Union{AbstractString,AbstractChar},
            ::Val{mode},
            prefer_left::Bool = true) where {mode}
    maxwidth >= 0 || throw(ArgumentError("maxwidth $maxwidth should be non-negative"))
    check_textwidth(str, maxwidth) && return nothing

    l0, _ = left, right = firstindex(str), lastindex(str)
    width = textwidth(replacement)
    # used to balance the truncated width on either side
    rm_width_left, rm_width_right, force_other = 0, 0, false
    @inbounds while true
        if mode === :left || (mode === :center && (!prefer_left || left > l0))
            rm_width = textwidth(str[right])
            if mode === :left || (rm_width_right <= rm_width_left || force_other)
                force_other = false
                (width += rm_width) <= maxwidth || break
                rm_width_right += rm_width
                right = prevind(str, right)
            else
                force_other = true
            end
        end
        if mode ∈ (:right, :center)
            rm_width = textwidth(str[left])
            if mode === :left || (rm_width_left <= rm_width_right || force_other)
                force_other = false
                (width += textwidth(str[left])) <= maxwidth || break
                rm_width_left += rm_width
                left = nextind(str, left)
            else
                force_other = true
            end
        end
    end
    return prevind(str, left), nextind(str, right)
end
```
-/
def stringTruncateBoundaries {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (maxwidth : Index) (replacement : R) (mode : TruncMode)
    (preferLeft : Bool := true) : Except E (Option (Index × Index)) := do
  if maxwidth.val < 0 then
    throw (ops.argumentError ("maxwidth " ++ toString maxwidth.val ++ " should be non-negative"))
  if ← checkTextwidth ops str maxwidth then return none
  let left := ops.firstindex str
  let right := ops.lastindex str
  let width ← ops.textwidthReplacement replacement
  let (left, right) ← truncateLoop ops str maxwidth mode preferLeft
    (ops.iterationBound str * 2 + 4) left right width (int 0) (int 0) false
  let left ← ops.prevind str left
  let right ← ops.nextind str right
  return some (left, right)

/--
Julia source: base/strings/util.jl:609-617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rtruncate(str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar} = '…')
    ret = string_truncate_boundaries(str, Int(maxwidth), replacement, Val(:right))
    if isnothing(ret)
        return string(str)
    else
        left, _ = ret::Tuple{Int,Int}
        @views return str[begin:left] * replacement
    end
end
```
-/
def rtruncate {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (maxwidth : Index) (replacement : R) : Except E S := do
  match ← stringTruncateBoundaries ops str maxwidth replacement .right true with
  | none => ops.stringify str
  | some (left, _) => do
    let view ← ops.substring str (ops.firstindex str) left
    let replacement ← ops.stringifyReplacement replacement
    ops.concat [.view view, .string replacement]

/--
Julia source: base/strings/util.jl:642-650 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ltruncate(str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar} = '…')
    ret = string_truncate_boundaries(str, Int(maxwidth), replacement, Val(:left))
    if isnothing(ret)
        return string(str)
    else
        _, right = ret::Tuple{Int,Int}
        @views return replacement * str[right:end]
    end
end
```
-/
def ltruncate {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (maxwidth : Index) (replacement : R) : Except E S := do
  match ← stringTruncateBoundaries ops str maxwidth replacement .left true with
  | none => ops.stringify str
  | some (_, right) => do
    let view ← ops.substring str right (ops.lastindex str)
    let replacement ← ops.stringifyReplacement replacement
    ops.concat [.string replacement, .view view]

/--
Julia source: base/strings/util.jl:676-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ctruncate(str::AbstractString, maxwidth::Integer, replacement::Union{AbstractString,AbstractChar} = '…'; prefer_left::Bool = true)
    ret = string_truncate_boundaries(str, Int(maxwidth), replacement, Val(:center), prefer_left)
    if isnothing(ret)
        return string(str)
    else
        left, right = ret::Tuple{Int,Int}
        @views return str[begin:left] * replacement * str[right:end]
    end
end
```
-/
def ctruncate {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (maxwidth : Index) (replacement : R) (preferLeft : Bool := true) : Except E S := do
  match ← stringTruncateBoundaries ops str maxwidth replacement .center preferLeft with
  | none => ops.stringify str
  | some (left, right) => do
    let leftView ← ops.substring str (ops.firstindex str) left
    let rightView ← ops.substring str right (ops.lastindex str)
    let replacement ← ops.stringifyReplacement replacement
    ops.concat [.view leftView, .string replacement, .view rightView]
/-! ## Dense strings and IO prefixes -/

structure DenseStringOps (S E : Type) where
  ncodeunits : S → Index
  sizeof : S → Index
  memcmp : S → S → Index → Except E Int
  memcmpFrom : S → Index → S → Index → Except E Int
  nextind : S → Index → Except E Index
  thisind : S → Index → Except E Index

/--
Julia source: base/strings/util.jl:69-78 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function startswith(a::DenseUTF8String, b::DenseUTF8String)
    cub = ncodeunits(b)
    if ncodeunits(a) < cub
        false
    elseif _memcmp(a, b, sizeof(b)) == 0
        nextind(a, cub) == cub + 1 # check that end of `b` doesn't match a partial character in `a`
    else
        false
    end
end
```
-/
def startswithDense {S E : Type} (ops : DenseStringOps S E)
    (a b : S) : Except E Bool := do
  let cub := ops.ncodeunits b
  if (ops.ncodeunits a).val < cub.val then return false
  if (← ops.memcmp a b (ops.sizeof b)) = 0 then
    return (← ops.nextind a cub).val == (cub + int 1).val
  return false

/--
Julia source: base/strings/util.jl:83-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable function startswith(a::Union{String,SubString{String}}, b::Union{String,SubString{String}})
    @invoke startswith(a::DenseUTF8String, b::DenseUTF8String)
end
```
-/
def startswithFast {D F E : Type} (ops : DenseStringOps D E)
    (toDense : F → D) (a b : F) : Except E Bool :=
  startswithDense ops (toDense a) (toDense b)

structure PrefixIOOps (IO C E : Type) where
  mark : IO → Except E IO
  readChar : IO → Except E (C × IO)
  readBytes : IO → Index → Except E (List UInt8 × IO)
  reset : IO → Except E IO

/--
Julia source: base/strings/util.jl:93-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function startswith(io::IO, prefix::Base.Chars)
    mark(io)
    c = read(io, Char)
    reset(io)
    return c in prefix
end
```
-/
def startswithIOChars {IO C Q E : Type} (ops : PrefixIOOps IO C E)
    (member : C → Q → Bool) (io : IO) (chars : Q) : Except E (Bool × IO) := do
  let io ← ops.mark io
  let (c, io) ← ops.readChar io
  let io ← ops.reset io
  return (member c chars, io)

/--
Julia source: base/strings/util.jl:99-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function startswith(io::IO, prefix::UTF8String)
    mark(io)
    s = read(io, ncodeunits(prefix))
    reset(io)
    return s == codeunits(prefix)
end
```
-/
def startswithIOUTF8 {IO S E : Type} (ops : PrefixIOOps IO UInt32 E)
    (ncodeunits : S → Index) (codeunits : S → List UInt8)
    (equalBytes : List UInt8 → List UInt8 → Bool) (io : IO) (pre : S) : Except E (Bool × IO) := do
  let io ← ops.mark io
  let (bytes, io) ← ops.readBytes io (ncodeunits pre)
  let io ← ops.reset io
  return (equalBytes bytes (codeunits pre), io)

/--
Julia source: base/strings/util.jl:105-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
startswith(io::IO, prefix::AbstractString) = startswith(io, String(prefix)::String)
```
-/
def startswithIOAbstract {IO S P E : Type}
    (ops : PrefixIOOps IO UInt32 E) (ncodeunits : S → Index)
    (codeunits : S → List UInt8) (equalBytes : List UInt8 → List UInt8 → Bool)
    (toString : P → Except E S) (io : IO) (pre : P) : Except E (Bool × IO) := do
  startswithIOUTF8 ops ncodeunits codeunits equalBytes io (← toString pre)

/--
Julia source: base/strings/util.jl:107-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function endswith(a::DenseUTF8String, b::DenseUTF8String)
    astart = ncodeunits(a) - ncodeunits(b) + 1
    if astart < 1
        false
    elseif GC.@preserve(a, _memcmp(pointer(a, astart), b, sizeof(b))) == 0
        thisind(a, astart) == astart # check that end of `b` doesn't match a partial character in `a`
    else
        false
    end
end
```
-/
def endswithDense {S E : Type} (ops : DenseStringOps S E)
    (a b : S) : Except E Bool := do
  let astart := ops.ncodeunits a - ops.ncodeunits b + int 1
  if astart.val < 1 then return false
  if (← ops.memcmpFrom a astart b (ops.sizeof b)) = 0 then
    return (← ops.thisind a astart).val == astart.val
  return false

/--
Julia source: base/strings/util.jl:120-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow :foldable function endswith(a::Union{String,SubString{String}}, b::Union{String,SubString{String}})
    @invoke endswith(a::DenseUTF8String, b::DenseUTF8String)
end
```
-/
def endswithFast {D F E : Type} (ops : DenseStringOps D E)
    (toDense : F → D) (a b : F) : Except E Bool :=
  endswithDense ops (toDense a) (toDense b)
/--
Julia source: base/strings/util.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
endswith(s) = Base.Fix2(endswith, s)
```
-/
def endswithFix {S P E : Type}
    (fix2 : (S → P → Except E Bool) → P → S → Except E Bool)
    (ends : S → P → Except E Bool) (suffix : P) : S → Except E Bool :=
  fix2 ends suffix

/--
Julia source: base/strings/util.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
startswith(s) = Base.Fix2(startswith, s)
```
-/
def startswithFix {S P E : Type}
    (fix2 : (S → P → Except E Bool) → P → S → Except E Bool)
    (starts : S → P → Except E Bool) (pre : P) : S → Except E Bool :=
  fix2 starts pre

/--
Julia source: base/strings/util.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
contains(needle) = Base.Fix2(contains, needle)
```
-/
def containsFix {H N : Type}
    (fix2 : (H → N → Bool) → N → H → Bool)
    (contains : H → N → Bool) (needle : N) : H → Bool :=
  fix2 contains needle
/-! ## Hex conversion, ASCII validation, and rest -/

inductive HexDigit (A C : Type) where
  | byte : UInt8 → HexDigit A C
  | abstractChar : A → HexDigit A C

/--
Julia source: base/strings/util.jl:1278-1283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function number_from_hex(c::UInt8)
    UInt8('0') <= c <= UInt8('9') && return c - UInt8('0')
    c |= 0b0100000
    UInt8('a') <= c <= UInt8('f') && return c - UInt8('a') + 0x0a
    throw(ArgumentError("byte is not an ASCII hexadecimal digit"))
end
```
-/
def numberFromHexByte {E : Type} (argumentError : String → E)
    (c : UInt8) : Except E UInt8 := do
  if 0x30 ≤ c && c ≤ 0x39 then return c - 0x30
  let c := c ||| 0x20
  if 0x61 ≤ c && c ≤ 0x66 then return c - 0x61 + 0x0a
  throw (argumentError "byte is not an ASCII hexadecimal digit")

/--
Julia source: base/strings/util.jl:1277-1277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline number_from_hex(c::Char) = number_from_hex(UInt8(c))
```
-/
def numberFromHexChar {C E : Type} (argumentError : String → E)
    (toUInt8 : C → Except E UInt8) (c : C) : Except E UInt8 := do
  numberFromHexByte argumentError (← toUInt8 c)

/--
Julia source: base/strings/util.jl:1276-1276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline number_from_hex(c::AbstractChar) = number_from_hex(Char(c)::Char)
```
-/
def numberFromHexAbstract {A C E : Type} (argumentError : String → E)
    (toChar : A → Except E C) (toUInt8 : C → Except E UInt8) (c : A) : Except E UInt8 := do
  numberFromHexChar argumentError toUInt8 (← toChar c)

/-- The Julia overload selected by the element type of the hexadecimal iterator. -/
def numberFromHex {A C E : Type} (argumentError : String → E)
    (toChar : A → Except E C) (toUInt8 : C → Except E UInt8) :
    HexDigit A C → Except E UInt8
  | .byte c => numberFromHexByte argumentError c
  | .abstractChar c => numberFromHexAbstract argumentError toChar toUInt8 c

structure HexIteratorOps (Itr A C State E : Type) where
  length : Itr → Index
  iterateFirst : Itr → Except E (Option (HexDigit A C × State))
  iterateNext : Itr → State → Except E (Option (HexDigit A C × State))

structure ByteArrayOps (Array I E : Type) where
  length : Array → Index
  eachindex : Array → List I
  set : Array → I → UInt8 → Except E Array

/--
Julia source: base/strings/util.jl:1260-1274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hex2bytes!(dest::AbstractArray{UInt8}, itr)
    isodd(length(itr)) && throw(ArgumentError("length of iterable must be even"))
    @boundscheck 2*length(dest) != length(itr) && throw(ArgumentError("length of output array must be half of the length of input iterable"))
    iszero(length(itr)) && return dest

    next = iterate(itr)
    @inbounds for i in eachindex(dest)
        x,state = next::NTuple{2,Any}
        y,state = iterate(itr, state)::NTuple{2,Any}
        next = iterate(itr, state)
        dest[i] = number_from_hex(x) << 4 + number_from_hex(y)
    end

    return dest
end
```
-/
def hex2bytesBang {Array I Itr A C State E : Type}
    (arrayOps : ByteArrayOps Array I E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (checkBounds : Bool) (dest : Array) (itr : Itr) : Except E Array := do
  let inputLength := iterOps.length itr
  if inputLength.val % 2 != 0 then
    throw (argumentError "length of iterable must be even")
  if checkBounds && (int 2 * arrayOps.length dest).val != inputLength.val then
    throw (argumentError "length of output array must be half of the length of input iterable")
  if inputLength.val = 0 then return dest
  let next ← iterOps.iterateFirst itr
  let rec loop (indices : List I) (dest : Array)
      (next : Option (HexDigit A C × State)) : Except E Array :=
    match indices with
    | [] => .ok dest
    | i :: rest => do
      let (x, state) ← assertTuple next
      let (y, state) ← assertTuple (← iterOps.iterateNext itr state)
      let next ← iterOps.iterateNext itr state
      let high ← numberFromHex argumentError toChar toUInt8 x
      let low ← numberFromHex argumentError toChar toUInt8 y
      let dest ← arrayOps.set dest i ((high <<< 4) + low)
      loop rest dest next
  loop (arrayOps.eachindex dest) dest next

/--
Julia source: base/strings/util.jl:1235-1235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hex2bytes end
```
-/
def hex2bytes_generic_decl {Args R E : Type}
    (dispatch : Args → Option (Except E R) := fun _ => none) (args : Args) :
    Except (MethodCallError Args E) R :=
  match dispatch args with
  | some (.ok r) => .ok r
  | some (.error err) => .error (.base err)
  | none => .error (.methodError "hex2bytes" args)

/--
Julia source: base/strings/util.jl:1240-1244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hex2bytes!(dest::AbstractArray{UInt8}, s::String)
    sizeof(s) != length(s) && throw(ArgumentError("input string must consist of hexadecimal characters only"))

    hex2bytes!(dest, transcode(UInt8, s))
end
```
-/
def hex2bytesString {Array I Itr A C State S E : Type}
    (arrayOps : ByteArrayOps Array I E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (sizeof length : S → Index) (transcode : S → Except E Itr)
    (checkBounds : Bool) (dest : Array) (s : S) : Except E Array := do
  if (sizeof s).val != (length s).val then
    throw (argumentError "input string must consist of hexadecimal characters only")
  let itr ← transcode s
  hex2bytesBang arrayOps iterOps assertTuple argumentError toChar toUInt8 checkBounds dest itr

/--
Julia source: base/strings/util.jl:1237-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hex2bytes(s) = hex2bytes!(Vector{UInt8}(undef, length(s)::Int >> 1), s)
```
-/
def hex2bytesWrapper {Array S E : Type}
    (length : S → Index) (shiftRightOne : Index → Index)
    (allocate : Index → Except E Array) (decode : Array → S → Except E Array)
    (s : S) : Except E Array := do
  let dest ← allocate (shiftRightOne (length s))
  decode dest s

/-- The two lowercase hexadecimal digits for a byte. -/
def hexHighIndex (x : UInt8) : Index := int ((1 : Int) + (x >>> 4).toNat)
def hexLowIndex (x : UInt8) : Index := int ((1 : Int) + (x &&& 0xf).toNat)

structure Bytes2HexOps (Itr State S P E : Type) where
  isUInt8Iterator : Itr → Bool
  length : Itr → Index
  allocate : Index → Except E S
  pointer : S → P
  enumerate : Itr → IterSteps (Index × UInt8) State E
  hexChar : Index → UInt8
  store : S → P → UInt8 → Index → Except E S
  argumentError : String → E

/-- Interleaved `for (i, x) in enumerate(itr)` loop storing both lowercase hex digits at each step. -/
def bytes2hexStore {Itr State S P E : Type} (ops : Bytes2HexOps Itr State S P E)
    (p : P) : IterSteps (Index × UInt8) State E → S → Except E S
  | .done, str => .ok str
  | .fail err, _ => .error err
  | .yield (i, x) state next, str => do
    let str ← ops.store str p (ops.hexChar (hexHighIndex x)) (int 2 * i - int 1)
    let str ← ops.store str p (ops.hexChar (hexLowIndex x)) (int 2 * i)
    bytes2hexStore ops p (next state) str

/--
Julia source: base/strings/util.jl:1316-1327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bytes2hex(itr)
    eltype(itr) === UInt8 || throw(ArgumentError("eltype of iterator not UInt8"))
    str = Base._string_n(2*length(itr))
    GC.@preserve str begin
        p = pointer(str)
        for (i, x) in enumerate(itr)
            unsafe_store!(p, @inbounds(hex_chars[1 + x >> 4]), 2i - 1)
            unsafe_store!(p, @inbounds(hex_chars[1 + x & 0xf]), 2i)
        end
    end
    return str
end
```
-/
def bytes2hex {Itr State S P E : Type} (ops : Bytes2HexOps Itr State S P E)
    (itr : Itr) : Except E S := do
  if !ops.isUInt8Iterator itr then
    throw (ops.argumentError "eltype of iterator not UInt8")
  let str ← ops.allocate (int 2 * ops.length itr)
  let p := ops.pointer str
  bytes2hexStore ops p (ops.enumerate itr) str

/--
Julia source: base/strings/util.jl:1314-1314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bytes2hex end
```
-/
def bytes2hex_generic_decl {Args R E : Type}
    (dispatch : Args → Option (Except E R) := fun _ => none) (args : Args) :
    Except (MethodCallError Args E) R :=
  match dispatch args with
  | some (.ok r) => .ok r
  | some (.error err) => .error (.base err)
  | none => .error (.methodError "bytes2hex" args)
/-- Interleaved `for x in itr` stream hex-printing loop without requiring `length(itr)`. -/
def bytes2hexIOLoop {State IO C E : Type}
    (hexChar : Index → UInt8) (charOfByte : UInt8 → C)
    (print : IO → C → C → Except E IO) :
    IterSteps UInt8 State E → IO → Except E IO
  | .done, io => .ok io
  | .fail err, _ => .error err
  | .yield x state next, io => do
    let io ← print io (charOfByte (hexChar (hexHighIndex x))) (charOfByte (hexChar (hexLowIndex x)))
    bytes2hexIOLoop hexChar charOfByte print (next state) io

/--
Julia source: base/strings/util.jl:1329-1334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bytes2hex(io::IO, itr)
    eltype(itr) === UInt8 || throw(ArgumentError("eltype of iterator not UInt8"))
    for x in itr
        print(io, Char(hex_chars[1 + x >> 4]), Char(hex_chars[1 + x & 0xf]))
    end
end
```
-/
def bytes2hexIO {Itr State IO C E : Type}
    (iterate : Itr → IterSteps UInt8 State E)
    (isUInt8Iterator : Itr → Bool) (hexChar : Index → UInt8)
    (charOfByte : UInt8 → C) (print : IO → C → C → Except E IO)
    (argumentError : String → E) (io : IO) (itr : Itr) : Except E IO := do
  if !isUInt8Iterator itr then
    throw (argumentError "eltype of iterator not UInt8")
  bytes2hexIOLoop hexChar charOfByte print (iterate itr) io


structure AsciiOps (S E : Type) where
  sizeof : S → Index
  codeunit : S → Index → UInt8
  repr : S → String
  argumentError : String → E

/--
Julia source: base/strings/util.jl:1337-1342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ascii(s::String)
    for i in 1:sizeof(s)
        @inbounds codeunit(s, i) < 0x80 || __throw_invalid_ascii(s, i)
    end
    return s
end
```
-/
def asciiString {S E : Type} (ops : AsciiOps S E) (throwInvalid : S → Index → E)
    (s : S) : Except E S :=
  let rec loop : List Nat → Except E S
    | [] => .ok s
    | k :: rest =>
      let i := int (Int.ofNat k + 1)
      if (ops.codeunit s i).toNat < 0x80 then loop rest
      else .error (throwInvalid s i)
  loop (List.range (ops.sizeof s).val.toNat)

/--
Julia source: base/strings/util.jl:1343-1343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline __throw_invalid_ascii(s::String, i::Int) = throw(ArgumentError("invalid ASCII at index $i in $(repr(s))"))
```
-/
def __throw_invalid_ascii {S E : Type} (ops : AsciiOps S E)
    (s : S) (i : Index) : E :=
  ops.argumentError ("invalid ASCII at index " ++ toString i.val ++ " in " ++ ops.repr s)

/--
Julia source: base/strings/util.jl:1364-1364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ascii(x::AbstractString) = ascii(String(x)::String)
```
-/
def asciiAbstract {A S E : Type} (ops : AsciiOps S E)
    (toString : A → Except E S) (s : A) : Except E S := do
  asciiString ops (__throw_invalid_ascii ops) (← toString s)

/--
Julia source: base/strings/util.jl:1366-1366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.rest(s::Union{String,SubString{String}}, i=1) = SubString(s, i)
```
-/
def restFast {S R E : Type} (substringFrom : S → Index → Except E R)
    (s : S) (i : Index := int 1) : Except E R :=
  substringFrom s i

structure RestOps (S Iter State C IO O E : Type) where
  restIterator : S → List State → Except E Iter
  iterateFirst : Iter → Except E (Option (C × State))
  iterateNext : Iter → State → Except E (Option (C × State))
  iterationBound : Iter → Nat
  newIOBuffer : Except E IO
  print : IO → C → Except E IO
  takeString : IO → Except E O

/--
Julia source: base/strings/util.jl:1367-1373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.rest(s::AbstractString, st...)
    io = IOBuffer()
    for c in Iterators.rest(s, st...)
        print(io, c)
    end
    return takestring!(io)
end
```
-/
def restGeneric {S Iter State C IO O E : Type} (ops : RestOps S Iter State C IO O E)
    (s : S) (states : List State) : Except E O := do
  let io ← ops.newIOBuffer
  let iter ← ops.restIterator s states
  let first ← ops.iterateFirst iter
  let rec loop (fuel : Nat) (io : IO) (current : Option (C × State)) : Except E O :=
    match fuel with
    | 0 => ops.takeString io
    | n + 1 =>
      match current with
      | none => ops.takeString io
      | some (c, state) => do
        let io ← ops.print io c
        let next ← ops.iterateNext iter state
        loop n io next
  loop (ops.iterationBound iter + 1) io first
/-! ## Splitting iterators -/
/--
Julia source: base/strings/util.jl:772-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachsplit end
```
-/
def eachsplit_generic_decl {Args R E : Type}
    (dispatch : Args → Option (Except E R) := fun _ => none) (args : Args) :
    Except (MethodCallError Args E) R :=
  match dispatch args with
  | some (.ok r) => .ok r
  | some (.error err) => .error (.base err)
  | none => .error (.methodError "eachsplit" args)


/--
Julia source: base/strings/util.jl:776-781 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct SplitIterator{S<:AbstractString,F}
    str::S
    splitter::F
    limit::Int
    keepempty::Bool
end
```
-/
structure SplitIteratorModel (S F : Type) where
  str : S
  splitter : F
  limit : Index
  keepempty : Bool

/--
Julia source: base/strings/util.jl:783-783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:SplitIterator{T}}) where T = SubString{T}
```
-/
def splitEltype {T F : Type} (_ : SplitIteratorModel T F) : Type :=
  JuliaLean.base.strings.substring.SubString T

/--
Julia source: base/strings/util.jl:784-784 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:SplitIterator{<:SubString{T}}}) where T = SubString{T}
```
-/
def splitEltypeOfSubstring {T F : Type}
    (_ : SplitIteratorModel (JuliaLean.base.strings.substring.SubString T) F) : Type :=
  JuliaLean.base.strings.substring.SubString T

/--
Julia source: base/strings/util.jl:786-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:SplitIterator}) = SizeUnknown()
```
-/
def splitIteratorSize {T F : Type} (_ : SplitIteratorModel T F) :
    JuliaLean.base.generator.IteratorSize :=
  .sizeUnknown

structure SplitStringOps (S R E : Type) where
  firstindex : S → Index
  lastindex : S → Index
  ncodeunits : S → Index
  iterationBound : S → Nat
  nextind : S → Index → Except E Index
  prevind : S → Index → Except E Index
  substringUnchecked : S → Index → Index → Except E R
  substringFrom : S → Index → Except E R
  substringChecked : S → Index → Index → Except E R

abbrev SplitState := Index × Index × Index

/-- The final piece emitted after no more split is found. -/
def splitTail {S R F E : Type} (ops : SplitStringOps S R E)
    (iter : SplitIteratorModel S F) (i k n : Index) :
    Except E (Option (R × SplitState)) := do
  if !iter.keepempty && i.val > (ops.ncodeunits iter.str).val then return none
  let sub ← ops.substringFrom iter.str i
  return some (sub, (ops.ncodeunits iter.str + int 2, k, n + int 1))

/--
Julia source: base/strings/util.jl:791-807 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(iter::SplitIterator, (i, k, n)=(firstindex(iter.str), firstindex(iter.str), 0))
    i - 1 > ncodeunits(iter.str)::Int && return nothing
    r = findnext(iter.splitter, iter.str, k)::Union{Nothing,Int,UnitRange{Int}}
    while r !== nothing && n != iter.limit - 1 && first(r) <= ncodeunits(iter.str)
        j, k = first(r), nextind(iter.str, last(r))::Int
        k_ = k <= j ? nextind(iter.str, j)::Int : k
        if i < k
            substr = @inbounds SubString(iter.str, i, prevind(iter.str, j)::Int)
            (iter.keepempty || i < j) && return (substr, (k, k_, n + 1))
            i = k
        end
        k = k_
        r = findnext(iter.splitter, iter.str, k)::Union{Nothing,Int,UnitRange{Int}}
    end
    iter.keepempty || i <= ncodeunits(iter.str) || return nothing
    @inbounds SubString(iter.str, i), (ncodeunits(iter.str) + 2, k, n + 1)
end
```
-/
def iterateSplit {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → Except E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (state : Option SplitState := none) :
    Except E (Option (R × SplitState)) := do
  let state := state.getD (ops.firstindex iter.str, ops.firstindex iter.str, int 0)
  let i := state.1
  let k := state.2.1
  let n := state.2.2
  if (i - int 1).val > (ops.ncodeunits iter.str).val then return none
  let r ← findnext iter.splitter iter.str k
  let rec loop (fuel : Nat) (i k n : Index) (r : Option (Index × Index)) :
      Except E (Option (R × SplitState)) :=
    match fuel with
    | 0 => splitTail ops iter i k n
    | fuel + 1 =>
      match r with
      | none => splitTail ops iter i k n
      | some (a, b) =>
        if n.val = (iter.limit - int 1).val || a.val > (ops.ncodeunits iter.str).val then
          splitTail ops iter i k n
        else do
          let k ← ops.nextind iter.str b
          let k_ ← if k.val ≤ a.val then ops.nextind iter.str a else pure k
          if i.val < k.val then do
            let before ← ops.prevind iter.str a
            let sub ← ops.substringUnchecked iter.str i before
            if iter.keepempty || i.val < a.val then
              return some (sub, (k, k_, n + int 1))
            let r ← findnext iter.splitter iter.str k_
            loop fuel k k_ n r
          else do
            let r ← findnext iter.splitter iter.str k_
            loop fuel i k_ n r
  loop (ops.iterationBound iter.str + 2) i k n r

structure PartitionIteratorModel (S : Type) where
  c : S
  n : Index

structure PartitionOps (S R E : Type) where
  ncodeunits : S → Index
  firstindex : S → Index
  lastindex : S → Index
  nextindN : S → Index → Index → Except E Index
  nextind : S → Index → Except E Index
  substring : S → Index → Index → Except E R

/--
Julia source: base/strings/util.jl:810-810 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T<:AbstractString} = SubString{T}
```
-/
def partitionEltype {T : Type} (_ : PartitionIteratorModel T) : Type :=
  JuliaLean.base.strings.substring.SubString T

/--
Julia source: base/strings/util.jl:812-812 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{PartitionIterator{T}}) where {T<:SubString} = T
```
-/
def partitionEltypeOfSubstring {S : Type}
    (_ : PartitionIteratorModel (JuliaLean.base.strings.substring.SubString S)) : Type :=
  JuliaLean.base.strings.substring.SubString S

/--
Julia source: base/strings/util.jl:814-818 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(itr::PartitionIterator{<:AbstractString}, state = firstindex(itr.c))
    state > ncodeunits(itr.c) && return nothing
    r = min(nextind(itr.c, state, itr.n - 1), lastindex(itr.c))
    return SubString(itr.c, state, r), nextind(itr.c, r)
end
```
-/
def iteratePartition {S R E : Type} (ops : PartitionOps S R E)
    (iter : PartitionIteratorModel S) (state : Option Index := none) :
    Except E (Option (R × Index)) := do
  let state := state.getD (ops.firstindex iter.c)
  if state.val > (ops.ncodeunits iter.c).val then return none
  let through ← ops.nextindN iter.c state (iter.n - int 1)
  let r := if through.val < (ops.lastindex iter.c).val then through else ops.lastindex iter.c
  let sub ← ops.substring iter.c state r
  let next ← ops.nextind iter.c r
  return some (sub, next)

/--
Julia source: base/strings/util.jl:820-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::T, splitter; limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString} =
    SplitIterator(str, splitter, limit, keepempty)
```
-/
def eachsplitGeneric {S F N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (str : S) (splitter : F) (limit : N) (keepempty : Bool) :
    Except E (SplitIteratorModel S F) := do
  if !isInt limit then throw (methodError "SplitIterator")
  let limit ← toIndex limit
  return ⟨str, splitter, limit, keepempty⟩

/--
Julia source: base/strings/util.jl:823-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::T, splitter::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}};
          limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachsplit(str, in(splitter); limit, keepempty)
```
-/
def eachsplitChars {S Q C N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (member : Q → C → Bool) (str : S) (chars : Q) (limit : N) (keepempty : Bool) :
    Except E (SplitIteratorModel S (C → Bool)) :=
  eachsplitGeneric isInt toIndex methodError str (fun c => member chars c) limit keepempty

/--
Julia source: base/strings/util.jl:827-828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::T, splitter::AbstractChar; limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachsplit(str, isequal(splitter); limit, keepempty)
```
-/
def eachsplitChar {S C N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (equal : C → C → Bool) (str : S) (delimiter : C) (limit : N) (keepempty : Bool) :
    Except E (SplitIteratorModel S (C → Bool)) :=
  eachsplitGeneric isInt toIndex methodError str (fun c => equal c delimiter) limit keepempty

/--
Julia source: base/strings/util.jl:831-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::AbstractString; limit::Integer=0, keepempty=false) =
    eachsplit(str, isspace; limit, keepempty)
```
-/
def eachsplitWhitespace {S C N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (isspace : C → Bool) (str : S) (limit : N) (keepempty : Bool := false) :
    Except E (SplitIteratorModel S (C → Bool)) :=
  eachsplitGeneric isInt toIndex methodError str isspace limit keepempty

/--
Julia source: base/strings/util.jl:870-870 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eachrsplit end
```
-/
def eachrsplit_generic_decl {Args R E : Type}
    (dispatch : Args → Option (Except E R) := fun _ => none) (args : Args) :
    Except (MethodCallError Args E) R :=
  match dispatch args with
  | some (.ok r) => .ok r
  | some (.error err) => .error (.base err)
  | none => .error (.methodError "eachrsplit" args)

/--
Julia source: base/strings/util.jl:872-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct RSplitIterator{S <: AbstractString, F}
    str::S
    splitter::F
    limit::Int
    keepempty::Bool
end
```
-/
structure RSplitIteratorModel (S F : Type) where
  str : S
  splitter : F
  limit : Index
  keepempty : Bool
/--
Julia source: base/strings/util.jl:879-879 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:RSplitIterator{T}}) where T = SubString{T}
```
-/
def rsplitEltype {T F : Type} (_ : RSplitIteratorModel T F) : Type :=
  JuliaLean.base.strings.substring.SubString T

/--
Julia source: base/strings/util.jl:880-880 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{<:RSplitIterator{<:SubString{T}}}) where T = SubString{T}
```
-/
def rsplitEltypeOfSubstring {T F : Type}
    (_ : RSplitIteratorModel (JuliaLean.base.strings.substring.SubString T) F) : Type :=
  JuliaLean.base.strings.substring.SubString T

/--
Julia source: base/strings/util.jl:882-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IteratorSize(::Type{<:RSplitIterator}) = SizeUnknown()
```
-/
def rsplitIteratorSize {T F : Type} (_ : RSplitIteratorModel T F) :
    JuliaLean.base.generator.IteratorSize :=
  .sizeUnknown

/--
Julia source: base/strings/util.jl:884-885 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::T, splitter; limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString} =
    RSplitIterator(str, splitter, limit, keepempty)
```
-/
def eachrsplitGeneric {S F N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (str : S) (splitter : F) (limit : N) (keepempty : Bool) :
    Except E (RSplitIteratorModel S F) := do
  if !isInt limit then throw (methodError "RSplitIterator")
  let limit ← toIndex limit
  return ⟨str, splitter, limit, keepempty⟩

/--
Julia source: base/strings/util.jl:887-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::T, splitter::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}};
          limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachrsplit(str, in(splitter); limit, keepempty)
```
-/
def eachrsplitChars {S Q C N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (member : Q → C → Bool) (str : S) (chars : Q) (limit : N) (keepempty : Bool) :
    Except E (RSplitIteratorModel S (C → Bool)) :=
  eachrsplitGeneric isInt toIndex methodError str (fun c => member chars c) limit keepempty

/--
Julia source: base/strings/util.jl:891-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::T, splitter::AbstractChar; limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachrsplit(str, isequal(splitter); limit, keepempty)
```
-/
def eachrsplitChar {S C N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (equal : C → C → Bool) (str : S) (delimiter : C) (limit : N) (keepempty : Bool) :
    Except E (RSplitIteratorModel S (C → Bool)) :=
  eachrsplitGeneric isInt toIndex methodError str (fun c => equal c delimiter) limit keepempty

/--
Julia source: base/strings/util.jl:895-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::AbstractString; limit::Integer=0, keepempty=false) =
    eachrsplit(str, isspace; limit, keepempty)
```
-/
def eachrsplitWhitespace {S C N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (isspace : C → Bool) (str : S) (limit : N) (keepempty : Bool := false) :
    Except E (RSplitIteratorModel S (C → Bool)) :=
  eachrsplitGeneric isInt toIndex methodError str isspace limit keepempty

abbrev RSplitState := Index × Index

/--
Julia source: base/strings/util.jl:898-927 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.iterate(it::RSplitIterator, (to, remaining_splits)=(lastindex(it.str), it.limit-1))
    to < 0 && return nothing
    from = 1
    next_to = -1
    while !iszero(remaining_splits)
        pos = findprev(it.splitter, it.str, to)
        # If no matches: It returns the rest of the string, then the iterator stops.
        if pos === nothing
            from = 1
            next_to = -1
            break
        else
            from = nextind(it.str, last(pos))
            # pos can be empty if we search for a zero-width delimiter, in which
            # case pos is to:to-1.
            # In this case, next_to must be to - 1, except if to is 0 or 1, in
            # which case, we must stop iteration for some reason.
            next_to = (isempty(pos) & (to < 2)) ? -1 : prevind(it.str, first(pos))

            # If the element we emit is empty, discard it based on keepempty
            if from > to && !(it.keepempty)
                to = next_to
                continue
            end
            break
        end
    end
    from > to && !(it.keepempty) && return nothing
    return (SubString(it.str, from, to), (next_to, remaining_splits-1))
end
```
-/
def iterateRSplit {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → Except E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (state : Option RSplitState := none) :
    Except E (Option (R × RSplitState)) := do
  let (to, remaining) := state.getD (ops.lastindex iter.str, iter.limit - int 1)
  if to.val < 0 then return none
  let rec loop (fuel : Nat) (remaining to frm nextTo : Index) :
      Except E (Index × Index × Index) :=
    match fuel with
    | 0 => .ok (frm, nextTo, to)
    | fuel + 1 =>
      if remaining.val = 0 then .ok (frm, nextTo, to)
      else do
        let pos ← findprev iter.splitter iter.str to
        match pos with
        | none => .ok (int 1, int (-1), to)
        | some (a, b) => do
          let frm ← ops.nextind iter.str b
          let nextTo ← if b.val < a.val && to.val < 2 then pure (int (-1))
            else ops.prevind iter.str a
          if frm.val > to.val && !iter.keepempty then
            loop fuel remaining nextTo frm nextTo
          else .ok (frm, nextTo, to)
  let (frm, nextTo, to) ← loop (ops.iterationBound iter.str + 1)
    remaining to (int 1) (int (-1))
  if frm.val > to.val && !iter.keepempty then return none
  let sub ← ops.substringChecked iter.str frm to
  return some (sub, (nextTo, remaining - int 1))

/--
Julia source: base/strings/util.jl:958-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function split(str::T, splitter;
               limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}
    collect(eachsplit(str, splitter; limit, keepempty))
end
```
-/
def splitGeneric {S F R N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index)
    (methodError : String → E) (collect : SplitIteratorModel S F → Except E (List R))
    (str : S) (splitter : F) (limit : N) (keepempty : Bool) : Except E (List R) := do
  collect (← eachsplitGeneric isInt toIndex methodError str splitter limit keepempty)
/--
Julia source: base/strings/util.jl:964-966 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
split(str::AbstractString;
      limit::Integer=0, keepempty::Bool=false) =
    split(str, isspace; limit, keepempty)
```
-/
def splitWhitespace {S C R N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index)
    (methodError : String → E) (collect : SplitIteratorModel S (C → Bool) → Except E (List R))
    (isspace : C → Bool) (str : S) (limit : N) (keepempty : Bool := false) :
    Except E (List R) :=
  splitGeneric isInt toIndex methodError collect str isspace limit keepempty

/--
Julia source: base/strings/util.jl:1001-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rsplit(str::T, splitter;
               limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}
    reverse!(collect(eachrsplit(str, splitter; limit, keepempty)))
end
```
-/
def rsplitGeneric {S F R N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (collect : RSplitIteratorModel S F → Except E (List R)) (reverse : List R → List R)
    (str : S) (splitter : F) (limit : N) (keepempty : Bool) : Except E (List R) := do
  return reverse (← collect (← eachrsplitGeneric isInt toIndex methodError str splitter limit keepempty))

/--
Julia source: base/strings/util.jl:1007-1009 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rsplit(str::AbstractString;
      limit::Integer=0, keepempty::Bool=false) =
    rsplit(str, isspace; limit, keepempty)
```
-/
def rsplitWhitespace {S C R N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (collect : RSplitIteratorModel S (C → Bool) → Except E (List R)) (reverse : List R → List R)
    (isspace : C → Bool) (str : S) (limit : N) (keepempty : Bool := false) :
    Except E (List R) :=
  rsplitGeneric isInt toIndex methodError collect reverse str isspace limit keepempty
/-! ## Replacement helper dispatch -/

structure ReplaceRange where
  first : Index
  last : Index

/--
Julia source: base/strings/util.jl:1011-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_replace(io, repl::Union{<:AbstractString, <:AbstractChar}, str, r, pattern) =
    write(io, repl)
```
-/
def replaceLiteral {IO R S Pat E : Type}
    (write : IO → R → Except E (IO × Index)) (io : IO) (repl : R)
    (_str : S) (_range : ReplaceRange) (_pattern : Pat) : Except E (IO × Index) :=
  write io repl

/--
Julia source: base/strings/util.jl:1013-1022 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace(io, repl, str, r, pattern)
    if applicable(position, io)
        p1 = position(io)
        print(io, repl)
        p2 = position(io)
        p2 - p1
    else
        write(io, repr(repl))
    end
end
```
-/
def replaceShown {IO R S Pat E : Type}
    (applicablePosition : IO → Bool) (position : IO → Except E Index)
    (print : IO → R → Except E IO) (repr : R → String)
    (write : IO → String → Except E (IO × Index)) (io : IO) (repl : R)
    (_str : S) (_range : ReplaceRange) (_pattern : Pat) : Except E (IO × Index) := do
  if applicablePosition io then
    let p1 ← position io
    let io ← print io repl
    let p2 ← position io
    return (io, p2 - p1)
  else write io (repr repl)

/--
Julia source: base/strings/util.jl:1023-1024 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_replace(io, repl::Function, str, r, pattern) =
    _replace(io, repl(SubString(str, first(r), last(r))), str, r, pattern)
```
-/
def replaceFunction {IO S Sub R Pat E : Type}
    (substring : S → Index → Index → Except E Sub)
    (replace : IO → R → S → ReplaceRange → Pat → Except E (IO × Index))
    (repl : Sub → Except E R) (io : IO) (str : S) (range : ReplaceRange)
    (pattern : Pat) : Except E (IO × Index) := do
  let matched ← substring str range.first range.last
  replace io (← repl matched) str range pattern

/--
Julia source: base/strings/util.jl:1025-1026 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_replace(io, repl::Function, str, r, pattern::Function) =
    _replace(io, repl(str[first(r)]), str, r, pattern)
```
-/
def replaceCharFunction {IO S C R Pat E : Type}
    (firstIndex : ReplaceRange → Index) (getindex : S → Index → Except E C)
    (replace : IO → R → S → ReplaceRange → Pat → Except E (IO × Index))
    (repl : C → Except E R) (io : IO) (str : S) (range : ReplaceRange)
    (pattern : Pat) : Except E (IO × Index) := do
  replace io (← repl (← getindex str (firstIndex range))) str range pattern

/--
Julia source: base/strings/util.jl:1028-1028 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pat_replacer(x) = x
```
-/
def patReplacer {P : Type} (pattern : P) : P := pattern

/--
Julia source: base/strings/util.jl:1029-1029 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_free_pat_replacer(x) = nothing
```
-/
def freePatReplacer {P : Type} (_pattern : P) : Unit := ()

/--
Julia source: base/strings/util.jl:1031-1031 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pat_replacer(x::AbstractChar) = isequal(x)
```
-/
def patReplacerChar {C F : Type} (isequal : C → F) (x : C) : F := isequal x

/--
Julia source: base/strings/util.jl:1032-1032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pat_replacer(x::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}}) = in(x)
```
-/
def patReplacerChars {Q F : Type} (membership : Q → F) (x : Q) : F := membership x
/-! ## Replacement engine -/

structure ReplacePair (P R : Type) where
  pattern : P
  replacement : R

structure ReplaceInitOps (S P Q R E : Type) where
  patternReplacer : P → Q
  firstindex : S → Index
  lastindex : S → Index
  nextind : S → Index → Except E Index
  findnext : Q → S → Index → Except E (Option ReplaceRange)
  domainError : Index → E

/-- Maps no-match results to the sentinel range used by the replacement loop. -/
def replaceSentinel (e1 : Index) : ReplaceRange := ⟨e1 + int 1, int 0⟩

/--
Julia source: base/strings/util.jl:1035-1050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace_init(str, pat_repl::NTuple{N, Pair}, count::Int) where N
    count < 0 && throw(DomainError(count, "`count` must be non-negative."))
    e1 = nextind(str, lastindex(str)) # sizeof(str)+1
    a = firstindex(str)
    patterns = map(p -> _pat_replacer(first(p)), pat_repl)
    replaces = map(last, pat_repl)
    rs = map(patterns) do p
        r = findnext(p, str, a)
        if r === nothing || first(r) == 0
            return e1+1:0
        end
        r isa Int && (r = r:r) # findnext / performance fix
        return r
    end
    return e1, patterns, replaces, rs, all(>(e1), map(first, rs))
end
```
-/
def replaceInit {S P Q R E : Type} (ops : ReplaceInitOps S P Q R E)
    (str : S) (pairs : List (ReplacePair P R)) (count : Index) :
    Except E (Index × List Q × List R × List ReplaceRange × Bool) := do
  if count.val < 0 then throw (ops.domainError count)
  let e1 ← ops.nextind str (ops.lastindex str)
  let first := ops.firstindex str
  let patterns := pairs.map fun pair => ops.patternReplacer pair.pattern
  let replaces := pairs.map (·.replacement)
  let ranges ← patterns.mapM fun pattern => do
    match ← ops.findnext pattern str first with
    | none => return replaceSentinel e1
    | some range =>
      if range.first.val = 0 then return replaceSentinel e1
      else return range
  let notfound := ranges.all fun range => range.first.val > e1.val
  return (e1, patterns, replaces, ranges, notfound)

structure ReplaceStep (IO : Type) where
  io : IO
  ranges : List ReplaceRange
  selected : Index
  range : ReplaceRange
  bytesWritten : Index
  nextIndex : Index


structure ReplaceOnceOps (S P Q R IO E : Type) where
  argmin : List Index → Index
  selectRange : List ReplaceRange → Index → Except E ReplaceRange
  selectPattern : List Q → Index → Except E Q
  selectReplacement : List R → Index → Except E R
  first : ReplaceRange → Index
  last : ReplaceRange → Index
  unsafeWrite : IO → S → Index → Index → Except E IO
  replace : IO → R → S → ReplaceRange → Q → Except E (IO × Index)
  nextind : S → Index → Except E Index
  findnext : Q → S → Index → Except E (Option ReplaceRange)

/-- Refreshes only pattern matches whose previous range starts before the next search index. -/
def replaceRefresh {S Q E : Type} (findnext : Q → S → Index → Except E (Option ReplaceRange))
    (str : S) (e1 k : Index) : List Q → List ReplaceRange → Except E (List ReplaceRange)
  | [], _ => .ok []
  | _ :: _, [] => .ok []
  | pattern :: patterns, range :: ranges => do
    let range ← if range.first.val < k.val then do
      match ← findnext pattern str k with
      | none => pure (replaceSentinel e1)
      | some found =>
        if found.first.val = 0 then pure (replaceSentinel e1)
        else pure found
    else pure range
    let rest ← replaceRefresh findnext str e1 k patterns ranges
    return range :: rest

/--
Julia source: base/strings/util.jl:1068-1104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace_once(io::IO, str, start::Int, e1::Int,
                       patterns::Tuple, replaces::Tuple, rs::Tuple,
                       count::Int, n::Int, i::Int)
    x = argmin(map(first, rs)) # TODO: or argmin(rs), to pick the shortest first match ?
    r = rs[x]
    j, k = first(r), last(r)
    j > e1 && return rs, x, r, 0, i
    nb = if i == start || i <= k
        # copy out preserved portion
        GC.@preserve str unsafe_write(io, pointer(str, i), UInt(j-i))
        # copy out replacement string
        _replace(io, replaces[x], str, r, patterns[x])
    else
        0
    end
    if k < j
        i = j
        j == e1 && return rs, x, r, nb, i
        k = nextind(str, j)
    else
        i = k = nextind(str, k)
    end
    n == count && return rs, x, r, nb, i
    let k = k
        rs = map(patterns, rs) do p, r
            if first(r) < k
                r = findnext(p, str, k)
                if r === nothing || first(r) == 0
                    return e1+1:0
                end
                r isa Int && (r = r:r) # findnext / performance fix
            end
            return r
        end
    end
    return rs, x, r, nb, i
end
```
-/
def replaceOnce {S P Q R IO E : Type} (ops : ReplaceOnceOps S P Q R IO E)
    (io : IO) (str : S) (start e1 : Index) (patterns : List Q) (replaces : List R)
    (ranges : List ReplaceRange) (count n i : Index) :
    Except E (ReplaceStep IO) := do
  let selected := ops.argmin (ranges.map ops.first)
  let range ← ops.selectRange ranges selected
  let j := ops.first range
  let k := ops.last range
  if j.val > e1.val then return ⟨io, ranges, selected, range, int 0, i⟩
  let (io, bytesWritten) ← if i.val = start.val || i.val ≤ k.val then do
    let io ← ops.unsafeWrite io str i (j - i)
    let replacement ← ops.selectReplacement replaces selected
    let pattern ← ops.selectPattern patterns selected
    ops.replace io replacement str range pattern
  else pure (io, int 0)
  let (i, k) ← if k.val < j.val then do
    if j.val = e1.val then return ⟨io, ranges, selected, range, bytesWritten, j⟩
    let nextK ← ops.nextind str j
    pure (j, nextK)
  else do
    let next ← ops.nextind str k
    pure (next, next)
  if n.val = count.val then return ⟨io, ranges, selected, range, bytesWritten, i⟩
  let ranges ← replaceRefresh ops.findnext str e1 k patterns ranges
  return ⟨io, ranges, selected, range, bytesWritten, i⟩

structure ReplaceFinishOps (S P R IO E : Type) where
  firstindex : S → Index
  first : ReplaceRange → Index
  writeRest : IO → S → Index → Except E IO
  iterationBound : Index → Nat
/--
Julia source: base/strings/util.jl:1053-1066 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace_finish(io::IO, str, count::Int,
                         e1::Int, patterns::Tuple, replaces::Tuple, rs::Tuple)
    n = 1
    i = start = firstindex(str)
    while n <= count
        rs, _, r, _, i = @inline _replace_once(
            io, str, start, e1, patterns, replaces, rs, count, n, i)
        first(r) >= e1 && break
        n += 1
    end
    foreach(_free_pat_replacer, patterns)
    write(io, SubString(str, i))
    return io
end
```
-/
def replaceFinish {S P Q R IO E : Type}
    (ops : ReplaceFinishOps S P R IO E)
    (once : IO → S → Index → Index → List Q → List R → List ReplaceRange → Index → Index → Index → Except E (ReplaceStep IO))
    (io : IO) (str : S) (count e1 : Index) (patterns : List Q)
    (replaces : List R) (ranges : List ReplaceRange) : Except E IO := do
  let start := ops.firstindex str
  let rec loop (fuel : Nat) (io : IO) (ranges : List ReplaceRange) (n i : Index) :
      Except E (IO × List ReplaceRange × Index) :=
    match fuel with
    | 0 => .ok (io, ranges, i)
    | fuel + 1 =>
      if n.val > count.val then .ok (io, ranges, i)
      else do
        let step ← once io str start e1 patterns replaces ranges count n i
        if (ops.first step.range).val ≥ e1.val then .ok (step.io, step.ranges, step.nextIndex)
        else loop fuel step.io step.ranges (n + int 1) step.nextIndex
  let (io, _, i) ← loop (ops.iterationBound count + 1) io ranges (int 1) start
  let _ ← patterns.mapM fun pattern => pure (freePatReplacer pattern)
  let io ← ops.writeRest io str i
  return io

structure ReplaceEngineOps (S P Q R IO O E : Type) where
  initOps : ReplaceInitOps S P Q R E
  finishOps : ReplaceFinishOps S P R IO E
  onceOps : ReplaceOnceOps S P Q R IO E
  writeString : IO → S → Except E IO
  newBuffer : S → Except E IO
  takeString : IO → Except E O
  toString : S → Except E O
 

/--
Julia source: base/strings/util.jl:1107-1120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace_(io::IO, str, pat_repl::NTuple{N, Pair}, count::Int) where N
    if count == 0
        write(io, str)
        return io
    end
    e1, patterns, replaces, rs, notfound = _replace_init(str, pat_repl, count)
    if notfound
        foreach(_free_pat_replacer, patterns)
        write(io, str)
        return io
    end
    return _replace_finish(io, str, count, e1, patterns, replaces, rs)
end

```
-/
def replaceIOEngine {S P Q R IO E : Type} (ops : ReplaceEngineOps S P Q R IO IO E)
    (io : IO) (str : S) (pairs : List (ReplacePair P R)) (count : Index) : Except E IO := do
  if count.val = 0 then
    return ← ops.writeString io str
  let (e1, patterns, replaces, ranges, notfound) ← replaceInit ops.initOps str pairs count
  if notfound then
    let _ ← patterns.mapM fun pattern => pure (freePatReplacer pattern)
    return ← ops.writeString io str
  replaceFinish ops.finishOps (replaceOnce ops.onceOps) io str count e1 patterns replaces ranges

/--
Julia source: base/strings/util.jl:1122-1131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _replace_(str, pat_repl::NTuple{N, Pair}, count::Int) where N
    count == 0 && return String(str)
    e1, patterns, replaces, rs, notfound = _replace_init(str, pat_repl, count)
    if notfound
        foreach(_free_pat_replacer, patterns)
        return String(str)
    end
    out = IOBuffer(sizehint=floor(Int, 1.2sizeof(str)))
    return takestring!(_replace_finish(out, str, count, e1, patterns, replaces, rs))
end
```
-/
def replaceStringEngine {S P Q R IO O E : Type} (ops : ReplaceEngineOps S P Q R IO O E)
    (str : S) (pairs : List (ReplacePair P R)) (count : Index) : Except E O := do
  if count.val = 0 then return ← ops.toString str
  let (e1, patterns, replaces, ranges, notfound) ← replaceInit ops.initOps str pairs count
  if notfound then
    let _ ← patterns.mapM fun pattern => pure (freePatReplacer pattern)
    return ← ops.toString str
  let io ← ops.newBuffer str
  let io ← replaceFinish ops.finishOps (replaceOnce ops.onceOps) io str count e1 patterns replaces ranges
  ops.takeString io

/--
Julia source: base/strings/util.jl:1183-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(io::IO, s::AbstractString, pat_f::Pair...; count=typemax(Int)) =
    _replace_(io, String(s), pat_f, Int(count))
```
-/
def replaceIO {A S P Q R N IO E : Type}
    (toString : A → Except E S) (toInt : N → Except E Index)
    (ops : ReplaceEngineOps S P Q R IO IO E) (io : IO) (str : A)
    (pairs : List (ReplacePair P R)) (count : N) : Except E IO := do
  let str ← toString str
  let count ← toInt count
  replaceIOEngine ops io str pairs count

/--
Julia source: base/strings/util.jl:1186-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace(s::AbstractString, pat_f::Pair...; count=typemax(Int)) =
    _replace_(String(s), pat_f, Int(count))
```
-/
def replaceString {A S P Q R N IO O E : Type}
    (toString : A → Except E S) (toInt : N → Except E Index)
    (ops : ReplaceEngineOps S P Q R IO O E) (str : A)
    (pairs : List (ReplacePair P R)) (count : N) : Except E O := do
  let str ← toString str
  let count ← toInt count
  replaceStringEngine ops str pairs count

end JuliaLean.base.strings.util
