import JuliaLean.base.regex
import JuliaLean.base.parse
import JuliaLean.Registry.Types
import JuliaLean.base.iobuffer
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.substring
import JuliaLean.base.generator
import JuliaLean.base.float
import JuliaLean.base.strings.stringview
import JuliaLean.base.reduce
import JuliaLean.base.array
import JuliaLean.base.strings.search
import JuliaLean.base.strings.unicode
import JuliaLean.base.operators
import JuliaLean.base.anyall
import JuliaLean.base.char
import JuliaLean.base.set
import JuliaLean.base.dict
import JuliaLean.base.iddict
import JuliaLean.base.idset
import JuliaLean.base.reshapedarray
import JuliaLean.base.range
import JuliaLean.base.abstractdict
import JuliaLean.base.hashing
import JuliaLean.base.tuple

/-!
# Model of base/strings/util.jl

The source methods are generic over AbstractString and take operations from other Julia files as typed parameters.
-/

namespace JuliaLean.base.strings.util

open JuliaLean.base.strings.basic
export JuliaLean.base.reduce (whileLoop whileLoop_some_unfold)

def partialBind {E : Type u} {A B : Type} (result : Option (Except E A))
    (next : A → Option (Except E B)) : Option (Except E B) :=
  match result with
  | none => none
  | some (.error err) => some (.error err)
  | some (.ok value) => next value

def foldString {S R C CU CT E A : Type} (ops : StringOps S R C CU CT E)
    (f : A → C → Except E A) (s : S) (init : A) : Option (Except E A) :=
  match ops.iterateFirst s with
  | .error e => some (.error e)
  | .ok none => some (.ok init)
  | .ok (some (c, i)) =>
    whileLoop (fun (acc, c, i) => do
      let acc ← f acc c
      match ← ops.iterateAt s i with
      | none => return .inl acc
      | some (c', i') => return .inr (acc, c', i')) (init, c, i)

/-! ## Prefix, suffix, and containment -/

def startswith.step {S T RA RB C D CU1 CU2 CT1 CT2 E : Type}
    (opsA : StringOps S RA C CU1 CT1 E) (opsB : StringOps T RB D CU2 CT2 E)
    (equalChar : C → D → Except E Bool) (a : S) (b : T)
    (state : Option (C × Index) × Option (D × Index)) :
    Except E (Sum Bool (Option (C × Index) × Option (D × Index))) := do
  let (i, j) := state
  match j with
  | none => return .inl true
  | some (d, nextB) =>
    match i with
    | none => return .inl false
    | some (c, nextA) =>
      if ← equalChar c d then
        let i ← opsA.iterateAt a nextA
        let j ← opsB.iterateAt b nextB
        return .inr (i, j)
      else return .inl false

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
    (equalChar : C → D → Except E Bool) (a : S) (b : T) : Option (Except E Bool) :=
  match opsA.iterateFirst a with
  | .error e => some (.error e)
  | .ok i =>
    match opsB.iterateFirst b with
    | .error e => some (.error e)
    | .ok j =>
      whileLoop (startswith.step opsA opsB equalChar a b) (i, j)

/--
Julia source: base/strings/util.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
startswith(str::AbstractString, chars::Chars) = !isempty(str) && first(str)::AbstractChar in chars
```
-/
def startswithChars {S Q C E : Type}
    (isempty : S → Except E Bool) (first : S → Except E C) (member : C → Q → Except E Bool)
    (str : S) (chars : Q) : Except E Bool := do
  if ← isempty str then return false
  return ← member (← first str) chars

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
    (equalChar : C → D → Except E Bool) (a : S) (b : T) : Option (Except E Bool) :=
  let a := reverseA a
  let b := reverseB b
  match opsA.iterateFirst a with
  | .error e => some (.error e)
  | .ok i =>
    match opsB.iterateFirst b with
    | .error e => some (.error e)
    | .ok j =>
      whileLoop (startswith.step opsA opsB equalChar a b) (i, j)

/--
Julia source: base/strings/util.jl:67-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
endswith(str::AbstractString, chars::Chars) = !isempty(str) && last(str) in chars
```
-/
def endswithChars {S Q C E : Type}
    (isempty : S → Except E Bool) (last : S → Except E C) (member : C → Q → Except E Bool)
    (str : S) (chars : Q) : Except E Bool := do
  if ← isempty str then return false
  return ← member (← last str) chars

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
    (isempty : S → Except E Bool) (whole : S → Except E R)
    (firstindex lastindex : S → Except E I) (nextind : S → I → N → Except E I)
    (prevind : S → I → N → Except E I) (substring : S → I → I → Except E R)
    (s : S) (head tail : N) : Except E R := do
  if ← isempty s then return ← whole s
  let first ← nextind s (← firstindex s) head
  let last ← prevind s (← lastindex s) tail
  substring s first last

/-! ## Prefix and suffix removal -/

def chopprefix.step {S P R C D E : Type}
    (iterateS : S → Index → Except E (Option (C × Index)))
    (iterateP : P → Index → Except E (Option (D × Index)))
    (empty : S → Except E R) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (equalChar : C → D → Except E Bool) (s : S) (pre : P)
    (state : Index × Option (C × Index) × Option (D × Index)) :
    Except E (Sum R (Index × Option (C × Index) × Option (D × Index))) := do
  let (k, i, j) := state
  match j with
  | none =>
    match i with
    | none => return .inl (← empty s)
    | some _ => return .inl (← subFrom s k)
  | some (d, nextP) =>
    match i with
    | none => return .inl (← whole s)
    | some (c, nextS) =>
      if ← equalChar c d then
        let i ← iterateS s nextS
        let j ← iterateP pre nextP
        return .inr (nextS, i, j)
      else return .inl (← whole s)

def chopprefix.loop {S P R C D E : Type}
    (iterateS : S → Index → Except E (Option (C × Index)))
    (iterateP : P → Index → Except E (Option (D × Index)))
    (empty : S → Except E R) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (equalChar : C → D → Except E Bool) (s : S) (pre : P)
    (k : Index) (i : Option (C × Index)) (j : Option (D × Index)) :
    Option (Except E R) :=
  whileLoop (chopprefix.step iterateS iterateP empty subFrom whole equalChar s pre) (k, i, j)

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
    (firstindex : S → Except E Index) (empty : S → Except E R)
    (subFrom : S → Index → Except E R) (whole : S → Except E R)
    (equalChar : C → D → Except E Bool) (s : S) (pre : P) : Option (Except E R) :=
  match firstindex s with
  | .error e => some (.error e)
  | .ok k =>
    match iterateFirstS s with
    | .error e => some (.error e)
    | .ok i =>
      match iterateFirstP pre with
      | .error e => some (.error e)
      | .ok j =>
        chopprefix.loop iterateS iterateP empty subFrom whole equalChar s pre k i j

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
    (isempty : S → Except E Bool) (first : S → Except E C) (firstindex : S → Except E Index)
    (nextind : S → Index → Except E Index) (subFrom : S → Index → Except E R)
    (whole : S → Except E R) (equalChar : C → D → Except E Bool) (s : S) (pre : D) :
    Except E R := do
  if !(← isempty s) then
    if ← equalChar (← first s) pre then
      return ← subFrom s (← nextind s (← firstindex s))
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
def chopsuffix.step {S RS RP R C D E : Type}
    (iterateS : RS → Index → Except E (Option (C × Index)))
    (iterateP : RP → Index → Except E (Option (D × Index)))
    (empty : S → Except E R) (firstindex : S → Except E Index)
    (through : S → Index → Index → Except E R) (whole : S → Except E R)
    (equalChar : C → D → Except E Bool) (s : S) (reverseS : RS) (reverseP : RP)
    (state : Index × Option (C × Index) × Option (D × Index)) :
    Except E (Sum R (Index × Option (C × Index) × Option (D × Index))) := do
  let (k, i, j) := state
  match j with
  | none =>
    match i with
    | none => return .inl (← empty s)
    | some _ => return .inl (← through s (← firstindex s) k)
  | some (d, nextP) =>
    match i with
    | none => return .inl (← whole s)
    | some (c, nextS) =>
      if ← equalChar c d then
        let i ← iterateS reverseS nextS
        let j ← iterateP reverseP nextP
        return .inr (nextS, i, j)
      else return .inl (← whole s)
def chopsuffix.loop {S RS RP R C D E : Type}
    (iterateS : RS → Index → Except E (Option (C × Index)))
    (iterateP : RP → Index → Except E (Option (D × Index)))
    (empty : S → Except E R) (firstindex : S → Except E Index)
    (through : S → Index → Index → Except E R) (whole : S → Except E R)
    (equalChar : C → D → Except E Bool) (s : S) (reverseS : RS) (reverseP : RP)
    (k : Index) (i : Option (C × Index)) (j : Option (D × Index)) :
    Option (Except E R) :=
  whileLoop (chopsuffix.step iterateS iterateP empty firstindex through whole
    equalChar s reverseS reverseP) (k, i, j)


def chopsuffix {S P RS RP R C D E : Type}
    (reverseS : S → RS) (reverseP : P → RP)
    (iterateFirstS : RS → Except E (Option (C × Index)))
    (iterateFirstP : RP → Except E (Option (D × Index)))
    (iterateS : RS → Index → Except E (Option (C × Index)))
    (iterateP : RP → Index → Except E (Option (D × Index)))
    (lastindex : S → Except E Index)
    (firstindex : S → Except E Index) (empty : S → Except E R)
    (through : S → Index → Index → Except E R) (whole : S → Except E R)
    (equalChar : C → D → Except E Bool) (s : S) (suffix : P) : Option (Except E R) :=
  let a := reverseS s
  let b := reverseP suffix
  match lastindex s with
  | .error e => some (.error e)
  | .ok k =>
    match iterateFirstS a with
    | .error e => some (.error e)
    | .ok i =>
      match iterateFirstP b with
      | .error e => some (.error e)
      | .ok j =>
        chopsuffix.loop iterateS iterateP empty firstindex through whole
          equalChar s a b k i j

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
    (isempty : S → Except E Bool) (last : S → Except E C) (firstindex lastindex : S → Except E Index)
    (prevind : S → Index → Except E Index) (through : S → Index → Index → Except E R)
    (whole : S → Except E R) (equalChar : C → D → Except E Bool) (s : S) (suffix : D) :
    Except E R := do
  if !(← isempty s) then
    if ← equalChar (← last s) suffix then
      let fi ← firstindex s
      let stop ← prevind s (← lastindex s)
      return ← through s fi stop
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
    (lastindex : S → Except E Index) (getindex : S → Index → Except E C)
    (prevind : S → Index → Except E Index) (substring : S → Index → Index → Except E R)
    (equalChar : C → C → Except E Bool) (newline carriageReturn : C) (s : S) : Except E R := do
  let i ← lastindex s
  if i.val < 1 then return ← substring s (int 1) i
  if !(← equalChar (← getindex s i) newline) then return ← substring s (int 1) i
  let j ← prevind s i
  if j.val < 1 then return ← substring s (int 1) j
  if !(← equalChar (← getindex s j) carriageReturn) then return ← substring s (int 1) j
  substring s (int 1) (← prevind s j)

/-! ## Whitespace and character stripping -/

structure StripOps (S R C FState BState E : Type) where
  lastindex : S → Except E Index
  firstindex : S → Except E Index
  addOne : Index → Index
  substring : S → Index → Index → Except E R
  pairsFirst : S → Except E (Option ((Index × C) × FState))
  pairsNext : S → FState → Except E (Option ((Index × C) × FState))
  reversePairsFirst : S → Except E (Option ((Index × C) × BState))
  reversePairsNext : S → BState → Except E (Option ((Index × C) × BState))

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
def lstrip.loop {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Except E Bool) (s : S) (e : Index) (first : Option ((Index × C) × FS)) :
    Option (Except E R) :=
  whileLoop (fun current => do
    match current with
    | none => return .inl (← ops.substring s (ops.addOne e) e)
    | some ((i, c), state) =>
      if !(← f c) then return .inl (← ops.substring s i e)
      else return .inr (← ops.pairsNext s state)) first

def lstrip {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Except E Bool) (s : S) : Option (Except E R) :=
  match ops.lastindex s with
  | .error err => some (.error err)
  | .ok e =>
    match ops.pairsFirst s with
    | .error err => some (.error err)
    | .ok first =>
      lstrip.loop ops f s e first

/--
Julia source: base/strings/util.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lstrip(s::AbstractString) = lstrip(isspace, s)
```
-/
def lstripDefault {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (isspace : C → Except E Bool) (s : S) : Option (Except E R) :=
  lstrip ops isspace s

/--
Julia source: base/strings/util.jl:424-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lstrip(s::AbstractString, chars::Chars) = lstrip(in(chars), s)
```
-/
def lstripChars {S R C Q FS BS E : Type} (ops : StripOps S R C FS BS E)
    (member : C → Q → Except E Bool) (chars : Q) (s : S) : Option (Except E R) :=
  lstrip ops (fun c => member c chars) s

/--
Julia source: base/strings/util.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lstrip(::AbstractString, ::AbstractString) = throw(ArgumentError("Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))
```
-/
def lstripStringError {S T R E : Type} (argumentError : String → E)
    (_s : S) (_chars : T) : Option (Except E R) :=
  some (.error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))

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
def rstrip.loop {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Except E Bool) (s : S) (first : Option ((Index × C) × BS)) :
    Option (Except E R) :=
  whileLoop (fun current => do
    match current with
    | none => return .inl (← ops.substring s (int 1) (int 0))
    | some ((i, c), state) =>
      if !(← f c) then return .inl (← ops.substring s (int 1) i)
      else return .inr (← ops.reversePairsNext s state)) first

def rstrip {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (f : C → Except E Bool) (s : S) : Option (Except E R) :=
  match ops.reversePairsFirst s with
  | .error err => some (.error err)
  | .ok first =>
    rstrip.loop ops f s first

/--
Julia source: base/strings/util.jl:457-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rstrip(s::AbstractString) = rstrip(isspace, s)
```
-/
def rstripDefault {S R C FS BS E : Type} (ops : StripOps S R C FS BS E)
    (isspace : C → Except E Bool) (s : S) : Option (Except E R) :=
  rstrip ops isspace s

/--
Julia source: base/strings/util.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rstrip(s::AbstractString, chars::Chars) = rstrip(in(chars), s)
```
-/
def rstripChars {S R C Q FS BS E : Type} (ops : StripOps S R C FS BS E)
    (member : C → Q → Except E Bool) (chars : Q) (s : S) : Option (Except E R) :=
  rstrip ops (fun c => member c chars) s

/--
Julia source: base/strings/util.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rstrip(::AbstractString, ::AbstractString) = throw(ArgumentError("Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))
```
-/
def rstripStringError {S T R E : Type} (argumentError : String → E)
    (_s : S) (_chars : T) : Option (Except E R) :=
  some (.error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))

/--
Julia source: base/strings/util.jl:486-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(s::AbstractString) = lstrip(rstrip(s))
```
-/
def stripDefault {S R T C FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (isspace : C → Except E Bool) (s : S) : Option (Except E T) :=
  match rstripDefault opsS isspace s with
  | none => none
  | some (.error err) => some (.error err)
  | some (.ok right) => lstripDefault opsR isspace right

/--
Julia source: base/strings/util.jl:487-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(s::AbstractString, chars::Chars) = lstrip(rstrip(s, chars), chars)
```
-/
def stripChars {S R T C Q FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (member : C → Q → Except E Bool) (chars : Q) (s : S) : Option (Except E T) :=
  match rstripChars opsS member chars s with
  | none => none
  | some (.error err) => some (.error err)
  | some (.ok right) => lstripChars opsR member chars right

/--
Julia source: base/strings/util.jl:488-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(::AbstractString, ::AbstractString) = throw(ArgumentError("Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))
```
-/
def stripStringError {S U R E : Type} (argumentError : String → E)
    (_s : S) (_chars : U) : Option (Except E R) :=
  some (.error (argumentError "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"))

/--
Julia source: base/strings/util.jl:489-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
strip(f, s::AbstractString) = lstrip(f, rstrip(f, s))
```
-/
def stripPredicate {S R T C FS BS FS2 BS2 E : Type}
    (opsS : StripOps S R C FS BS E) (opsR : StripOps R T C FS2 BS2 E)
    (f : C → Except E Bool) (s : S) : Option (Except E T) :=
  match rstrip opsS f s with
  | none => none
  | some (.error err) => some (.error err)
  | some (.ok right) => lstrip opsR f right

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
      let previousIsCR := cu.getD (ncu - (if twoBytes then 1 else 0) - 1) 0 == 0x0d
      let hasCR := Bool.and (Bool.and hasLF twoBytes) previousIsCR
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
def padRemainderString.loop {S C R FS E : Type}
    (ops : PadRemainderOps S C R FS E) (p : S) (r : Index)
    (first : Option ((Index × C) × FS)) (width : Index) :
    Option (Except E R) :=
  whileLoop (fun (current, width) => do
    match current with
    | none => return .inl (← ops.whole p)
    | some ((i, c), state) =>
      let charWidth ← ops.textwidthChar c
      let width := width + charWidth
      if width.val ≥ r.val then return .inl (← ops.viewPrefix p i)
      else
        let next ← ops.pairsNext p state
        return .inr (next, width)) (first, width)

def padRemainderString {S C R FS E : Type}
    (ops : PadRemainderOps S C R FS E) (p : S) (r : Index) : Option (Except E R) :=
  match ops.pairsFirst p with
  | .error err => some (.error err)
  | .ok first =>
    padRemainderString.loop ops p r first (int 0)

/--
Julia source: base/strings/util.jl:524-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pad_remainder(p::AbstractChar, r::Int) = p
```
-/
def padRemainderChar {C : Type} (_r : Index) (p : C) : C := p

/-- Dispatch to the concrete pad-remainder method. -/
def padRemainder {S C R FS E : Type} (ops : PadRemainderOps S C R FS E)
    (p : PadInput S C) (r : Index) : Option (Except E (PadPart S C R)) :=
  match p with
  | .string str =>
    match padRemainderString ops str r with
    | none => none
    | some (.error err) => some (.error err)
    | some (.ok view) => some (.ok (.view view))
  | .character c => some (.ok (.value (.character (padRemainderChar r c))))

structure PadValueOps (S C R O N E : Type) where
  toInt : N → Except E Index
  signed : Index → Index
  textwidth : PadInput S C → Option (Except E Index)
  isAnnotated : PadInput S C → Except E Bool
  repr : PadInput S C → Except E String
  ncodeunits : PadInput S C → Except E Nat
  isString : PadInput S C → Bool
  codeunitIsUInt8 : PadInput S C → Bool
  argumentError : String → E
  divrem : Index → Index → Except E (Index × Index)
  repeatPad : PadInput S C → Index → Except E (PadInput S C)
  assemble : Bool → List (PadPart S C R) → Except E O

/-- The zero-width pad error text of lpad. -/
def lpadZeroWidthMessage {S C R O N E : Type} (ops : PadValueOps S C R O N E)
    (s p : PadInput S C) : Except E String := do
  let rp ← ops.repr p
  let ncu ← ops.ncodeunits p
  return rp ++ " has zero textwidth" ++
    (if ncu != 1 then "" else
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
    (s p : PadInput S C) (n : N) : Option (Except E O) :=
  let checkAnnotated : Except E Bool := do
    if ← ops.isAnnotated s then pure true else ops.isAnnotated p
  partialBind (some checkAnnotated) fun stringfn =>
    partialBind (some (ops.toInt n)) fun n =>
      partialBind (ops.textwidth s) fun ws =>
        let m := ops.signed n - ws
        if m.val ≤ 0 then some (ops.assemble stringfn [.value s])
        else
          partialBind (ops.textwidth p) fun l =>
            let finish : Except E (Sum O (PadInput S C × Index)) := do
              if l.val = 0 then throw (ops.argumentError (← lpadZeroWidthMessage ops s p))
              let (q, r) ← ops.divrem m l
              let pq ← ops.repeatPad p q
              if r.val = 0 then return Sum.inl (← ops.assemble stringfn [.value pq, .value s])
              return Sum.inr (pq, r)
            partialBind (some finish) fun
              | .inl output => some (.ok output)
              | .inr (pq, r) =>
                partialBind (padRemainder remOps p r) fun rem =>
                  some (ops.assemble stringfn [.value pq, rem, .value s])

/--
Julia source: base/strings/util.jl:511-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lpad(s, n::Integer, p::Union{AbstractChar,AbstractString}=' ') = lpad(string(s)::AbstractString, n, string(p))
```
-/
def lpadWrapper {A B X S C R O N E FS : Type}
    (ops : PadValueOps S C R O N E) (remOps : PadRemainderOps S C R FS E)
    (stringA : A → Except E X) (assertString : X → Except E S)
    (stringB : B → Except E (PadInput S C)) (s : A) (n : N) (p : B) :
    Option (Except E O) :=
  partialBind (some (do assertString (← stringA s))) fun s =>
    partialBind (some (stringB p)) fun p =>
      lpad ops remOps (.string s) p n
/-- The zero-width pad error text of rpad. -/
def rpadZeroWidthMessage {S C R O N E : Type} (ops : PadValueOps S C R O N E)
    (s p : PadInput S C) : Except E String := do
  let rp ← ops.repr p
  let ncu ← ops.ncodeunits p
  return rp ++ " has zero textwidth" ++
    (if ncu != 1 then "" else
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
    (s p : PadInput S C) (n : N) : Option (Except E O) :=
  let checkAnnotated : Except E Bool := do
    if ← ops.isAnnotated s then pure true else ops.isAnnotated p
  partialBind (some checkAnnotated) fun stringfn =>
    partialBind (some (ops.toInt n)) fun n =>
      partialBind (ops.textwidth s) fun ws =>
        let m := ops.signed n - ws
        if m.val ≤ 0 then some (ops.assemble stringfn [.value s])
        else
          partialBind (ops.textwidth p) fun l =>
            let finish : Except E (Sum O (PadInput S C × Index)) := do
              if l.val = 0 then throw (ops.argumentError (← rpadZeroWidthMessage ops s p))
              let (q, r) ← ops.divrem m l
              let pq ← ops.repeatPad p q
              if r.val = 0 then return Sum.inl (← ops.assemble stringfn [.value s, .value pq])
              return Sum.inr (pq, r)
            partialBind (some finish) fun
              | .inl output => some (.ok output)
              | .inr (pq, r) =>
                partialBind (padRemainder remOps p r) fun rem =>
                  some (ops.assemble stringfn [.value s, .value pq, rem])

/--
Julia source: base/strings/util.jl:564-564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rpad(s, n::Integer, p::Union{AbstractChar,AbstractString}=' ') = rpad(string(s)::AbstractString, n, string(p))
```
-/
def rpadWrapper {A B X S C R O N E FS : Type}
    (ops : PadValueOps S C R O N E) (remOps : PadRemainderOps S C R FS E)
    (stringA : A → Except E X) (assertString : X → Except E S)
    (stringB : B → Except E (PadInput S C)) (s : A) (n : N) (p : B) :
    Option (Except E O) :=
  partialBind (some (do assertString (← stringA s))) fun s =>
    partialBind (some (stringB p)) fun p =>
      rpad ops remOps (.string s) p n
/-! ## Width-aware truncation -/

inductive TruncMode where
  | left
  | right
  | center
  deriving DecidableEq

structure TruncModeOps (M : Type) where
  isLeft : M → Bool
  isCenter : M → Bool
  isRightOrCenter : M → Bool

def truncModeOps : TruncModeOps TruncMode where
  isLeft mode := mode == .left
  isCenter mode := mode == .center
  isRightOrCenter mode := mode == .right || mode == .center
structure TruncModeVal (M : Type) where
  value : M

inductive TruncPiece (S V : Type) where
  | string : S → TruncPiece S V
  | view : V → TruncPiece S V

structure TruncateOps (S V R C E : Type) where
  iterateFirst : S → Except E (Option (C × Index))
  iterateAt : S → Index → Except E (Option (C × Index))
  textwidthChar : C → Except E Index
  textwidthReplacement : R → Option (Except E Index)
  getindex : S → Index → Except E C
  firstindex : S → Except E Index
  lastindex : S → Except E Index
  prevind : S → Index → Except E Index
  nextind : S → Index → Except E Index
  substring : S → Index → Index → Except E V
  stringify : S → Except E S
  stringifyReplacement : R → Except E S
  concat : List (TruncPiece S V) → Except E S
  argumentError : String → E
  toInt : Int → Except E Index
/-- Incremental character-width check stopping as soon as the accumulated width exceeds `maxwidth`. -/
def checkTextwidthLoop {S C E : Type}
    (iterateAt : S → Index → Except E (Option (C × Index)))
    (textwidthChar : C → Except E Index) (str : S) (maxwidth : Int)
    (c : C) (i : Index) (total : Index) : Option (Except E Bool) :=
  whileLoop (fun (total, c, i) => do
    let cw ← textwidthChar c
    let total := total + cw
    if total.val > maxwidth then return .inl false
    else
      match ← iterateAt str i with
      | none => return .inl true
      | some (c', i') => return .inr (total, c', i')) (total, c, i)

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
    (str : S) (maxwidth : Int) : Option (Except E Bool) :=
  match ops.iterateFirst str with
  | .error err => some (.error err)
  | .ok none => some (.ok true)
  | .ok (some (c, i)) =>
    checkTextwidthLoop ops.iterateAt ops.textwidthChar str maxwidth c i (int 0)

/-- The width of the character at one valid string index. -/
def textwidthAt {S V R C E : Type} (ops : TruncateOps S V R C E)
    (str : S) (i : Index) : Except E Index := do
  ops.textwidthChar (← ops.getindex str i)

/-- The character-removal loop shared by the truncation modes. -/
def truncateLoop {S V R C E M : Type} (ops : TruncateOps S V R C E)
    (modeOps : TruncModeOps M) (str : S) (maxwidth : Int) (mode : M) (preferLeft : Bool)
    (left0 left right width removedLeft removedRight : Index) (forceOther : Bool) :
    Option (Except E (Index × Index)) :=
  whileLoop (fun (left, right, width, removedLeft, removedRight, forceOther) => do
    let removeRight := modeOps.isLeft mode ||
      (modeOps.isCenter mode && (!preferLeft || left.val > left0.val))
    let firstStep ←
      if removeRight then do
        let removed ← textwidthAt ops str right
        if modeOps.isLeft mode || removedRight.val ≤ removedLeft.val || forceOther then
          if (width + removed).val ≤ maxwidth then do
            let right ← ops.prevind str right
            pure (some (right, width + removed, removedRight + removed, false))
          else pure none
        else pure (some (right, width, removedRight, true))
      else pure (some (right, width, removedRight, forceOther))
    match firstStep with
    | none => return .inl (left, right)
    | some (right, width, removedRight, forceOther) =>
      if modeOps.isRightOrCenter mode then do
        let removed ← textwidthAt ops str left
        if modeOps.isLeft mode || removedLeft.val ≤ removedRight.val || forceOther then
          let again ← textwidthAt ops str left
          if (width + again).val ≤ maxwidth then do
            let left ← ops.nextind str left
            return .inr (left, right, width + again, removedLeft + removed, removedRight, false)
          else return .inl (left, right)
        else return .inr (left, right, width, removedLeft, removedRight, true)
      else return .inr (left, right, width, removedLeft, removedRight, forceOther))
    (left, right, width, removedLeft, removedRight, forceOther)
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
def stringTruncateBoundaries {S V R C E M : Type} (ops : TruncateOps S V R C E)
    (modeOps : TruncModeOps M) (str : S) (maxwidth : Int) (replacement : R)
    (mode : TruncModeVal M)
    (preferLeft : Bool := true) : Option (Except E (Option (Index × Index))):=
  if maxwidth < 0 then
    some (.error (ops.argumentError ("maxwidth " ++ toString maxwidth ++ " should be non-negative")))
  else
    match checkTextwidth ops str maxwidth with
    | none => none
    | some (.error err) => some (.error err)
    | some (.ok true) => some (.ok none)
    | some (.ok false) =>
      match ops.firstindex str with
      | .error err => some (.error err)
      | .ok left0 =>
        match ops.lastindex str with
        | .error err => some (.error err)
        | .ok right =>
          match ops.textwidthReplacement replacement with
          | none => none
          | some (.error err) => some (.error err)
          | some (.ok width) =>
            match truncateLoop ops modeOps str maxwidth mode.value preferLeft left0 left0 right
                width (int 0) (int 0) false with
            | none => none
            | some (.error err) => some (.error err)
            | some (.ok (left, right)) =>
              match ops.prevind str left with
              | .error err => some (.error err)
              | .ok left =>
                match ops.nextind str right with
                | .error err => some (.error err)
                | .ok right => some (.ok (some (left, right)))

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
    (str : S) (maxwidth : Int) (replacement : R) : Option (Except E S) :=
  partialBind (some (ops.toInt maxwidth)) fun maxwidth =>
    partialBind (stringTruncateBoundaries ops truncModeOps str maxwidth.val replacement ⟨.right⟩ true)
      fun boundaries =>
        match boundaries with
        | none => some (ops.stringify str)
        | some (left, _) =>
          partialBind (some (ops.firstindex str)) fun firstIdx =>
            partialBind (some (ops.substring str firstIdx left)) fun view =>
              partialBind (some (ops.stringifyReplacement replacement)) fun replacement =>
                some (ops.concat [.view view, .string replacement])

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
    (str : S) (maxwidth : Int) (replacement : R) : Option (Except E S) :=
  partialBind (some (ops.toInt maxwidth)) fun maxwidth =>
    partialBind (stringTruncateBoundaries ops truncModeOps str maxwidth.val replacement ⟨.left⟩ true)
      fun boundaries =>
        match boundaries with
        | none => some (ops.stringify str)
        | some (_, right) =>
          partialBind (some (ops.lastindex str)) fun lastIdx =>
            partialBind (some (ops.substring str right lastIdx)) fun view =>
              partialBind (some (ops.stringifyReplacement replacement)) fun replacement =>
                some (ops.concat [.string replacement, .view view])

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
    (str : S) (maxwidth : Int) (replacement : R) (preferLeft : Bool := true) :
    Option (Except E S) :=
  partialBind (some (ops.toInt maxwidth)) fun maxwidth =>
    partialBind (stringTruncateBoundaries ops truncModeOps str maxwidth.val replacement
        ⟨.center⟩ preferLeft) fun boundaries =>
      match boundaries with
      | none => some (ops.stringify str)
      | some (left, right) =>
        partialBind (some (ops.firstindex str)) fun firstIdx =>
          partialBind (some (ops.substring str firstIdx left)) fun leftView =>
            partialBind (some (ops.lastindex str)) fun lastIdx =>
              partialBind (some (ops.substring str right lastIdx)) fun rightView =>
                partialBind (some (ops.stringifyReplacement replacement)) fun replacement =>
                  some (ops.concat [.view leftView, .string replacement, .view rightView])
/-! ## Dense strings and IO prefixes -/

structure DenseStringOps (S E : Type) where
  Ptr : Type
  pointer : S → Index → Except E Ptr
  ncodeunits : S → Index
  sizeof : S → Index
  memcmp : S → S → Index → Except E Int
  memcmpPointer : Ptr → S → Index → Except E Int
  nextind : S → Index → Except E Index
  thisind : S → Index → Except E Index

def stringViewDenseOps {V P E : Type}
    (pointerAt : V → Index → Except E P) (length : V → Index)
    (memcmp : JuliaLean.base.strings.stringview.StringView V →
      JuliaLean.base.strings.stringview.StringView V → Index → Except E Int)
    (memcmpPointer : P → JuliaLean.base.strings.stringview.StringView V → Index → Except E Int)
    (nextind thisind : JuliaLean.base.strings.stringview.StringView V → Index → Except E Index) :
    DenseStringOps (JuliaLean.base.strings.stringview.StringView V) E where
  Ptr := P
  pointer := JuliaLean.base.strings.stringview.pointerStringViewAt pointerAt
  ncodeunits := JuliaLean.base.strings.stringview.ncodeunitsStringView length
  sizeof := JuliaLean.base.strings.stringview.sizeofStringView length
  memcmp := memcmp
  memcmpPointer := memcmpPointer
  nextind := nextind
  thisind := thisind

def subStringViewDenseOps {V P E : Type}
    (pointerData : V → P) (addOffset : P → Index → P)
    (addIndex : P → Index → Except E P)
    (memcmp : JuliaLean.base.strings.substring.SubString (JuliaLean.base.strings.stringview.StringView V) →
      JuliaLean.base.strings.substring.SubString (JuliaLean.base.strings.stringview.StringView V) →
      Index → Except E Int)
    (memcmpPointer : P →
      JuliaLean.base.strings.substring.SubString (JuliaLean.base.strings.stringview.StringView V) →
      Index → Except E Int)
    (nextind thisind :
      JuliaLean.base.strings.substring.SubString (JuliaLean.base.strings.stringview.StringView V) →
      Index → Except E Index) :
    DenseStringOps
      (JuliaLean.base.strings.substring.SubString (JuliaLean.base.strings.stringview.StringView V)) E where
  Ptr := P
  pointer := JuliaLean.base.strings.stringview.pointerSubStringViewAt
    pointerData addOffset (fun i => i - int 1) addIndex
  ncodeunits := JuliaLean.base.strings.substring.ncodeunitsSubString
  sizeof := JuliaLean.base.strings.substring.ncodeunitsSubString
  memcmp := memcmp
  memcmpPointer := memcmpPointer
  nextind := nextind
  thisind := thisind

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

/-- `in`'s result: an exception `E`, `none` when a user collection's `iterate` never returns
`nothing`, or the three-valued result (`Truth`: `true`, `false` or `missing`). -/
def liftIn {E α : Type} (x : Except E α) : ExceptT E Option α := ExceptT.mk (some x)

/-- A `Bool` as Julia's three-valued `true`/`false`/`missing` (operators.lean `Truth`). -/
def truth (b : Bool) : operators.Truth := if b then .true else .false

/-- char.jl:263 `==(x::Char, y::Char) = bitcast(UInt32, x) == bitcast(UInt32, y)`. -/
def eqChar {E : Type} (x y : char.JChar) : Except E operators.Truth :=
  pure (truth (char.eq_Char x y))

/-- char.jl:270 `==(x::AbstractChar, y::AbstractChar) = Char(x)::Char == Char(y)::Char`, for
two `AbstractChar` types without a more specific `==`. A user `AbstractChar` type may define
its own `==`, which may also return `missing`; every `eq` below is the pair's method, with
`Truth` results. -/
def eqAbstractChar {X Y E : Type} (toCharX : X → char.CharResult char.JChar)
    (toCharY : Y → char.CharResult char.JChar) (liftC : char.CharError → E) (x : X) (y : Y) :
    Except E operators.Truth :=
  ((char.eq_AbstractChar toCharX toCharY char.eq_Char x y).map truth).mapError liftC

/-- char.jl:261 `in(x::AbstractChar, y::AbstractChar) = x == y`. -/
def memberChar {C D E : Type} (eq : C → D → Except E operators.Truth) (c : C) (y : D) :
    ExceptT E Option operators.Truth :=
  liftIn (eq c y)

/-- A tuple of at most 31 characters: operators.jl:1459, `itr[1] == x` element first, and the
three-valued `_in_tuple` result (`result | v`, operators.jl:1466-1470). -/
def memberTuple {τ C E : Type} {Elem : τ → Type} {ts : List τ}
    (eq : {t : τ} → Elem t → C → Except E operators.Truth) (c : C)
    (itr : operators.HTuple Elem ts) : ExceptT E Option operators.Truth :=
  liftIn (operators.inTupleM eq c itr)

/-- operators.jl:1455 `in(x, itr::Any) = any(==(x), itr)` through the installed `inAny`, with
anyall.jl:115 `any(f, itr) = _any(f, itr, :)` as `anyIterate` over the collection's own
`iterate` (for an `AbstractVector` without its own, abstractarray.jl:1250-1259, whose
abstractarray.lean `iterateArray`/`iterateInteger`/`iterateCartesian` call its `getindex`).
`==(x)` is `Fix2(==, x)` (operators.jl:1270), so each call is `element == c`. -/
def memberAny {A C Q St E : Type} (iterate : Q → Option St → ExceptT E Option (Option (A × St)))
    (eq : A → C → Except E operators.Truth) (c : C) (itr : Q) : ExceptT E Option operators.Truth :=
  operators.inAny
    (fun fx itr => anyall.anyIterate (iterate itr) (fun a => liftIn (fx.f a fx.x ())) false none)
    eq c itr

/-- The elements of a tuple, in order. -/
def htupleElems {τ : Type} {Elem : τ → Type} :
    {ts : List τ} → operators.HTuple Elem ts → List (Σ t, Elem t)
  | [], .nil => []
  | t :: _, .cons v rest => ⟨t, v⟩ :: htupleElems rest

/-- A tuple of 32 or more characters (`Any32`, tuple.jl:364-368): operators.jl:1474
`invoke(in, Tuple{Any,Any}, x, itr)` (operators.lean `inAny32`) runs operators.jl:1455 over
tuple.jl's `iterate` (tuple.lean `iterateTuple`). -/
def memberAny32 {τ C E : Type} {Elem : τ → Type} {ts : List τ}
    (eq : {t : τ} → Elem t → C → Except E operators.Truth) (c : C)
    (itr : operators.HTuple Elem ts) : ExceptT E Option operators.Truth :=
  operators.inAny32
    (fun c xs => memberAny (fun xs st => pure (tuple.iterateTuple xs (st.getD 1)))
      (fun (a : Σ t, Elem t) c => eq a.2 c) c xs)
    c (htupleElems itr)

open JuliaLean.base.range in
/-- range.jl:1495-1498 `in(x::AbstractChar, r::AbstractRange{<:AbstractChar})`. -/
def memberCharRange {X R T S M E : Type} [JIsempty R] [JStep R S] [JIszero S]
    [JFirst R T] [JEq X T] [JMinimum R T] [JLe T X] [JMaximum R T] [JLe X T] [JCtor JInt64 X]
    [JCtor JInt64 T] [JMod JInt64 S M] [JEq M JInt64] (liftX : Exc → E) (c : X) (r : R) :
    ExceptT E Option operators.Truth :=
  liftIn (((in_AbstractChar_AbstractRange c r).map truth).mapError liftX)

/-- dict.jl:254 `key === k || isequal(key, k)`: the builtin `===` first, then `isequalM`. -/
def matchesKeyM {Q K E : Type} (egal : Q → K → Bool) (isequal : Q → K → Except E Bool) (q : Q)
    (k : K) : Except E Bool :=
  if egal q k then pure true else isequal q k

/-- hashing.lean `hash_finalizer` (hashing.jl:56-61) on `UInt64`. -/
def hashFinalizer64 (u : UInt64) : UInt64 :=
  UInt64.ofNat (hashing.hashFinalizer (JInt.wrap .u64 u.toNat)).val.toNat

/-- hashing.jl:3 `HASH_SEED` (hashing.lean `hashSeed`). -/
def hashSeed64 : UInt64 := UInt64.ofNat hashing.hashSeed.val.toNat

/-- hashing.jl:40 `hash(data) = hash(data, HASH_SEED)` on a `Char`: char.jl:265-266. -/
def hashChar {E : Type} (x : char.JChar) : Except E (JInt .u64) :=
  pure (JInt.wrap .u64 (char.hash_Char hashFinalizer64 x hashSeed64).toNat)

/-- hashing.jl:40 on any other `AbstractChar`: char.jl:271 `hash(x::AbstractChar, h::UInt) =
hash(Char(x)::Char, h)`, whose conversion may throw. -/
def hashAbstractChar {C E : Type} (toChar : C → char.CharResult char.JChar)
    (liftC : char.CharError → E) (x : C) : Except E (JInt .u64) := do
  let h ← (char.hash_AbstractChar toChar (char.hash_Char hashFinalizer64) x hashSeed64).mapError
    liftC
  pure (JInt.wrap .u64 h.toNat)

/-- set.jl:92 `in(x, s::Set) = haskey(s.dict, x)` and dict.jl:553 `haskey(h::Dict, key) =
(ht_keyindex(h, key) >= 0)`, for a character `c` of any `AbstractChar` type and a set of any
key type: `hash` is `hashChar` or `hashAbstractChar`, `matchesKey` is `matchesKeyM`. -/
def memberSet {C K E : Type} (liftD : dict.DictError → E) (hash : C → Except E (JInt .u64))
    (matchesKey : C → K → Except E Bool) (c : C) (s : set.SetModel K) :
    ExceptT E Option operators.Truth :=
  liftIn (do return truth ((← dict.htKeyindexM liftD hash matchesKey s.dict c) >= 0))

/-- dict.jl:554 `in(key, v::KeySet{<:Any, <:Dict}) = (ht_keyindex(v.dict, key) >= 0)`. -/
def memberDictKeys {C K V E : Type} (liftD : dict.DictError → E)
    (hash : C → Except E (JInt .u64)) (matchesKey : C → K → Except E Bool) (c : C)
    (keys : dict.KeySet K V) : ExceptT E Option operators.Truth :=
  liftIn (do return truth ((← dict.htKeyindexM liftD hash matchesKey keys.dict c) >= 0))

/-- iddict.jl:185 `in(k, v::KeySet{<:Any,<:IdDict})` (by object identity). -/
def memberIdDictKeys (ops : iddict.Callees) (c keysDict : UInt64) :
    JuliaLean.src.identity_runtime.M operators.Truth := do
  return truth (← iddict.inKeySet ops keysDict c)

/-- idset.jl:47 `in(x, s::IdSet) = haskey(s, x)` (by object identity). -/
def memberIdSet (ops : idset.Callees) (c set : UInt64) :
    JuliaLean.src.identity_runtime.M operators.Truth := do
  return truth (← idset.«in» ops c set)

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
util.jl:93-98 `startswith(io::IO, prefix::Base.Chars)`:
`mark`, `read(io, Char)` and `reset`, then `c in prefix`, the membership above for the
collection's type, returned as is (`missing` included).
-/
def startswithIOChars {IO C Q E : Type} (ops : PrefixIOOps IO C E)
    (member : C → Q → ExceptT E Option operators.Truth) (io : IO) (chars : Q) :
    ExceptT E Option (operators.Truth × IO) := do
  let io ← liftIn (ops.mark io)
  let (c, io) ← liftIn (ops.readChar io)
  let io ← liftIn (ops.reset io)
  return (← member c chars, io)

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
  let aPointer ← ops.pointer a astart
  if (← ops.memcmpPointer aPointer b (ops.sizeof b)) = 0 then
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
  length : Itr → Except E Index
  iterateFirst : Itr → Except E (Option (HexDigit A C × State))
  iterateNext : Itr → State → Except E (Option (HexDigit A C × State))

structure ByteArrayOps (Array I IS E : Type) where
  length : EStateM E Array Index
  eachindex : EStateM E Array IS
  iterateIndex : IS → Option IS → EStateM E Array (Option (I × IS))
  set : I → UInt8 → EStateM E Array Unit

def liftHexExcept {E Array A : Type} : Except E A → EStateM E Array A
  | .ok a => pure a
  | .error err => throw err

def runHexState {E Array α : Type} (act : EStateM E Array α) (dest : Array) :
    Except (E × Array) (α × Array) :=
  match act.run dest with
  | .ok a dest' => .ok (a, dest')
  | .error err dest' => .error (err, dest')

def toHexResult {E Array α : Type} :
    Option (Except (E × Array) (α × Array)) → Option (EStateM.Result E Array α)
  | none => none
  | some (.ok (a, dest)) => some (.ok a dest)
  | some (.error (err, dest)) => some (.error err dest)
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
def hex2bytesBang.loop {Array I IS Itr A C State E : Type}
    (arrayOps : ByteArrayOps Array I IS E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (itr : Itr) (indices : IS) (dest : Array) (next : Option (HexDigit A C × State)) :
    Option (EStateM.Result E Array Array) :=
  toHexResult <| whileLoop (fun (dest, idxSt, next) => do
    let (stepIdx, dest) ← runHexState (arrayOps.iterateIndex indices idxSt) dest
    match stepIdx with
    | none => return .inl (dest, dest)
    | some (i, idxSt') =>
      let (next', dest') ← runHexState (do
        let (x, state) ← liftHexExcept (assertTuple next)
        let step1 ← liftHexExcept (iterOps.iterateNext itr state)
        let (y, state) ← liftHexExcept (assertTuple step1)
        let next' ← liftHexExcept (iterOps.iterateNext itr state)
        let high ← liftHexExcept (numberFromHex argumentError toChar toUInt8 x)
        let shifted := high <<< 4
        let low ← liftHexExcept (numberFromHex argumentError toChar toUInt8 y)
        arrayOps.set i (shifted + low)
        pure next') dest
      return .inr (dest', some idxSt', next')) (dest, none, next)

def hex2bytesBang {Array I IS Itr A C State E : Type}
    (arrayOps : ByteArrayOps Array I IS E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (checkBounds : Bool) (dest : Array) (itr : Itr) : Option (EStateM.Result E Array Array) :=
  let pre : EStateM E Array (Sum Array (IS × Option (HexDigit A C × State))) := do
    let len1 ← liftHexExcept (iterOps.length itr)
    if len1.val % 2 != 0 then
      throw (argumentError "length of iterable must be even")
    if checkBounds then
      let destLen ← arrayOps.length
      let len2 ← liftHexExcept (iterOps.length itr)
      if (int 2 * destLen).val != len2.val then
        throw (argumentError "length of output array must be half of the length of input iterable")
    let len3 ← liftHexExcept (iterOps.length itr)
    if len3.val = 0 then return .inl (← get)
    let next ← liftHexExcept (iterOps.iterateFirst itr)
    let indices ← arrayOps.eachindex
    return .inr (indices, next)
  match pre.run dest with
  | .error err dest' => some (.error err dest')
  | .ok (.inl out) dest' => some (.ok out dest')
  | .ok (.inr (indices, next)) dest' =>
    hex2bytesBang.loop arrayOps iterOps assertTuple argumentError toChar toUInt8 itr
      indices dest' next

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
def hex2bytesString {Array I IS Itr A C State S E : Type}
    (arrayOps : ByteArrayOps Array I IS E) (iterOps : HexIteratorOps Itr A C State E)
    (assertTuple : Option (HexDigit A C × State) → Except E (HexDigit A C × State))
    (argumentError : String → E) (toChar : A → Except E C) (toUInt8 : C → Except E UInt8)
    (sizeof length : S → Index) (transcode : S → Except E Itr)
    (checkBounds : Bool) (dest : Array) (s : S) : Option (EStateM.Result E Array Array) :=
  if (sizeof s).val != (length s).val then
    some (.error (argumentError "input string must consist of hexadecimal characters only") dest)
  else
    match transcode s with
    | .error err => some (.error err dest)
    | .ok itr =>
      hex2bytesBang arrayOps iterOps assertTuple argumentError toChar toUInt8 checkBounds dest itr

/--
Julia source: base/strings/util.jl:1237-1237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hex2bytes(s) = hex2bytes!(Vector{UInt8}(undef, length(s)::Int >> 1), s)
```
-/
def hex2bytesWrapper {Array S E : Type}
    (length : S → Index) (shiftRightOne : Index → Index)
    (allocate : Index → Except E Array)
    (decode : Array → S → Option (EStateM.Result E Array Array))
    (s : S) : Option (Except E Array) :=
  partialBind (some (allocate (shiftRightOne (length s)))) fun dest =>
    match decode dest s with
    | none => none
    | some (.ok out _) => some (.ok out)
    | some (.error err _) => some (.error err)

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
def restFast {S R I E : Type} (substringFrom : S → I → Except E R)
    (s : S) (i : I) : Except E R :=
  substringFrom s i

def restFastDefault {S R E : Type} (substringFrom : S → Index → Except E R)
    (s : S) : Except E R :=
  restFast substringFrom s (int 1)

structure RestOps (S Iter Args State C IO O : Type) (E : Type u) where
  restIterator : S → Args → Except E Iter
  iterateFirst : Iter → Except E (Option (C × State))
  iterateNext : Iter → State → Except E (Option (C × State))
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
def restGeneric.loop {S Iter Args State C IO O : Type} {E : Type u}
    (ops : RestOps S Iter Args State C IO O E) (iter : Iter) (io : IO)
    (first : Option (C × State)) : Option (Except E O) :=
  whileLoop (fun (io, current) => do
    match current with
    | none => return .inl (← ops.takeString io)
    | some (c, state) =>
      let io ← ops.print io c
      let next ← ops.iterateNext iter state
      return .inr (io, next)) (io, first)

def restGeneric {S Iter Args State C IO O : Type} {E : Type u}
    (ops : RestOps S Iter Args State C IO O E)
    (s : S) (states : Args) : Option (Except E O) :=
  partialBind (some ops.newIOBuffer) fun io =>
    partialBind (some (ops.restIterator s states)) fun iter =>
      partialBind (some (ops.iterateFirst iter)) fun first =>
        restGeneric.loop ops iter io first
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
  firstindex : S → Except E Index
  lastindex : S → Except E Index
  ncodeunits : S → Except E Index
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
  let ncu ← ops.ncodeunits iter.str
  if !iter.keepempty && i.val > ncu.val then return none
  let sub ← ops.substringFrom iter.str i
  let ncu2 ← ops.ncodeunits iter.str
  return some (sub, (ncu2 + int 2, k, n + int 1))

open JuliaLean.base.strings.search (SearchM liftE findnextString findprevString findnextPredicate findprevPredicate findnextChar findprevChar SearchStringOps DenseOps indexOps MatchRange)

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
util.jl:791-807 `iterate(::SplitIterator)` with a `findnext` that may not terminate.
-/
def iterateSplitLoop {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → SearchM E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (i k n : Index) (r : Option (Index × Index)) :
    SearchM E (Option (R × SplitState)) := do
  match r with
  | none => liftE (splitTail ops iter i k n)
  | some (a, b) =>
    if n.val = (iter.limit - int 1).val then liftE (splitTail ops iter i k n)
    else
      let ncu ← liftE (ops.ncodeunits iter.str)
      if a.val > ncu.val then liftE (splitTail ops iter i k n)
      else
        let k ← liftE (ops.nextind iter.str b)
        let k_ ← if k.val ≤ a.val then liftE (ops.nextind iter.str a) else pure k
        if i.val < k.val then
          let before ← liftE (ops.prevind iter.str a)
          let sub ← liftE (ops.substringUnchecked iter.str i before)
          if iter.keepempty || i.val < a.val then pure (some (sub, (k, k_, n + int 1)))
          else
            let r ← findnext iter.splitter iter.str k_
            iterateSplitLoop ops findnext iter k k_ n r
        else
          let r ← findnext iter.splitter iter.str k_
          iterateSplitLoop ops findnext iter i k_ n r
partial_fixpoint

/-- util.jl:791-807. -/
def iterateSplit {S R F E : Type} (ops : SplitStringOps S R E)
    (findnext : F → S → Index → SearchM E (Option (Index × Index)))
    (iter : SplitIteratorModel S F) (state : Option SplitState := none) :
    SearchM E (Option (R × SplitState)) := do
  let (i, k, n) ← match state with
    | some st => pure st
    | none => do
      let i ← liftE (ops.firstindex iter.str)
      let k ← liftE (ops.firstindex iter.str)
      pure (i, k, int 0)
  let ncu ← liftE (ops.ncodeunits iter.str)
  if (i - int 1).val > ncu.val then pure none
  else
    let r ← findnext iter.splitter iter.str k
    iterateSplitLoop ops findnext iter i k n r

structure PartitionIteratorModel (S : Type) where
  c : S
  n : Index

structure PartitionOps (S R E : Type) where
  ncodeunits : S → Except E Index
  firstindex : S → Except E Index
  lastindex : S → Except E Index
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
  let state ← match state with
    | some st => pure st
    | none => ops.firstindex iter.c
  let ncu ← ops.ncodeunits iter.c
  if state.val > ncu.val then return none
  let through ← ops.nextindN iter.c state (iter.n - int 1)
  let lastIdx ← ops.lastindex iter.c
  let r := if through.val < lastIdx.val then through else lastIdx
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

/-- The keyword lowering's checks, in declaration order: `limit::Integer`, then
`keepempty::Bool`. -/
def keywordChecks {N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E) (limit : N) (keepempty : K) :
    Except E Bool := do
  if !isInteger limit then throw (limitTypeError limit)
  match asBool keepempty with
  | some b => pure b
  | none => throw (keepemptyTypeError keepempty)

/-- unicode.jl:624 `isspace(c::AbstractChar)` (unicode.lean `isspace`), whose conversions may
throw. -/
def isspaceM {C E : Type} (cops : JuliaLean.base.strings.unicode.CharOps C)
    (P : JuliaLean.base.strings.unicode.Utf8proc)
    (liftU : JuliaLean.base.strings.unicode.UnicodeError → E) (c : C) : ExceptT E Option Bool :=
  ExceptT.mk (some ((JuliaLean.base.strings.unicode.isspace cops P c).mapError liftU))

/-- util.jl:820-821 `eachsplit(str, splitter; limit::Integer=0, keepempty::Bool=true)`; the
installed `eachsplitGeneric` keeps the default constructor's `limit::Int` `MethodError`. -/
def eachsplitKw {S F N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (str : S) (splitter : F) (limit : N) (keepempty : K) :
    Except E (SplitIteratorModel S F) := do
  let keepempty ← keywordChecks isInteger asBool limitTypeError keepemptyTypeError limit keepempty
  eachsplitGeneric isInt toIndex methodError str splitter limit keepempty

/--
Julia source: base/strings/util.jl:823-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::T, splitter::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}};
          limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachsplit(str, in(splitter); limit, keepempty)
```
util.jl:823-825, for a splitter of type `Tuple{Vararg{AbstractChar}}`,
`AbstractVector{<:AbstractChar}` or `Set{<:AbstractChar}` only (any other `AbstractSet` reaches
util.jl:820 unchanged): `limit::Integer` is checked (the untyped `keepempty` is checked by
util.jl:820), and the splitter is `in(splitter)` (`Fix2(in, splitter)`, operators.jl:1453),
called as `in(c, splitter)`: R9-7's three-valued membership for the collection's type, which
may throw or not terminate. Its search is R9-10 `predicateSplitterFindnext` on
`booleanContext` (a `missing` is a `TypeError` in search.jl:350's `&&`).
-/
def eachsplitCharsKw {S Q C N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (member : C → Q → ExceptT E Option operators.Truth) (str : S) (chars : Q) (limit : N)
    (keepempty : K) : Except E (SplitIteratorModel S (C → ExceptT E Option operators.Truth)) := do
  if !isInteger limit then throw (limitTypeError limit)
  eachsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError
    str (fun c => member c chars) limit keepempty

/--
Julia source: base/strings/util.jl:827-828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::T, splitter::AbstractChar; limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachsplit(str, isequal(splitter); limit, keepempty)
```
util.jl:827-828: the splitter is `isequal(splitter)` (operators.jl:1259), the
`Fix2(isequal, splitter)` value (operators.lean `fixIsequal`, which takes `isequal` as a
parameter). Calling it is `isequal(c, splitter)` by dispatch: `isequal` is the pair's own
method, which may throw, for example a user `AbstractChar` type's `isequal`; only for a pair with
no more specific method is it the operators.jl:196 fallback `(c == splitter)::Bool`, R9-7
`isequalM typeError eq` on the pair's three-valued `==`. Its search dispatches on the `Fix2`:
R9-10 `isequalCharSplitterFindnext` (search.jl:143-166, the installed
`findnextChar`) for a `UTF8String`, otherwise `predicateSplitterFindnext` on
`fun c => liftE (pred.f c pred.x ())`.
-/
def eachsplitCharKw {S C D N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (isequal : C → D → Except E Bool) (str : S) (delimiter : D)
    (limit : N) (keepempty : K) :
    Except E (SplitIteratorModel S
      (operators.Fix 2 (C → D → Unit → Except E Bool) D operators.Fix2OpTag.isequal delimiter)) := do
  if !isInteger limit then throw (limitTypeError limit)
  eachsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError
    str (operators.fixIsequal isequal delimiter) limit keepempty

/--
Julia source: base/strings/util.jl:831-832 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachsplit(str::AbstractString; limit::Integer=0, keepempty=false) =
    eachsplit(str, isspace; limit, keepempty)
```
util.jl:831-832 (`keepempty=false` default): the splitter is `isspace`.
-/
def eachsplitWhitespaceKw {S C N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (cops : JuliaLean.base.strings.unicode.CharOps C) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (liftU : JuliaLean.base.strings.unicode.UnicodeError → E) (str : S) (limit : N)
    (keepempty : K) : Except E (SplitIteratorModel S (C → ExceptT E Option Bool)) := do
  if !isInteger limit then throw (limitTypeError limit)
  eachsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError
    str (isspaceM cops P liftU) limit keepempty

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

/-- util.jl:884-885. -/
def eachrsplitKw {S F N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (str : S) (splitter : F) (limit : N) (keepempty : K) :
    Except E (RSplitIteratorModel S F) := do
  let keepempty ← keywordChecks isInteger asBool limitTypeError keepemptyTypeError limit keepempty
  eachrsplitGeneric isInt toIndex methodError str splitter limit keepempty

/--
Julia source: base/strings/util.jl:887-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::T, splitter::Union{Tuple{Vararg{AbstractChar}},AbstractVector{<:AbstractChar},Set{<:AbstractChar}};
          limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachrsplit(str, in(splitter); limit, keepempty)
```
util.jl:887-889 (as util.jl:823-825: tuples, vectors and `Set`s of `AbstractChar` only).
-/
def eachrsplitCharsKw {S Q C N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (member : C → Q → ExceptT E Option operators.Truth) (str : S) (chars : Q) (limit : N)
    (keepempty : K) : Except E (RSplitIteratorModel S (C → ExceptT E Option operators.Truth)) := do
  if !isInteger limit then throw (limitTypeError limit)
  eachrsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError
    str (fun c => member c chars) limit keepempty

/--
Julia source: base/strings/util.jl:891-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::T, splitter::AbstractChar; limit::Integer=0, keepempty=true) where {T<:AbstractString} =
    eachrsplit(str, isequal(splitter); limit, keepempty)
```
util.jl:891-892 (as util.jl:827-828: `isequal` is the pair's own method;
`isequalCharSplitterFindprev`, search.jl:209-230, for a `UTF8String`).
-/
def eachrsplitCharKw {S C D N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (isequal : C → D → Except E Bool) (str : S) (delimiter : D)
    (limit : N) (keepempty : K) :
    Except E (RSplitIteratorModel S
      (operators.Fix 2 (C → D → Unit → Except E Bool) D operators.Fix2OpTag.isequal delimiter)) := do
  if !isInteger limit then throw (limitTypeError limit)
  eachrsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError
    str (operators.fixIsequal isequal delimiter) limit keepempty

/--
Julia source: base/strings/util.jl:895-896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eachrsplit(str::AbstractString; limit::Integer=0, keepempty=false) =
    eachrsplit(str, isspace; limit, keepempty)
```
util.jl:895-896 (`keepempty=false` default).
-/
def eachrsplitWhitespaceKw {S C N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (cops : JuliaLean.base.strings.unicode.CharOps C) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (liftU : JuliaLean.base.strings.unicode.UnicodeError → E) (str : S) (limit : N)
    (keepempty : K) : Except E (RSplitIteratorModel S (C → ExceptT E Option Bool)) := do
  if !isInteger limit then throw (limitTypeError limit)
  eachrsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError
    str (isspaceM cops P liftU) limit keepempty

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
util.jl:898-927 inner `while`.
-/
def iterateRSplitLoop {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → SearchM E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (remaining to frm nextTo : Index) :
    SearchM E (Index × Index × Index) := do
  if remaining.val = 0 then pure (frm, nextTo, to)
  else
    match ← findprev iter.splitter iter.str to with
    | none => pure (int 1, int (-1), to)
    | some (a, b) =>
      let frm ← liftE (ops.nextind iter.str b)
      let nextTo ← if b.val < a.val && to.val < 2 then pure (int (-1))
        else liftE (ops.prevind iter.str a)
      if frm.val > to.val && !iter.keepempty then
        iterateRSplitLoop ops findprev iter remaining nextTo frm nextTo
      else pure (frm, nextTo, to)
partial_fixpoint

/-- util.jl:898-927. -/
def iterateRSplit {S R F E : Type} (ops : SplitStringOps S R E)
    (findprev : F → S → Index → SearchM E (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) (state : Option RSplitState := none) :
    SearchM E (Option (R × RSplitState)) := do
  let (to, remaining) ← match state with
    | some st => pure st
    | none => do
      let lastIdx ← liftE (ops.lastindex iter.str)
      pure (lastIdx, iter.limit - int 1)
  if to.val < 0 then pure none
  else
    let (frm, nextTo, to) ← iterateRSplitLoop ops findprev iter remaining to (int 1) (int (-1))
    if frm.val > to.val && !iter.keepempty then pure none
    else
      let sub ← liftE (ops.substringChecked iter.str frm to)
      pure (some (sub, (nextTo, remaining - int 1)))

/-- util.jl:793, 803 `findnext(iter.splitter, iter.str, k)::Union{Nothing,Int,UnitRange{Int}}`
for an `AbstractString` splitter (search.jl:507); `search` is `searchRange` over
`searchindexDense` (both dense UTF-8) or `searchindexGeneric`. -/
def stringSplitterFindnext {S T E : Type}
    (search : S → T → Index → SearchM E (Option MatchRange)) (t : T) (s : S) (k : Index) :
    SearchM E (Option (Index × Index)) := do
  return (← findnextString indexOps search t s k).map fun r => (r.first, r.last)

/-- util.jl:903 `findprev(it.splitter, it.str, to)` for an `AbstractString` splitter
(search.jl:821). -/
def stringSplitterFindprev {S T E : Type}
    (rsearch : S → T → Index → SearchM E (Option MatchRange)) (t : T) (s : S) (k : Index) :
    SearchM E (Option (Index × Index)) := do
  return (← findprevString indexOps rsearch t s k).map fun r => (r.first, r.last)

/-- search.jl:350, 675 `testf(s[i]) && return i` with a three-valued `testf` (R9-7's `in`): a
`missing` in that Boolean context is a `TypeError`. -/
def booleanContext {C E : Type} (nonBoolean : E) (testf : C → SearchM E operators.Truth) (c : C) :
    SearchM E Bool := do
  match ← testf c with
  | .true => pure true
  | .false => pure false
  | .missing => throw nonBoolean

/-- util.jl:793, 795, 803 for a predicate splitter through search.jl:343 (`findnextPredicate`):
an `Int` match `i` gives `first(i) = last(i) = i` (number.jl). This is the dispatch for every
`Function` splitter except `Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar}` on a
`UTF8String` (stringview.jl:6), which goes to search.jl:143-166
(`isequalCharSplitterFindnext`). -/
def predicateSplitterFindnext {S C E : Type} (ops : SearchStringOps S C E)
    (testf : C → SearchM E Bool) (s : S) (k : Index) : SearchM E (Option (Index × Index)) := do
  return (← findnextPredicate ops indexOps testf s k).map fun i => (i, i)

/-- util.jl:903 for a predicate splitter through search.jl:668 (`findprevPredicate`), with the
same exception as `predicateSplitterFindnext` (search.jl:209-230, `isequalCharSplitterFindprev`). -/
def predicateSplitterFindprev {S C E : Type} (ops : SearchStringOps S C E)
    (testf : C → SearchM E Bool) (s : S) (k : Index) : SearchM E (Option (Index × Index)) := do
  return (← findprevPredicate ops indexOps testf s k).map fun i => (i, i)

/-- util.jl:793, 795, 803 for an `isequal(splitter)` or `==(splitter)` splitter
(`Fix2{<:Union{typeof(isequal),typeof(==)},<:AbstractChar}`, operators.lean `Fix`) on a
`UTF8String`: search.jl:143-166, the installed `findnextChar`, which converts `Char(pred.x)`
and searches bytes instead of calling the predicate. -/
def isequalCharSplitterFindnext {S A C F FT X E : Type} {fTag : FT} {xTag : X}
    (ops : SearchStringOps S JuliaLean.base.char.JChar E) (bytes : DenseOps A UInt8 E)
    (codeunits : S → A) (chars : JuliaLean.base.strings.search.CharOps C E) (pred : operators.Fix 2 F C fTag xTag) (s : S)
    (k : Index) : SearchM E (Option (Index × Index)) := do
  return (← liftE (findnextChar ops bytes codeunits chars indexOps pred.x s k)).map fun i => (i, i)

/-- util.jl:903 for the same splitter on a `UTF8String`: search.jl:209-230, the installed
`findprevChar`. -/
def isequalCharSplitterFindprev {S A C F FT X E : Type} {fTag : FT} {xTag : X}
    (ops : SearchStringOps S JuliaLean.base.char.JChar E) (bytes : DenseOps A UInt8 E)
    (codeunits : S → A) (chars : JuliaLean.base.strings.search.CharOps C E) (pred : operators.Fix 2 F C fTag xTag) (s : S)
    (k : Index) : SearchM E (Option (Index × Index)) := do
  return (← liftE (findprevChar ops bytes codeunits chars indexOps pred.x s k)).map fun i => (i, i)

open JuliaLean.base.array (MutationM MutableMemory MemoryLayout MemoryLayoutMetadata collectKnownUnknown
  similarForUnknown mutableAllocate push1361 growend growendInternal mutableStorage mutableLength
  mutableSet mutableGet reverseDims reverseColon reverseBang midpoint)
open JuliaLean.base.abstractarray (similarTypeVarargs similarFallback)

/-- One monad for `split`/`rsplit`: the `Vector{SubString{T}}` store, the iterators' exception
type `E`, and non-termination (`none`). -/
abbrev SplitM (S E : Type) :=
  ExceptT E (StateT (MutableMemory (JuliaLean.base.strings.substring.SubString S)) Option)

def liftPartial {S E α : Type} (r : Option (Except E α)) : SplitM S E α :=
  ExceptT.mk (StateT.mk fun mem => r.map (·, mem))

def liftMutation {S E α : Type} (liftA : JuliaLean.base.array.Error → E)
    (act : MutationM (JuliaLean.base.strings.substring.SubString S) α) : SplitM S E α :=
  ExceptT.mk (StateT.mk fun mem =>
    let (r, mem') := act.run.run mem
    some (r.mapError liftA, mem'))

/-- `for x in iter` over `iterate(::SplitIterator)` (Julia's `for` lowering), on R9-10's
`iterateSplit`, whose `findnext` may not terminate. -/
def splitForIn {S F E β : Type}
    (ops : SplitStringOps S (JuliaLean.base.strings.substring.SubString S) E)
    (findnext : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (iter : SplitIteratorModel S F)
    (body : JuliaLean.base.strings.substring.SubString S → β → SplitM S E (ForInStep β))
    (state : Option SplitState) (b : β) : SplitM S E β := do
  match ← liftPartial (iterateSplit ops findnext iter state).run with
  | none => pure b
  | some (x, next) =>
      match ← body x b with
      | .done b => pure b
      | .yield b => splitForIn ops findnext iter body (some next) b
partial_fixpoint

/-- `for x in iter` over `iterate(::RSplitIterator)` (Julia's `for` lowering), on R9-10's
`iterateRSplit`. -/
def rsplitForIn {S F E β : Type}
    (ops : SplitStringOps S (JuliaLean.base.strings.substring.SubString S) E)
    (findprev : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (iter : RSplitIteratorModel S F)
    (body : JuliaLean.base.strings.substring.SubString S → β → SplitM S E (ForInStep β))
    (state : Option RSplitState) (b : β) : SplitM S E β := do
  match ← liftPartial (iterateRSplit ops findprev iter state).run with
  | none => pure b
  | some (x, next) =>
      match ← body x b with
      | .done b => pure b
      | .yield b => rsplitForIn ops findprev iter body (some next) b
partial_fixpoint

/-- array.jl:703-704 `_similar_for(1:1, SubString{T}, itr, SizeUnknown(), nothing)`:
`similar(1:1, SubString{T}, 0)`, abstractarray.jl:823 then 834, `Vector{SubString{T}}(undef, 0)`. -/
def similarSplitVector {S E X : Type} (layout : Option MemoryLayout)
    (liftA : JuliaLean.base.array.Error → E) (c : Unit) (t : Unit) (itr : X) : SplitM S E Nat :=
  liftMutation liftA (similarForUnknown
    (fun c (t : Unit) n => similarTypeVarargs
      (similarFallback (fun (_ : Unit) dims =>
        mutableAllocate layout 0 (dims.headD JuliaLean.base.array.zero)))
      c t [n]) c t itr)

/-- array.jl:1353-1365 `push!(a, x)` with `x isa SubString{T}` (the `for` body discards the
returned vector). -/
def pushSplitPiece {S E : Type} (layout : MemoryLayoutMetadata)
    (liftA : JuliaLean.base.array.Error → E) (a : Nat)
    (x : JuliaLean.base.strings.substring.SubString S) : SplitM S E Unit :=
  liftMutation liftA (do
    let _ ← JuliaLean.base.array.push (fun _ => true) id pure
      (push1361 (growend (mutableStorage layout) pure (growendInternal (mutableStorage layout)))
        mutableLength mutableSet) a x
    pure ())

/-- array.jl:771, 780-786 `collect(itr)` of a `SplitIterator`. -/
def collectSplit {S F E : Type} (layout : MemoryLayoutMetadata)
    (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (JuliaLean.base.strings.substring.SubString S) E)
    (findnext : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (iter : SplitIteratorModel S F) : SplitM S E Nat :=
  letI : ForIn (SplitM S E) (SplitIteratorModel S F)
      (JuliaLean.base.strings.substring.SubString S) :=
    ⟨fun it b body => splitForIn ops findnext it body none b⟩
  collectKnownUnknown (fun _ => ()) (fun c t => similarSplitVector layout.allocation liftA c t iter)
    (pushSplitPiece layout liftA) () iter

/-- array.jl:771, 780-786 `collect(itr)` of an `RSplitIterator`. -/
def collectRSplit {S F E : Type} (layout : MemoryLayoutMetadata)
    (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (JuliaLean.base.strings.substring.SubString S) E)
    (findprev : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (iter : RSplitIteratorModel S F) : SplitM S E Nat :=
  letI : ForIn (SplitM S E) (RSplitIteratorModel S F)
      (JuliaLean.base.strings.substring.SubString S) :=
    ⟨fun it b body => rsplitForIn ops findprev it body none b⟩
  collectKnownUnknown (fun _ => ()) (fun c t => similarSplitVector layout.allocation liftA c t iter)
    (pushSplitPiece layout liftA) () iter

/-- array.jl:2266-2267, 2312-2328 `reverse!(v)` of the collected `Vector`. -/
def reverseVector {α : Type} (a : Nat) : MutationM α Nat :=
  reverseDims (fun a (_ : Unit) => reverseColon (fun _ => pure JuliaLean.base.array.one)
    mutableLength
    (reverseBang pure pure pure (fun _ => pure JuliaLean.base.array.one) mutableLength
      (fun lo hi => pure (midpoint (· + ·) (· - ·)
        (fun x n => JuliaLean.JInt.wrap .i64 ((x.val % 2 ^ 64) / 2 ^ n.val.toNat)) lo hi))
      mutableGet mutableSet) a) a ()

/--
Julia source: base/strings/util.jl:958-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function split(str::T, splitter;
               limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}
    collect(eachsplit(str, splitter; limit, keepempty))
end
```
-/
def splitGeneric {S F N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (layout : MemoryLayoutMetadata) (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (JuliaLean.base.strings.substring.SubString S) E)
    (findnext : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (str : S) (splitter : F) (limit : N) (keepempty : Bool) : SplitM S E Nat := do
  collectSplit layout liftA ops findnext
    (← liftPartial (some (eachsplitGeneric isInt toIndex methodError str splitter limit keepempty)))
open JuliaLean.base.strings.substring (SubString)
/-- util.jl:958-961: the typed keywords are checked, then `splitGeneric` above runs
`collect(eachsplit(...))`, whose keyword checks pass on the same values. A
`Chars`, `AbstractChar` or whitespace splitter reaches util.jl:823-832 through `eachsplit`'s
dispatch, so its `splitter` here is the predicate `eachsplitCharsKw`/`eachsplitCharKw`/
`isspaceM` builds. -/
def splitKw {S F N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (layout : MemoryLayoutMetadata) (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (SubString S) E)
    (findnext : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (str : S) (splitter : F) (limit : N) (keepempty : K) : SplitM S E Nat := do
  let keepempty ← liftPartial
    (some (keywordChecks isInteger asBool limitTypeError keepemptyTypeError limit keepempty))
  splitGeneric isInt toIndex methodError layout liftA ops findnext str splitter
    limit keepempty

/--
Julia source: base/strings/util.jl:964-966 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
split(str::AbstractString;
      limit::Integer=0, keepempty::Bool=false) =
    split(str, isspace; limit, keepempty)
```
-/
def splitWhitespaceKw {S C N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (layout : MemoryLayoutMetadata) (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (SubString S) E)
    (findnext : (C → ExceptT E Option Bool) → S → Index → ExceptT E Option (Option (Index × Index)))
    (cops : JuliaLean.base.strings.unicode.CharOps C) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (liftU : JuliaLean.base.strings.unicode.UnicodeError → E) (str : S) (limit : N)
    (keepempty : K) : SplitM S E Nat := do
  let _ ← liftPartial
    (some (keywordChecks isInteger asBool limitTypeError keepemptyTypeError limit keepempty))
  splitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError layout
    liftA ops findnext str (isspaceM cops P liftU) limit keepempty

/--
Julia source: base/strings/util.jl:1001-1004 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rsplit(str::T, splitter;
               limit::Integer=0, keepempty::Bool=true) where {T<:AbstractString}
    reverse!(collect(eachrsplit(str, splitter; limit, keepempty)))
end
```
-/
def rsplitGeneric {S F N E : Type}
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (layout : MemoryLayoutMetadata) (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (JuliaLean.base.strings.substring.SubString S) E)
    (findprev : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (str : S) (splitter : F) (limit : N) (keepempty : Bool) : SplitM S E Nat := do
  let a ← collectRSplit layout liftA ops findprev
    (← liftPartial (some (eachrsplitGeneric isInt toIndex methodError str splitter limit keepempty)))
  liftMutation liftA (reverseVector a)

/-- util.jl:1001-1004, then `rsplitGeneric` above. -/
def rsplitKw {S F N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (layout : MemoryLayoutMetadata) (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (SubString S) E)
    (findprev : F → S → Index → ExceptT E Option (Option (Index × Index)))
    (str : S) (splitter : F) (limit : N) (keepempty : K) : SplitM S E Nat := do
  let keepempty ← liftPartial
    (some (keywordChecks isInteger asBool limitTypeError keepemptyTypeError limit keepempty))
  rsplitGeneric isInt toIndex methodError layout liftA ops findprev str splitter
    limit keepempty

/--
Julia source: base/strings/util.jl:1007-1009 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rsplit(str::AbstractString;
      limit::Integer=0, keepempty::Bool=false) =
    rsplit(str, isspace; limit, keepempty)
```
-/
def rsplitWhitespaceKw {S C N K E : Type} (isInteger : N → Bool) (asBool : K → Option Bool)
    (limitTypeError : N → E) (keepemptyTypeError : K → E)
    (isInt : N → Bool) (toIndex : N → Except E Index) (methodError : String → E)
    (layout : MemoryLayoutMetadata) (liftA : JuliaLean.base.array.Error → E)
    (ops : SplitStringOps S (SubString S) E)
    (findprev : (C → ExceptT E Option Bool) → S → Index → ExceptT E Option (Option (Index × Index)))
    (cops : JuliaLean.base.strings.unicode.CharOps C) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (liftU : JuliaLean.base.strings.unicode.UnicodeError → E) (str : S) (limit : N)
    (keepempty : K) : SplitM S E Nat := do
  let _ ← liftPartial
    (some (keywordChecks isInteger asBool limitTypeError keepemptyTypeError limit keepempty))
  rsplitKw isInteger asBool limitTypeError keepemptyTypeError isInt toIndex methodError layout
    liftA ops findprev str (isspaceM cops P liftU) limit keepempty
/-! ## Replacement helper dispatch -/

structure ReplaceRange where
  first : Index
  last : Index

inductive ReplaceSearchResult where
  | index : Index → ReplaceSearchResult
  | range : ReplaceRange → ReplaceSearchResult

def replaceSearchFirst : ReplaceSearchResult → Index
  | .index index => index
  | .range range => range.first

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
  firstindex : S → Except E Index
  lastindex : S → Except E Index
  nextind : S → Index → Except E Index
  findnext : Q → S → Index → Except E (Option ReplaceSearchResult)
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
  let e1 ← ops.nextind str (← ops.lastindex str)
  let first ← ops.firstindex str
  let patterns := pairs.map fun pair => ops.patternReplacer pair.pattern
  let replaces := pairs.map (·.replacement)
  let ranges ← patterns.mapM fun pattern => do
    match ← ops.findnext pattern str first with
    | none => return replaceSentinel e1
    | some found =>
      if (replaceSearchFirst found).val == 0 then
        return replaceSentinel e1
      else
        match found with
        | .index index => return ⟨index, index⟩
        | .range range => return range
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
  findnext : Q → S → Index → Except E (Option ReplaceSearchResult)

/-- Refreshes only pattern matches whose previous range starts before the next search index. -/
def replaceRefresh {S Q E : Type} (findnext : Q → S → Index → Except E (Option ReplaceSearchResult))
    (str : S) (e1 k : Index) : List Q → List ReplaceRange → Except E (List ReplaceRange)
  | [], _ => .ok []
  | _ :: _, [] => .ok []
  | pattern :: patterns, range :: ranges => do
    let range ← if range.first.val < k.val then do
      match ← findnext pattern str k with
      | none => pure (replaceSentinel e1)
      | some found =>
        if (replaceSearchFirst found).val == 0 then
          pure (replaceSentinel e1)
        else
          match found with
          | .index index => pure ⟨index, index⟩
          | .range foundRange => pure foundRange
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
  firstindex : S → Except E Index
  first : ReplaceRange → Index
  writeRest : IO → S → Index → Except E IO
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
def replaceFinish.loop {S P Q R IO E : Type}
    (ops : ReplaceFinishOps S P R IO E)
    (once : IO → S → Index → Index → List Q → List R → List ReplaceRange → Index → Index → Index → Except E (ReplaceStep IO))
    (str : S) (count e1 : Index) (patterns : List Q) (replaces : List R)
    (start : Index) (io : IO) (ranges : List ReplaceRange) (n i : Index) :
    Option (Except E (IO × List ReplaceRange × Index)) :=
  whileLoop (fun (io, ranges, n, i) => do
    if n.val > count.val then return .inl (io, ranges, i)
    let step ← once io str start e1 patterns replaces ranges count n i
    if (ops.first step.range).val ≥ e1.val then
      return .inl (step.io, step.ranges, step.nextIndex)
    else return .inr (step.io, step.ranges, n + int 1, step.nextIndex))
    (io, ranges, n, i)

def replaceFinish {S P Q R IO E : Type}
    (ops : ReplaceFinishOps S P R IO E)
    (once : IO → S → Index → Index → List Q → List R → List ReplaceRange → Index → Index → Index → Except E (ReplaceStep IO))
    (io : IO) (str : S) (count e1 : Index) (patterns : List Q)
    (replaces : List R) (ranges : List ReplaceRange) : Option (Except E IO) :=
  partialBind (some (ops.firstindex str)) fun start =>
    partialBind (replaceFinish.loop ops once str count e1 patterns replaces start io ranges
      (int 1) start) fun (io, _, i) =>
        partialBind (some (patterns.mapM fun pattern => pure (freePatReplacer pattern))) fun _ =>
          some (ops.writeRest io str i)

structure ReplaceEngineOps (S P Q R IO O E : Type) where
  initOps : ReplaceInitOps S P Q R E
  finishOps : ReplaceFinishOps S P R IO E
  onceOps : ReplaceOnceOps S P Q R IO E
  writeString : IO → S → Except E IO
  sizeof : S → Except E Index
  newBuffer : Index → Except E IO
  liftJ : JlError → E
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
    (io : IO) (str : S) (pairs : List (ReplacePair P R)) (count : Index) :
    Option (Except E IO) :=
  if count.val = 0 then some (ops.writeString io str)
  else
    partialBind (some (replaceInit ops.initOps str pairs count)) fun
      (e1, patterns, replaces, ranges, notfound) =>
        if notfound then
          partialBind (some (patterns.mapM fun pattern => pure (freePatReplacer pattern))) fun _ =>
            some (ops.writeString io str)
        else replaceFinish ops.finishOps (replaceOnce ops.onceOps)
          io str count e1 patterns replaces ranges

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
    (str : S) (pairs : List (ReplacePair P R)) (count : Index) : Option (Except E O) :=
  if count.val = 0 then some (ops.toString str)
  else
    partialBind (some (replaceInit ops.initOps str pairs count)) fun
      (e1, patterns, replaces, ranges, notfound) =>
        if notfound then
          partialBind (some (patterns.mapM fun pattern => pure (freePatReplacer pattern))) fun _ =>
            some (ops.toString str)
        else
          let newOut : Except E IO := do
            let size ← ops.sizeof str
            let x : JuliaLean.base.float.FV .f64 :=
              JuliaLean.base.float.mul_float (JuliaLean.Promotion.Fl.ofBits 0x3FF3333333333333)
                (JuliaLean.base.float.floatOfInt .f64 size)
            let hint ← (JuliaLean.base.float.intOfFloat .i64
              (JuliaLean.base.float.round_Down_llvm x)).mapError ops.liftJ
            ops.newBuffer hint
          partialBind (some newOut) fun io =>
            partialBind (replaceFinish ops.finishOps (replaceOnce ops.onceOps)
                io str count e1 patterns replaces ranges) fun io =>
              some (ops.takeString io)

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
    (pairs : List (ReplacePair P R)) (count : N) : Option (Except E IO) :=
  partialBind (some (toString str)) fun str =>
    partialBind (some (toInt count)) fun count =>
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
    (pairs : List (ReplacePair P R)) (count : N) : Option (Except E O) :=
  partialBind (some (toString str)) fun str =>
    partialBind (some (toInt count)) fun count =>
      replaceStringEngine ops str pairs count

end JuliaLean.base.strings.util

namespace JuliaLean.Strings

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

namespace JuliaLean.Strings

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


/-!
# `startswith(io::IO, prefix)`

`base/strings/util.jl:87-105` (master `bbfa0ce4150`) on an `IOBuffer`, with the
`IOBuffer` model of the IOBuffers area (`JuliaLean/IOBuffers/Model.lean`) and the
generic `read(io::IO, ::Type{Char})` of `base/io.jl:1091-1106`.

A `Char` is its 32-bit bit pattern, as in `JuliaLean/Strings`.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.IOBuffers

/-- The continuation-byte loop of `read(io::IO, ::Type{Char})`, `base/io.jl:1097-1103`:
`while s ≥ l && !eof(io); peek(io) & 0xc0 == 0x80 || break; b = read(io, UInt8);
c |= UInt32(b) << s; s -= 8; end`. `s` starts at 16 and drops by 8 per step while
`l ≥ 0`, so three steps exhaust the loop; the first argument is that bound. -/
def readCharLoop (l : Int) : Nat → Int → UInt32 → M UInt32
  | 0, _, c => pure c
  | k + 1, s, c => do
    let io ← get
    if !(decide (s ≥ l) && !eof io) then return c
    let p ← peekByte
    if (p &&& 0xc0) != 0x80 then return c
    let b ← readByte
    readCharLoop l k (s - 8) (c ||| (b.toUInt32 <<< UInt32.ofNat s.toNat))

/-- `read(io::IO, ::Type{Char})`, `base/io.jl:1091-1106`. `leading_ones(b0)` is
`Strings.clo32` of the byte in the top position; `l = 0x08 * (0x04 - lo)`. -/
def readChar : M UInt32 := do
  let b0 ← readByte
  let lo := Strings.clo32 (b0.toUInt32 <<< 24)
  let c : UInt32 := b0.toUInt32 <<< 24
  if 2 ≤ lo ∧ lo ≤ 4 then readCharLoop (8 * (4 - (lo : Int))) 3 16 c else pure c

/-- `startswith(io::IO, prefix::Base.Chars)`, `base/strings/util.jl:93-98`, for a
tuple or vector of characters `cs`: `mark(io); c = read(io, Char); reset(io); c in prefix`. -/
def startswithChars (cs : List UInt32) : M Bool := do
  discard mark
  let c ← readChar
  discard reset
  return cs.contains c

/-- `startswith(io::IO, prefix::UTF8String)`, `base/strings/util.jl:99-104`:
`mark(io); s = read(io, ncodeunits(prefix)); reset(io); s == codeunits(prefix)`. -/
def startswithStr (p : List UInt8) : M Bool := do
  discard mark
  let s ← readN (i p.length)
  discard reset
  return s == p

/-! ## Registry -/

open JuliaLean.Registry

end JuliaLean.StringUtil


/-!
# `hex2bytes` and `bytes2hex`, `base/strings/util.jl:1192-1334`

Master `bbfa0ce4150`. A byte vector is a `List UInt8`. The generic
`hex2bytes!(dest, itr)` is modelled once over an iteration protocol
(`iterate(itr)` and `iterate(itr, state)`) and an element conversion
(`number_from_hex`), and instantiated for `codeunits(s::String)` and for
`SubString{String}`.
-/

namespace JuliaLean.StringUtil

open JuliaLean.Strings JuliaLean.Registry

/-- `ArgumentError(msg)`. -/
abbrev argErr (msg : String) : SErr := .jl (.argumentError msg)

/-- `hex_chars`, `base/char.jl:308-311`: `'0'..'9'` then `'a'..'z'`. -/
def hexChars : List UInt8 :=
  [0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
   0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d,
   0x6e, 0x6f, 0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a]

/-- `hex_chars[1 + x >> 4]` (`>>` binds tighter than `+`). -/
def hexHi (x : UInt8) : UInt8 := hexChars.getD (x >>> 4).toNat 0

/-- `hex_chars[1 + x & 0xf]`. -/
def hexLo (x : UInt8) : UInt8 := hexChars.getD (x &&& 0xf).toNat 0

/-- The bytes the loop of `bytes2hex` stores: `hexHi x` at `2i - 1` and
`hexLo x` at `2i` for the `i`-th byte `x` (`base/strings/util.jl:1321-1324`). -/
def bytes2hexFill (b : List UInt8) : List UInt8 := b.flatMap fun x => [hexHi x, hexLo x]

/-- `bytes2hex(itr)` for `itr::Vector{UInt8}`, `base/strings/util.jl:1316-1327`.
The `eltype` check passes. `2*length(itr)` is an `Int` product, and
`_string_n(n)` converts it with `convert(Csize_t, n)` (`base/strings/string.jl:184`),
which throws `InexactError` for negative `n`. -/
def bytes2hex (b : List UInt8) : SJl JStr :=
  let n := ix 2 * ix b.length
  if n.val < 0 then .error (.jl (.inexactError "UInt64"))
  else stringN n.val.toNat fun _ => bytes2hexFill b

/-- `number_from_hex(c::UInt8)`, `base/strings/util.jl:1278-1283`. -/
def numberFromHexByte (c : UInt8) : SJl UInt8 :=
  if 0x30 ≤ c ∧ c ≤ 0x39 then .ok (c - 0x30)
  else
    let c := c ||| 0x20
    if 0x61 ≤ c ∧ c ≤ 0x66 then .ok (c - 0x61 + 0x0a)
    else .error (argErr "byte is not an ASCII hexadecimal digit")

/-- `number_from_hex(c::Char) = number_from_hex(UInt8(c))`, `base/strings/util.jl:1277`.
`UInt8(c)` is `UInt8(codepoint(c))` (`base/char.jl:56`): `codepoint` throws
`InvalidCharError` for a malformed `c`, and the checked conversion of the
`UInt32` throws `InexactError` above `0xff`. -/
def numberFromHexChar (c : UInt32) : SJl UInt8 :=
  match codepoint c with
  | .error e => .error e
  | .ok u => if u ≤ 0xff then numberFromHexByte u.toUInt8 else .error (.jl (.inexactError "UInt8"))

/-- The loop of `hex2bytes!(dest, itr)`, `base/strings/util.jl:1265-1271`, over
`k` remaining entries of `dest`; `next` is the pending `iterate` result. The
`::NTuple{2,Any}` assertions fail (`TypeError`, here `.assertion`) only when
`itr` yields fewer than `2 * length(dest)` elements, which the length checks
before the loop exclude. -/
def hexLoop {α σ : Type} (it : σ → SJl (Option (α × σ))) (conv : α → SJl UInt8) :
    Nat → Option (α × σ) → SJl (List UInt8)
  | 0, _ => .ok []
  | k + 1, next =>
    match next with
    | none => .error .assertion
    | some (x, st) =>
      match it st with
      | .error e => .error e
      | .ok none => .error .assertion
      | .ok (some (y, st)) =>
        match it st with
        | .error e => .error e
        | .ok next =>
          match conv x with
          | .error e => .error e
          | .ok hx =>
            match conv y with
            | .error e => .error e
            | .ok hy => (hexLoop it conv k next).map (fun rest => ((hx <<< 4) + hy) :: rest)

/-- `hex2bytes!(dest, itr)`, `base/strings/util.jl:1260-1274`, with `length(dest) =
destLen` and `length(itr) = len`; `start` is `iterate(itr)`, `it` is
`iterate(itr, state)` and `conv` is `number_from_hex`. The result is the
contents of `dest`; when `len = 0` the checks force `destLen = 0`. -/
def hex2bytesBang {α σ : Type} (destLen len : JInt64) (start : SJl (Option (α × σ)))
    (it : σ → SJl (Option (α × σ))) (conv : α → SJl UInt8) : SJl (List UInt8) :=
  if len.val % 2 ≠ 0 then .error (argErr "length of iterable must be even")
  else if (ix 2 * destLen).val ≠ len.val then
    .error (argErr "length of output array must be half of the length of input iterable")
  else if len.val = 0 then .ok []
  else
    match start with
    | .error e => .error e
    | .ok next => hexLoop it conv destLen.val.toNat next

/-- `x >> 1` for `x::Int`: arithmetic shift, i.e. floor division by 2. -/
def shr1 (x : JInt64) : JInt64 := JInt.wrap .i64 (x.val / 2)

/-- `iterate` over `codeunits(s)` (a byte vector); the state is the list of
remaining bytes. -/
def cuIt (st : List UInt8) : Option (UInt8 × List UInt8) :=
  match st with
  | [] => none
  | x :: rest => some (x, rest)

/-- `hex2bytes(s::String)`: `hex2bytes(s) = hex2bytes!(Vector{UInt8}(undef,
length(s) >> 1), s)` (`base/strings/util.jl:1237`), then the String method
(`:1240-1244`): `sizeof(s) != length(s)` throws, else
`hex2bytes!(dest, transcode(UInt8, s))` with `transcode(UInt8, s) = codeunits(s)`
(`base/strings/cstring.jl:178,163`). -/
def hex2bytes (s : JStr) : SJl (List UInt8) :=
  if (ncodeunits s).val ≠ (length s).val then
    .error (argErr "input string must consist of hexadecimal characters only")
  else
    hex2bytesBang (shr1 (length s)) (ncodeunits s) (.ok (cuIt s.bytes)) (fun st => .ok (cuIt st))
      numberFromHexByte

/-- `hex2bytes(ss::SubString{String})`: `:1237` with `length(ss)`
(`base/strings/substring.jl:144`), then the generic `hex2bytes!` (`:1260-1274`)
iterating the characters (`base/strings/substring.jl:151-158`) and converting
each with `number_from_hex(::Char)`. -/
def hex2bytesSub (ss : JSub) : SJl (List UInt8) :=
  match subLength ss with
  | .error e => .error e
  | .ok len => hex2bytesBang (shr1 len) len (subIterate ss (ix 1)) (subIterate ss) numberFromHexChar

end JuliaLean.StringUtil


/-!
# `split` and `rsplit`, `base/strings/util.jl:772-1009`

Master `bbfa0ce4150`. The iterators `SplitIterator` and `RSplitIterator` are
modelled over an arbitrary splitter, given as the function
`k ↦ findnext(splitter, str, k)` (resp. `findprev`) that the iterators call. A
`findnext` result `j::Int` (a character predicate) is the range `j:j`.

`while` loops carry an explicit iteration bound (`fuel`); each docstring states
why the bound is never reached for a splitter whose `findnext` returns ranges
starting at or after `k` (resp. ending at or before the search position).
-/

namespace JuliaLean.StringUtil

open JuliaLean.Strings JuliaLean.Registry

/-- `k ↦ findnext(splitter, str, k)` or `findprev`: `nothing` or a range `first:last`. -/
abbrev Finder := JInt64 → SJl (Option (JInt64 × JInt64))

/-- `findnext(isequal(c), s, k)` for a `Char` `c`, as a range `j:j`. -/
def charFinder (c : UInt32) (s : JStr) : Finder :=
  fun k => (findnextChar c s k).map (Option.map fun j => (j, j))

/-- `findnext(t, s, k)` for a String delimiter `t`. -/
def strFinder (t s : JStr) : Finder :=
  fun k => (findnextStr t s k).map (Option.map fun p => (ix p.1, ix p.2))

/-- `findprev(t, s, k)` for a String delimiter `t`. -/
def strFinderPrev (t s : JStr) : Finder :=
  fun k => (findprevStr t s k).map (Option.map fun p => (ix p.1, ix p.2))

abbrev SplitState := JInt64 × JInt64 × JInt64
abbrev SplitStep := SJl (Option (JSub × SplitState))

/-- `lastindex(s::String) = thisind(s, ncodeunits(s))`, `base/strings/string.jl:249`;
the same function as `Strings.lastindex`, written without a `match` so that
proofs can unfold it on a symbolic string (unfolding `Strings.lastindex` makes
Lean evaluate `thisind` on the symbolic length). -/
def lastIdx (s : JStr) : JInt64 := (thisind s (ncodeunits s)).toOption.getD (ix 0)

/-- After the `while` loop of `iterate(::SplitIterator, (i, k, n))`,
`base/strings/util.jl:805-806`. -/
def splitTail (s : JStr) (keepempty : Bool) (i k n : JInt64) : SplitStep :=
  if !keepempty && !decide (i.val ≤ (ncodeunits s).val) then .ok none
  else (substring s i (lastIdx s) false).map fun sub => some (sub, (ncodeunits s + ix 2, k, n + ix 1))

/-- The `while` loop of `iterate(::SplitIterator, (i, k, n))`,
`base/strings/util.jl:794-804`; `r` is the pending `findnext` result. Every pass
that does not return sets `k` to `k_ > first(r) ≥ k`, so for a splitter whose
ranges start at or after `k` the loop exits after at most `ncodeunits(s) + 1`
passes (once `first(r) > ncodeunits(s)`); the bound `ncodeunits(s) + 2` is never
reached. -/
def splitLoop (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) :
    Nat → JInt64 → JInt64 → JInt64 → Option (JInt64 × JInt64) → SplitStep
  | 0, i, k, n, _ => splitTail s keepempty i k n
  | _ + 1, i, k, n, none => splitTail s keepempty i k n
  | fuel + 1, i, k, n, some (a, b) =>
    if !(decide (n.val ≠ (limit - ix 1).val) && decide (a.val ≤ (ncodeunits s).val)) then
      splitTail s keepempty i k n
    else
      match nextind s b with
      | .error e => .error e
      | .ok k1 =>
        match (if k1.val ≤ a.val then nextind s a else .ok k1) with
        | .error e => .error e
        | .ok k_ =>
          if i.val < k1.val then
            match prevind s a with
            | .error e => .error e
            | .ok pj =>
              match substring s i pj false with
              | .error e => .error e
              | .ok sub =>
                if keepempty || decide (i.val < a.val) then .ok (some (sub, (k1, k_, n + ix 1)))
                else
                  match fnext k_ with
                  | .error e => .error e
                  | .ok r => splitLoop s fnext limit keepempty fuel k1 k_ n r
          else
            match fnext k_ with
            | .error e => .error e
            | .ok r => splitLoop s fnext limit keepempty fuel i k_ n r

/-- `iterate(iter::SplitIterator, (i, k, n))`, `base/strings/util.jl:791-807`. -/
def splitIterate (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool)
    (i k n : JInt64) : SplitStep :=
  if (i - ix 1).val > (ncodeunits s).val then .ok none
  else
    match fnext k with
    | .error e => .error e
    | .ok r => splitLoop s fnext limit keepempty (s.bytes.length + 2) i k n r

/-- `collect` of a `SplitIterator`. Every yielded piece either consumes at least
one code unit of a delimiter occurrence or ends the iteration, so
`ncodeunits(s) + 2` calls suffice for such splitters. -/
def splitAll (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) :
    Nat → SplitState → SJl (List JSub)
  | 0, _ => .ok []
  | fuel + 1, st =>
    match splitIterate s fnext limit keepempty st.1 st.2.1 st.2.2 with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (sub, st')) => (splitAll s fnext limit keepempty fuel st').map (sub :: ·)

/-- `split(str, splitter; limit, keepempty) = collect(eachsplit(str, splitter; limit,
keepempty))` (`base/strings/util.jl:958-961`) for `limit::Int`; the iterator starts
at `(firstindex(str), firstindex(str), 0)` (`:791`). -/
def splitGen (s : JStr) (fnext : Finder) (limit : JInt64) (keepempty : Bool) : SJl (List JSub) :=
  splitAll s fnext limit keepempty (s.bytes.length + 2) (ix 1, ix 1, ix 0)

/-- `eachsplit(str, splitter; limit::Integer, keepempty)` collected
(`base/strings/util.jl:820-821,958-961`) for a `limit` of integer type `t`: the call
`SplitIterator(str, splitter, limit, keepempty)` reaches the default constructor,
whose `limit` field is `Int` (`:776-781`); default constructors do not convert, so
any other integer type is a `MethodError`. -/
def eachsplitTyped (s : JStr) (fnext : Finder) (t : IntTy) (limit : JInt t) (keepempty : Bool) :
    SJl (List JSub) :=
  match t, limit with
  | .i64, l => splitGen s fnext l keepempty
  | _, _ => .error (.jl (.methodError "SplitIterator"))

/-- The `while !iszero(remaining_splits)` loop of `iterate(::RSplitIterator, (to,
remaining_splits))`, `base/strings/util.jl:902-924`, entered with
`remaining_splits ≠ 0` (which the loop never changes). Returns `(from, next_to,
to)`. Only `continue` (`from > to && !keepempty`) loops, setting `to =
prevind(str, first(pos)) < to` for a splitter whose ranges end at or before
`to`; the bound `to + 1` is never reached for such splitters. -/
def rsplitLoop (s : JStr) (fprev : Finder) (keepempty : Bool) :
    Nat → JInt64 → SJl (JInt64 × JInt64 × JInt64)
  | fuel, to =>
    match fprev to with
    | .error e => .error e
    | .ok none => .ok (ix 1, ix (-1), to)
    | .ok (some (a, b)) =>
      match nextind s b with
      | .error e => .error e
      | .ok frm =>
        match (if decide (b.val < a.val) && decide (to.val < 2) then .ok (ix (-1)) else prevind s a) with
        | .error e => .error e
        | .ok nextTo =>
          if decide (frm.val > to.val) && !keepempty then
            match fuel with
            | 0 => .ok (frm, nextTo, to)
            | fuel + 1 => rsplitLoop s fprev keepempty fuel nextTo
          else .ok (frm, nextTo, to)

/-- `from`, `next_to` and `to` after the loop of `base/strings/util.jl:900-924`. -/
def rsplitRes (s : JStr) (fprev : Finder) (keepempty : Bool) (to rem : JInt64) :
    SJl (JInt64 × JInt64 × JInt64) :=
  if rem.val = 0 then .ok (ix 1, ix (-1), to)
  else rsplitLoop s fprev keepempty (to.val.toNat + 1) to

/-- `iterate(it::RSplitIterator, (to, remaining_splits))`, `base/strings/util.jl:898-927`.
The final `SubString(it.str, from, to)` is checked (no `@inbounds`). -/
def rsplitIterate (s : JStr) (fprev : Finder) (keepempty : Bool) (to rem : JInt64) :
    SJl (Option (JSub × (JInt64 × JInt64))) :=
  if to.val < 0 then .ok none
  else
    match rsplitRes s fprev keepempty to rem with
    | .error e => .error e
    | .ok (frm, nextTo, to') =>
      if decide (frm.val > to'.val) && !keepempty then .ok none
      else (substring s frm to').map fun sub => some (sub, (nextTo, rem - ix 1))

/-- `collect` of an `RSplitIterator`; each piece decreases `to` for splitters as
in `rsplitLoop`, so `ncodeunits(s) + 2` calls suffice. -/
def rsplitAll (s : JStr) (fprev : Finder) (keepempty : Bool) :
    Nat → JInt64 × JInt64 → SJl (List JSub)
  | 0, _ => .ok []
  | fuel + 1, st =>
    match rsplitIterate s fprev keepempty st.1 st.2 with
    | .error e => .error e
    | .ok none => .ok []
    | .ok (some (sub, st')) => (rsplitAll s fprev keepempty fuel st').map (sub :: ·)

/-- `rsplit(str, splitter; limit, keepempty) = reverse!(collect(eachrsplit(...)))`,
`base/strings/util.jl:1001-1004`, from the state `(lastindex(str), limit - 1)` (`:898`). -/
def rsplitGen (s : JStr) (fprev : Finder) (limit : JInt64) (keepempty : Bool) : SJl (List JSub) :=
  (rsplitAll s fprev keepempty (s.bytes.length + 2) (lastIdx s, limit - ix 1)).map List.reverse

/-! ## Splitter contracts and joins -/

/-- `join(pieces, d)` as bytes. -/
def joinBytes (d : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [p] => p
  | p :: q :: ps => p ++ d ++ joinBytes d (q :: ps)

end JuliaLean.StringUtil


/-!
# `lstrip`, `rstrip`, `strip` and `chomp` on `String`

`base/strings/util.jl:371-489` (master `bbfa0ce4150`) for `s::String` and a character
predicate `f`, with the String model of `JuliaLean/Strings` (a `Char` is its 32-bit bit
pattern; strings are arbitrary byte sequences, valid UTF-8 or not).

`pairs(s::AbstractString)` is `Iterators.IterableStatePairs(s)` (`base/iterators.jl:1725`):
its key is the `iterate` state. So `lstrip` walks the string with `iterate` alone, starting at
`first(keys(s)) = 1` (`base/iterators.jl:1708-1712`, `base/strings/basic.jl:583`), and
`rstrip` walks `Iterators.reverse(s)` with `getindex` and `prevind`
(`base/strings/basic.jl:775`) from `last(keys(s)) = lastindex(s)` (`base/strings/basic.jl:584`,
`base/iterators.jl:1717-1721`); `Strings.rstrip` models the latter.

The loops below take the iteration function as a parameter: whnf of `iterate s i` on a
symbolic string does not terminate in practice (see `JuliaLean/Transcode/Bridge.lean`), so a
loop that matches on `iterate s i` directly has no usable equation lemmas.
-/

namespace JuliaLean.StringUtil.Strip

open JuliaLean JuliaLean.Strings

/-! ## Models -/

/-- The loop of `lstrip(f, s)`, `base/strings/util.jl:416-422`, for `s::String`:
`for (i::Int, c::AbstractChar) in pairs(s); !f(c) && return @inbounds SubString(s, i, e); end;
SubString(s, e+1, e)`, with `next = iterate(s, ·)`. The first argument bounds the remaining
iterations: every step increases the state and `iterate` returns `nothing` once it exceeds
`ncodeunits(s)`. -/
def lstripStrLoop (f : UInt32 → Bool) (s : JStr) (next : JInt64 → Option (UInt32 × JInt64))
    (e : JInt64) : Nat → JInt64 → SJl JSub
  | 0, _ => substring s (e + ix 1) e
  | k + 1, i =>
    match next i with
    | none => substring s (e + ix 1) e
    | some (c, i') => if !f c then substring s i e false else lstripStrLoop f s next e k i'

/-- `lstrip(f, s::String)`, `base/strings/util.jl:416-422`, with `e = lastindex(s)`. -/
def lstripStr (f : UInt32 → Bool) (s : JStr) : SJl JSub :=
  lstripStrLoop f s (iterate s) (lastindex s) (s.bytes.length + 1) (ix 1)

/-- `SubString(s::SubString, i::Int, j::Int)`, `base/strings/substring.jl:112-115`:
`@boundscheck i ≤ j && checkbounds(s, i:j)`, then `SubString(s.string, s.offset+i,
s.offset+j)`. `checked = false` models a call under `@inbounds`, which (through
`@propagate_inbounds`) also skips the bounds checks of the inner constructor. -/
def subSubstring (ss : JSub) (i j : JInt64) (checked : Bool := true) : SJl JSub :=
  if checked && decide (i.val ≤ j.val) && !(decide (1 ≤ i.val) && decide (j.val ≤ ss.ncu.val)) then
    .error boundsErr
  else substring ss.str (ss.offset + i) (ss.offset + j) checked

/-- The loop of `lstrip(f, s)`, `base/strings/util.jl:416-422`, for `s::SubString{String}`,
with `next = iterate(s, ·)` (`base/strings/substring.jl:151-158`). Bound as for
`lstripStrLoop`: each successful step increases the state. -/
def lstripSubLoop (f : UInt32 → Bool) (ss : JSub) (next : JInt64 → SJl (Option (UInt32 × JInt64)))
    (e : JInt64) : Nat → JInt64 → SJl JSub
  | 0, _ => subSubstring ss (e + ix 1) e
  | k + 1, i =>
    match next i with
    | .error err => .error err
    | .ok none => subSubstring ss (e + ix 1) e
    | .ok (some (c, i')) => if !f c then subSubstring ss i e false else lstripSubLoop f ss next e k i'

/-- `lstrip(f, s::SubString{String})`, `base/strings/util.jl:416-422`. `lastindex(s) =
thisind(s, ncodeunits(s))` is `_thisind_str` on the SubString (`base/strings/substring.jl:174,178`),
which reads the SubString's own code units `codeunit(s.string, s.offset + i)`
(`base/strings/substring.jl:146-149`): `JSub.view` for every SubString the constructors build
(`offset + ncodeunits ≤ ncodeunits(string)`). -/
def lstripSub (f : UInt32 → Bool) (ss : JSub) : SJl JSub :=
  lstripSubLoop f ss (subIterate ss) (lastindex ss.view) (ss.ncu.val.toNat + 1) (ix 1)

/-- `strip(f, s) = lstrip(f, rstrip(f, s))`, `base/strings/util.jl:489`, for `s::String`:
`rstrip` returns a `SubString{String}`, which `lstrip` then walks. -/
def strip (f : UInt32 → Bool) (s : JStr) : SJl JSub := do
  let r ← Strings.rstrip f s
  lstripSub f r

section
attribute [local irreducible] iterate
end

end JuliaLean.StringUtil.Strip

namespace JuliaLean.StringUtil

open JuliaLean.Registry

end JuliaLean.StringUtil


/-!
# `lpad` and `rpad` on `String`

`base/strings/util.jl:511-584` (master `bbfa0ce4150`) for `s::String`, `n::Int` and a pad
`p::String`, with `textwidth` from `JuliaLean/StringUtil/Width.lean` (the utf8proc width table
is the parameter `cw`).
-/

namespace JuliaLean.StringUtil.Pad

open JuliaLean JuliaLean.Strings JuliaLean.StringUtil.Strip

/-! ## Models -/

/-- The loop of `_pad_remainder(p::AbstractString, r::Int)`, `base/strings/util.jl:516-523`:
`width = 0; for (i, c) in pairs(p); width += Int(textwidth(c))::Int; width >= r && return
@view p[begin:i]; end; return SubString(p)`, with `next = iterate(p, ·)` (the key of
`pairs(p)` is the iteration state, `base/iterators.jl:1725`). `@view p[begin:i]` is the
checked `SubString(p, 1, i)` (`base/strings/substring.jl:122`). The first argument bounds the
remaining iterations as in `Strip.lstripStrLoop`. -/
def padRemLoop (cw : UInt32 → Int) (p : JStr) (next : JInt64 → Option (UInt32 × JInt64))
    (r : JInt64) : Nat → JInt64 → JInt64 → SJl JSub
  | 0, _, _ => .ok (wholeSub p)
  | k + 1, i, width =>
    match next i with
    | none => .ok (wholeSub p)
    | some (c, i') =>
      let width := width + ix (textwidthChar cw c)
      if width.val ≥ r.val then substring p (ix 1) i else padRemLoop cw p next r k i' width

/-- `_pad_remainder(p::AbstractString, r::Int)`, `base/strings/util.jl:516-523`. -/
def padRemainder (cw : UInt32 → Int) (p : JStr) (r : JInt64) : SJl JSub :=
  padRemLoop cw p (iterate p) r (p.bytes.length + 1) (ix 1) (ix 0)

/-- `string(a...)` for `String`/`SubString{String}` pieces, `base/strings/substring.jl:254-283`:
`_string_n(n)` for the summed code units, then each piece's bytes in order. -/
def stringConcat (pieces : List (List UInt8)) : SJl JStr :=
  stringN (pieces.map List.length).sum fun _ => pieces.flatten

/-- `lpad(s::String, n::Int, p::String)`, `base/strings/util.jl:526-544`:
`m = signed(n) - Int(textwidth(s))` (wrapping), `m ≤ 0 && return string(s)`,
`l = textwidth(p)`, `ArgumentError` if `l == 0`, `q, r = divrem(m, l)` (`div`, `rem`,
`base/div.jl:273-279`), then `string(p^q, s)` or `string(p^q, _pad_remainder(p, r), s)`.
`p^q` is `repeat(p, q)` (`base/strings/basic.jl:771`). -/
def lpadStr (cw : UInt32 → Int) (s : JStr) (n : JInt64) (p : JStr) : SJl JStr :=
  let m := n - ix (textwidth cw s)
  if m.val ≤ 0 then .ok s
  else
    let l := ix (textwidth cw p)
    if l.val = 0 then .error (.jl (.argumentError "pad has zero textwidth"))
    else
      match JInt.div m l, JInt.remInt m l with
      | .ok q, .ok r =>
        match repeatStr p q with
        | .error e => .error e
        | .ok pq =>
          if r.val = 0 then stringConcat [pq.bytes, s.bytes]
          else
            match padRemainder cw p r with
            | .error e => .error e
            | .ok rem => stringConcat [pq.bytes, rem.view.bytes, s.bytes]
      | _, _ => .error (.jl .divideError)

/-- `rpad(s::String, n::Int, p::String)`, `base/strings/util.jl:566-584`: as `lpadStr`, with
`string(s, p^q)` or `string(s, p^q, _pad_remainder(p, r))`. -/
def rpadStr (cw : UInt32 → Int) (s : JStr) (n : JInt64) (p : JStr) : SJl JStr :=
  let m := n - ix (textwidth cw s)
  if m.val ≤ 0 then .ok s
  else
    let l := ix (textwidth cw p)
    if l.val = 0 then .error (.jl (.argumentError "pad has zero textwidth"))
    else
      match JInt.div m l, JInt.remInt m l with
      | .ok q, .ok r =>
        match repeatStr p q with
        | .error e => .error e
        | .ok pq =>
          if r.val = 0 then stringConcat [s.bytes, pq.bytes]
          else
            match padRemainder cw p r with
            | .error e => .error e
            | .ok rem => stringConcat [s.bytes, pq.bytes, rem.view.bytes]
      | _, _ => .error (.jl .divideError)

end JuliaLean.StringUtil.Pad

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

open JuliaLean.Registry

end JuliaLean.StringUtil


/-!
# `rtruncate`, `ltruncate`, `ctruncate`, `base/strings/util.jl:586-735`

Master `bbfa0ce4150`, for `str::String`, a `String` replacement (a `Char`
replacement `c` behaves as `string(c)`) and `maxwidth::Int`. Column widths use
`textwidth` from `Width.lean`, parametrised by the utf8proc width `cw`.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings JuliaLean.Registry

inductive TMode where
  | left | right | center
  deriving DecidableEq, Repr

/-- `textwidth(str[i])` (`@inbounds getindex`, `base/strings/string.jl:540-545`). -/
def twAt (cw : UInt32 → Int) (s : JStr) (i : JInt64) : SJl JInt64 :=
  (getindex s i).map fun c => ix (textwidthChar cw c)

/-- The `while true` loop of `string_truncate_boundaries`,
`base/strings/util.jl:710-733`. Each pass moves `left` or `right` by one
character or breaks, except a pass that only sets `force_other`, which is
followed by a moving pass; and the loop breaks before consuming every
character because `textwidth(str) > maxwidth`. So `2 * ncodeunits(str) + 4`
passes are never exhausted. -/
def truncLoop (cw : UInt32 → Int) (s : JStr) (maxw : JInt64) (mode : TMode) (preferLeft : Bool) :
    Nat → JInt64 → JInt64 → JInt64 → JInt64 → JInt64 → Bool → SJl (JInt64 × JInt64)
  | 0, left, right, _, _, _, _ => .ok (left, right)
  | fuel + 1, left, right, width, rmL, rmR, force =>
    let blk1 : SJl (Option (JInt64 × JInt64 × JInt64 × Bool)) :=
      if decide (mode = .left) || (decide (mode = .center) && (!preferLeft || decide (left.val > 1))) then
        match twAt cw s right with
        | .error e => .error e
        | .ok rm =>
          if decide (mode = .left) || (decide (rmR.val ≤ rmL.val) || force) then
            if !decide ((width + rm).val ≤ maxw.val) then .ok none
            else (prevind s right).map fun r => some (r, width + rm, rmR + rm, false)
          else .ok (some (right, width, rmR, true))
      else .ok (some (right, width, rmR, force))
    match blk1 with
    | .error e => .error e
    | .ok none => .ok (left, right)
    | .ok (some (right, width, rmR, force)) =>
      if decide (mode = .right) || decide (mode = .center) then
        match twAt cw s left with
        | .error e => .error e
        | .ok rm =>
          if decide (mode = .left) || (decide (rmL.val ≤ rmR.val) || force) then
            match twAt cw s left with
            | .error e => .error e
            | .ok rm2 =>
              if !decide ((width + rm2).val ≤ maxw.val) then .ok (left, right)
              else
                match nextind s left with
                | .error e => .error e
                | .ok l => truncLoop cw s maxw mode preferLeft fuel l right (width + rm2) (rmL + rm) rmR false
          else truncLoop cw s maxw mode preferLeft fuel left right width rmL rmR true
      else truncLoop cw s maxw mode preferLeft fuel left right width rmL rmR force

/-- The loop of `check_textwidth(str, maxwidth)`, `base/strings/util.jl:687-695`. -/
def checkLoop (cw : UInt32 → Int) (maxw : JInt64) : List UInt32 → JInt64 → Bool
  | [], _ => true
  | c :: cs, tot =>
    if (tot + ix (textwidthChar cw c)).val > maxw.val then false
    else checkLoop cw maxw cs (tot + ix (textwidthChar cw c))

/-- `check_textwidth(str, maxwidth)`: `for c in str` iterates `chars str`. -/
def checkTextwidth (cw : UInt32 → Int) (s : JStr) (maxw : JInt64) : Bool :=
  checkLoop cw maxw (chars s) (ix 0)

/-- `string_truncate_boundaries(str, maxwidth, replacement, Val(mode), prefer_left)`,
`base/strings/util.jl:697-735`. -/
def truncBoundaries (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) (mode : TMode)
    (preferLeft : Bool) : SJl (Option (JInt64 × JInt64)) :=
  if maxw.val < 0 then .error (.jl (.argumentError s!"maxwidth {maxw.val} should be non-negative"))
  else if checkTextwidth cw s maxw then .ok none
  else
    match truncLoop cw s maxw mode preferLeft (2 * s.bytes.length + 4) (ix 1) (lastIdx s)
        (ix (textwidth cw r)) (ix 0) (ix 0) false with
    | .error e => .error e
    | .ok (left, right) =>
      match prevind s left with
      | .error e => .error e
      | .ok pl => (nextind s right).map fun nr => some (pl, nr)

/-- `a * b * ...` on Strings and SubStrings: `string(...)` stores the code units
of each argument in a fresh String (`base/strings/substring.jl:256-283`). -/
def concatStr (parts : List (List UInt8)) : SJl JStr :=
  stringN (parts.map List.length).sum fun _ => parts.flatten

/-- `rtruncate(str, maxwidth, replacement)`, `base/strings/util.jl:609-617`:
`str[begin:left] * replacement` under `@views`, i.e. the checked
`SubString(str, 1, left)`. -/
def rtruncate (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) : SJl JStr :=
  match truncBoundaries cw s r maxw .right true with
  | .error e => .error e
  | .ok none => .ok s
  | .ok (some (left, _)) =>
    match substring s (ix 1) left with
    | .error e => .error e
    | .ok sub => concatStr [sub.view.bytes, r.bytes]

/-- `ltruncate(str, maxwidth, replacement)`, `base/strings/util.jl:642-650`. -/
def ltruncate (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) : SJl JStr :=
  match truncBoundaries cw s r maxw .left true with
  | .error e => .error e
  | .ok none => .ok s
  | .ok (some (_, right)) =>
    match substring s right (lastIdx s) with
    | .error e => .error e
    | .ok sub => concatStr [r.bytes, sub.view.bytes]

/-- `ctruncate(str, maxwidth, replacement; prefer_left)`, `base/strings/util.jl:676-684`. -/
def ctruncate (cw : UInt32 → Int) (s r : JStr) (maxw : JInt64) (preferLeft : Bool := true) : SJl JStr :=
  match truncBoundaries cw s r maxw .center preferLeft with
  | .error e => .error e
  | .ok none => .ok s
  | .ok (some (left, right)) =>
    match substring s (ix 1) left with
    | .error e => .error e
    | .ok subL =>
      match substring s right (lastIdx s) with
      | .error e => .error e
      | .ok subR => concatStr [subL.view.bytes, r.bytes, subR.view.bytes]

end JuliaLean.StringUtil


/-!
# `replace(s, pat => repl, ...)` with fixed replacement strings

Model of `_replace_init`, `_replace_once`, `_replace_finish` and `_replace_`
(String result), `base/strings/util.jl:1035-1131` (master `bbfa0ce4150`), for
`N` pairs `pat => repl` where `repl` is a String or Char (`_replace(io, repl, ...)
= write(io, repl)`, `:1011-1012`) and each pattern is given by its finder
`k ↦ findnext(p, str, k)`. Regex patterns, function replacements and
`AnnotatedString` are out of scope.

* The output `IOBuffer` is the list of bytes written to it: `_replace_` creates
  it empty, only appends (`write`, `unsafe_write`), and `takestring!` returns
  those bytes.
* `_free_pat_replacer` is `nothing` for non-Regex patterns (`:1029`) and is
  omitted.
* `nrep` is instrumentation: the number of `_replace` calls so far. Julia has
  no such variable; it is recorded so the number of replacements can be stated.
-/

namespace JuliaLean.StringUtil

open JuliaLean JuliaLean.Strings

/-- What `findnext(p, str, k)` returns: `nothing`, an `Int` (Char and
character-collection patterns) or a range `first:last` (String patterns). -/
inductive Found where
  | nothing
  | idx (i : JInt64)
  | range (a b : JInt64)
  deriving Repr

/-- A `UnitRange{Int}` `first:last`. -/
abbrev Rng := JInt64 × JInt64

/-- A pair `pat => repl`: the finder `k ↦ findnext(_pat_replacer(pat), str, k)`
for the fixed `str`, and the bytes `write(io, repl)` writes. -/
structure Pair where
  find : JInt64 → SJl Found
  repl : List UInt8

instance : Inhabited Pair := ⟨⟨fun _ => .ok .nothing, []⟩⟩

/-- The body of the `map` closures at `base/strings/util.jl:1042-1047` and
`:1094-1098` after `r = findnext(p, str, k)`:
`r === nothing || first(r) == 0` gives `e1+1:0`, and an `Int` `r` becomes `r:r`. -/
def toRange (e1 : JInt64) : Found → Rng
  | .nothing => (e1 + ix 1, ix 0)
  | .idx i => if i.val = 0 then (e1 + ix 1, ix 0) else (i, i)
  | .range a b => if a.val = 0 then (e1 + ix 1, ix 0) else (a, b)

/-- `findnext(p, str, k)` followed by `toRange`. -/
def findRange (p : Pair) (e1 k : JInt64) : SJl Rng :=
  match p.find k with
  | .error e => .error e
  | .ok f => .ok (toRange e1 f)

/-- `rs = map(patterns) do p ... findnext(p, str, a) ... end`,
`base/strings/util.jl:1041-1048`. -/
def findAll (e1 a : JInt64) : List Pair → SJl (List Rng)
  | [] => .ok []
  | p :: ps =>
    match findRange p e1 a with
    | .error e => .error e
    | .ok r =>
      match findAll e1 a ps with
      | .error e => .error e
      | .ok rs => .ok (r :: rs)

/-- `_replace_init(str, pat_repl, count)`, `base/strings/util.jl:1035-1050`,
returning `(e1, rs, notfound)`; `firstindex(str) = 1`. -/
def replaceInit (s : JStr) (ps : List Pair) (count : JInt64) : SJl (JInt64 × List Rng × Bool) :=
  if count.val < 0 then .error (.jl (.domainError "`count` must be non-negative."))
  else
    match nextind s (lastindex s) with
    | .error e => .error e
    | .ok e1 =>
      match findAll e1 (firstindex s) ps with
      | .error e => .error e
      | .ok rs => .ok (e1, rs, rs.all fun r => decide (r.1.val > e1.val))

/-- The fold of `argmin(itr) = findmin(itr)[2]` (`base/reduce.jl:1060,946-947,917-919`):
`_rf_findmin((fm, im), (fx, ix)) = isgreater(fm, fx) ? (fx, ix) : (fm, im)`, and for
`Int`s `isgreater(fm, fx)` is `fx < fm`, so the first minimal
element wins. Indices are zero-based here. -/
def argminAux : List JInt64 → Nat → Nat → JInt64 → Nat
  | [], _, im, _ => im
  | x :: xs, k, im, fm =>
    if x.val < fm.val then argminAux xs (k + 1) k x else argminAux xs (k + 1) im fm

/-- `argmin(map(first, rs))`, `base/strings/util.jl:1071`. Never called on an
empty tuple: `_replace_` returns before `_replace_finish` when `N = 0`. -/
def argmin : List JInt64 → Nat
  | [] => 0
  | x :: xs => argminAux xs 1 0 x

/-- `GC.@preserve str unsafe_write(io, pointer(str, i), UInt(nb))`,
`base/strings/util.jl:1077`: `UInt(nb)` throws `InexactError` for `nb < 0`; then
`nb` bytes of `str` from index `i`. (Julia reads raw memory; every call made
under the finder contract stays inside `str`.) -/
def copyOut (s : JStr) (i nb : JInt64) : SJl (List UInt8) :=
  if nb.val < 0 then .error (.jl (.inexactError "UInt64"))
  else .ok ((s.bytes.drop (i.val - 1).toNat).take nb.val.toNat)

/-- `rs = map(patterns, rs) do p, r; if first(r) < k; r = findnext(p, str, k); ...`,
`base/strings/util.jl:1091-1102`. -/
def refresh (e1 k : JInt64) : List Pair → List Rng → SJl (List Rng)
  | p :: ps, r :: rs =>
    let r' : SJl Rng := if r.1.val < k.val then findRange p e1 k else .ok r
    match r' with
    | .error e => .error e
    | .ok r' =>
      match refresh e1 k ps rs with
      | .error e => .error e
      | .ok rs' => .ok (r' :: rs')
  | _, _ => .ok []

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1068-1104`, returning `(rs, r, i)` (the caller discards
`x` and `nb`) together with the output bytes `io` and the instrumentation `nrep`. -/
def replaceOnce (s : JStr) (ps : List Pair) (start e1 : JInt64) (rs : List Rng)
    (count n i : JInt64) (io : List UInt8) (nrep : Nat) :
    SJl (List Rng × Rng × JInt64 × List UInt8 × Nat) :=
  let x := argmin (rs.map (·.1))
  let r := rs.getD x (ix 0, ix 0)
  let j := r.1
  let k := r.2
  if j.val > e1.val then .ok (rs, r, i, io, nrep)
  else
    let w : SJl (List UInt8 × Nat) :=
      if i.val = start.val ∨ i.val ≤ k.val then
        match copyOut s i (j - i) with
        | .error e => .error e
        | .ok b => .ok (io ++ b ++ (ps.getD x default).repl, nrep + 1)
      else .ok (io, nrep)
    match w with
    | .error e => .error e
    | .ok (io, nrep) =>
      if k.val < j.val then
        if j.val = e1.val then .ok (rs, r, j, io, nrep)
        else
          match nextind s j with
          | .error e => .error e
          | .ok k =>
            if n.val = count.val then .ok (rs, r, j, io, nrep)
            else
              match refresh e1 k ps rs with
              | .error e => .error e
              | .ok rs => .ok (rs, r, j, io, nrep)
      else
        match nextind s k with
        | .error e => .error e
        | .ok k =>
          if n.val = count.val then .ok (rs, r, k, io, nrep)
          else
            match refresh e1 k ps rs with
            | .error e => .error e
            | .ok rs => .ok (rs, r, k, io, nrep)

/-- The loop `while n <= count ... end` of `_replace_finish`,
`base/strings/util.jl:1057-1062`, returning `(i, io, nrep)`. The first argument
bounds the remaining iterations: it starts at `count` with `n = 1`, so it is
`count - n + 1` and reaches `0` exactly when `n <= count` fails. (`n += 1` could
wrap only after `typemax(Int)` iterations, which needs a finder that keeps
returning ranges before `k`.) -/
def finishLoop (s : JStr) (ps : List Pair) (count start e1 : JInt64) :
    Nat → List Rng → JInt64 → JInt64 → List UInt8 → Nat → SJl (JInt64 × List UInt8 × Nat)
  | 0, _, _, i, io, nrep => .ok (i, io, nrep)
  | f + 1, rs, n, i, io, nrep =>
    if !decide (n.val ≤ count.val) then .ok (i, io, nrep)
    else
      match replaceOnce s ps start e1 rs count n i io nrep with
      | .error e => .error e
      | .ok (rs, r, i, io, nrep) =>
        if r.1.val ≥ e1.val then .ok (i, io, nrep)
        else finishLoop s ps count start e1 f rs (n + ix 1) i io nrep

/-- `write(io, SubString(str, i))` at the end of `_replace_finish`,
`base/strings/util.jl:1064`, with `SubString(str, i) = SubString(str, i, li)` and
`li = lastindex(str)`. -/
def writeRest (s : JStr) (i li : JInt64) (io : List UInt8) (nrep : Nat) :
    SJl (List UInt8 × Nat) :=
  match substring s i li with
  | .error e => .error e
  | .ok sub => .ok (io ++ sub.view.bytes, nrep)

/-- `_replace_finish(io, str, count, e1, patterns, replaces, rs)`,
`base/strings/util.jl:1053-1066`: the loop, then `write(io, SubString(str, i))`. -/
def replaceFinish (s : JStr) (ps : List Pair) (count e1 : JInt64) (rs : List Rng) :
    SJl (List UInt8 × Nat) :=
  let start := firstindex s
  match finishLoop s ps count start e1 count.val.toNat rs (ix 1) start [] 0 with
  | .error e => .error e
  | .ok (i, io, nrep) => writeRest s i (lastindex s) io nrep

/-- `_replace_(str, pat_repl, count)`, `base/strings/util.jl:1122-1131`: the code
units of the returned String, with the number of `_replace` calls. -/
def replaceN (s : JStr) (ps : List Pair) (count : JInt64) : SJl (List UInt8 × Nat) :=
  if count.val = 0 then .ok (s.bytes, 0)
  else
    match replaceInit s ps count with
    | .error e => .error e
    | .ok (e1, rs, notfound) =>
      if notfound then .ok (s.bytes, 0)
      else replaceFinish s ps count e1 rs

/-- `replace(s::String, pat_f::Pair...; count)`, `base/strings/util.jl:1186-1187`:
the code units of the result. -/
def replace (s : JStr) (ps : List Pair) (count : JInt64) : SJl (List UInt8) :=
  match replaceN s ps count with
  | .error e => .error e
  | .ok (out, _) => .ok out

/-- `typemax(Int)`, the default `count`. -/
def typemaxInt : JInt64 := ix (2 ^ 63 - 1)

end JuliaLean.StringUtil


/-! Coverage models for `base/strings/util.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Util

open JuliaLean JuliaLean.Strings

def startswith (a b : List UInt32) := b.isPrefixOf a
def startswithChars (chars s : List UInt32) : Bool :=
  match s with | [] => false | c :: _ => chars.contains c
def endswith (a b : List UInt32) := b.reverse.isPrefixOf a.reverse
def endswithChars (chars s : List UInt32) : Bool :=
  match s.getLast? with | none => false | some c => chars.contains c
def startswithDense (a b : List UInt8) := b.isPrefixOf a
def startswithFast (a b : List UInt8) := startswithDense a b
def startswithIO (unread pre : List UInt8) := pre.isPrefixOf unread
def endswithDense (a b : List UInt8) := b.reverse.isPrefixOf a.reverse
def endswithFast (a b : List UInt8) := endswithDense a b
def contains (occursin : α → α → Bool) (haystack needle : α) := occursin needle haystack
def endswithFix (suffix s : List UInt32) := endswith s suffix
def startswithFix (pre s : List UInt32) := startswith s pre
def containsFix (needle haystack : List UInt8) := needle.isSublist haystack

def chopprefix (s pre : List UInt32) : List UInt32 :=
  if pre.isPrefixOf s then s.drop pre.length else s
def chopprefixFast := chopprefix
def chopprefixChar (s : List UInt32) (pre : UInt32) : List UInt32 :=
  match s with | c :: cs => if c == pre then cs else c :: cs | [] => []
def chopsuffix (s suffix : List UInt32) : List UInt32 :=
  if suffix.reverse.isPrefixOf s.reverse then s.take (s.length - suffix.length) else s
def chopsuffixFast := chopsuffix
def chopsuffixChar (s : List UInt32) (suffix : UInt32) : List UInt32 :=
  if s.getLast? == some suffix then s.dropLast else s

def lstripDefault (s : JStr) := Strings.lstrip (fun _ => false) s
def lstripChars (chars : List UInt32) (s : JStr) := Strings.lstrip (chars.contains ·) s
def lstripStringError : SJl JSub := .error (.jl (.argumentError "second argument must be Chars"))
def rstripDefault (s : JStr) := Strings.rstrip (fun _ => false) s
def rstripChars (chars : List UInt32) (s : JStr) := Strings.rstrip (chars.contains ·) s
def rstripStringError : SJl JSub := .error (.jl (.argumentError "second argument must be Chars"))
def stripDefault (s : JStr) := Strings.rstrip (fun _ => false) s >>= Strings.lstrip (fun _ => false) ∘ JSub.view
def stripChars (chars : List UInt32) (s : JStr) :=
  Strings.rstrip (chars.contains ·) s >>= Strings.lstrip (chars.contains ·) ∘ JSub.view
def stripStringError : SJl JSub := .error (.jl (.argumentError "second argument must be Chars"))
def stripPredicate (f : UInt32 → Bool) (s : JStr) := Strings.rstrip f s >>= Strings.lstrip f ∘ JSub.view

def lpadGeneric (toString : α → JStr) (s pad : α) (n : JInt64) (tw : JInt64) :=
  Strings.lpad (toString s) tw n
def padRemainderChar (c : UInt32) (_r : Int) := c
def rpadGeneric (impl : α → JInt64 → α → β) (s pad : α) (n : JInt64) := impl s n pad
def truncateBoundaries := JuliaLean.StringUtil.truncBoundaries

def eachsplitCtor := JuliaLean.StringUtil.splitGen
def splitEltype : String := "SubString"
def splitIteratorSize : String := "SizeUnknown"
def splitIterate := JuliaLean.StringUtil.splitIterate
def partitionEltype : String := "SubString"
def partitionIterate (s : JStr) (n state : JInt64) := Strings.partitionIterate s n state
def eachsplitChars := JuliaLean.StringUtil.splitGen
def eachsplitChar := JuliaLean.StringUtil.splitGen
def eachsplitWhitespace := JuliaLean.StringUtil.splitGen
def eachrsplitCtor := JuliaLean.StringUtil.rsplitGen
def rsplitEltype : String := "SubString"
def rsplitIteratorSize : String := "SizeUnknown"
def eachrsplitChars := JuliaLean.StringUtil.rsplitGen
def eachrsplitChar := JuliaLean.StringUtil.rsplitGen
def eachrsplitWhitespace := JuliaLean.StringUtil.rsplitGen
def rsplitIterate := JuliaLean.StringUtil.rsplitIterate
def splitCollect := JuliaLean.StringUtil.splitGen
def splitWhitespace := JuliaLean.StringUtil.splitGen
def rsplitCollect := JuliaLean.StringUtil.rsplitGen
def rsplitWhitespace := JuliaLean.StringUtil.rsplitGen

def replaceLiteral (replacement : List UInt8) := replacement
def replaceShown (showFn : α → List UInt8) (replacement : α) := showFn replacement
def replaceFunction (f : JSub → List UInt8) (s : JSub) := f s
def replaceCharFunction (f : UInt32 → List UInt8) (c : UInt32) := f c
def patReplacer {α : Type} (x : α) := x
def freePatReplacer (_x : α) : Unit := ()
def patReplacerChar (c : UInt32) (x : UInt32) := x == c
def patReplacerChars (cs : List UInt32) (x : UInt32) := cs.contains x
def replaceIO := JuliaLean.StringUtil.replaceN
def replaceString := JuliaLean.StringUtil.replace

def hex2bytes := JuliaLean.StringUtil.hex2bytes
def hex2bytesBang {α σ : Type} (destLen len : JInt64) (start : SJl (Option (α × σ)))
    (it : σ → SJl (Option (α × σ))) (conv : α → SJl UInt8) :=
  JuliaLean.StringUtil.hex2bytesBang destLen len start it conv
def numberFromHexChar := JuliaLean.StringUtil.numberFromHexChar
def bytes2hex := JuliaLean.StringUtil.bytes2hex
def bytes2hexIO (bytes : List UInt8) := JuliaLean.StringUtil.bytes2hexFill bytes
def ascii (s : JStr) : SJl JStr := if Strings.isascii s then .ok s else .error (.jl (.argumentError "invalid ASCII"))
def throwInvalidAscii : SJl Unit := .error (.jl (.argumentError "invalid ASCII"))
def asciiAbstract (toString : α → JStr) (s : α) := ascii (toString s)
def restFast (s : JStr) (i : JInt64) := Strings.substring s i (Strings.lastindex s)
def restGeneric (collect : α → List UInt32) (s : α) := collect s

end JuliaLean.StringsCovA.Util


namespace JuliaLean.StringsCovA.UtilRebuilt
open JuliaLean JuliaLean.Strings

/- Source-faithful method models for `base/strings/util.jl`.  These are kept
separate from the earlier shared specifications because coverage is per Julia
method: a wrapper records its own call, and a loop retains its own exit order. -/

def pairedPrefix : List UInt32 → List UInt32 → Bool
  | _, [] => true
  | [], _ :: _ => false
  | a :: as, b :: bs => if a == b then pairedPrefix as bs else false

def reversePrefix (source suffix : List UInt32) : Bool :=
  pairedPrefix source.reverse suffix.reverse

def isContinuation (byte : UInt8) : Bool := byte &&& 0xc0 == 0x80

def boundaryAfter (bytes : List UInt8) (count : Nat) : Bool :=
  count == 0 || count == bytes.length ||
    match bytes[count]? with
    | none => false
    | some byte => !isContinuation byte

def denseStarts (source pre : List UInt8) : Bool :=
  let count := pre.length
  if source.length < count then false
  else if source.take count == pre then boundaryAfter source count
  else false

def denseEnds (source suffix : List UInt8) : Bool :=
  let start := source.length - suffix.length
  if source.length < suffix.length then false
  else if (source.drop start).take suffix.length == suffix then
    start == 0 || match source[start]? with
      | none => false
      | some byte => !isContinuation byte
  else false

inductive BinaryFn where | startswith | endswith | contains
  deriving Repr, DecidableEq

structure Fix2 (A : Type) where
  fn : BinaryFn
  stored : A

def startsFix (pre : A) : Fix2 A := ⟨.startswith, pre⟩
def endsFix (suffix : A) : Fix2 A := ⟨.endswith, suffix⟩
def containsFix (needle : A) : Fix2 A := ⟨.contains, needle⟩

def chopPrefixLoop (source pre : List UInt32) : List UInt32 :=
  if pairedPrefix source pre then source.drop pre.length else source

def chopSuffixLoop (source suffix : List UInt32) : List UInt32 :=
  if reversePrefix source suffix then source.take (source.length - suffix.length) else source

def juliaSpace (character : UInt32) : Bool :=
  JuliaLean.ParsePrint.IntParse.isspaceChar character.toNat

def lstripDefault (source : JStr) := Strings.lstrip juliaSpace source
def rstripDefault (source : JStr) := Strings.rstrip juliaSpace source
def stripDefault (source : JStr) :=
  Strings.rstrip juliaSpace source >>= Strings.lstrip juliaSpace ∘ JSub.view

def bothStringsMessage : String :=
  "Both arguments are strings. The second argument should be a `Char` or collection of `Char`s"

def stringArgumentError : SJl JSub := .error (.jl (.argumentError bothStringsMessage))

def lpadWrapper (toString : A → JStr) (implementation : JStr → JInt64 → JStr → R)
    (source padding : A) (width : JInt64) : R :=
  implementation (toString source) width (toString padding)
def rpadWrapper := @lpadWrapper

inductive StringType where | abstract (name : String) | subString (parent : StringType)
  deriving Repr, DecidableEq
inductive IteratorSize where | sizeUnknown
  deriving Repr, DecidableEq

def splitEltype (parent : StringType) : StringType := .subString parent
def splitEltypeSub (parent : StringType) : StringType := .subString parent
def partitionEltype (parent : StringType) : StringType := .subString parent
def partitionEltypeSub (parent : StringType) : StringType := parent
structure SplitIteratorModel (S F : Type) where
  source : S
  splitter : F
  limit : JInt64
  keepempty : Bool

def eachsplitCtor (source : S) (splitter : F) (limit : JInt64) (keepempty : Bool) :
    SplitIteratorModel S F := ⟨source, splitter, limit, keepempty⟩

def eachsplitChars (source : S) (chars : List UInt32) (limit : JInt64) (keepempty : Bool) :=
  eachsplitCtor source (fun c => chars.contains c) limit keepempty
def eachsplitChar (source : S) (splitter : UInt32) (limit : JInt64) (keepempty : Bool) :=
  eachsplitCtor source (fun c => c == splitter) limit keepempty
def eachsplitWhitespace (source : S) (limit : JInt64) (keepempty : Bool) :=
  eachsplitCtor source juliaSpace limit keepempty
def eachrsplitCtor := @eachsplitCtor
def eachrsplitChars := @eachsplitChars
def eachrsplitChar := @eachsplitChar
def eachrsplitWhitespace := @eachsplitWhitespace

structure WriteResult where
  bytes : List UInt8
  count : Nat
  deriving Repr, DecidableEq

def replaceLiteral (initial replacement : List UInt8) : WriteResult :=
  ⟨initial ++ replacement, replacement.length⟩

def replaceShown (showValue reprValue : A → List UInt8) (positionApplicable : Bool)
    (replacement : A) (initial : List UInt8) : WriteResult :=
  let rendered := if positionApplicable then showValue replacement else reprValue replacement
  ⟨initial ++ rendered, rendered.length⟩

def replaceFunction (function : JSub → R) (recursiveReplace : List UInt8 → R → O)
    (source : JSub) (initial : List UInt8) : O := recursiveReplace initial (function source)

def replaceCharFunction (function : UInt32 → R) (recursiveReplace : List UInt8 → R → O)
    (character : UInt32) (initial : List UInt8) : O := recursiveReplace initial (function character)
structure PreparedPredicate where
  apply : UInt32 → Bool

def prepareChar (character : UInt32) : PreparedPredicate := ⟨fun candidate => candidate == character⟩
def prepareChars (chars : List UInt32) : PreparedPredicate := ⟨fun candidate => chars.contains candidate⟩

def replaceIO (initial : List UInt8) (source : JStr) (pairs : List JuliaLean.StringUtil.Pair)
    (count : JInt64) : SJl (WriteResult × Nat) :=
  match JuliaLean.StringUtil.replaceN source pairs count with
  | .error error => .error error
  | .ok (bytes, replacements) => .ok (⟨initial ++ bytes, bytes.length⟩, replacements)

def hex2bytesGeneric (length : S → JInt64) (allocate : JInt64 → D)
    (decode : D → S → R) (source : S) : R :=
  decode (allocate (JuliaLean.StringUtil.shr1 (length source))) source

def numberFromAbstractChar (toChar : A → SJl UInt32) (character : A) : SJl UInt8 :=
  match toChar character with
  | .error error => .error error
  | .ok char => JuliaLean.StringUtil.numberFromHexChar char

def bytes2hexIterator (eltypeUInt8 : Bool) (bytes : List UInt8) : SJl (List UInt8) :=
  if eltypeUInt8 then .ok (JuliaLean.StringUtil.bytes2hexFill bytes)
  else .error (.jl (.argumentError "eltype of iterator not UInt8"))

def bytes2hexIO (initial : List UInt8) (eltypeUInt8 : Bool) (bytes : List UInt8) :
    SJl (List UInt8 × Unit) :=
  match bytes2hexIterator eltypeUInt8 bytes with
  | .error error => .error error
  | .ok encoded => .ok (initial ++ encoded, ())

inductive AsciiResult where
  | ascii
  | invalid (index : Nat) (source : List UInt8)
  deriving Repr, DecidableEq

def asciiLoop (source : List UInt8) : Nat → List UInt8 → AsciiResult
  | _, [] => .ascii
  | index, byte :: rest =>
      if byte < 0x80 then asciiLoop source (index + 1) rest else .invalid index source

def ascii (source : List UInt8) : AsciiResult := asciiLoop source 1 source

def asciiAbstract (toString : A → List UInt8) (source : A) : AsciiResult := ascii (toString source)

structure RestView (S : Type) where
  parent : S
  start : JInt64
def restFast (source : S) (index : JInt64) : RestView S := ⟨source, index⟩

def restGeneric (printChar : UInt32 → List UInt8) (remaining : List UInt32) : List UInt8 :=
  remaining.flatMap printChar

end JuliaLean.StringsCovA.UtilRebuilt

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- `UInt(x)` for an `Int`: `InexactError` when negative. -/
def convU (x : JInt64) : RJl Nat :=
  match JInt.convert (IntTy.u64.name) .u64 x.val with
  | .error e => .error (.str (.jl e))
  | .ok u => .ok u.val.toNat

/-- The per-pattern search of `_replace_init` (`base/strings/util.jl:1041-1048`) and
`_replace_once` (`:1092-1101`): `findnext(p, str, k)`, with `nothing` or
`first(r) == 0` mapped to `e1+1:0`. -/
def replaceFind (re : Regex) (s : JStr) (e1 k : JInt64) : RJl (JInt64 × JInt64) :=
  match findnextRe re s k with
  | .error e => .error e
  | .ok none => .ok (mkRange (e1 + ix 1) (ix 0))
  | .ok (some r) => if r.1.val = 0 then .ok (mkRange (e1 + ix 1) (ix 0)) else .ok r

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1068-1104`, for one pattern (`N = 1`, so `x = 1` and `rs`
is a single range) with a `String` replacement (`_replace(io, repl::String, ...)
= write(io, repl)`, `:1011-1012`). Returns `(rs, r, i, out)`. `unsafe_write(io,
pointer(str, i), UInt(j-i))` copies `j - i` code units starting at index `i`. -/
def replaceOnce (re : Regex) (s repl : JStr) (start e1 : JInt64) (rs : JInt64 × JInt64)
    (count n i : JInt64) (out : List UInt8) :
    RJl ((JInt64 × JInt64) × (JInt64 × JInt64) × JInt64 × List UInt8) :=
  let r := rs
  let j := r.1
  let k := r.2
  if j.val > e1.val then .ok (rs, r, i, out)
  else
    let written : RJl (List UInt8) :=
      if decide (i.val = start.val) || decide (i.val ≤ k.val) then
        match convU (j - i) with
        | .error e => .error e
        | .ok len => .ok (out ++ (s.bytes.drop (i.val - 1).toNat).take len ++ repl.bytes)
      else .ok out
    match written with
    | .error e => .error e
    | .ok out =>
      -- `some (i, k)` continues; `none` is the `j == e1 && return` after `i = j`
      let step : SJl (Option (JInt64 × JInt64)) :=
        if k.val < j.val then
          if j.val = e1.val then .ok none
          else (fun k' => some (j, k')) <$> nextind s j
        else (fun k' => some (k', k')) <$> nextind s k
      match step with
      | .error e => .error (.str e)
      | .ok none => .ok (rs, r, j, out)
      | .ok (some (i, k)) =>
        if n.val = count.val then .ok (rs, r, i, out)
        else if rs.1.val < k.val then
          match replaceFind re s e1 k with
          | .error e => .error e
          | .ok rs' => .ok (rs', r, i, out)
        else .ok (rs, r, i, out)

/-- The `while n <= count` loop of `_replace_finish`, `base/strings/util.jl:1057-1062`.
Bound `ncodeunits(s) + 3`: the start `j` of the range handled by successive passes
increases strictly (the next search starts at `nextind(str, j)` or later), every
pass that continues has `j < e1 = ncodeunits(s) + 1`, so there are at most
`ncodeunits(s) + 2` passes. -/
def replaceLoop (re : Regex) (s repl : JStr) (start e1 count : JInt64) :
    Nat → (JInt64 × JInt64) → JInt64 → JInt64 → List UInt8 → RJl (JInt64 × List UInt8)
  | 0, _, _, i, out => .ok (i, out)
  | f + 1, rs, n, i, out =>
    if !decide (n.val ≤ count.val) then .ok (i, out)
    else
      match replaceOnce re s repl start e1 rs count n i out with
      | .error e => .error e
      | .ok (rs, r, i, out) =>
        if r.1.val ≥ e1.val then .ok (i, out)
        else replaceLoop re s repl start e1 count f rs (n + ix 1) i out

/-- `_replace_finish(io, str, count, e1, patterns, replaces, rs)`,
`base/strings/util.jl:1053-1066`, ending with `write(io, SubString(str, i))`. -/
def replaceFinish (re : Regex) (s repl : JStr) (count e1 : JInt64) (rs : JInt64 × JInt64) :
    RJl (List UInt8) :=
  match replaceLoop re s repl (ix 1) e1 count (s.bytes.length + 3) rs (ix 1) (ix 1) [] with
  | .error e => .error e
  | .ok (i, out) =>
    match substring s i (lastindex s) with
    | .error e => .error (.str e)
    | .ok ss => .ok (out ++ ss.view.bytes)

/-- `typemax(Int)`, the default `count` of `replace`. -/
def intMax : JInt64 := ix (2 ^ 63 - 1)

/-- `replace(s, re => repl::String; count)` = `_replace_(String(s), (re => repl,), Int(count))`,
`base/strings/util.jl:1186-1187`, `:1122-1131`, `:1035-1050`; the result is the
code units of the returned String. -/
def replace (re : Regex) (s repl : JStr) (count : JInt64 := intMax) : RJl (List UInt8) :=
  if count.val = 0 then .ok s.bytes
  else if count.val < 0 then .error (.str (.jl (.domainError "`count` must be non-negative.")))
  else
    match nextind s (lastindex s) with
    | .error e => .error (.str e)
    | .ok e1 =>
      match replaceFind re s e1 (ix 1) with
      | .error e => .error e
      | .ok rs =>
        if rs.1.val > e1.val then .ok s.bytes
        else replaceFinish re s repl count e1 rs

end JuliaLean.RegexUnicode.Core


namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## The `replace` driver, `base/strings/util.jl` -/

/-- A match `j:k` (1-based, inclusive) with its match data. -/
structure Rng where
  j : I
  k : I
  md : Ovec

/-- `findnext(pat::RegexAndMatchData, str, i)`, `base/regex.jl:646`, i.e. `_findnext_re`
(`base/regex.jl:491-512`), followed by the `r === nothing || first(r) == 0` sentinel
`e1+1:0` of `_replace_init`/`_replace_once` (`base/strings/util.jl:1044-1049, 1095-1098`).
The range is `(start+1):prevind(str, end+1)`. -/
def findnextRe (p : Pat) (s : List UInt8) (e1 idx : I) : Except IOErr Rng :=
  if (s.length + 1 : Int) < idx.val then .error (.jl .boundsError)
  else
    match exec p s (idx.val - 1).toNat with
    | some ov =>
      match ov.getD 0 none with
      | some (a, b) => if a + 1 = 0 then .ok ⟨e1 + i 1, i 0, []⟩ else .ok ⟨i (a + 1), i b, ov⟩
      | none => .ok ⟨e1 + i 1, i 0, []⟩
    | none => .ok ⟨e1 + i 1, i 0, []⟩

/-- `typemax(Int)`, the default `count`. -/
def countMax : I := imaxval

/-- `_replace_once(io, str, start, e1, patterns, replaces, rs, count, n, i)`,
`base/strings/util.jl:1067-1102`, for one pattern: the new `rs`, the processed `r`, and
the new `i`. -/
def replaceOnce (p : Pat) (s repl : List UInt8) (start e1 count n : I) (r : Rng) (i0 : I) :
    SM (Rng × Rng × I) := do
  let j := r.j
  let k := r.k
  if e1.val < j.val then return (r, r, i0)
  if i0 = start ∨ i0.val ≤ k.val then
    -- copy out preserved portion: unsafe_write(io, pointer(str, i), UInt(j-i))
    let nbytes ← liftE (toU (j - i0).val)
    let _ ← unsafeWriteIO ((s.drop (i0.val - 1).toNat).take nbytes.val.toNat)
    -- copy out replacement string
    let _ ← substStep ⟨s, r.md, []⟩ repl
  let (i1, k1) ←
    if k.val < j.val then
      if j = e1 then return (r, r, j)
      pure (j, j + i 1)
    else pure (k + i 1, k + i 1)
  if n = count then return (r, r, i1)
  let r' ← if j.val < k1.val then liftE (findnextRe p s e1 k1) else pure r
  return (r', r, i1)

/-- The loop of `_replace_finish`, `base/strings/util.jl:1052-1063`; returns `i`. -/
def finishLoop (p : Pat) (s repl : List UInt8) (start e1 count : I) : Nat → I → Rng → I → SM I
  | 0, _, _, i0 => pure i0
  | f + 1, n, r, i0 => do
    if count.val < n.val then return i0
    let (r', rr, i1) ← replaceOnce p s repl start e1 count n r i0
    if e1.val ≤ rr.j.val then return i1
    finishLoop p s repl start e1 count f (n + i 1) r' i1

/-- `_replace_finish(io, str, count, e1, patterns, replaces, rs)`,
`base/strings/util.jl:1052-1064`. -/
def replaceFinish (p : Pat) (s repl : List UInt8) (e1 : I) (r : Rng) : SM Unit := do
  let i1 ← finishLoop p s repl (i 1) e1 countMax (s.length + 2) (i 1) r (i 1)
  -- write(io, SubString(str, i))
  let _ ← unsafeWriteIO (s.drop (i1.val - 1).toNat)

/-- `replace(io, s, r => repl)` with `count = typemax(Int)`: `base/strings/util.jl:1183`,
`_replace_(io, str, pat_repl, count)` (`1105-1116`). -/
def replaceIO (p : Pat) (s repl : List UInt8) : SM Unit := do
  let e1 := i (s.length + 1)
  let r ← liftE (findnextRe p s e1 (i 1))
  if e1.val < r.j.val then
    let _ ← unsafeWriteIO s
    return
  replaceFinish p s repl e1 r

/-- `floor(Int, 1.2 * n)` in `Float64` arithmetic for `0 ≤ n < 2^53`: the double `1.2` is
`5404319552844595 / 2^52`, and the product is rounded to 53 significant bits, ties to
even. -/
def floor12 (n : Nat) : Nat :=
  let p := n * 5404319552844595
  let b := bitLength 128 p
  if b ≤ 53 then p / 2 ^ 52
  else
    let sh := b - 53
    let q := p / 2 ^ sh
    let rm := p % 2 ^ sh
    let half := 2 ^ (sh - 1)
    let q := if half < rm ∨ (rm = half ∧ q % 2 = 1) then q + 1 else q
    q * 2 ^ sh / 2 ^ 52

/-- `replace(s, r => repl)`: `base/strings/util.jl:1186`, `_replace_(str, pat_repl, count)`
(`1119-1131`): the bytes of the returned `String`. -/
def replaceStr (p : Pat) (s repl : List UInt8) : Except IOErr (List UInt8) := do
  let e1 := i (s.length + 1)
  let r ← findnextRe p s e1 (i 1)
  if e1.val < r.j.val then return s
  let out ← iobufferEmpty (some true) (some true) none (some true) (2 ^ 63 - 1)
    (some (floor12 s.length))
  match (replaceFinish p s repl e1 r) (.buf out) with
  | .error e _ => .error e
  | .ok _ (.other _) => .error (.jl (.methodError "takestring!"))
  | .ok _ (.buf io) =>
    match takestring io with
    | .ok bs _ => .ok bs
    | .error e _ => .error e

/-- ASCII text. -/
def isAscii (s : List UInt8) : Bool := s.all (· < 128)

end JuliaLean.RegexUnicode.Subst
