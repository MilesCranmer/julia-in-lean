import JuliaLean.ShowCov.Basic

/-!
# Delimited lists, summaries, `showarg`, bit chunks, `dump`, `alignment`
(`base/show.jl:1562-1626, 2990-3440`)

Elements are given as their shown text (`none` for an unassigned slot).
-/

namespace JuliaLean.ShowCov.Containers

open JuliaLean.ShowCov

/-! ## `show_delim_array` -/

/-- The `while true` loop of `show_delim_array(io, itr::Union{AbstractArray,SimpleVector}, ...)`,
`base/show.jl:1570-1585`, from index `i` to `l` (fuel `l - i + 1`). -/
def delimArrayLoop (elt : Int → Option String) (delim : String) (delimOne : Bool) (l : Int) :
    Nat → Int → Bool → Out
  | 0, _, _ => []
  | fuel + 1, i, first =>
    let shown := match elt i with | some s => s | none => "#undef"
    if i = l then [shown] ++ (if delimOne && first then [delim] else [])
    else [shown, delim, " "] ++ delimArrayLoop elt delim delimOne l fuel (i + 1) false

/-- `show_delim_array(io, itr::Union{AbstractArray,SimpleVector}, op, delim, cl, delim_one, i1, l)`,
`base/show.jl:1562-1589`. `circular` is what `show_circular(io, itr)` printed. -/
def showDelimArray (elt : Int → Option String) (op delim cl : String) (delimOne : Bool)
    (circular : Option String) (i1 l : Int) : Out :=
  [op] ++
  (match circular with
   | some m => [m]
   | none => if l ≥ i1 then delimArrayLoop elt delim delimOne l (l - i1 + 1).toNat i1 true else []) ++
  [cl]

/-- The element loop of `show_delim_array(io, itr, ...)`, `base/show.jl:1604-1620`:
`count` is `i1 - 1` (after the skipping loop leaves `i1` at `min(i1, 1)`); the
loop stops after the last element or once `i1 > n`. -/
def delimIterLoop (delim : String) (delimOne : Bool) (n : Int) : Int → Bool → List String → Out
  | _, _, [] => []
  | count, first, x :: rest =>
    let count := count + 1
    if rest.isEmpty ∨ count > n then [x] ++ (if delimOne && first then [delim] else [])
    else [x, delim, " "] ++ delimIterLoop delim delimOne n count false rest

/-- `show_delim_array(io, itr, op, delim, cl, delim_one, i1=1, n=typemax(Int))`,
`base/show.jl:1591-1623`, for an iterator producing `xs`: skips `i1 - 1`
elements, then shows elements until the iterator ends or `n` have been shown. -/
def showDelimIter (xs : List String) (op delim cl : String) (delimOne : Bool)
    (circular : Option String) (i1 : Int) (n : Int) : Out :=
  [op] ++
  (match circular with
   | some m => [m]
   | none => delimIterLoop delim delimOne n (min i1 1 - 1) true (xs.drop (i1 - 1).toNat)) ++
  [cl]

/-- `show(io, t::Tuple)`, `show(io, v::SimpleVector)`, `show(io, z::Iterators.Zip)`,
`base/show.jl:1625-1626, 3396`. -/
def showTuple (xs : List String) (circular : Option String) : Out :=
  showDelimIter xs "(" "," ")" true circular 1 (2 ^ 63 - 1)
def showSvec (xs : List String) (circular : Option String) : Out :=
  showDelimArray (fun i => if 1 ≤ i then xs[(i - 1).toNat]? else none) "svec(" "," ")" false circular 1 xs.length
def showZip (xs : List String) (circular : Option String) : Out :=
  showDelimIter xs "zip(" "," ")" false circular 1 (2 ^ 63 - 1)

/-- `show(io, e::Iterators.Enumerate)`, `base/show.jl:3391-3395`. -/
def showEnumerate (itr : String) : Out := ["enumerate(", itr, ")"]

/-! ## Summaries -/

/-- `summary(io, x) = print(io, typeof(x))` and `summary(x)` (the string),
`base/show.jl:3249-3254`. -/
def summaryAny (typeText : String) : String := typeText

/-- `dims2string(d)`, `base/show.jl:3258-3260`. -/
def dims2string (d : List Int) : String :=
  match d with
  | [] => "0-dimensional"
  | [n] => toString n ++ "-element"
  | _ => "×".intercalate (d.map toString)

/-- An axis: `Base.OneTo(n)`, an `IdentityUnitRange`/`Slice` over `indices`
(printed as `string(i.indices)`), or another range printed as `text`. -/
inductive Axis where
  | oneTo (n : Int)
  | wrapped (indicesText : String) (len : Int)
  | other (text : String) (len : Int)

def Axis.len : Axis → Int
  | .oneTo n => n
  | .wrapped _ l => l
  | .other _ l => l

/-- `_indsstring(i) = string(i)` and the `IdentityUnitRange`/`Slice` method,
`base/show.jl:3263-3264`; `Base.OneTo(n)` prints `Base.OneTo(n)`. -/
def indsstring : Axis → String
  | .oneTo n => "Base.OneTo(" ++ toString n ++ ")"
  | .wrapped t _ => t
  | .other t _ => t

/-- `inds2string(inds) = join(map(_indsstring,inds), '×')`, `base/show.jl:3262`. -/
def inds2string (inds : List Axis) : String := "×".intercalate (inds.map indsstring)

def isOneTo : Axis → Bool
  | .oneTo _ => true
  | _ => false

/-- `summary(io, a::AbstractArray) = array_summary(io, a, axes(a))` and both
`array_summary` methods, `base/show.jl:3267-3276`. -/
def arraySummary (inds : List Axis) (showargText : String) : Out :=
  [dims2string (inds.map Axis.len), " ", showargText] ++
  (if inds.all isOneTo then [] else [" with indices ", inds2string inds])

/-- `summary(io, mref::GenericMemoryRef)`, `base/show.jl:3279-3284`;
`offset = Core.memoryrefoffset(mref)` (1-based). -/
def summaryMemoryRef (memLength offset : Int) (showargText : String) : Out :=
  [toString (memLength - offset + 1), "-element ", showargText]

/-- `summary(io, f::Function) = show(io, MIME"text/plain"(), f)`, `base/show.jl:3287`. -/
def summaryFunction (plainText : String) : String := plainText

/-! ## `showarg` -/

/-- `showarg(io, x, toplevel)` fallback and the `Array{Union{}}` method,
`base/show.jl:3335-3347`. -/
def showargAny (typeText : String) (toplevel : Bool) : Out :=
  (if toplevel then [] else ["::"]) ++ [typeText]
/-- `showarg(io, T::Type, toplevel)`, `base/show.jl:3339-3342`. -/
def showargType (typeText : String) (toplevel : Bool) : Out :=
  (if toplevel then [] else ["::"]) ++ ["Type{", typeText, "}"]

/-- An index of a `SubArray`: a `Slice` or another index printed as `text`. -/
inductive Ind where
  | slice
  | other (text : String)

/-- `showindices(io, inds...)`, `base/show.jl:3358-3362`. -/
def showindices : List Ind → Out
  | [] => []
  | .slice :: rest => [", :"] ++ showindices rest
  | .other t :: rest => [", ", t] ++ showindices rest

/-- `showarg(io, v::SubArray, toplevel)`, `base/show.jl:3350-3357`; `parentArg`
is `showarg(io, parent(v), false)`. -/
def showargSubArray (parentArg : Out) (inds : List Ind) (eltype : String) (toplevel : Bool) : Out :=
  ["view("] ++ parentArg ++ showindices inds ++ [")"] ++
  (if toplevel then [" with eltype ", eltype] else [])

/-- `showarg(io, r::ReshapedArray, toplevel)`, `base/show.jl:3364-3373`. -/
def showargReshaped (parentArg : Out) (dims : List Int) (eltype : String) (toplevel : Bool) : Out :=
  ["reshape("] ++ parentArg ++
  (if dims.isEmpty then [] else [", ", ", ".intercalate (dims.map toString)]) ++ [")"] ++
  (if toplevel then [" with eltype ", eltype] else [])

/-- `showarg` for `NonReshapedReinterpretArray` and `ReshapedReinterpretArray`,
`base/show.jl:3375-3387`. -/
def showargReinterpret (T : String) (parentArg : Out) : Out :=
  ["reinterpret(", T, ", "] ++ parentArg ++ [")"]
def showargReinterpretReshape (T : String) (parentArg : Out) (eltype : String) (toplevel : Bool) : Out :=
  ["reinterpret(reshape, ", T, ", "] ++ parentArg ++ [")"] ++
  (if toplevel then [" with eltype ", eltype] else [])

/-- The three `showarg` methods for `Iterators.Pairs`, `base/show.jl:3399-3409`. -/
def showargPairsArray (T : String) : Out := ["pairs(IndexLinear(), ::", T, ")"]
def showargPairsNamedTuple : Out := ["pairs(::NamedTuple)"]
def showargPairsGeneric (D I : String) : Out := ["Iterators.Pairs(::", D, ", ::", I, ")"]

/-! ## Bit chunks -/

/-- `print_bit_chunk(io, c::UInt64, l = 64)`, `base/show.jl:3415-3423`, and the
`stdout` forms (`:3425-3426`). -/
def printBitChunk (c : Nat) (l : Nat := 64) : List Char :=
  (List.range l).flatMap (fun s =>
    [if (c / 2 ^ s) % 2 = 1 then '1' else '0'] ++ (if (s + 1) % 8 = 0 then [' '] else []))

/-- `bitshow(io, B::BitArray)` and `bitstring(B) = sprint(bitshow, B)`,
`base/show.jl:3428-3440`: chunks are the 64-bit words of `B.chunks`, `len`
is `length(B)`. -/
def bitshow (chunks : List Nat) (len : Nat) : List Char :=
  if len = 0 then [] else
  let l := (len - 1) % 64 + 1
  (chunks.dropLast.flatMap (fun c => printBitChunk c ++ [':', ' '])) ++ printBitChunk (chunks.getLastD 0) l

/-- The bits of a chunk list in index order, with `l` bits from the last chunk. -/
def bitsOf (chunks : List Nat) (len : Nat) : List Char :=
  (List.range len).map (fun i => if (chunks.getD (i / 64) 0 / 2 ^ (i % 64)) % 2 = 1 then '1' else '0')

/-! ## `dump` -/

/-- What `dump` sees in a value: a leaf printed in one line, a structure with
named fields (`none` for an undefined field), or a `Function` (printed
with its type and no fields). -/
inductive DV where
  | leaf (line : String)
  | node (header : String) (fields : List (String × Option DV))
  | func (line : String)

/-- `dump(io::IOContext, x, n, indent)` for a field structure and leaves,
`base/show.jl:3010-3047`: lines with their nesting depth (the header line has
depth 0, a field of a depth-`k` node has depth `k + 1`). Fields are printed
only while `n > 0`. -/
def dumpLines : Nat → Nat → DV → List (Nat × String)
  | _, d, .leaf s => [(d, s)]
  | _, d, .func s => [(d, s)]
  | 0, d, .node h _ => [(d, h)]
  | n + 1, d, .node h fs =>
    (d, h) :: fs.attach.flatMap (fun ⟨(name, v), _⟩ =>
      match v with
      | none => [(d + 1, name ++ ": #undef")]
      | some v => dumpLines n (d + 1) v)

/-- `dump(io, x; maxdepth = 8)`, `base/show.jl:3130-3133`, and `dump(arg; maxdepth)`
(`:3163-3167`, to `stdout` with `:limit => true`). -/
def dumpTop (maxdepth : Nat) (x : DV) : List (Nat × String) := dumpLines maxdepth 0 x

/-- `dump_elts(io, x::Array, n, indent, i0, i1)` (`base/show.jl:3049-3059`) and
the `:limit` choice of `dump(io, x::Array, ...)` (`:3061-3084`): the element
indices shown. -/
def dumpArrayIndices (limit : Bool) (lx : Nat) : List Nat :=
  if limit then
    (List.range (if lx ≤ 10 then lx else 5)).map (· + 1) ++
    (if lx > 10 then (List.range 5).map (· + (lx - 4)) else [])
  else (List.range lx).map (· + 1)

/-- One-line `dump` methods, `base/show.jl:3043-3047`. -/
def dumpModule (m : String) : String := "Module " ++ m
def dumpString (shown : String) : String := "String " ++ shown
def dumpSymbol (name : String) : String := "Symbol " ++ name
def dumpUnion (printed : String) : String := printed
def dumpPtr (printed : String) : String := printed

/-- `dump(io::IOContext, x::SimpleVector, n, indent)` header, `base/show.jl:2990-3008`. -/
def dumpSvecHeader (isEmpty : Bool) : String := if isEmpty then "empty SimpleVector" else "SimpleVector"

/-- The header of `dump(io::IOContext, x::DataType, n, indent)`, `base/show.jl:3087-3098`. -/
def dumpTypeHeader (isStruct isMutable isTuple isPrimitive isAbstract isAny : Bool)
    (typeText supertypeText : String) : String :=
  let isStruct := isStruct && !isTuple
  let isMut := isStruct && isMutable
  (if isMut then "mutable " else "") ++ (if isStruct then "struct " else "") ++
  (if isPrimitive then "primitive type " else "") ++ (if isAbstract then "abstract type " else "") ++
  typeText ++ (if isAny then "" else " <: " ++ supertypeText)

/-! ## `alignment` -/

/-- `alignment(io, x::Any) = (0, alignment_from_show(io, x))`, and the
`Number`/`Integer` methods `(alignment_from_show(io, x), 0)`, `base/show.jl:3191-3193`;
`w` is `textwidth(sprint(show, x, context=nocolor(io)))` (`alignment_from_show`,
`base/show.jl:3170-3173`). -/
def alignmentAny (w : Nat) : Int × Int := (0, w)
def alignmentNumber (w : Nat) : Int × Int := (w, 0)

/-- The captures of `match(r"^(.*?)((?:[\.eEfF].*)?)$", s)`: the lazy first
group stops at the first `.`, `e`, `E`, `f` or `F` (or takes everything). -/
def splitRealAt (s : List Char) : List Char × List Char :=
  (s.takeWhile (fun c => c ∉ ['.', 'e', 'E', 'f', 'F']), s.dropWhile (fun c => c ∉ ['.', 'e', 'E', 'f', 'F']))

/-- `alignment(io, x::Real)`, `base/show.jl:3194-3199`; `tw` is `textwidth`. -/
def alignmentReal (tw : Char → Nat) (s : List Char) : Int × Int :=
  let (a, b) := splitRealAt s
  ((a.map tw).sum, (b.map tw).sum)

/-- The captures of `match(r"^(.*?/)(/.*)$", s)`: split after the first `/`
that is followed by another `/`; `none` if there is no `//`. -/
def splitRational : List Char → Option (List Char × List Char)
  | [] => none
  | [_] => none
  | c :: d :: rest =>
    if c = '/' ∧ d = '/' then some (['/'], '/' :: rest)
    else (splitRational (d :: rest)).map (fun (a, b) => (c :: a, b))

/-- `alignment(io, x::Rational)`, `base/show.jl:3206-3211`. -/
def alignmentRational (tw : Char → Nat) (s : List Char) : Int × Int :=
  match splitRational s with
  | none => ((s.map tw).sum, 0)
  | some (a, b) => ((a.map tw).sum, (b.map tw).sum)

/-- The captures of `match(r"^(.*[^ef][\+\-])(.*)$", s)`: the greedy first
group ends at the last `+`/`-` that has a preceding character other than
`e`/`f`; `none` if there is none. -/
def splitComplex (s : List Char) : Option (List Char × List Char) :=
  let n := s.length
  let ok (k : Nat) : Bool :=
    1 ≤ k && k < n && (s.getD k ' ' = '+' || s.getD k ' ' = '-') &&
      s.getD (k - 1) ' ' ≠ 'e' && s.getD (k - 1) ' ' ≠ 'f'
  match ((List.range n).filter ok).getLast? with
  | some k => some (s.take (k + 1), s.drop (k + 1))
  | none => none

/-- `alignment(io, x::Complex)`, `base/show.jl:3200-3205`. -/
def alignmentComplex (tw : Char → Nat) (s : List Char) : Int × Int :=
  match splitComplex s with
  | none => ((s.map tw).sum, 0)
  | some (a, b) => ((a.map tw).sum, (b.map tw).sum)

/-- `alignment(io, x::Pair)`, `base/show.jl:3213-3224`. -/
def alignmentPair (fullwidth : Int) (delimited : Bool) (firstWidth : Int) (firstDelimited compact : Bool) :
    Int × Int :=
  if !delimited then
    let left := firstWidth + (if firstDelimited then 0 else 2) + (if compact then 0 else 1)
    (left + 1, fullwidth - left - 1)
  else (0, fullwidth)

/-- `nocolor(io) = IOContext(io, :color => false)`, `base/show.jl:3169`: the
property list with `:color => false` pushed. -/
def nocolor (props : List (String × String)) : List (String × String) := ("color", "false") :: props

end JuliaLean.ShowCov.Containers
