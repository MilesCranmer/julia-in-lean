import JuliaLean.Core

/-!
# Model of `base/rawbigfloats.jl`

`BigFloatData` is a list of unsigned words. Word width, unchecked limb access,
bit operations, integer-range iteration, and conversion to `R` are typed
interfaces to Julia's unsigned and integer primitives. Machine indices use
`JInt .i64`, including wrapping arithmetic.
-/

namespace JuliaLean.base.rawbigfloats

open JuliaLean

abbrev I := JInt .i64

def int (value : Int) : I := JInt.wrap .i64 value

def BigFloatData (Word : Type) := List Word

inductive Direction where
  | ascending
  | descending
  deriving DecidableEq, Repr

structure Ops (Word R : Type) where
  wordBytes : I
  zeroWord : Word
  wordAtUnchecked : BigFloatData Word → I → Word
  wordIsZero : Word → Bool
  wordModBool : Word → Bool
  wordShiftLeft : Word → I → Word
  wordShiftRight : Word → I → Word
  divremToZero : I → I → Jl (I × I)
  anyIntRange : (I → Bool) → I → I → Bool
  foldIntRange : {State : Type} → I → I → State → (State → I → Jl State) → Jl State
  zeroR : R
  ofWord : Word → Jl R
  shiftLeftR : R → I → R
  orR : R → R → R

/--
Julia source: base/rawbigfloats.jl:5-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
elem_count(x::BigFloatData, ::Val{:words}) = length(x)
elem_count(x::Unsigned, ::Val{:bits}) = sizeof(x) * 8
word_length(::BigFloatData{T}) where {T} = elem_count(zero(T), Val(:bits))
elem_count(x::BigFloatData{T}, ::Val{:bits}) where {T} = word_length(x) * elem_count(x, Val(:words))
reversed_index(n::Int, i::Int) = n - i - 1
reversed_index(x, i::Int, v::Val) = reversed_index(elem_count(x, v), i)::Int
split_bit_index(x::BigFloatData, i::Int) = divrem(i, word_length(x), RoundToZero)
```
-/
def elemCountWords {Word : Type} (x : BigFloatData Word) : I :=
  JInt.wrap .i64 (x.length : Int)

def elemCountUnsignedBits {Word R : Type} (ops : Ops Word R) (_x : Word) : I :=
  ops.wordBytes * int 8

def wordLength {Word R : Type} (ops : Ops Word R) (_x : BigFloatData Word) : I :=
  elemCountUnsignedBits ops ops.zeroWord

def elemCountDataBits {Word R : Type} (ops : Ops Word R) (x : BigFloatData Word) : I :=
  wordLength ops x * elemCountWords x

def reversedIndexInt (n i : I) : I := n - i - int 1

def reversedIndex {X V : Type} (elemCount : X → V → I) (x : X) (i : I) (v : V) : I :=
  reversedIndexInt (elemCount x v) i

def splitBitIndex {Word R : Type} (ops : Ops Word R) (x : BigFloatData Word) (i : I) :
    Jl (I × I) :=
  ops.divremToZero i (wordLength ops x)

/--
Julia source: base/rawbigfloats.jl:17-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_elem(x::BigFloatData{T}, i::Int, ::Val{:words}, ::Val{:ascending}) where {T}
    @inbounds return x[i + 1]::T
end
```
-/
def getElemWordsAscending {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (i : I) : Word :=
  ops.wordAtUnchecked x (i + int 1)

/--
Julia source: base/rawbigfloats.jl:21-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_elem(x, i::Int, v::Val, ::Val{:descending})
    j = reversed_index(x, i, v)
    get_elem(x, j, v, Val(:ascending))
end
```
-/
def getElemDescending {X V A : Type} (elemCount : X → V → I)
    (getAscending : X → I → V → A) (x : X) (i : I) (v : V) : A :=
  getAscending x (reversedIndex elemCount x i v) v

private def getElemWords {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (i : I) (direction : Direction) : Word :=
  match direction with
  | .ascending => getElemWordsAscending ops x i
  | .descending =>
      getElemDescending (fun data (_ : Unit) => elemCountWords data)
        (fun data index (_ : Unit) => getElemWordsAscending ops data index) x i ()

/--
Julia source: base/rawbigfloats.jl:26-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
word_is_nonzero(x::BigFloatData, i::Int, v::Val) = !iszero(get_elem(x, i, Val(:words), v))

word_is_nonzero(x::BigFloatData, v::Val) = let x = x
    i -> word_is_nonzero(x, i, v)
end
```
-/
def wordIsNonzero {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (i : I) (direction : Direction) : Bool :=
  !ops.wordIsZero (getElemWords ops x i direction)

def wordIsNonzeroClosure {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (direction : Direction) : I → Bool :=
  fun i => wordIsNonzero ops x i direction

/--
Julia source: base/rawbigfloats.jl:36-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tail_is_nonzero(x::BigFloatData, len::Int, ::Val{:words})
    any(word_is_nonzero(x, Val(:ascending)), 0:(len - 1))
end
```
-/
def tailWordsNonzero {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (len : I) : Bool :=
  ops.anyIntRange (wordIsNonzeroClosure ops x .ascending) (int 0) (len - int 1)

/--
Julia source: base/rawbigfloats.jl:44-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tail_is_nonzero(x::BigFloatData, len::Int, i::Int, ::Val{:word})
    !iszero(len) &&
    !iszero(get_elem(x, i, Val(:words), Val(:ascending)) << (word_length(x) - len))
end
```
-/
def tailWordNonzero {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (len i : I) : Bool :=
  len != int 0 &&
    !ops.wordIsZero (ops.wordShiftLeft (getElemWordsAscending ops x i) (wordLength ops x - len))

/--
Julia source: base/rawbigfloats.jl:53-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tail_is_nonzero(x::BigFloatData, len::Int, ::Val{:bits})
    if 0 < len
        word_count, bit_count_in_word = split_bit_index(x, len)
        tail_is_nonzero(x, bit_count_in_word, word_count, Val(:word)) ||
        tail_is_nonzero(x, word_count, Val(:words))
    else
        false
    end::Bool
end
```
-/
def tailBitsNonzero {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (len : I) : Jl Bool := do
  if int 0 < len then
    let (wordCount, bitCount) ← splitBitIndex ops x len
    if tailWordNonzero ops x bitCount wordCount then pure true
    else pure (tailWordsNonzero ops x wordCount)
  else
    pure false

/--
Julia source: base/rawbigfloats.jl:66-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_elem(x::Unsigned, i::Int, ::Val{:bits}, ::Val{:ascending})
    (x >>> i) % Bool
end
```
-/
def getElemUnsignedBitAscending {Word R : Type} (ops : Ops Word R) (x : Word) (i : I) : Bool :=
  ops.wordModBool (ops.wordShiftRight x i)

/--
Julia source: base/rawbigfloats.jl:73-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_elem(x::BigFloatData, i::Int, ::Val{:bits}, v::Val{:ascending})
    vb = Val(:bits)
    if 0 ≤ i < elem_count(x, vb)
        word_index, bit_index_in_word = split_bit_index(x, i)
        word = get_elem(x, word_index, Val(:words), v)
        get_elem(word, bit_index_in_word, vb, v)
    else
        false
    end::Bool
end
```
-/
def getElemDataBitAscending {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (i : I) : Jl Bool := do
  if int 0 ≤ i ∧ i < elemCountDataBits ops x then
    let (wordIndex, bitIndex) ← splitBitIndex ops x i
    let word := getElemWordsAscending ops x wordIndex
    pure (getElemUnsignedBitAscending ops word bitIndex)
  else
    pure false

private def getElemDataBitDescending {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (i : I) : Jl Bool :=
  getElemDescending (fun data (_ : Unit) => elemCountDataBits ops data)
    (fun data index (_ : Unit) => getElemDataBitAscending ops data index) x i ()

private def getElemWordsDescending {Word R : Type} (ops : Ops Word R)
    (x : BigFloatData Word) (i : I) : Word :=
  getElemDescending (fun data (_ : Unit) => elemCountWords data)
    (fun data index (_ : Unit) => getElemWordsAscending ops data index) x i ()

/--
Julia source: base/rawbigfloats.jl:89-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function truncated(::Type{R}, x::BigFloatData, len::Int) where {R<:Integer}
    ret = zero(R)
    if 0 < len
        word_count, bit_count_in_word = split_bit_index(x, len)
        k = word_length(x)
        vals = (Val(:words), Val(:descending))
        lenx = elem_count(x, first(vals))

        for w ∈ 0:(word_count - 1)
            ret <<= k
            if w < lenx # if the output type is larger, truncate turns into zero-extend
                word = get_elem(x, w, vals...)
                ret |= R(word)
            end
        end

        if !iszero(bit_count_in_word)
            ret <<= bit_count_in_word
            if word_count < lenx # if the output type is larger, truncate turns into zero-extend
                wrd = get_elem(x, word_count, vals...)
                ret |= R(wrd >>> (k - bit_count_in_word))
            end
        end
    end
    ret::R
end
```
-/
def truncated {Word R : Type} (ops : Ops Word R) (x : BigFloatData Word) (len : I) : Jl R := do
  if int 0 < len then
    let (wordCount, bitCount) ← splitBitIndex ops x len
    let wordWidth := wordLength ops x
    let dataWords := elemCountWords x
    let ret ← ops.foldIntRange (int 0) (wordCount - int 1) ops.zeroR (fun ret w => do
      let ret := ops.shiftLeftR ret wordWidth
      if w < dataWords then
        let word := getElemWordsDescending ops x w
        let converted ← ops.ofWord word
        pure (ops.orR ret converted)
      else
        pure ret)
    let ret := if bitCount != int 0 then ops.shiftLeftR ret bitCount else ret
    if bitCount != int 0 && wordCount < dataWords then
      let word := getElemWordsDescending ops x wordCount
      let shifted := ops.wordShiftRight word (wordWidth - bitCount)
      let converted ← ops.ofWord shifted
      pure (ops.orR ret converted)
    else
      pure ret
  else
    pure ops.zeroR

/--
Julia source: base/rawbigfloats.jl:116-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct BigFloatDataRoundingIncrementHelper{T<:Unsigned}
    n::BigFloatData{T}
    trunc_len::Int

    final_bit::Bool
    round_bit::Bool

```
-/
structure BigFloatDataRoundingIncrementHelper (Word : Type) where
  n : BigFloatData Word
  truncLen : I
  finalBit : Bool
  roundBit : Bool

/--
Julia source: base/rawbigfloats.jl:123-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function BigFloatDataRoundingIncrementHelper{T}(n::BigFloatData{T}, len::Int) where {T<:Unsigned}
        vals = (Val(:bits), Val(:descending))
        f = get_elem(n, len - 1, vals...)
        r = get_elem(n, len    , vals...)
        new{T}(n, len, f, r)
    end
end
```
-/
def roundingHelperInner {Word R : Type} (ops : Ops Word R)
    (n : BigFloatData Word) (len : I) : Jl (BigFloatDataRoundingIncrementHelper Word) := do
  let finalBit ← getElemDataBitDescending ops n (len - int 1)
  let roundBit ← getElemDataBitDescending ops n len
  pure ⟨n, len, finalBit, roundBit⟩

/--
Julia source: base/rawbigfloats.jl:131-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BigFloatDataRoundingIncrementHelper(n::BigFloatData{T}, len::Int) where {T<:Unsigned}
    BigFloatDataRoundingIncrementHelper{T}(n, len)
end
```
-/
def roundingHelperOuter {Word R : Type} (ops : Ops Word R)
    (n : BigFloatData Word) (len : I) : Jl (BigFloatDataRoundingIncrementHelper Word) := do
  let helper ← roundingHelperInner ops n len
  pure helper

/--
Julia source: base/rawbigfloats.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(h::BigFloatDataRoundingIncrementHelper)(::Rounding.FinalBit) = h.final_bit
```
-/
def roundingFinalBit {Word : Type} (helper : BigFloatDataRoundingIncrementHelper Word) : Bool :=
  helper.finalBit

/--
Julia source: base/rawbigfloats.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(h::BigFloatDataRoundingIncrementHelper)(::Rounding.RoundBit) = h.round_bit
```
-/
def roundingRoundBit {Word : Type} (helper : BigFloatDataRoundingIncrementHelper Word) : Bool :=
  helper.roundBit

/--
Julia source: base/rawbigfloats.jl:139-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (h::BigFloatDataRoundingIncrementHelper)(::Rounding.StickyBit)
    v = Val(:bits)
    n = h.n
    tail_is_nonzero(n, elem_count(n, v) - h.trunc_len - 1, v)
end
```
-/
def roundingStickyBit {Word R : Type} (ops : Ops Word R)
    (helper : BigFloatDataRoundingIncrementHelper Word) : Jl Bool :=
  let n := helper.n
  tailBitsNonzero ops n (elemCountDataBits ops n - helper.truncLen - int 1)

end JuliaLean.base.rawbigfloats
