import JuliaLean.Core
import JuliaLean.base.int

namespace JuliaLean.base.ntuple

open JuliaLean JuliaLean.base.int

/-!
# Model of `base/ntuple.jl`

Typed model of every method at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a 64-bit
platform. Tuple fields carry their individual element types, and each source method keeps its
control flow and call order. Operations owned by other Base files are typed function parameters.
-/

abbrev I64 := JInt .i64
abbrev TupleField := Sigma fun α : Type => α
abbrev TupleValue := List TupleField

inductive NtupleError where
  | base (error : JlError)
  | typeError
  | external (name message : String)
  deriving Repr, DecidableEq

universe u v
abbrev NtupleResult (α : Type u) := Except NtupleError α

/--
Julia source: base/ntuple.jl:36-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ntuple(f::F, n::Int) where F
    @noinline
    (n >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", n)))
    ([f(i) for i = 1:n]...,)
end
```
-/
def _ntuple {m : Type u → Type v} [Monad m] [MonadExceptOf NtupleError m] {β : Type u}
    (f : I64 → m β) (n : I64) (oneTo : I64 → m (ULift.{u} (List I64))) : m (List β) :=
  if n.val ≥ 0 then do
    let indices ← oneTo n
    List.mapM f indices.down
  else
    throwThe NtupleError (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString n.val)))

/--
Julia source: base/ntuple.jl:5-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    ntuple(f, n::Integer)

Create a tuple of length `n`, computing each element as `f(i)`,
where `i` is the index of the element.

# Examples
```jldoctest
julia> ntuple(i -> 2*i, 4)
(2, 4, 6, 8)
```
"""
@inline function ntuple(f::F, n::Int) where F
    # marked inline since this benefits from constant propagation of `n`
    t = n == 0  ? () :
        n == 1  ? (f(1),) :
        n == 2  ? (f(1), f(2)) :
        n == 3  ? (f(1), f(2), f(3)) :
        n == 4  ? (f(1), f(2), f(3), f(4)) :
        n == 5  ? (f(1), f(2), f(3), f(4), f(5)) :
        n == 6  ? (f(1), f(2), f(3), f(4), f(5), f(6)) :
        n == 7  ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7)) :
        n == 8  ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8)) :
        n == 9  ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8), f(9)) :
        n == 10 ? (f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8), f(9), f(10)) :
        _ntuple(f, n)
    return t
end
````
-/
def ntupleInt {m : Type u → Type v} [Monad m] [MonadExceptOf NtupleError m] {β : Type u}
    (f : I64 → m β) (n : I64) (oneTo : I64 → m (ULift.{u} (List I64))) : m (List β) :=
  if n.val = 0 then pure []
  else if n.val = 1 then do
    let x1 ← f (lit .i64 1)
    pure [x1]
  else if n.val = 2 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    pure [x1, x2]
  else if n.val = 3 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    pure [x1, x2, x3]
  else if n.val = 4 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    pure [x1, x2, x3, x4]
  else if n.val = 5 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    pure [x1, x2, x3, x4, x5]
  else if n.val = 6 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    pure [x1, x2, x3, x4, x5, x6]
  else if n.val = 7 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    pure [x1, x2, x3, x4, x5, x6, x7]
  else if n.val = 8 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    let x8 ← f (lit .i64 8)
    pure [x1, x2, x3, x4, x5, x6, x7, x8]
  else if n.val = 9 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    let x8 ← f (lit .i64 8)
    let x9 ← f (lit .i64 9)
    pure [x1, x2, x3, x4, x5, x6, x7, x8, x9]
  else if n.val = 10 then do
    let x1 ← f (lit .i64 1)
    let x2 ← f (lit .i64 2)
    let x3 ← f (lit .i64 3)
    let x4 ← f (lit .i64 4)
    let x5 ← f (lit .i64 5)
    let x6 ← f (lit .i64 6)
    let x7 ← f (lit .i64 7)
    let x8 ← f (lit .i64 8)
    let x9 ← f (lit .i64 9)
    let x10 ← f (lit .i64 10)
    pure [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10]
  else
    _ntuple f n oneTo

/--
Julia source: base/ntuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ntuple(f::F, n::Integer) where F = ntuple(f, convert(Int, n)::Int)
```
-/
def ntupleInteger {m : Type u → Type v} [Monad m] [MonadExceptOf NtupleError m] {β : Type u}
    {I : Type} (f : I64 → m β) (convertInt : I → Jl I64) (n : I)
    (oneTo : I64 → m (ULift.{u} (List I64))) : m (List β) :=
  match convertInt n with
  | .ok nInt => ntupleInt f nInt oneTo
  | .error e => throwThe NtupleError (.base e)

/--
Julia source: base/ntuple.jl:42-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ntupleany(f, n)
    @noinline
    (n >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", n)))
    (Any[f(i) for i = 1:n]...,)
end
```
-/
def ntupleAny {N I : Type} (f : I → NtupleResult TupleField) (n : N)
    (isNonnegative : N → NtupleResult (ULift Bool))
    (oneTo : N → NtupleResult (ULift (List I)))
    (showValue : N → String) : NtupleResult TupleValue := do
  let nonnegative ← isNonnegative n
  if nonnegative.down then
    let indices ← oneTo n
    List.mapM f indices.down
  else
    .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ showValue n)))

/--
Julia source: base/ntuple.jl:48-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    ntuple(f, ::Val{N})

Create a tuple of length `N`, computing each element as `f(i)`,
where `i` is the index of the element. By taking a `Val(N)`
argument, it is possible that this version of ntuple may
generate more efficient code than the version taking the
length as an integer. But `ntuple(f, N)` is preferable to
`ntuple(f, Val(N))` in cases where `N` cannot be determined
at compile time.

# Examples
```jldoctest
julia> ntuple(i -> 2*i, Val(4))
(2, 4, 6, 8)
```
"""
@inline function ntuple(f::F, ::Val{N}) where {F,N}
    (N::Int >= 0) || throw(ArgumentError(LazyString("tuple length should be ≥ 0, got ", N)))
    if @generated
        :(@ntuple $N i -> f(i))
    else
        Tuple(f(i) for i = 1:(N::Int))
    end
end
````
-/
def ntupleVal {N : Type} (f : I64 → NtupleResult TupleField) (n : N)
    (assertInt : N → NtupleResult (ULift I64))
    (generated : Bool)
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue)
    (oneTo : I64 → NtupleResult (ULift (List I64))) : NtupleResult TupleValue := do
  let sizeLift ← assertInt n
  let size := sizeLift.down
  if size.val ≥ 0 then
    if generated then
      generatedNtuple size f
    else do
      let rangeSizeLift ← assertInt n
      let indices ← oneTo rangeSizeLift.down
      List.mapM f indices.down
  else
    .error (.base (.argumentError ("tuple length should be ≥ 0, got " ++ toString size.val)))

/--
Julia source: base/ntuple.jl:74-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function fill_to_length(t::Tuple, val, ::Val{_N}) where {_N}
    M = length(t)
    N = _N::Int
    M > N && throw(ArgumentError(LazyString("input tuple of length ", M, ", requested ", N)))
    if @generated
        quote
            (t..., $(fill(:val, (_N::Int) - length(t.parameters))...))
        end
    else
        (t..., fill(val, N-M)...)
    end
end
```
-/
def fillToLength {N : Type} (t : TupleValue) (val : TupleField) (n : N)
    (length : TupleValue → NtupleResult (ULift I64))
    (assertInt : N → NtupleResult (ULift I64))
    (fill : TupleField → I64 → NtupleResult TupleValue)
    (generated : Bool) : NtupleResult TupleValue := do
  let lengthLift ← length t
  let m := lengthLift.down
  let requestedLift ← assertInt n
  let requested := requestedLift.down
  if m.val > requested.val then
    .error (.base (.argumentError ("input tuple of length " ++ toString m.val ++
      ", requested " ++ toString requested.val)))
  else if generated then
    let count := sub_int requested (lit .i64 (Int.ofNat t.length))
    let padding ← fill val count
    pure (t ++ padding)
  else
    let count := sub_int requested m
    let padding ← fill val count
    pure (t ++ padding)

/--
Julia source: base/ntuple.jl:89-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reverse(t::NTuple{N}) where N
    ntuple(Val{N}()) do i
        t[end+1-i]
    end::typeof(t)
end
```
-/
def reverseNTuple {α : Type} (t : List α) (n : I64)
    (oneTo : I64 → NtupleResult (ULift (List I64)))
    (generated : Bool)
    (generatedNtuple : I64 → (I64 → NtupleResult TupleField) → NtupleResult TupleValue)
    (endIndex : List α → I64)
    (getindex : List α → I64 → NtupleResult (ULift α))
    (asNTuple : TupleValue → NtupleResult (ULift (List α))) :
    NtupleResult (ULift (List α)) := do
  let result ← ntupleVal (fun i => do
      let last := endIndex t
      let endPlusOne := add_int last (lit .i64 1)
      let index := sub_int endPlusOne i
      let value ← getindex t index
      pure ⟨α, value.down⟩)
    n (fun size => .ok (.up size)) generated generatedNtuple oneTo
  asNTuple result

end JuliaLean.base.ntuple

namespace JuliaLean.Tuples

inductive Err where
  | jl (e : JlError)
  | typeError
  | fieldError
  | errorException
  deriving Repr, DecidableEq, Inhabited

abbrev R (α : Type) := Except Err α

def bounds {α : Type} : R α := .error (.jl .boundsError)
def argErr {α : Type} (msg : String) : R α := .error (.jl (.argumentError msg))
def liftJ {α : Type} : Jl α → R α
  | .ok a => .ok a
  | .error e => .error (.jl e)

/-- Julia exception type of an error (messages are ignored). -/
def Err.kind : Err → String
  | .jl (.overflowError _) => "OverflowError"
  | .jl (.argumentError _) => "ArgumentError"
  | .jl .boundsError => "BoundsError"
  | .jl (.inexactError _) => "InexactError"
  | .jl .divideError => "DivideError"
  | .jl (.domainError _) => "DomainError"
  | .jl (.methodError _) => "MethodError"
  | .jl .eofError => "EOFError"
  | .typeError => "TypeError"
  | .fieldError => "FieldError"
  | .errorException => "ErrorException"

/-! ## Scalar indices -/

/-- A scalar `Integer` index: one of the ten `BitInteger` types, or `Bool`. -/
inductive Idx where
  | int (t : IntTy) (v : JInt t)
  | bool (b : Bool)

/-- The mathematical value of an index (`true` is 1). -/
def Idx.val : Idx → Int
  | .int _ v => v.val
  | .bool b => if b then 1 else 0

/-- `getfield(t, i::Int)` with bounds checking. -/
def getfield {α : Type} (t : List α) (i : Int) : R α :=
  if 1 ≤ i then
    match t[(i - 1).toNat]? with
    | some a => .ok a
    | none => bounds
  else bounds
/-- `ntuple(f, n::Int)`, `base/ntuple.jl:17-32,36-40`: lengths 0..10 are unrolled,
other lengths go to `_ntuple`, which rejects negative `n`. -/
def ntupleInt {α : Type} (f : Nat → α) (n : Int) : R (List α) :=
  if 0 ≤ n ∧ n ≤ 10 then .ok ((List.range n.toNat).map fun k => f (k + 1))
  else if n ≥ 0 then .ok ((List.range n.toNat).map fun k => f (k + 1))
  else argErr s!"tuple length should be ≥ 0, got {n}"

/-- `ntuple(f, n::Integer) = ntuple(f, convert(Int, n))`, `base/ntuple.jl:33`. -/
def ntuple {α : Type} (f : Nat → α) (t : IntTy) (n : JInt t) : R (List α) := do
  let m ← liftJ (JInt.convert (IntTy.i64.name) .i64 n.val)
  ntupleInt f m.val

/-- `ntuple(f, ::Val{N})`, `base/ntuple.jl:65-72` (`N::Int`). -/
def ntupleVal {α : Type} (f : Nat → α) (N : JInt .i64) : R (List α) :=
  if N.val ≥ 0 then .ok ((List.range N.val.toNat).map fun k => f (k + 1))
  else argErr s!"tuple length should be ≥ 0, got {N.val}"

/-- `fill_to_length`, the specialised methods `base/tuple.jl:442-445` and the
general method `base/ntuple.jl:74-85`. -/
def fillToLength {α : Type} (t : List α) (v : α) (N : JInt .i64) : R (List α) :=
  if (t.length : Int) = N.val then .ok t
  else if t.length = 0 ∧ N.val = 1 then .ok [v]
  else if t.length = 1 ∧ N.val = 2 then .ok (t ++ [v])
  else if t.length = 0 ∧ N.val = 2 then .ok [v, v]
  else if (t.length : Int) > N.val then argErr "input tuple of length M, requested N"
  else .ok (t ++ List.replicate (N.val - t.length).toNat v)
/-- `reverse(t::NTuple{N})`, `base/ntuple.jl:89-93`: `ntuple(i -> t[end+1-i], Val(N))`. -/
def reverseNTuple {α : Type} (t : List α) : R (List α) :=
  (List.range t.length).mapM fun (k : Nat) => getfield t ((t.length : Int) + 1 - ((k : Int) + 1))

end JuliaLean.Tuples

namespace JuliaLean.Tuples

/-- A `BitInteger` value together with its type. -/
abbrev AnyInt := (u : IntTy) × JInt u

/-- `promote(x, y)` for two `BitInteger`s, `base/promotion.jl:397-401,423-428` with the
rules of `base/int.jl:809-822`: `convert` both to the promoted type. -/
def promoteInts {s t : IntTy} (x : JInt s) (y : JInt t) :
    R (JInt (IntTy.promote s t) × JInt (IntTy.promote s t)) := do
  let a ← liftJ (JInt.convert ((IntTy.promote s t).name) (IntTy.promote s t) x.val)
  let b ← liftJ (JInt.convert ((IntTy.promote s t).name) (IntTy.promote s t) y.val)
  pure (a, b)

/-- `a - b` for `BitInteger`s, `base/int.jl:1092-1099`: both operands are wrapped
into `promote_type` (`a % T`), then the wrapping same-type `-`. -/
def subMixed {s t : IntTy} (a : JInt s) (b : JInt t) : JInt (IntTy.promote s t) :=
  JInt.rem (IntTy.promote s t) a - JInt.rem (IntTy.promote s t) b

/-- `a + b` for `BitInteger`s, `base/int.jl:1092-1099`. -/
def addMixed {s t : IntTy} (a : JInt s) (b : JInt t) : JInt (IntTy.promote s t) :=
  JInt.rem (IntTy.promote s t) a + JInt.rem (IntTy.promote s t) b

/-- `abs(y) = flipsign(y, y)` for a signed integer, `base/int.jl:234` (wraps at `typemin`). -/
def absSigned {t : IntTy} (y : JInt t) : JInt t := if y.val < 0 then -y else y

/-- `rem(x, y)` for `y::Int`. An unsigned `x` takes `rem(x::Unsigned, y::BitSigned) =
rem(x, unsigned(abs(y)))` (`base/int.jl:279`, `unsigned` reinterprets, `:262`); otherwise,
and then, `rem(x::Real, y::Real) = rem(promote(x, y)...)` (`base/promotion.jl:520`) and the
checked intrinsic (`base/int.jl:355-358`). -/
def remByInt {s : IntTy} (x : JInt s) (y : JInt64) : R AnyInt :=
  if s.signed then do
    let p ← promoteInts x y
    let r ← liftJ (JInt.remInt p.1 p.2)
    pure ⟨_, r⟩
  else do
    let u : JInt .u64 := JInt.rem .u64 (absSigned y)
    let p ← promoteInts x u
    let r ← liftJ (JInt.remInt p.1 p.2)
    pure ⟨_, r⟩

/-- `iseven(n::Real) = isinteger(n) && iszero(rem(Integer(n), 2))`, `base/int.jl:181`. -/
def iseven {s : IntTy} (n : JInt s) : R Bool := do
  let r ← remByInt n (JInt.lit .i64 2)
  pure (decide (r.2.val = 0))

/-- `mod1(x::Real, y::Real) = mod1(promote(x, y)...)` (`base/promotion.jl:522`), then
`mod1(x::T, y::T) = (m = mod(x, y); iszero(m) ? y : m)` (`base/operators.jl:914`) with the
same-type `mod` of `base/int.jl:331-351`. -/
def mod1 {s t : IntTy} (x : JInt s) (y : JInt t) : R (JInt (IntTy.promote s t)) := do
  let p ← promoteInts x y
  let m ← liftJ (JInt.mod p.1 p.2)
  pure (if m.val = 0 then p.2 else m)

/-- `mod(x, y)` for `y::Int`: `mod(x::Unsigned, y::Signed)` (`base/int.jl:347-350`:
`remval = signed(rem(x, y))`, then `remval + (!iszero(remval) && y < zero(y))*y`, the
`Bool*Int` product being `0` or `y`), otherwise `mod(x::Real, y::Real) =
mod(promote(x, y)...)` (`base/promotion.jl:521`) and the same-type method. -/
def modByInt {s : IntTy} (x : JInt s) (y : JInt64) : R AnyInt :=
  if s.signed then do
    let p ← promoteInts x y
    let m ← liftJ (JInt.mod p.1 p.2)
    pure ⟨_, m⟩
  else do
    let r ← remByInt x y
    let remval := JInt.rem r.1.toSigned r.2
    let c : JInt64 := if remval.val ≠ 0 ∧ y.val < 0 then y else JInt.lit .i64 0
    pure ⟨_, addMixed remval c⟩

end JuliaLean.Tuples


namespace JuliaLean.SortTuplesCov

open JuliaLean

/-- `ntupleany(f, n)`, `base/ntuple.jl:42-46`: reject negative lengths,
otherwise call `f` at the one-based indices and erase the element types to Any. -/
def ntupleAny {V : Type} (f : Nat → V) (n : Int) : Jl (List V) :=
  if n ≥ 0 then .ok ((List.range n.toNat).map fun i => f (i + 1))
  else .error (.argumentError "tuple length should be ≥ 0")

end JuliaLean.SortTuplesCov
