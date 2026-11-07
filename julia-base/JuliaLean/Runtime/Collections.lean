import JuliaLean.Core
import JuliaLean.Runtime.Float

namespace JuliaLean.Dicts

/-- Exceptions (and non-termination) of the modelled calls. -/
inductive DErr where
  /-- `KeyError(key)` -/
  | keyError
  /-- `TypeError(:var"dict key", K, key)` from `KeyTypeError`, `base/abstractdict.jl:15` -/
  | keyTypeError
  /-- `ArgumentError`, e.g. `pop!` of an empty `Dict` -/
  | argumentError
  /-- `UndefRefError` from reading a `#undef` key or value (never happens on a well-formed table) -/
  | undefRef
  /-- `throw(h)` in `ht_keyindex`, `base/dict.jl:246` (never happens on a well-formed table) -/
  | thrownDict
  /-- An error of a shared Julia primitive, e.g. `InexactError` from `convert` -/
  | jl (e : JlError)
  /-- The call never returns: a Julia loop runs forever -/
  | diverges
  deriving Repr, DecidableEq, Inhabited

abbrev DR (α : Type) := Except DErr α

/-- Hashing and comparison of keys of type `K`. -/
structure KeyOps (K : Type) where
  /-- `hash(key)::UInt` -/
  hash : K → JInt .u64
  /-- `key === k || isequal(key, k)` -/
  eq : K → K → Bool
  /-- `max_values(K)`, `base/abstractset.jl:92-103` (`typemax(Int)` for most types) -/
  maxValues : JInt .i64 := JInt.typemax .i64

/-- The `isequal`/`hash` contract of the `Dict` docstring (`base/dict.jl:35`,
`hash` docstring `base/hashing.jl:12-16`): `isequal` is an equivalence relation
and `isequal(x, y)` implies `hash(x) == hash(y)`. -/
structure KeyOps.Lawful {K : Type} (o : KeyOps K) : Prop where
  refl : ∀ a, o.eq a a = true
  symm : ∀ a b, o.eq a b = true → o.eq b a = true
  trans : ∀ a b c, o.eq a b = true → o.eq b c = true → o.eq a c = true
  hash_eq : ∀ a b, o.eq a b = true → o.hash a = o.hash b

/-- Pointwise update of a `Memory` modelled as a function: `m[i] = x`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (x : α) : Nat → α :=
  fun j => if j = i then x else f j

/-- The fields of `mutable struct Dict{K,V}`, `base/dict.jl:65-90`. -/
structure Table (K V : Type) where
  size : Nat
  slots : Nat → Nat
  keys : Nat → Option K
  vals : Nat → Option V
  ndel : Nat
  count : Nat
  age : JInt .u64
  idxfloor : Nat
  maxprobe : Nat
  popcursor : Nat


/-- How a value of type `Q` meets keys of type `K`. -/
structure Conv (Q K : Type) where
  /-- `x isa K` (with the value as a `K`) -/
  isa : Q → Option K
  /-- `convert(K, x)` -/
  convert : Q → DR K
  /-- `hash(x)` -/
  hash : Q → JInt .u64
  /-- `x === k || isequal(x, k)` -/
  iseq : Q → K → Bool
  /-- Whether the iterator element type is a subtype of the set key type. -/
  eltypeSubtype : Bool := false

/-- The chain of an `ImmutableDict`, most recent pair first
(`iterate`, `base/dict.jl:860-863`). -/
abbrev IDict (K V : Type) := List (K × V)

/-- The two keys `1` and `1.0`: `isequal` but not `===`. -/
inductive OneKey where
  | int | float
  deriving DecidableEq

end JuliaLean.Dicts

namespace JuliaLean.DictsCov

open JuliaLean.Dicts

/-- How a value of type `W` is stored in a `Memory{V}`. -/
structure VConv (W V : Type) where
  /-- `x isa V` (with the value as a `V`) -/
  isa : W → Option V
  /-- `convert(V, x)::V` -/
  convert : W → DR V

/-- Whether an iterator over a `Dict` yields keys (`KeySet`) or values (`ValueIterator`). -/
inductive Part where
  | keys
  | vals
  deriving DecidableEq

/-- An element of `keys(d)` or `values(d)`. -/
def Part.Elem (K V : Type) : Part → Type
  | .keys => K
  | .vals => V

/-- Exceptions thrown by the generic methods. -/
inductive GErr where
  /-- `KeyError(key)` -/
  | keyError
  /-- `MethodError` for the function `fn` -/
  | methodError (fn : String)
  /-- `error(msg)` -/
  | errorException (msg : String)
  /-- `ArgumentError(msg)` -/
  | argumentError (msg : String)
  /-- An exception of a concrete dictionary type or of `convert` -/
  | dict (e : DErr)
  deriving Repr, DecidableEq

abbrev GR (α : Type) := Except GErr α

/-- Lift an error of the `Dict` model. -/
def liftD {α : Type} : DR α → GR α
  | .ok a => .ok a
  | .error e => .error (.dict e)

/-- A Julia type `AbstractDict{K,V}` subtype: its name and parameters. -/
structure DictTy (T : Type) where
  name : String
  K : T
  V : T
  deriving Repr, DecidableEq

/-- The interface of a concrete `AbstractDict` type used by the generic methods. -/
structure DictOps (T D K V : Type) where
  /-- `for (k, v) in d` -/
  pairs : D → List (K × V)
  /-- `get(d, k, secret_table_token)`, `none` for the token -/
  get : D → K → Option V
  /-- `setindex!(d, v, k)` -/
  setindex : D → V → K → GR D
  /-- `delete!(d, k)` -/
  delete : D → K → GR D
  /-- `empty(d, K, V)` -/
  emptyT : D → T → T → D
  /-- `empty!(d)` -/
  emptyBang : D → GR D
  /-- `length(d)` -/
  length : D → Nat
  /-- `sizehint!(d, n; shrink = false)` -/
  sizehint : D → Nat → D
  /-- `haslength(d)` (`IteratorSize(d) isa HasLength`) -/
  hasLength : D → Bool
  /-- `typeof(d)` -/
  typeOf : D → DictTy T

end JuliaLean.DictsCov

namespace JuliaLean.DictsCov.EqTable

/-- A key slot: `NULL`, the deletion marker `nothing`, or an `Int` key. -/
inductive KSlot where
  | null
  | nothing
  | key (k : Int)
  deriving Repr, DecidableEq

/-- `d.ht`: pairs `(key slot, value or NULL)`, slot `i` at `ht[2i], ht[2i+1]`. -/
abbrev Mem := List (KSlot × Option Int)

/-- `mutable struct IdDict{Int,Int}`, base/iddict.jl:25-31. -/
structure IdD where
  ht : Mem
  count : Nat
  ndel : Nat
  deriving Repr, DecidableEq

end JuliaLean.DictsCov.EqTable

namespace JuliaLean.IdDicts

/-- Julia values used as keys, values and elements. -/
inductive JVal where
  | int (n : Int)
  | flt (n : Int)
  | sym (s : String)
  | str (s : String)
  | vec (id : Nat) (c : Int)
  | fvec (id : Nat) (c : Int)
  | nothing
  deriving Repr, DecidableEq

/-- Julia types used as type parameters. -/
inductive JTy where
  | any | int | flt | sym | str | vec | fvec | nothing
  deriving Repr, DecidableEq

/-- Exceptions of the modelled calls (types only). -/
inductive IErr where
  | keyError
  /-- `TypeError`: `KeyTypeError` (base/abstractdict.jl:15) or a failed `::T` -/
  | typeError
  /-- `MethodError` from `convert` -/
  | methodError
  | argumentError
  /-- `ErrorException`, e.g. from `finalizer` on an immutable (base/gcutils.jl:44) -/
  | errorException
  /-- a failed `@assert` -/
  | assertionError
  deriving Repr, DecidableEq

/-- A call's final state together with its result: Julia mutates in place,
so a call that throws after a mutation leaves the mutated state. -/
abbrev Out (σ α : Type) := σ × Except IErr α

/-- `decide` on call results. -/
instance instDecidableEqExceptIErr {α} [DecidableEq α] : DecidableEq (Except IErr α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (by intro h'; cases h'; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

end JuliaLean.IdDicts

namespace JuliaLean.BitSetsCov.Coll

abbrev SetState := List Nat

def insert (s : SetState) (x : Nat) : SetState :=
  if x ∈ s then s else s ++ [x]

def ofList (xs : List Nat) : SetState := xs.foldl insert []

def erase (s : SetState) (x : Nat) : SetState := s.erase x

end JuliaLean.BitSetsCov.Coll

namespace JuliaLean.Reduce

open JuliaLean.Float

/-- A Julia value. -/
inductive Val where
  | int (t : IntTy) (x : JInt t)
  | f64 (x : F64)
  | bool (b : Bool)
  | missing
  deriving DecidableEq

/-- A Julia element type: concrete types, `Union{a, b}` and `Union{}` (`bottom`). -/
inductive Ty where
  | int (t : IntTy)
  | f64
  | bool
  | missing
  | union (a b : Ty)
  | bottom
  deriving DecidableEq, Repr

namespace Val

/-- `Float64(v)` for a real number. -/
def toF64 : Val → F64
  | .int _ x => F64.ofJInt x
  | .f64 x => x
  | .bool b => if b then F64.one else F64.zero
  | .missing => F64.nan

/-- `T(b)` for a `Bool` and an integer type. -/
def boolInt (t : IntTy) (b : Bool) : JInt t := JInt.lit t (if b then 1 else 0)

/-- Binary arithmetic after promotion: `missing` absorbs (`base/missing.jl:116-127`), two
integers meet in `IntTy.promote` with wrapping conversion, a `Bool` meets an integer in the
integer's type, anything meeting a `Float64` becomes `Float64`. -/
def numBin (opI : (t : IntTy) → JInt t → JInt t → Val) (opF : F64 → F64 → Val)
    (opB : Bool → Bool → Val) : Val → Val → Val
  | .missing, _ => .missing
  | _, .missing => .missing
  | .int s x, .int t y =>
    let p := IntTy.promote s t
    opI p (JInt.rem p x) (JInt.rem p y)
  | .bool a, .int t y => opI t (boolInt t a) y
  | .int t x, .bool b => opI t x (boolInt t b)
  | .bool a, .bool b => opB a b
  | x, y => opF (toF64 x) (toF64 y)

end Val

end JuliaLean.Reduce

namespace JuliaLean.base.reduce

inductive FoldInit (α : Type) where
  | initial
  | value (x : α)
  deriving Repr

inductive MappingIdentity where
  | identity | abs | abs2 | other
  deriving Repr, DecidableEq

class MapCallable (F : Type) (Input : Type) (Output : outParam Type) where
  apply : F → Input → Output
  mappingKind : F → MappingIdentity := fun _ => .other
  isIdentity : F → Bool := fun _ => false
  identityTypes : ∀ f, isIdentity f = true → Input = Output := by intros; contradiction
  identityValues : ∀ f x, isIdentity f = true → HEq (apply f x) x := by intros; contradiction

inductive JIterator : Type → Type 1 where
  | values {α : Type} (xs : List α) : JIterator α
  | generator {F α β : Type} [MapCallable F α β] (f : F) (itr : JIterator α) : JIterator β
  | filter {α : Type} (predicate : α → Bool) (itr : JIterator α) : JIterator α
  | flatten {α : Type} (itr : JIterator (List α)) : JIterator α

structure EmptyReducer (Result : Type) where
  empty : Jl Result

structure MappingEmptyCall (Result : Type) where
  Arg : Type
  emptyOp : EmptyReducer Arg
  apply : Arg → Jl Result
  zero : Jl Arg


structure Reducer (Acc Input : Type) where
  first : Input → FoldInit Acc
  step : FoldInit Acc → Input → FoldInit Acc
  empty : Jl Acc
  mappingAbs : MappingEmptyCall Acc :=
    ⟨Acc, ⟨empty⟩, fun _ => .error (.methodError "abs"), .error (.methodError "zero")⟩
  mappingAbs2 : MappingEmptyCall Acc :=
    ⟨Acc, ⟨empty⟩, fun _ => .error (.methodError "abs2"), .error (.methodError "zero")⟩
  isMax : Bool := false

inductive EltypeStatus where
  | hasEltype
  | unknown
  deriving Repr, DecidableEq

end JuliaLean.base.reduce

namespace JuliaLean.ReduceCov.Indices

/-- The range types wrapped here. -/
inductive RT where
  | oneTo
  | unitRange
  deriving DecidableEq, Repr

/-- Types for the promotion rules: `Slice{R}`, `IdentityUnitRange{R}`, the UnionAlls
`Slice` and `IdentityUnitRange`, and `LinearIndices{N, Tuple{R...}}`. -/
inductive WT where
  | slice (r : RT)
  | ident (r : RT)
  | sliceAll
  | identAll
  | linIdx (rs : List RT)
  deriving DecidableEq, Repr

/-- Element types that `el_same` compares: `Int` or a range type. -/
inductive ElT where
  | int
  | range (r : RT)
  deriving DecidableEq, Repr

/-- `eltype` of a wrapper type: every `Slice` and `IdentityUnitRange` has `Int` elements. -/
def WT.eltype : WT → ElT
  | _ => .int

/-- `promote_typejoin(a, b)` of two wrapper types. -/
def WT.typejoin (a b : WT) : WT :=
  if a = b then a else match a with
    | .slice _ | .sliceAll => .sliceAll
    | _ => .identAll

end JuliaLean.ReduceCov.Indices

namespace JuliaLean.base.reduce

instance {Input Output : Type} : MapCallable (Input → Output) Input Output where
  apply := fun f x => f x

end JuliaLean.base.reduce

namespace JuliaLean.base.abstractset

open JuliaLean

/-- The type token inspected by `max_values`. -/
inductive JuliaType where
  | other
  | bitInteger (t : IntTy)
  | bool
  | nothing
  | union (a b : JuliaType)
  deriving Repr, DecidableEq

end JuliaLean.base.abstractset
