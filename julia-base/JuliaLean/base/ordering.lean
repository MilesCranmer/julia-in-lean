import JuliaLean.Core
import JuliaLean.base.tuple

namespace JuliaLean.base.ordering

inductive OrderingError where
  | boundsError
  | typeError
  | errorException (message : String)
  deriving Repr, DecidableEq, Inhabited

abbrev OrderingResult (α : Type) := Except OrderingError α

class Ordering (O : Type) : Prop where

structure ForwardOrdering where

instance : Ordering ForwardOrdering := ⟨⟩

def Forward : ForwardOrdering := {}

structure ReverseOrdering (Fwd : Type) [Ordering Fwd] where
  fwd : Fwd

instance {Fwd : Type} [Ordering Fwd] : Ordering (ReverseOrdering Fwd) := ⟨⟩

structure By (T O : Type) where
  callable : T
  order : O

instance {T O : Type} : Ordering (By T O) := ⟨⟩

structure Lt (A : Type) where
  lt : A → A → OrderingResult Bool

instance {A : Type} : Ordering (Lt A) := ⟨⟩

structure Perm (O V : Type) where
  order : O
  data : V

instance {O V : Type} : Ordering (Perm O V) := ⟨⟩

def Reverse : ReverseOrdering ForwardOrdering := ⟨Forward⟩


/-! ## Source-backed constructor methods -/

/--
Julia source: base/ordering.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReverseOrdering(rev::ReverseOrdering) = rev.fwd
```
-/
def reverseOrdering_unwrap {Fwd : Type} [Ordering Fwd] (rev : ReverseOrdering Fwd) : Fwd :=
  rev.fwd

/--
Julia source: base/ordering.jl:47-47 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReverseOrdering(fwd::Fwd) where {Fwd} = ReverseOrdering{Fwd}(fwd)
```
-/
def reverseOrdering_wrap {Fwd : Type} [Ordering Fwd] (fwd : Fwd) : ReverseOrdering Fwd :=
  ⟨fwd⟩

/--
Julia source: base/ordering.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReverseOrdering() = ReverseOrdering(ForwardOrdering())
```
-/
def reverseOrdering_default : ReverseOrdering ForwardOrdering :=
  reverseOrdering_wrap (ForwardOrdering.mk)

/--
Julia source: base/ordering.jl:56-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reverse(o::Ordering) = ReverseOrdering(o)
```
-/
def reverseOrdering {O : Type} [Ordering O] (o : O) : ReverseOrdering O :=
  reverseOrdering_wrap o

/--
Julia source: base/ordering.jl:86-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
By(by) = By(by, Forward)
```
-/
def byDefault {T : Type} (keyFn : T) : By T ForwardOrdering :=
  ⟨keyFn, Forward⟩

/--
Julia source: base/ordering.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReverseOrdering(by::By) = By(by.by, ReverseOrdering(by.order))
```
-/
def reverseOrdering_by {T O : Type} [Ordering O] (byValue : By T O) : By T (ReverseOrdering O) :=
  ⟨byValue.callable, reverseOrdering_wrap byValue.order⟩

/--
Julia source: base/ordering.jl:111-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ReverseOrdering(perm::Perm) = Perm(ReverseOrdering(perm.order), perm.data)
```
-/
def reverseOrdering_perm {O V : Type} [Ordering O] (perm : Perm O V) : Perm (ReverseOrdering O) V :=
  ⟨reverseOrdering_wrap perm.order, perm.data⟩

/-! ## Source-backed comparisons -/

/--
Julia source: base/ordering.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lt(o::ForwardOrdering,       a, b) = isless(a,b)
```
-/
def ltForward {A : Type} (_o : ForwardOrdering) (isless : A → A → OrderingResult Bool)
    (a b : A) : OrderingResult Bool :=
  isless a b

/--
Julia source: base/ordering.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lt(o::ReverseOrdering,       a, b) = lt(o.fwd,b,a)
```
-/
def ltReverse {O A B : Type} [Ordering O] (o : ReverseOrdering O)
    (lt : O → A → A → OrderingResult B) (a b : A) : OrderingResult B :=
  lt o.fwd b a

/--
Julia source: base/ordering.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lt(o::By,                    a, b) = lt(o.order,o.by(a),o.by(b))
```
-/
def ltBy {T O A K : Type} (o : By T O) (apply : T → A → OrderingResult K)
    (lt : O → K → K → OrderingResult Bool) (a b : A) : OrderingResult Bool :=
  match apply o.callable a with
  | .error e => .error e
  | .ok ka =>
    match apply o.callable b with
    | .error e => .error e
    | .ok kb => lt o.order ka kb

/--
Julia source: base/ordering.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lt(o::Lt,                    a, b) = o.lt(a,b)
```
-/
def ltLt {A : Type} (o : Lt A) (a b : A) : OrderingResult Bool :=
  o.lt a b

/--
Julia source: base/ordering.jl:123-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function lt(p::Perm, a::Integer, b::Integer)
    da = p.data[a]
    db = p.data[b]
    (lt(p.order, da, db)::Bool) | (!(lt(p.order, db, da)::Bool) & (a < b))
end
```
-/
def assertBool : Option Bool → OrderingResult Bool
  | .some value => .ok value
  | .none => .error .typeError

def ltPerm {O V I A : Type} [Ordering O] (p : Perm O V)
    (lt : O → A → A → OrderingResult (Option Bool)) (get : V → I → OrderingResult A)
    (indexLess : I → I → OrderingResult Bool) (a b : I) : OrderingResult Bool :=
  match get p.data a with
  | .error e => .error e
  | .ok da =>
    match get p.data b with
    | .error e => .error e
    | .ok db =>
      match lt p.order da db with
      | .error e => .error e
      | .ok abValue =>
        match assertBool abValue with
        | .error e => .error e
        | .ok ab =>
          match lt p.order db da with
          | .error e => .error e
          | .ok baValue =>
            match assertBool baValue with
            | .error e => .error e
            | .ok ba =>
              match indexLess a b with
              | .error e => .error e
              | .ok indexResult => .ok (ab || (!ba && indexResult))

/-! ## `_ord` and `_by` models -/

inductive KeyArg : Type → Type → Type 1 where
  | identity {A : Type} : KeyArg A A
  | transform {A K T : Type} (fn : T) (apply : T → A → OrderingResult K) : KeyArg A K

abbrev KeyedOrdering {A K : Type} : KeyArg A K → Type → Type
  | .identity, O => O
  | .transform (T := T) _ _, O => By T O
inductive OrderArg (A : Type) where
  | forward (o : ForwardOrdering) (isless : A → A → OrderingResult Bool)
  | reverseForward (o : ReverseOrdering ForwardOrdering)
      (isless : A → A → OrderingResult Bool)
  | other {O : Type} [Ordering O] (o : O) (lt : O → A → A → OrderingResult Bool)

/--
Julia source: base/ordering.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_by(by, order::Ordering) = By(by, order)
```
-/
def byGeneric {T O : Type} (fn : T) (order : O) : By T O :=
  ⟨fn, order⟩

/--
Julia source: base/ordering.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_by(::typeof(identity), order::Ordering) = order
```
-/
def byIdentity {A O : Type} (_identity : A → A) (order : O) : O :=
  order

def _by {A K O : Type} (byArg : KeyArg A K) (order : O) :
    KeyedOrdering byArg O :=
  match byArg with
  | .identity => byIdentity (A := A) (fun x => x) order
  | .transform fn _ => byGeneric fn order

def reverseKeyedOrdering {A K O : Type} [Ordering O] (byArg : KeyArg A K)
    (order : KeyedOrdering byArg O) : KeyedOrdering byArg (ReverseOrdering O) :=
  match byArg with
  | .identity => reverseOrdering order
  | .transform _ _ => reverseOrdering_by order

inductive OrdResult (A K : Type) where
  | plain {O : Type} (inst : Ordering O) (inner : O)
      (compare : O → A → A → OrderingResult Bool) : OrdResult A K
  | keyed {T O : Type} (inst : Ordering O) (inner : By T O)
      (apply : T → A → OrderingResult K)
      (compare : O → K → K → OrderingResult Bool) : OrdResult A K

def ordCompare {A K : Type} (o : OrdResult A K) (a b : A) : OrderingResult Bool :=
  match o with
  | .plain _ inner compare => compare inner a b
  | .keyed _ inner apply compare => ltBy inner apply compare a b

def ordResultReverse {A K : Type} (o : OrdResult A K) : OrdResult A K :=
  match o with
  | .plain (O := O) inst inner compare =>
      letI : Ordering O := inst
      .plain (inferInstance : Ordering (ReverseOrdering O))
        (reverseOrdering inner) (fun reversed a b => ltReverse reversed compare a b)
  | .keyed (O := O) inst inner apply compare =>
      letI : Ordering O := inst
      .keyed (inferInstance : Ordering (ReverseOrdering O))
        (reverseOrdering_by inner) apply
        (fun reversed a b => ltReverse reversed compare a b)

def packageOrd {A K O : Type} [Ordering O] (byArg : KeyArg A K)
    (order : KeyedOrdering byArg O)
    (compare : O → K → K → OrderingResult Bool) : OrdResult A K :=
  match byArg with
  | .identity => .plain inferInstance order (fun o a b => compare o a b)
  | .transform _ apply => .keyed inferInstance order apply compare
/--
Julia source: base/ordering.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt::typeof(isless), by, order::Ordering)                         = _by(by, order)
```
-/
def ordIslessGeneric {A K O : Type} [Ordering O] (keyArg : KeyArg A K) (order : O) :
    KeyedOrdering keyArg O :=
  _by keyArg order

/--
Julia source: base/ordering.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt::typeof(isless), by, order::ForwardOrdering)                  = _by(by, order)  # disambiguation
```
-/
def ordIslessForward {A K : Type} (keyArg : KeyArg A K) (order : ForwardOrdering) :
    KeyedOrdering keyArg ForwardOrdering :=
  _by keyArg order

/--
Julia source: base/ordering.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt::typeof(isless), by, order::ReverseOrdering{ForwardOrdering}) = _by(by, order)  # disambiguation
```
-/
def ordIslessReverseForward {A K : Type} (keyArg : KeyArg A K)
    (order : ReverseOrdering ForwardOrdering) :
    KeyedOrdering keyArg (ReverseOrdering ForwardOrdering) :=
  _by keyArg order

/--
Julia source: base/ordering.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt,                 by, order::ForwardOrdering)                  = _by(by, Lt(lt))
```
-/
def ordCustomForward {A K : Type} (lt : K → K → OrderingResult Bool)
    (keyArg : KeyArg A K) (_order : ForwardOrdering) : KeyedOrdering keyArg (Lt K) :=
  _by keyArg ⟨lt⟩

/--
Julia source: base/ordering.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt,                 by, order::ReverseOrdering{ForwardOrdering}) = reverse(_by(by, Lt(lt)))
```
-/
def ordCustomReverseForward {A K : Type} (lt : K → K → OrderingResult Bool)
    (keyArg : KeyArg A K) (_order : ReverseOrdering ForwardOrdering) :
    KeyedOrdering keyArg (ReverseOrdering (Lt K)) :=
  reverseKeyedOrdering keyArg (_by keyArg ⟨lt⟩)

/--
Julia source: base/ordering.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt,                 by, order::Ordering) = error("Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")
```
-/
def ordCustomOther {A K O : Type} [Ordering O] (_lt : K → K → OrderingResult Bool)
    (_by : KeyArg A K) (_order : O) (_compare : O → K → K → OrderingResult Bool) :
    Except OrderingError (OrdResult A K) :=
  .error (.errorException
    "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")

def ordDispatch {A K : Type}
    (lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool))
    (keyArg : KeyArg A K) (order : OrderArg K) : Except OrderingError (OrdResult A K) := do
  match lt, order with
  | .inl isless, .forward o _ =>
      pure (packageOrd keyArg (ordIslessForward keyArg o)
        (fun f a b => ltForward f isless a b))
  | .inl isless, .reverseForward o _ =>
      pure (packageOrd keyArg (ordIslessReverseForward keyArg o)
        (fun reversed a b =>
          ltReverse reversed (fun f x y => ltForward f isless x y) a b))
  | .inl _, @OrderArg.other _ O inst o compare => do
      letI : Ordering O := inst
      pure (packageOrd keyArg (ordIslessGeneric keyArg o) compare)
  | .inr custom, .forward o _ =>
      pure (packageOrd keyArg (ordCustomForward custom keyArg o)
        (fun inner a b => ltLt inner a b))
  | .inr custom, .reverseForward o _ =>
      pure (packageOrd keyArg (ordCustomReverseForward custom keyArg o)
        (fun reversed a b =>
          ltReverse reversed (fun inner x y => ltLt inner x y) a b))
  | .inr custom, @OrderArg.other _ O inst o compare => do
      letI : Ordering O := inst
      ordCustomOther custom keyArg o compare

/--
Julia source: base/ordering.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ord(lt, by, rev::Nothing, order::Ordering=Forward) = _ord(lt, by, order)
```
-/
def ordNothing {A K : Type} (lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool))
    (keyArg : KeyArg A K) (_rev : Unit) (order : OrderArg K) :
    Except OrderingError (OrdResult A K) :=
  ordDispatch lt keyArg order

/--
Julia source: base/ordering.jl:157-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ord(lt, by, rev::Bool, order::Ordering=Forward)
    o = _ord(lt, by, order)
    return rev ? ReverseOrdering(o) : o
end
```
-/
def ordBool {A K : Type} (lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool))
    (keyArg : KeyArg A K) (rev : Bool) (order : OrderArg K) :
    Except OrderingError (OrdResult A K) :=
  match ordDispatch lt keyArg order with
  | .error e => .error e
  | .ok o => .ok (if rev then ordResultReverse o else o)

/-! ## `ordtype` methods -/

structure TypeToken where
  name : String
  deriving Repr, DecidableEq, Inhabited

structure OrdtypeCall (O : Type) where
  call : {V : Type} → O → V → TypeToken

def anyType : TypeToken := ⟨"Any"⟩

/--
Julia source: base/ordering.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ordtype(o::ReverseOrdering, vs::AbstractArray) = ordtype(o.fwd, vs)
```
-/
def ordtypeReverse {O V : Type} [Ordering O] (ordtype : OrdtypeCall O)
    (o : ReverseOrdering O) (vs : V) : TypeToken :=
  ordtype.call o.fwd vs

/--
Julia source: base/ordering.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ordtype(o::Perm,            vs::AbstractArray) = ordtype(o.order, o.data)
```
-/
def ordtypePerm {O V W : Type} [Ordering O] (ordtype : OrdtypeCall O)
    (o : Perm O V) (_vs : W) : TypeToken :=
  ordtype.call o.order o.data

/--
Julia source: base/ordering.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ordtype(o::By,              vs::AbstractArray) = try typeof(o.by(vs[1])) catch; Any end
```
-/
def ordtypeBy {T A K O V : Type} (getFirst : V → OrderingResult A)
    (apply : T → A → OrderingResult K) (typeof : K → TypeToken) (o : By T O)
    (vs : V) : TypeToken :=
  match getFirst vs with
  | .error _ => anyType
  | .ok x => match apply o.callable x with
    | .error _ => anyType
    | .ok key => typeof key

/--
Julia source: base/ordering.jl:174-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ordtype(o::Ordering,        vs::AbstractArray) = eltype(vs)
```
-/
def ordtypeOrdering {O V : Type} [Ordering O] (eltype : V → TypeToken)
    (_o : O) (vs : V) : TypeToken :=
  eltype vs

end JuliaLean.base.ordering

namespace JuliaLean.Sort

/-- Constructor-normal orderings from `base/ordering.jl:31-111`.
`forward` and `custom` carry the underlying `isless` and `Lt` comparisons;
the Boolean records their optional ReverseOrdering wrapper. By and Perm
remain outside that wrapper, as required by the specialized constructors.
Explicit parametric ReverseOrdering constructors that bypass those methods
are outside this representation. Data lookup in Perm is restricted to valid indices. -/
inductive Ordering : Type → Type 1 where
  | forward {α : Type} (cmp : α → α → Bool) (rev : Bool := false) : Ordering α
  | custom {α : Type} (cmp : α → α → Bool) (rev : Bool := false) : Ordering α
  | by {α β : Type} (f : α → β) (order : Ordering β) : Ordering α
  | perm {α : Type} (order : Ordering α) (data : Int → α) : Ordering Int

/-- `ReverseOrdering` dispatch, `base/ordering.jl:46-48,110-111`. -/
def reverseOrdering : Ordering α → Ordering α
  | .forward cmp rev => .forward cmp (!rev)
  | .custom cmp rev => .custom cmp (!rev)
  | .by f order => .by f (reverseOrdering order)
  | .perm order data => .perm (reverseOrdering order) data

/-- `lt`, including the eager Boolean Perm tie breaker,
`base/ordering.jl:118-127`. -/
def orderingLt : Ordering α → α → α → Bool
  | .forward cmp rev, a, b => if rev then cmp b a else cmp a b
  | .custom cmp rev, a, b => if rev then cmp b a else cmp a b
  | .by f order, a, b => orderingLt order (f a) (f b)
  | .perm order data, a, b =>
      orderingLt order (data a) (data b) ||
        (!(orderingLt order (data b) (data a)) && decide (a < b))

/-- Function identity is part of Julia dispatch, rather than extensional equality. -/
inductive ByArg (α : Type) where
  | identity
  | transform (f : α → α)

/-- `_by`, `base/ordering.jl:136-137`. -/
def applyBy (key : ByArg α) (order : Ordering α) : Ordering α :=
  match key with
  | .identity => order
  | .transform f => .by f order

/-- `_ord`, `base/ordering.jl:130-137`. `none` denotes the actual `isless`
function object; `some` denotes a custom comparator. Ambiguous arguments
produce Julia's ErrorException, represented separately because Core has no
ErrorException constructor. -/
def baseOrd (cmp : Option (α → α → Bool)) (key : ByArg α)
    (order : Ordering α) : Except String (Ordering α) :=
  match cmp with
  | none => .ok (applyBy key order)
  | some f => match order with
    | .forward _ false => .ok (applyBy key (.custom f))
    | .forward _ true => .ok (reverseOrdering (applyBy key (.custom f)))
    | _ => .error "ErrorException: Passing both lt= and order= arguments is ambiguous"

/-- `ord`, `base/ordering.jl:155-160`; Nothing and false leave `_ord` unchanged. -/
def ord (cmp : Option (α → α → Bool)) (key : ByArg α)
    (rev : Option Bool) (order : Ordering α) : Except String (Ordering α) := do
  let o ← baseOrd cmp key order
  pure (if rev == some true then reverseOrdering o else o)

end JuliaLean.Sort


/-!
Model of `base/ordering.jl` (module `Base.Order`, master `bbfa0ce4150`).

Orderings compare values of a universe `V`. `isl` is `isless` on `V`; `idx`
reads the `Integer` value of an argument of `lt(::Perm, a, b)`. A Julia
vector is the `List V` of its elements, indexed from 1; `eltypeOf` gives the
element type of a vector and `typeOf` the type of a value, both opaque.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds)

/-- The `Ordering` structs of `base/ordering.jl:29-108`: `ForwardOrdering()`,
`ReverseOrdering{Fwd}(fwd)`, `By(by, order)`, `Lt(lt)` and `Perm(order, data)`. -/
inductive Ordering (V : Type) where
  | forward
  | rev (fwd : Ordering V)
  | by (f : V → V) (order : Ordering V)
  | ltf (f : V → V → Bool)
  | perm (order : Ordering V) (data : List V)

namespace Ordering

variable {V : Type}

/-- `ReverseOrdering(x)`: `ReverseOrdering(rev::ReverseOrdering) = rev.fwd`
(`base/ordering.jl:46`), `ReverseOrdering(by::By) = By(by.by, ReverseOrdering(by.order))`
(`:110`), `ReverseOrdering(perm::Perm) = Perm(ReverseOrdering(perm.order), perm.data)`
(`:111`), and otherwise `ReverseOrdering{Fwd}(fwd)` (`:47`). -/
def reverseOrdering : Ordering V → Ordering V
  | .rev fwd => fwd
  | .by f o => .by f (reverseOrdering o)
  | .perm o d => .perm (reverseOrdering o) d
  | .forward => .rev .forward
  | .ltf f => .rev (.ltf f)

/-- `ReverseOrdering() = ReverseOrdering(ForwardOrdering())`, `base/ordering.jl:48`;
this is the constant `Reverse` (`:72`). -/
def reverseDefault : Ordering V := reverseOrdering .forward

/-- `reverse(o::Ordering) = ReverseOrdering(o)`, `base/ordering.jl:56`. -/
def reverse (o : Ordering V) : Ordering V := reverseOrdering o

/-- `By(by) = By(by, Forward)`, `base/ordering.jl:86`. -/
def byDefault (f : V → V) : Ordering V := .by f .forward

/-- `lt(o, a, b)`, `base/ordering.jl:118-127`. The `Perm` method reads
`p.data[a]` and `p.data[b]` with bounds checking, evaluates both comparisons
(non-short-circuit `|` and `&`), and breaks ties by `a < b`. -/
def lt (isl : V → V → Bool) (idx : V → Int) : Ordering V → V → V → R Bool
  | .forward, a, b => .ok (isl a b)
  | .rev fwd, a, b => lt isl idx fwd b a
  | .by f o, a, b => lt isl idx o (f a) (f b)
  | .ltf f, a, b => .ok (f a b)
  | .perm o d, a, b => do
    let da ← getfield d (idx a)
    let db ← getfield d (idx b)
    let x ← lt isl idx o da db
    let y ← lt isl idx o db da
    pure (x || (!y && decide (idx a < idx b)))

/-- The `lt` keyword of `ord`: the function `isless` itself, or any other function. -/
inductive LtArg (V : Type) where
  | isless
  | fn (f : V → V → Bool)

/-- The `by` keyword of `ord`: the function `identity` itself, or any other function. -/
inductive ByArg (V : Type) where
  | identity
  | fn (f : V → V)

/-- `_by(by, order) = By(by, order)`, `_by(::typeof(identity), order) = order`,
`base/ordering.jl:136-137`. -/
def by_ (b : ByArg V) (o : Ordering V) : Ordering V :=
  match b with
  | .identity => o
  | .fn f => .by f o

/-- `_ord(lt, by, order)`, `base/ordering.jl:130-135`: with `lt === isless` the
order is kept (`:130-132`); otherwise `Forward` becomes `Lt(lt)` (`:133`),
`ReverseOrdering{ForwardOrdering}` becomes `reverse(_by(by, Lt(lt)))` (`:134`),
and every other order throws `ErrorException` (`:135`). -/
def ord_ (l : LtArg V) (b : ByArg V) (o : Ordering V) : R (Ordering V) :=
  match l, o with
  | .isless, o => .ok (by_ b o)
  | .fn f, .forward => .ok (by_ b (.ltf f))
  | .fn f, .rev .forward => .ok (reverse (by_ b (.ltf f)))
  | .fn _, _ => .error .errorException

/-- `ord(lt, by, rev::Nothing, order) = _ord(lt, by, order)` (`base/ordering.jl:155`)
and `ord(lt, by, rev::Bool, order)`, which reverses when `rev` (`:157-160`). -/
def ord (l : LtArg V) (b : ByArg V) (rev : Option Bool) (o : Ordering V) : R (Ordering V) :=
  match rev with
  | none => ord_ l b o
  | some r => do
    let o' ← ord_ l b o
    pure (if r then reverseOrdering o' else o')

/-- `ordtype(o, vs)`, `base/ordering.jl:170-174`. `vs[1]` of an empty vector
throws, which the `try` turns into `Any`. -/
def ordtype {T : Type} (typeOf : V → T) (eltypeOf : List V → T) (anyT : T) :
    Ordering V → List V → T
  | .rev fwd, vs => ordtype typeOf eltypeOf anyT fwd vs
  | .perm o d, _ => ordtype typeOf eltypeOf anyT o d
  | .by f _, vs => match vs with
    | [] => anyT
    | x :: _ => typeOf (f x)
  | .forward, vs => eltypeOf vs
  | .ltf _, vs => eltypeOf vs

end Ordering

open Ordering

variable {V : Type}

end JuliaLean.SortTuplesCov


/-! Generic coverage models for the `base/ordering.jl` overloads whose input
may contain user-defined `Ordering` subtypes.  The existing executable model
covers Base's concrete constructors; these wrappers retain an arbitrary
underlying order and its callbacks. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean.Tuples (R Err)

structure GenericReverse (O : Type) where
  fwd : O

structure GenericBy (F O : Type) where
  key : F
  order : O

structure GenericPerm (O D : Type) where
  order : O
  data : D

/-- Constructors at `base/ordering.jl:46-47,110-111`. -/
def reverseUnwrap {O : Type} (rev : GenericReverse O) : O := rev.fwd
def reverseWrap {O : Type} (isOrdering : O → Bool) (o : O) : R (GenericReverse O) :=
  if isOrdering o then .ok ⟨o⟩ else .error .typeError
def reverseBy {F O : Type} (reverse : O → R O) (o : GenericBy F O) : R (GenericBy F O) := do
  pure ⟨o.key, (← reverse o.order)⟩
def reversePerm {O D : Type} (reverse : O → O) (o : GenericPerm O D) : GenericPerm O D :=
  ⟨reverse o.order, o.data⟩

/-- `reverse(o::Ordering) = ReverseOrdering(o)`, `base/ordering.jl:56`. -/
def reverseMethod {O R : Type} (reverseOrdering : O → R) (o : O) : R := reverseOrdering o

inductive Compared where
  | bool (value : Bool)
  | other

def assertBool : Compared → R Bool
  | .bool b => .ok b
  | .other => .error .typeError

/-- `lt(p::Perm,a,b)`, `base/ordering.jl:123-127`.  Both order comparisons
are evaluated and asserted Bool before eager `|` and `&` combine them. -/
def permLtExact {V : Type} (get : Int → R V) (compare : V → V → R Compared)
    (a b : Int) : R Bool := do
  let da ← get a
  let db ← get b
  let ab ← compare da db >>= assertBool
  let ba ← compare db da >>= assertBool
  pure (ab || (!ba && decide (a < b)))

inductive ExistingOrder (O V : Type) where
  | existing (o : O)
  | forward
  | reverseForward
  | by (f : V → V) (order : ExistingOrder O V)
  | lt (f : V → V → Bool)
  | reverse (order : ExistingOrder O V)

def genericBy {O V : Type} (identity : Bool) (f : V → V)
    (o : ExistingOrder O V) : ExistingOrder O V := if identity then o else .by f o

/-- `_ord`, `_by`, and `ord`, `base/ordering.jl:130-160`, retaining arbitrary
existing order values for the isless path. -/
def genericOrd {O V : Type} (islessArg identityBy reverseResult : Bool)
    (keyFn : V → V) (lt : V → V → Bool) (o : ExistingOrder O V) : Except String (ExistingOrder O V) :=
  let base : Except String (ExistingOrder O V) :=
    if islessArg then Except.ok (genericBy identityBy keyFn o) else
    match o with
    | .forward => Except.ok (genericBy identityBy keyFn (.lt lt))
    | .reverseForward => Except.ok (.reverse (genericBy identityBy keyFn (.lt lt)))
    | _ => Except.error "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)"
  match base with
  | .error e => .error e
  | .ok result => .ok (if reverseResult then .reverse result else result)

/-- Generic `ordtype` overloads, `base/ordering.jl:170-174`. -/
def ordtypeReverseGeneric {O V T : Type} (ordtype : O → List V → T)
    (o : GenericReverse O) (vs : List V) : T := ordtype o.fwd vs
def ordtypePermGeneric {O V T : Type} (ordtype : O → List V → T)
    (o : GenericPerm O (List V)) (_ : List V) : T := ordtype o.order o.data
def ordtypeByGeneric {V T : Type} (keyFn : V → R T) (anyT : T) (vs : List V) : T :=
  match vs with
  | [] => anyT
  | x :: _ => match keyFn x with | .ok t => t | .error _ => anyT

end JuliaLean.SortTuplesCov
