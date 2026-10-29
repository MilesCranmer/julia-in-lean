import JuliaLean.Core

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

structure OrderingValue (α : Type) where
  compare : α → α → OrderingResult Bool

instance {α : Type} : Ordering (OrderingValue α) := ⟨⟩

def forwardValue {α : Type} (isless : α → α → OrderingResult Bool) : OrderingValue α :=
  ⟨fun a b => isless a b⟩

def reverseOrderingValue {α : Type} (o : OrderingValue α) : OrderingValue α :=
  ⟨fun a b => o.compare b a⟩


def ltOrdering {A : Type} (o : OrderingValue A) (a b : A) : OrderingResult Bool :=
  o.compare a b

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

inductive OrderArg (A : Type) where
  | forward (o : ForwardOrdering) (isless : A → A → OrderingResult Bool)
  | reverseForward (o : ReverseOrdering ForwardOrdering)
      (isless : A → A → OrderingResult Bool)
  | other {O : Type} (o : O) (lt : O → A → A → OrderingResult Bool)

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

/-- The result of `_ord`/`ord` for values of type `A` and keys of type `K`: a bare ordering on
the values, or a `By` wrapper whose key transform stays outside every later reversal, as
Julia's `ReverseOrdering(::By)` constructor fold (`base/ordering.jl:62`) requires. -/
inductive OrdResult (A K : Type) where
  | plain (inner : OrderingValue A) : OrdResult A K
  | keyed (keyOf : A → OrderingResult K) (inner : OrderingValue K) : OrdResult A K

/-- `lt` of the composite ordering: keys are read from `a` then `b`, then the inner order
compares the two keys (`base/ordering.jl:72`). -/
def ordCompare {A K : Type} (o : OrdResult A K) (a b : A) : OrderingResult Bool :=
  match o with
  | .plain inner => inner.compare a b
  | .keyed keyOf inner =>
    match keyOf a with
    | .error e => .error e
    | .ok ka =>
      match keyOf b with
      | .error e => .error e
      | .ok kb => inner.compare ka kb

/-- `ReverseOrdering` of a composite ordering: the reversal wraps the inner order, never the
key transform (`base/ordering.jl:22,62`). -/
def ordResultReverse {A K : Type} (o : OrdResult A K) : OrdResult A K :=
  match o with
  | .plain inner => .plain (reverseOrderingValue inner)
  | .keyed keyOf inner => .keyed keyOf (reverseOrderingValue inner)

def keyedOfBy {T A K : Type} (b : By T (OrderingValue K))
    (apply : T → A → OrderingResult K) : OrdResult A K :=
  .keyed (fun a => apply b.callable a) b.order

/-- `_by(by, order)`: keep the key transform outside the order it wraps. -/
def applyKeyArg {A K : Type} (keyArg : KeyArg A K) (inner : OrderingValue K) :
    OrdResult A K :=
  match keyArg with
  | .identity => byIdentity (A := A) id (.plain inner)
  | .transform fn apply => keyedOfBy (byGeneric fn inner) apply
/--
Julia source: base/ordering.jl:130-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt::typeof(isless), by, order::Ordering)                         = _by(by, order)
```
-/
def ordIslessGeneric {A K O : Type} (keyArg : KeyArg A K) (order : O)
    (lt : O → K → K → OrderingResult Bool) : OrdResult A K :=
  applyKeyArg keyArg ⟨fun a b => lt order a b⟩

/--
Julia source: base/ordering.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt::typeof(isless), by, order::ForwardOrdering)                  = _by(by, order)  # disambiguation
```
-/
def ordIslessForward {A K : Type} (keyArg : KeyArg A K) (_order : ForwardOrdering)
    (isless : K → K → OrderingResult Bool) : OrdResult A K :=
  applyKeyArg keyArg (forwardValue isless)

/--
Julia source: base/ordering.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt::typeof(isless), by, order::ReverseOrdering{ForwardOrdering}) = _by(by, order)  # disambiguation
```
-/
def ordIslessReverseForward {A K : Type} (keyArg : KeyArg A K)
    (_order : ReverseOrdering ForwardOrdering) (isless : K → K → OrderingResult Bool) :
    OrdResult A K :=
  applyKeyArg keyArg (reverseOrderingValue (forwardValue isless))

/--
Julia source: base/ordering.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt,                 by, order::ForwardOrdering)                  = _by(by, Lt(lt))
```
-/
def ordCustomForward {A K : Type} (lt : K → K → OrderingResult Bool)
    (keyArg : KeyArg A K) (_order : ForwardOrdering) : OrdResult A K :=
  applyKeyArg keyArg ⟨lt⟩

/--
Julia source: base/ordering.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt,                 by, order::ReverseOrdering{ForwardOrdering}) = reverse(_by(by, Lt(lt)))
```
-/
def ordCustomReverseForward {A K : Type} (lt : K → K → OrderingResult Bool)
    (keyArg : KeyArg A K) (_order : ReverseOrdering ForwardOrdering) : OrdResult A K :=
  applyKeyArg keyArg (reverseOrderingValue ⟨lt⟩)

/--
Julia source: base/ordering.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_ord(lt,                 by, order::Ordering) = error("Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")
```
-/
def ordCustomOther {A K O : Type} (_lt : K → K → OrderingResult Bool)
    (_by : KeyArg A K) (_order : O) (_compare : O → K → K → OrderingResult Bool) :
    OrderingResult (OrdResult A K) :=
  .error (.errorException
    "Passing both lt= and order= arguments is ambiguous; please pass order=Forward or order=Reverse (or leave default)")


def ordDispatch {A K : Type} (lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool))
    (keyArg : KeyArg A K) (order : OrderArg K) : OrderingResult (OrdResult A K) := do
  match lt, order with
  | .inl isless, .forward o _ => pure (ordIslessForward keyArg o isless)
  | .inl isless, .reverseForward o _ => pure (ordIslessReverseForward keyArg o isless)
  | .inl _, .other o compare => pure (ordIslessGeneric keyArg o compare)
  | .inr cmp, .forward o _ => pure (ordCustomForward cmp keyArg o)
  | .inr cmp, .reverseForward o _ => pure (ordCustomReverseForward cmp keyArg o)
  | .inr cmp, .other o compare => ordCustomOther cmp keyArg o compare

/--
Julia source: base/ordering.jl:155-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ord(lt, by, rev::Nothing, order::Ordering=Forward) = _ord(lt, by, order)
```
-/
def ordNothing {A K : Type} (lt : Sum (K → K → OrderingResult Bool) (K → K → OrderingResult Bool))
    (keyArg : KeyArg A K) (_rev : Unit) (order : OrderArg K) :
    OrderingResult (OrdResult A K) :=
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
    OrderingResult (OrdResult A K) :=
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
