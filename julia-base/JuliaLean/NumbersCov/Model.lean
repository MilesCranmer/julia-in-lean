import JuliaLean.Core
import JuliaLean.Complex.Model
import JuliaLean.Complex.IntModel
import JuliaLean.HashOps.Model
import JuliaLean.IntArith.Rational
import JuliaLean.Promotion.Hash
import JuliaLean.Promotion.Rationalize

/-!
Coverage models for the method families in `base/number.jl`,
`base/operators.jl`, `base/promotion.jl`, `base/rational.jl`, and
`base/complex.jl` at master `bbfa0ce4150`.

The arithmetic-heavy Rational and Complex methods reuse the exact models in
`JuliaLean.IntArith.Rational` and `JuliaLean.Complex`. The definitions below
model the remaining generic forwarding, scalar-as-collection, type-promotion,
function-adapter, and componentwise complex methods.
-/

namespace JuliaLean.NumbersCov

open JuliaLean

/-! ## Generic values used by source-level forwarding methods -/

structure GenericOps (α : Type) where
  eq : α → α → Bool
  lt : α → α → Bool
  le : α → α → Bool
  zero : α → α
  one : α → α
  oneunit : α → α
  castOneType : α → α
  convertZero : α → α
  convertOne : α → α
  neg : α → α
  pos : α → α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  rem : α → α → α
  mod : α → α → α
  pow : α → α → α
  powInt : α → Int → α
  widen : α → α
  atan2 : α → α → α
  isfinite : α → Bool
  isnan : α → Bool
  isinf : α → Bool

namespace NumberModel

/-- `convert(::Type{T}, x::T) = x`; `base/number.jl:6`. -/
def convertSame (x : α) : α := x

/-- `convert(::Type{T}, x::Number) = T(x)::T`; `base/number.jl:7`. -/
def convertNumber (convert : α → β) (x : α) : β := convert x

/-- `isinteger(x::Integer) = true`; `base/number.jl:22`. -/
def isintegerInteger (_ : Int) : Bool := true

/-- `isfinite(x::Number) = iszero(x-x)`; `base/number.jl:84`. -/
def isfiniteNumber (o : GenericOps α) (x : α) : Bool := o.eq (o.sub x x) (o.zero x)

/-- Scalar `size`; `base/number.jl:86`. -/
def size (_ : α) : List Nat := []

/-- Scalar `size(x,d)`; `base/number.jl:87`. -/
def sizeDim (_ : α) (d : Int) : Jl Nat := if d < 1 then .error .boundsError else .ok 1

/-- Scalar `axes`; `base/number.jl:88`. -/
def axes (_ : α) : List (Nat × Nat) := []

/-- Scalar `axes(x,d)`; `base/number.jl:89`. -/
def axesDim (_ : α) (d : Int) : Jl (Nat × Nat) :=
  if d < 1 then .error .boundsError else .ok (1, 1)

/-- `eltype(::Type{T}) = T`, represented by its type tag; `base/number.jl:90`. -/
def eltype (tag : α) : α := tag

/-- Both scalar `ndims` methods; `base/number.jl:91-92`. -/
def ndims (_ : α) : Nat := 0

/-- Scalar length and first/last index; `base/number.jl:93-97`. -/
def length (_ : α) : Nat := 1
def firstindex (_ : α) : Nat := 1
def lastindex (_ : α) : Nat := 1
def indexDim (d : Int) : Jl Nat := if d < 1 then .error .boundsError else .ok 1

/-- `IteratorSize(::Type{<:Number}) = HasShape{0}()`; encoded as rank zero;
`base/number.jl:98`. -/
def iteratorRank (_ : α) : Nat := 0

/-- `keys(::Number) = OneTo(1)`; `base/number.jl:99`. -/
def keys (_ : α) : List Nat := [1]

/-- Zero-argument scalar indexing; `base/number.jl:101`. -/
def getindex0 (x : α) : α := x

/-- Checked scalar indexing; `base/number.jl:102-111`. -/
def getindex1 (x : α) (i : Int) : Jl α := if i = 1 then .ok x else .error .boundsError
def getindexMany (x : α) (is : List Int) : Jl α :=
  if is.all (· = 1) then .ok x else .error .boundsError

/-- Nonthrowing scalar `get`; `base/number.jl:112-115`. -/
def get1 (x default : α) (i : Int) : α := if i = 1 then x else default
def getMany (x default : α) (is : List Int) : α := if is.all (· = 1) then x else default
def getThunk1 (f : Unit → α) (x : α) (i : Int) : α := if i = 1 then x else f ()
def getThunkMany (f : Unit → α) (x : α) (is : List Int) : α :=
  if is.all (· = 1) then x else f ()

/-- `first`, `last`, and `copy` on numbers; `base/number.jl:117-119`. -/
def identityNumber (x : α) : α := x

/-- Sign predicates; `base/number.jl:143,165,187`. -/
def signbit (o : GenericOps α) (x : α) : Bool := o.lt x (o.zero x)
def ispositive (o : GenericOps α) (x : α) : Bool := o.lt (o.zero x) x
def isnegative (o : GenericOps α) (x : α) : Bool := o.lt x (o.zero x)

/-- Generic and Real `sign`; `base/number.jl:211-213`. -/
def signNumber (o : GenericOps α) (x : α) : α :=
  if o.eq x (o.zero x) then
    o.div x (if signbit o (o.oneunit x) then o.neg (o.oneunit x) else o.oneunit x)
  else o.div x (if signbit o x then o.neg x else x)

def signReal (o : GenericOps α) (x : α) : α :=
  if o.lt x (o.zero x) then o.neg (o.one x)
  else if o.lt (o.zero x) x then o.one x else o.castOneType x

def signUnsigned (o : GenericOps α) (x : α) : α :=
  if o.lt (o.zero x) x then o.one x else o.zero x

/-- `abs`, `abs2`, `flipsign`, and `copysign`; `base/number.jl:214,238-271`. -/
def abs (o : GenericOps α) (x : α) : α := if signbit o x then o.neg x else x
def abs2Number (o : GenericOps α) (x : α) : α := o.powInt (abs o x) 2
def abs2Real (o : GenericOps α) (x : α) : α := o.mul x x
def flipsign (o : GenericOps α) (x y : α) : α := if signbit o y then o.neg x else o.pos x
def copysign (o : GenericOps α) (x y : α) : α :=
  if signbit o x != signbit o y then o.neg x else o.pos x

/-- `conj`, `transpose`, `adjoint`, and real `angle`; `base/number.jl:273-276`. -/
def conj (x : α) : α := x
def transpose (x : α) : α := x
def adjoint (x : α) : α := conj x
def angle (o : GenericOps α) (x : α) : α := o.atan2 (o.zero x) x

/-- `widemul`; `base/number.jl:327`. -/
def widemul (o : GenericOps α) (x y : α) : α := o.mul (o.widen x) (o.widen y)

/-- Scalar iteration and membership; `base/number.jl:329-334`. -/
def iterate (x : α) : Option (α × Unit) := some (x, ())
def iterateNext (_ : α) (_ : Unit) : Option (α × Unit) := none
def isempty (_ : α) : Bool := false
def mem (o : GenericOps α) (x y : α) : Bool := o.eq x y
def map (f : List α → β) (x : α) (ys : List α) : β := f (x :: ys)

/-- Generic zero/one/oneunit methods; `base/number.jl:363-432`. -/
def zeroValue (o : GenericOps α) (x : α) : α := o.convertZero x
def zeroType (convert : Int → α) : α := convert 0
def oneType (convert : Int → α) : α := convert 1
def oneValue (oneType : Unit → α) (_ : α) : α := oneType ()
def oneunitValue (cast : α → α) (one : α) : α := cast one
def oneunitType (cast : α → α) (one : α) : α := cast one

/-- `big(::Type{T}) = typeof(big(zero(T)))`; represented by composing the
three observable operations; `base/number.jl:452`. -/
def bigType (zero : α → β) (big : β → γ) (typeOf : γ → δ) (t : α) : δ :=
  typeOf (big (zero t))

/-- `Union{}(value)` in the zero, one, oneunit, and big fallbacks;
`base/number.jl:365,407,432,453`. Core rejects construction of Bottom. -/
def bottomCall (fn : String) : Jl α := .error (.argumentError fn)

end NumberModel

/-! ## Generic comparison and operator families -/

namespace OperatorModel

/-- `supertype(::DataType)` computes the deferred edge before reading it;
`base/operators.jl:86-94`. -/
def supertypeData (compute : α → Unit) (super : α → β) (t : α) : β :=
  let _ := compute t
  super t

/-- `getproperty(::DataType, ::Symbol)` special-cases `:super`;
`base/operators.jl:95-101`. -/
def getpropertyData (isSuper : γ → Bool) (supertype : α → β)
    (getfield : α → γ → β) (t : α) (s : γ) : β :=
  if isSuper s then supertype t else getfield t s

/-- UnionAll and Type-kind supertype methods; `base/operators.jl:102-105`. -/
def supertypeUnionAll (wrap : α → β → γ) (supertype : β → β) (v : α) (body : β) : γ :=
  wrap v (supertype body)
def supertypeTypeEq (anyType : α) : α := anyType
def supertypeTypeEgal (typeOf : α → β) (parameter : α) : β := typeOf parameter

structure FloatOrder (α : Type) where
  eq : α → α → Bool
  lt : α → α → Bool
  isnan : α → Bool
  signbit : α → Bool

def signequal (o : FloatOrder α) (x y : α) : Bool := o.signbit x == o.signbit y
def signless (o : FloatOrder α) (x y : α) : Bool := o.signbit x && !o.signbit y

/-- Float-aware `isequal`; `base/operators.jl:196-203`. -/
def isequalFloat (o : FloatOrder α) (x y : α) : Bool :=
  (o.isnan x && o.isnan y) || (signequal o x y && o.eq x y)

/-- Float-aware `isless`; `base/operators.jl:240-242`. -/
def islessFloat (o : FloatOrder α) (x y : α) : Bool :=
  (!o.isnan x && (o.isnan y || signless o x y)) || o.lt x y

/-- Optimized pair order; `base/operators.jl:248-249`. -/
def pairIsless (lt eq : α → α → Bool) (a b : α × α) : Bool :=
  lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2)

/-- Generic comparisons; `base/operators.jl:196,295,309-315,338,417-588`. -/
def isequal (eq : α → α → Bool) (x y : α) : Bool := eq x y
def isgreater (unordered : α → Bool) (lt : α → α → Bool) (x y : α) : Bool :=
  if unordered x || unordered y then lt x y else lt y x
def isunordered (_ : α) : Bool := false
def isunorderedFloat (isnan : α → Bool) (x : α) : Bool := isnan x
def typeEqual (typesEqual : α → α → Bool) (t s : α) : Bool := typesEqual t s
def typeVarTypeEqual (_ : α) (_ : β) : Bool := false
def ne (eq : α → α → Bool) (x y : α) : Bool := !eq x y
def neGeneric (eq : α → α → β) (not : β → γ) (x y : α) : γ := not (eq x y)
def ltFallback (lt : α → α → Bool) (x y : α) : Bool := lt x y
def gtFallback (lt : α → α → Bool) (x y : α) : Bool := lt y x
def leFallback (lt eq : α → α → Bool) (x y : α) : Bool := lt x y || eq x y
def leGeneric (lt : α → α → β) (eq : α → α → γ) (bitOr : β → γ → δ)
    (x y : α) : δ := bitOr (lt x y) (eq x y)
def geFallback (le : α → α → Bool) (x y : α) : Bool := le y x
def geGeneric (le : α → α → β) (x y : α) : β := le y x
def cmp (lt : α → α → Bool) (x y : α) : Int :=
  if lt x y then -1 else if lt y x then 1 else 0
def max (lt : α → α → Bool) (x y : α) : α := if lt y x then x else y
def min (lt : α → α → Bool) (x y : α) : α := if lt y x then y else x
def minmax (lt : α → α → Bool) (x y : α) : α × α := if lt y x then (y, x) else (x, y)

/-- Identity unary arithmetic methods; `base/operators.jl:605-611`. -/
def identity (x : α) : α := x

/-- `afoldl`; the source manually unrolls the first 31 applications and then
continues with the same left fold; `base/operators.jl:622-663`. -/
def afoldl (op : α → α → α) (a : α) (bs : List α) : α := bs.foldl op a

/-- Generated n-ary arithmetic methods; `base/operators.jl:666-675`. -/
def nary (op : α → α → α) (a b c : α) (xs : List α) : α :=
  afoldl op (op (op a b) c) xs

def intMin : Int := -(2^63)
def intMax : Int := 2^63 - 1

/-- Generic integer-count left shift; `base/operators.jl:735-740`. -/
def shiftLeftInteger (shiftInt : α → Int → α) (zero negOne : α)
    (nonnegative : α → Bool) (x : α) (c : Int) : α :=
  if intMin ≤ c && c ≤ intMax then shiftInt x c
  else if nonnegative x || 0 ≤ c then shiftInt zero 0 else negOne

/-- Generic integer-count arithmetic right shift; `base/operators.jl:780-788`. -/
def shiftRightInteger (shiftInt : α → Int → α) (zero negOne : α)
    (nonnegative : α → Bool) (x : α) (c : Int) : α :=
  if intMin ≤ c && c ≤ intMax then shiftInt x c
  else if nonnegative x || c < 0 then shiftInt zero 0 else negOne

/-- The `>>(x::Integer,c::Integer)` method rejects a machine `UInt` before its
range test; `base/operators.jl:780-788`. -/
def shiftRightGenericCount (shiftInt : α → Int → α) (zero negOne : α)
    (nonnegative : α → Bool) (x : α) (c : Int) (isMachineUInt : Bool) : Jl α :=
  if isMachineUInt then .error (.methodError ">>")
  else .ok (shiftRightInteger shiftInt zero negOne nonnegative x c)

/-- Generic integer-count logical right shift; `base/operators.jl:818-821`. -/
def shiftUnsignedRightInteger (shiftInt : α → Int → α) (zero : α) (x : α) (c : Int) : α :=
  if intMin ≤ c && c ≤ intMax then shiftInt x c else shiftInt zero 0

/-- Signed Int count redirects negative counts to the opposite shift;
`base/operators.jl:748,789,829`. -/
def shiftSignedCount (forward backward : α → Nat → α) (x : α) (c : Int) : α :=
  if 0 ≤ c then forward x c.toNat else backward x (-c).toNat

/-- Unsigned-count overloads, including the deliberate UInt MethodError;
`base/operators.jl:741-747,822-828`. -/
def shiftUnsignedCount (fn : α → Nat → α) (zero : α) (x : α)
    (c : Nat) (isMachineUInt : Bool) : Jl α :=
  if isMachineUInt then .error (.methodError "shift")
  else if c ≤ 2^64 - 1 then .ok (fn x c) else .ok (fn zero 0)

/-- `mod1`, `cldmod1`, and `fldmod1`; `base/operators.jl:914-952`. -/
def mod1 (mod : α → α → α) (iszero : α → Bool) (x y : α) : α :=
  let m := mod x y
  if iszero m then y else m
def cldmod1 (cld : α → α → β) (mod1 : α → α → γ) (x y : α) : β × γ :=
  (cld x y, mod1 x y)
def fldmod1 (fld1 : α → α → β) (mod1 : α → α → γ) (x y : α) : β × γ :=
  (fld1 x y, mod1 x y)

/-- Generic left division; `base/operators.jl:709`. -/
def leftDiv (adjoint : α → α) (div : α → α → α) (x y : α) : α :=
  adjoint (div (adjoint y) (adjoint x))

/-- `widen(x)`; `base/operators.jl:975`. -/
def widenValue (widenType : α → β) (convert : β → α → γ) (typeOf : α → α) (x : α) : γ :=
  convert (widenType (typeOf x)) x

def widenTypeError (typeName : String) : Jl α := .error (.methodError typeName)

/-- Function piping; `base/operators.jl:1001`. -/
def pipe (x : α) (f : α → β) : β := f x

/-- Stable type tags used by Returns and Fix constructors;
`base/operators.jl:1003-1004`. -/
def stableTypeof (typeOf : α → β) (x : α) : β := typeOf x
def stableTypeofType (hasFreeVars : α → Bool) (typeTag dataType : β) (t : α) : β :=
  if !hasFreeVars t then typeTag else dataType

structure Returns (α : Type) where value : α
def returnsTyped (value : α) : Returns α := ⟨value⟩
def returnsStable (value : α) : Returns α := ⟨value⟩
def Returns.call (r : Returns α) (_ : List β) : α := r.value

structure Composed (α : Type) where
  functions : List (α → α)

/-- `call_composed` and the ComposedFunction call; `base/operators.jl:1125-1129`. -/
def callComposed (fs : List (α → α)) (x : α) : α := fs.foldr (fun f x => f x) x
def Composed.call (c : Composed α) (x : α) : α := callComposed c.functions x
def compose1 (f : α → α) : Composed α := ⟨[f]⟩
def compose2 (f g : α → α) : Composed α := ⟨[f, g]⟩
def composeMany (f g : α → α) (hs : List (α → α)) : Composed α := ⟨f :: g :: hs⟩
def unwrapComposed (c : Composed α) : List (α → α) := c.functions
def unwrapSingle (f : α → α) : List (α → α) := [f]

/-- `Constructor{F}` and `maybeconstructor` preserve the callable behaviour;
`base/operators.jl:1131-1134`. -/
def constructorCall (f : List α → β) (args : List α) : β := f args
def maybeConstructorType (f : List α → β) : List α → β := f
def maybeConstructorValue (f : List α → β) : List α → β := f

/-- Observable text of composition show methods; `base/operators.jl:1140-1158`. -/
def showComposed (render showPart : α → String) (outerIsComposed : Bool)
    (outer inner : α) : String :=
  (if outerIsComposed then render outer else showPart outer) ++ " ∘ " ++ showPart inner
def showNegatedComposed (render : α → String) (inner : α) : String := "!" ++ render inner
def showComposedPart (render : α → String) (isOperator isNested : Bool) (x : α) : String :=
  if isOperator || isNested then "(" ++ render x ++ ")" else render x

/-- Predicate negation and its double-negation specialization;
`base/operators.jl:1182-1183`. -/
def negatePredicate (f : α → Bool) : α → Bool := fun x => !f x
def doubleNegationInner (f : α → Bool) : α → Bool := f

structure Fix (α β : Type) where
  n : Nat
  f : List α → β
  value : α

/-- `Fix{N}(f,x)` validates that N is an Int and positive;
`base/operators.jl:1206-1213`. -/
def Fix.make (n : Option Int) (f : List α → β) (value : α) : Jl (Fix α β) :=
  match n with
  | none => .error (.argumentError "Fix index must be Int")
  | some n =>
    if n < 1 then .error (.argumentError "Fix index must be positive")
    else .ok ⟨n.toNat, f, value⟩

/-- General Fix insertion; `base/operators.jl:1206-1224`. -/
def Fix.call (fix : Fix α β) (args : List α) : Jl β :=
  if fix.n < 1 then .error (.argumentError "Fix position")
  else if args.length < fix.n - 1 then .error (.argumentError "Fix arguments")
  else .ok (fix.f (args.take (fix.n - 1) ++ [fix.value] ++ args.drop (fix.n - 1)))

/-- Unary comparison constructors are `Fix2`; `base/operators.jl:1259-1335`. -/
def fix2 (f : α → α → β) (x : α) : α → β := fun y => f y x
def fixSecond (f : α → β → γ) (x : β) : α → γ := fun y => f y x

def fix1Call (f : α → α → β) (fixed arg : α) : β := f fixed arg
def fix2Call (f : α → α → β) (fixed arg : α) : β := f arg fixed

def showFix (renderF : (List α → β) → String) (render : α → String) (fix : Fix α β) : String :=
  "Fix{" ++ toString fix.n ++ "}(" ++ renderF fix.f ++ ", " ++ render fix.value ++ ")"

structure Splat (α β : Type) where f : List α → β
def Splat.call (s : Splat α β) (args : List α) : β := s.f args
def splat (f : List α → β) : Splat α β := ⟨f⟩
def unsplat (f : List α → β) : List α → β := fun args => f args
def unsplatSplat (s : Splat α β) : List α → β := s.f
def splatUnsplat (f : List α → β) : List α → β := f
def showSplat (render : (List α → β) → String) (s : Splat α β) : String :=
  "splat(" ++ render s.f ++ ")"

/-- `tap(f)`; `base/operators.jl:1438`. -/
def tap (f : α → β) : α → α := fun x => let _ := f x; x

inductive Truth where | false | missing | true
  deriving BEq, Repr

def Truth.not : Truth → Truth
  | .false => .true | .true => .false | .missing => .missing

def Truth.or : Truth → Truth → Truth
  | .true, _ | _, .true => .true
  | .missing, _ | _, .missing => .missing
  | .false, .false => .false

/-- Generic iterable membership with three-valued equality;
`base/operators.jl:1455`. -/
def mem (eq : α → α → Truth) (x : α) : List α → Truth
  | [] => .false
  | y :: ys => Truth.or (eq y x) (mem eq x ys)

/-- `∉`, `∋`, and `∌`; `base/operators.jl:1477-1500`. -/
def notMem (m : α → β → Truth) (x : α) (ys : β) : Truth := (m x ys).not
def contains (m : α → β → Truth) (ys : β) (x : α) : Truth := m x ys
def notContains (m : α → β → Truth) (ys : β) (x : α) : Truth := (m x ys).not

end OperatorModel

/-! ## Promotion source mechanisms -/

namespace PromotionModel

/-! A source-shaped type-object model for `typejoin`. Unlike the compact `Ty`
model used below for numeric promotion tables, this keeps TypeVar bounds,
UnionAll binders, DataType supertypes and parameters, tuple Varargs, TypeEq and
TypeEgal distinct. -/

inductive PType where
  | bottom
  | any
  | typeVar (id : Nat) (upper : PType)
  | unionAll (var body : PType)
  | union (left right : PType)
  | data (name wrapper : String) (params : List PType) (super : Option PType)
  | typeEq (parameter : PType)
  | typeEgal (parameter : PType)
  | vararg (element : PType) (length : Option Nat)
  | parameter (tag : String)
  deriving Repr, Inhabited

structure PTypeOps where
  egal : PType → PType → Bool
  subtype : PType → PType → Bool
  typeofParameter : PType → PType

def pIsType : PType → Bool
  | .bottom | .any | .unionAll .. | .union .. | .data .. | .typeEq .. | .typeEgal .. => true
  | _ => false

def pUnwrapVa : PType → PType
  | .vararg t _ => t
  | t => t

def pIsVararg : PType → Bool
  | .vararg .. => true
  | _ => false

def pFullVaLen (ps : List PType) : Nat × Bool :=
  match ps.getLast? with
  | none => (0, true)
  | some (.vararg _ (some n)) => (ps.length + n - 1, true)
  | some (.vararg _ none) => (ps.length, false)
  | some _ => (ps.length, true)

def pHasAncestorName : PType → String → Bool
  | .data name _ _ super, target =>
      if name = target then true
      else match super with
        | some s => pHasAncestorName s target
        | none => false
  | _, _ => false

def pAscendToName : PType → String → Option PType
  | t@(.data name _ _ super), target =>
      if name = target then some t
      else match super with
        | some s => pAscendToName s target
        | none => none
  | _, _ => none

def pReplaceMismatchedParams (ops : PTypeOps) : List PType → List PType → List PType
  | a :: as, b :: bs =>
      (if ops.egal a b || (ops.subtype a b && ops.subtype b a) then a
       else .parameter "_") :: pReplaceMismatchedParams ops as bs
  | _, _ => []

def pJoinParams (ops : PTypeOps) : Nat → List PType → List PType → List PType × List PType
  | _, [], _ | _, _, [] => ([], [])
  | i, a :: as, b :: bs =>
      let rest := pJoinParams ops (i + 1) as bs
      if ops.egal a b || (ops.subtype a b && ops.subtype b a) then
        (a :: rest.1, rest.2)
      else
        let v := PType.typeVar i .any
        (v :: rest.1, v :: rest.2)

mutual
/-- `typejoin(a,b)` in `base/promotion.jl:37-160`. Fuel bounds traversal of
recursive Union and UnionAll graphs; Julia's runtime type graph is finite. -/
def pTypejoin (ops : PTypeOps) : Nat → PType → PType → PType
  | 0, _, _ => .any
  | fuel + 1, .typeVar _ ub, b => pTypejoin ops fuel ub b
  | fuel + 1, a, .typeVar _ ub => pTypejoin ops fuel a ub
  | fuel + 1, a, b =>
      if ops.egal a b then a
      else if !pIsType a || !pIsType b then .any
      else if ops.subtype a b then b
      else if ops.subtype b a then a
      else match a, b with
        | .unionAll v body, b => .unionAll v (pTypejoin ops fuel body b)
        | a, .unionAll v body => .unionAll v (pTypejoin ops fuel a body)
        | .union x y, b => pTypejoin ops fuel (pTypejoin ops fuel x y) b
        | a, .union x y => pTypejoin ops fuel a (pTypejoin ops fuel x y)
        | .typeEgal x, b => pTypejoin ops fuel (ops.typeofParameter x) b
        | a, .typeEgal y => pTypejoin ops fuel a (ops.typeofParameter y)
        | .typeEq _, b =>
            let a := pAbstractType
            let b := match b with | .typeEq _ => pAbstractType | _ => b
            if ops.subtype a b then b else if ops.subtype b a then a else .any
        | a, .typeEq _ =>
            let b := pAbstractType
            if ops.subtype a b then b else if ops.subtype b a then a else .any
        | a@(.data an _aw ap _asup), b@(.data bn _bw bp _bsup) =>
            if an = "Tuple" then
              if bn = "Tuple" then pJoinTuples ops fuel ap bp else .any
            else if bn = "Tuple" then .any
            else pJoinData ops fuel a b
        | _, _ => .any

/-- Join the tuple parameter vectors at `base/promotion.jl:80-124`, including
empty tuples, fixed/open Vararg lengths, unequal expanded lengths, tail joins,
and the final-slot Vararg rule. -/
def pJoinTuples (ops : PTypeOps) (fuel : Nat) (ap bp : List PType) : PType :=
  let lar := ap.length
  let lbr := bp.length
  if lar = 0 then
    .data "Tuple" "Tuple" [.vararg (pTailFrom ops fuel bp 1) none] (some .any)
  else if lbr = 0 then
    .data "Tuple" "Tuple" [.vararg (pTailFrom ops fuel ap 1) none] (some .any)
  else
    let av := pFullVaLen ap
    let bv := pFullVaLen bp
    let laf := av.1
    let lbf := bv.1
    let init : List PType × Nat :=
      if laf < lbf then
        if pIsVararg (ap.getLastD .bottom) && !av.2 then
          let c := List.replicate laf .bottom
          let joined := pTypejoin ops fuel (pUnwrapVa (ap.getLastD .bottom))
            (pTailFrom ops fuel bp laf)
          (if laf = 0 then c else c.set (laf - 1) (.vararg joined none), laf - 1)
        else
          let c := (List.replicate (laf + 1) .bottom).set laf
            (.vararg (pTailFrom ops fuel bp (laf + 1)) none)
          (c, laf)
      else if lbf < laf then
        if pIsVararg (bp.getLastD .bottom) && !bv.2 then
          let c := List.replicate lbf .bottom
          let joined := pTypejoin ops fuel (pUnwrapVa (bp.getLastD .bottom))
            (pTailFrom ops fuel ap lbf)
          (if lbf = 0 then c else c.set (lbf - 1) (.vararg joined none), lbf - 1)
        else
          let c := (List.replicate (lbf + 1) .bottom).set lbf
            (.vararg (pTailFrom ops fuel ap (lbf + 1)) none)
          (c, lbf)
      else (List.replicate laf .bottom, laf)
    let c := (List.range init.2).foldl (fun c j =>
      let ai := ap.getD (min j (lar - 1)) .bottom
      let bi := bp.getD (min j (lbr - 1)) .bottom
      let ci := pTypejoin ops fuel (pUnwrapVa ai) (pUnwrapVa bi)
      c.set j (if j + 1 = c.length && (pIsVararg ai || pIsVararg bi)
        then .vararg ci none else ci)) init.1
    .data "Tuple" "Tuple" c (some .any)

/-- Ordinary DataType ancestry loop and invariant-parameter join at
`base/promotion.jl:128-159`. -/
def pJoinData (ops : PTypeOps) (fuel : Nat) (a b : PType) : PType :=
  match fuel, b with
  | 0, _ => .any
  | _, .any => .any
  | fuel + 1, .data bn bw bp bsup =>
      if pHasAncestorName a bn then
        match pAscendToName a bn with
        | some (.data _ _ ap asup) =>
            let joined := pJoinParams ops 1 ap bp
            joined.2.foldr (fun v body => .unionAll v body)
              (.data bn bw joined.1 asup)
        | _ => .any
      else match bsup with
        | some s => pJoinData ops fuel a s
        | none => .any
  | _, _ => .any

def pTailFrom (ops : PTypeOps) (fuel : Nat) (ps : List PType) (i : Nat) : PType :=
  if ps.length < i then pUnwrapVa (ps.getLastD .bottom)
  else (ps.drop (i - 1)).foldl (pTypejoin ops fuel) .bottom

/-- The abstract `Type` kind used when widening TypeEq operands;
`base/promotion.jl:65-75`. -/
def pAbstractType : PType := .data "Type" "Type" [] (some .any)
end

def pTypejoin0 : PType := .bottom
def pTypejoin1 (t : PType) : PType := t
def pTypejoin3 (ops : PTypeOps) (a b c : PType) : PType :=
  pTypejoin ops 64 (pTypejoin ops 64 a b) c
def pTypejoinMany (ops : PTypeOps) (a b c : PType) (ts : List PType) : PType :=
  ts.foldl (pTypejoin ops 64) (pTypejoin3 ops a b c)

def pTypesplit (ops : PTypeOps) : PType → PType → PType
  | a, b => if ops.subtype a b then .bottom else match a with
    | .union x y => .union (pTypesplit ops x b) (pTypesplit ops y b)
    | _ => a

def pPromoteTypesubtract (ops : PTypeOps) (nothing missing : PType) (a : PType) : PType :=
  if ops.egal a .any then a
  else if ops.subtype (.union nothing missing) a then pTypesplit ops a (.union nothing missing)
  else if ops.subtype nothing a then pTypesplit ops a nothing
  else if ops.subtype missing a then pTypesplit ops a missing
  else a

def pPromoteTypejoin (ops : PTypeOps) (a b : PType) : PType :=
  .union a (.union b (pTypejoin ops 64 a b))

def pTypejoinUnionParamsWith (ops : PTypeOps) (fuel : Nat) (recur : PType → PType) :
    List PType → Option (List PType)
  | [] => some []
  | p :: ps =>
      let u := pUnwrapVa p
      let ci := match u with
        | .bottom => some PType.bottom
        | .union a b => some (pTypejoin ops fuel a b)
        | .unionAll .. => none
        | t => some (recur t)
      match ci, pTypejoinUnionParamsWith ops fuel recur ps with
      | some c, some cs =>
          let c := match p with
            | .vararg _ n => PType.vararg c n
            | _ => c
          some (c :: cs)
      | _, _ => none

def pTypejoinUnionTupleWith (ops : PTypeOps) (fuel : Nat) (recur : PType → PType) :
    PType → PType
  | .data "Tuple" wrapper ps super =>
      match pTypejoinUnionParamsWith ops fuel recur ps with
      | some cs => .data "Tuple" wrapper cs super
      | none => .any
  | _ => .any

def pPromoteTypejoinUnion (ops : PTypeOps) : Nat → PType → PType
  | 0, _ => .any
  | _, .bottom => .bottom
  | _, .unionAll .. => .any
  | fuel + 1, .union a b =>
      pPromoteTypejoin ops (pPromoteTypejoinUnion ops fuel a)
        (pPromoteTypejoinUnion ops fuel b)
  | fuel + 1, t@(.data "Tuple" _ _ _) =>
      pTypejoinUnionTupleWith ops fuel (pPromoteTypejoinUnion ops fuel) t
  | _, .data n w ps s => .data n w ps s
  | _, .typeEq t => .typeEq t
  | _, _ => .any

def pTypejoinUnionTuple (ops : PTypeOps) (fuel : Nat) (t : PType) : PType :=
  pTypejoinUnionTupleWith ops fuel (pPromoteTypejoinUnion ops fuel) t

def pTailjoin (ops : PTypeOps) (ps : List PType) (i : Nat) : PType :=
  if ps.length < i then pUnwrapVa (ps.getLastD .bottom)
  else (ps.drop (i - 1)).foldl (pTypejoin ops 64) .bottom

inductive Ty where
  | bottom
  | any
  | atom (name : Nat) (ancestors : List Nat)
  | union (left right : Ty)
  | typeVar (upper : Ty)
  | unionAll (body : Ty)
  | typeEq (parameter : Ty)
  | tuple (parameters : List Ty)
  deriving BEq, Repr

def subtype : Ty → Ty → Bool
  | _, .any => true
  | .bottom, _ => true
  | a, b => a == b

def atomJoin (an : Nat) (aa : List Nat) (bn : Nat) (ba : List Nat) : Ty :=
  if an = bn then .atom an aa
  else match (an :: aa).find? (fun n => (bn :: ba).contains n) with
    | some n => .atom n []
    | none => .any

/-- Finite source model of `typejoin`; it follows the source branch order for
TypeVar, identity, subtyping, UnionAll, Union, Type equality kinds, tuples, and
ordinary datatype ancestry. Fuel represents Julia's finite type graph;
`base/promotion.jl:20-160`. -/
def typejoin : Nat → Ty → Ty → Ty
  | 0, _, _ => .any
  | fuel + 1, a, b =>
      match a, b with
      | .typeVar u, b => typejoin fuel u b
      | a, .typeVar u => typejoin fuel a u
      | a, b =>
        if a == b then a
        else if subtype a b then b
        else if subtype b a then a
        else match a, b with
          | .unionAll body, b => .unionAll (typejoin fuel body b)
          | a, .unionAll body => .unionAll (typejoin fuel a body)
          | .union x y, b => typejoin fuel (typejoin fuel x y) b
          | a, .union x y => typejoin fuel a (typejoin fuel x y)
          | .typeEq x, b => typejoin fuel x b
          | a, .typeEq y => typejoin fuel a y
          | .tuple xs, .tuple ys => .tuple (List.zipWith (typejoin fuel) xs ys)
          | .tuple _, _ | _, .tuple _ => .any
          | .atom an aa, .atom bn ba => atomJoin an aa bn ba
          | _, _ => .any

def typesplit : Ty → Ty → Ty
  | a, b => if subtype a b then .bottom else match a with
    | .union x y => .union (typesplit x b) (typesplit y b)
    | _ => a

def promoteTypejoin (a b : Ty) : Ty := .union a (.union b (typejoin 64 a b))

/-- `_promote_typesubtract`; `base/promotion.jl:202-207`. -/
def promoteTypesubtract (a : Ty) : Ty :=
  match a with
  | .any => .any
  | .union x y =>
      let withoutBottom := typesplit (.union x y) .bottom
      withoutBottom
  | _ => a

/-- Union normalization used by `promote_typejoin_union` and tuple elements;
`base/promotion.jl:209-253`. -/
def promoteTypejoinUnion : Nat → Ty → Ty
  | 0, _ => .any
  | _fuel + 1, .bottom => .bottom
  | _fuel + 1, .unionAll _ => .any
  | fuel + 1, .union a b => promoteTypejoin (promoteTypejoinUnion fuel a) (promoteTypejoinUnion fuel b)
  | fuel + 1, .tuple xs => .tuple (xs.map (promoteTypejoinUnion fuel))
  | _, t => t

/-- `full_va_len` and `tailjoin`; a `none` final length is an open Vararg;
`base/promotion.jl:256-280`. -/
def fullVaLen (params : List (Ty × Option Nat)) : Nat × Bool :=
  match params.getLast? with
  | none => (0, true)
  | some (_, some n) => (params.length + n - 1, true)
  | some (_, none) => (params.length, false)

def tailjoin (params : List Ty) (i : Nat) : Ty :=
  if params.length < i then params.getLastD .bottom
  else (params.drop (i - 1)).foldl (typejoin 64) .bottom

def promoteType : Nat → (Ty → Ty → Ty) → Ty → Ty → Ty
  | 0, _, _, _ => .any
  | fuel + 1, rule, a, b =>
      if a == .bottom then b
      else if b == .bottom then a
      else if a == b then a
      else
        let r1 := rule a b
        let r2 := rule b a
        if r1 == .bottom && r2 == .bottom then typejoin fuel a b
        else promoteType fuel rule r1 r2

def promoteType0 : Ty := .bottom
def promoteType1 (t : Ty) : Ty := t
def promoteType3 (rule : Ty → Ty → Ty) (t s u : Ty) : Ty :=
  promoteType 64 rule (promoteType 64 rule t s) u
def promoteTypeMany (rule : Ty → Ty → Ty) (t s u : Ty) (ts : List Ty) : Ty :=
  ts.foldl (promoteType 64 rule) (promoteType3 rule t s u)
def promoteRuleDefault (_ _ : Ty) : Ty := .bottom
def promoteRuleBottomLeft (_ : Ty) : Ty := .bottom
def promoteRuleBottomRight (t : Ty) : Ty := t
def promoteResult (rule : Ty → Ty → Ty) (t s r1 r2 : Ty) : Ty :=
  if r1 == .bottom && r2 == .bottom then typejoin 64 t s
  else promoteType 64 rule r1 r2

/-- Value promotion; `base/promotion.jl:397-441`. -/
def promote2 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y : α) : α × α :=
  let t := promoteType 64 rule (typeOf x) (typeOf y)
  (convert t x, convert t y)

def promote3 (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (x y z : α) : α × α × α :=
  let t := promoteType 64 rule (promoteType 64 rule (typeOf x) (typeOf y)) (typeOf z)
  (convert t x, convert t y, convert t z)

def promoteMany (typeOf : α → Ty) (convert : Ty → α → α) (rule : Ty → Ty → Ty)
    (xs : List α) : List α :=
  let t := (xs.map typeOf).foldl (promoteType 64 rule) .bottom
  xs.map (convert t)

def promoteTypeof1 (typeOf : α → Ty) (x : α) : Ty := typeOf x
def promoteTypeof2 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y : α) : Ty :=
  promoteType 64 rule (typeOf x) (typeOf y)
def promoteTypeof3 (typeOf : α → Ty) (rule : Ty → Ty → Ty) (x y z : α) : Ty :=
  promoteType3 rule (typeOf x) (typeOf y) (typeOf z)
def promoteTypeofMany (typeOf : α → Ty) (rule : Ty → Ty → Ty)
    (x y z : α) (xs : List α) : Ty :=
  (xs.map typeOf).foldl (promoteType 64 rule) (promoteTypeof3 typeOf rule x y z)

def promote0 : List α := []
def promote1 (x : α) : List α := [x]
def promoteSame (x y : α) (zs : List α) : List α := x :: y :: zs

/-- Circular-promotion check; `base/promotion.jl:443-452`. -/
def notSameType (sameType : List α → List α → Bool) (before after : List α) : Jl Unit :=
  if sameType before after then .error (.argumentError "promotion failed") else .ok ()

/-- Mixed arithmetic forwards after promotion; `base/promotion.jl:454-527`. -/
def promotedBinary (promote : α → α → α × α) (op : α → α → β) (x y : α) : β :=
  let p := promote x y
  op p.1 p.2

def promotedTernary (promote : α → α → α → α × α × α)
    (op : α → α → α → β) (x y z : α) : β :=
  let p := promote x y z
  op p.1 p.2.1 p.2.2

/-- `muladd` preserves strong zero before same-type dispatch;
`base/promotion.jl:510-514`. -/
def promotedMuladd (promote : α → α → α → α × α × α)
    (muladd : α → α → α → α) (isFalse : α → Bool) (a b c : α) : α :=
  let p := promote a b c
  if isFalse a || isFalse b then p.2.2 else muladd p.1 p.2.1 p.2.2

/-- `TupleOrBottom`; `base/promotion.jl:529-532`. -/
def tupleOrBottom (ts : List Ty) : Ty := if ts.contains .bottom then .bottom else .tuple ts

/-- `promote_op`; inference is supplied as the primitive `_return_type`;
`base/promotion.jl:641-645`. -/
def promoteOp (returnType : (α → β) → Ty → Ty) (f : α → β) (ts : List Ty) : Ty :=
  let arg := tupleOrBottom ts
  if arg == .bottom then .bottom else returnType f arg

/-- Same-type catch-all arithmetic; `base/promotion.jl:650-680`. -/
def noOp (_name : String) : Jl α := .error (.methodError "numeric operation")
def fallbackMuladd (mul add : α → α → α) (x y z : α) : α := add (mul x y) z
def fallbackEq (identical : α → α → Bool) (x y : α) : Bool := identical x y
def fallbackLe (eq lt : α → α → Bool) (x y : α) : Bool := eq x y || lt x y
def fallbackMax (lt : α → α → Bool) (x y : α) : α := if lt y x then x else y
def fallbackMin (lt : α → α → Bool) (x y : α) : α := if lt y x then y else x
def fallbackMinmax (lt : α → α → Bool) (x y : α) : α × α :=
  if lt y x then (y, x) else (x, y)
def fallbackUnary (x : α) : α := x

end PromotionModel

/-! ## Rational coverage additions -/

namespace RationalModel

open JuliaLean.IntArith.Rational

structure MathRat where
  num : Int
  den : Int
  deriving DecidableEq, Repr

structure Pair (α : Type) where
  re : α
  im : α
  deriving DecidableEq, Repr

/-- `unsafe_rational` inner and same-type outer constructors;
`base/rational.jl:14,17`. -/
def unsafeRat {t : IntTy} (num den : JInt t) : Rat t := ⟨num, den⟩

def unsafeMixed {t s} (num : JInt t) (den : JInt s) : Jl AnyRat := do
  let p := t.promote s
  let n ← JInt.convert p num.val
  let d ← JInt.convert p den.val
  return ⟨p, ⟨n, d⟩⟩

def checkedDenMixed {t s} (num : JInt t) (den : JInt s) : Jl AnyRat := do
  let p := t.promote s
  let n ← JInt.convert p num.val
  let d ← JInt.convert p den.val
  let r ← checkedDen n d
  return ⟨p, r⟩

/-- `__throw_rational_argerror_zero`; `base/rational.jl:30`. -/
def throwZero (typeName : String) : Jl α := .error (.argumentError typeName)

/-- `Bool(::Rational)` and integer conversion; `base/rational.jl:199-202`. -/
def boolOfRat {t} (x : Rat t) : Jl Bool :=
  if x.num.val = 0 && x.den.val = 1 then .ok false
  else if x.num.val = 1 && x.den.val = 1 then .ok true
  else .error (.inexactError "Bool")

def intOfRat (target : IntTy) {t} (x : Rat t) : Jl (JInt target) :=
  if x.den.val = 1 then JInt.convert target x.num.val
  else .error (.inexactError target.name)

def numeratorIntegral (x : α) : α := x
def denominatorIntegral (one : α → α) (x : α) : α := one x

/-- Complex rational accessors; the caller supplies checked multiplication,
division and lcm exactly as Julia dispatches them; `base/rational.jl:362-367,385`. -/
def numeratorComplex (numerator denominator : α → β) (checkedMul : β → β → β)
    (div : β → β → β) (complex : β → β → γ) (real imag : α → α) (z : α)
    (commonDen : β) : γ :=
  let r := real z
  let i := imag z
  complex (checkedMul (numerator r) (div commonDen (denominator r)))
    (checkedMul (numerator i) (div commonDen (denominator i)))

def denominatorComplex (denominator : α → β) (lcm : β → β → β)
    (real imag : α → α) (z : α) : β :=
  lcm (denominator (real z)) (denominator (imag z))

/-- Observable Rational display; `base/rational.jl:156-165`. -/
def showRat (render : α → String) (isOne : α → Bool) (typeInfoRational : Bool)
    (num den : α) : String :=
  if isOne den && typeInfoRational then render num else render num ++ "//" ++ render den

/-- Binary read/write preserve numerator then denominator order;
`base/rational.jl:167-174`. -/
def readPair (read : Unit → α × α) : α × α := read ()
def writePair (write : α → α → β) (num den : α) : β := write num den

/-- Rational parsing after `split('/', limit=2)`; `base/rational.jl:175-187`.
The split primitive supplies the exact one- or two-part result. -/
def parseParts (parse : String → α) (construct : α → α → β) (parts : List String) : Option β :=
  match parts with
  | [n] => some (construct (parse n) (parse "1"))
  | n :: d :: _ =>
      let d := if d.startsWith "/" then (d.drop 1).toString else d
      some (construct (parse n) (parse d))
  | _ => none

/-- Exact complex inverse helper; `base/rational.jl:120-135`. -/
def complexExactInv (isinf : α → Bool) (zero _neg conj : Pair α → Pair α)
    (abs2 : Pair α → α) (z : Pair α) : Pair α × α :=
  let n := if isinf z.re || isinf z.im then conj (zero z) else conj z
  (n, abs2 z)

/-- Integer specialization of `_complex_exact_inv`; `base/rational.jl:129-135`. -/
def complexExactInvInt {t} (z : Pair (JInt t)) : Jl (Pair (JInt t) × JInt t) := do
  let p ← divgcd z.re z.im
  let c ← JuliaLean.IntArith.Checked.checkedMul z.re p.1
  let d ← JuliaLean.IntArith.Checked.checkedMul z.im p.2
  let den ← JuliaLean.IntArith.Checked.checkedAdd c d
  let ni ← JuliaLean.IntArith.Checked.checkedNeg p.2
  return (⟨p.1, ni⟩, den)

/-- Generic exact division by Complex; `base/rational.jl:137-152`. -/
def divByComplex (exactInv : Pair α → Pair α × β)
    (mul : γ → Pair α → δ) (ratDiv : δ → β → ε)
    (x : γ) (y : Pair α) : ε :=
  let p := exactInv y
  ratDiv (mul x p.1) p.2

def complexDivReal (ratDiv : α → β → γ) (z : Pair α) (y : β) : Pair γ :=
  ⟨ratDiv z.re y, ratDiv z.im y⟩

def complexIntDiv {t} (x y : Pair (JInt t)) : Jl (Pair (Rat t)) := do
  let p ← divgcd y.re y.im
  let c2 ← JuliaLean.IntArith.Checked.checkedMul y.re p.1
  let d2 ← JuliaLean.IntArith.Checked.checkedMul y.im p.2
  let den ← JuliaLean.IntArith.Checked.checkedAdd c2 d2
  let ac ← JuliaLean.IntArith.Checked.checkedMul x.re p.1
  let bd ← JuliaLean.IntArith.Checked.checkedMul x.im p.2
  let nr ← JuliaLean.IntArith.Checked.checkedAdd ac bd
  let bc ← JuliaLean.IntArith.Checked.checkedMul x.im p.1
  let ad ← JuliaLean.IntArith.Checked.checkedMul x.re p.2
  let nad ← JuliaLean.IntArith.Checked.checkedNeg ad
  let ni ← JuliaLean.IntArith.Checked.checkedAdd bc nad
  return ⟨← ofInts nr den, ← ofInts ni den⟩

def arrayExactDiv (broadcast : α → β → γ) (xs : α) (y : β) : γ := broadcast xs y

/-- Integer `rationalize` overload. The keyword tolerance is accepted but not
read by the Julia body; `base/rational.jl:334-342`. -/
def rationalizeInteger (t : IntTy) (x _tol : Int) : MathRat :=
  if x < t.min then ⟨-1, 0⟩
  else if t.max < x then ⟨1, 0⟩
  else ⟨x, 1⟩

def rationalizeIntegerDefault (x : Int) : MathRat := ⟨x, 1⟩

/-- Rational accessors and predicates; `base/rational.jl:360-397,641-642`. -/
def signbit {t} (x : Rat t) : Bool := x.num.val < 0
def isinteger {t} (x : Rat t) : Bool := x.den.val == 1
def iszero {t} (x : Rat t) : Bool := x.num.val == 0
def isone {t} (x : Rat t) : Bool := x.num.val == 1 && x.den.val == 1
def decompose {t} (x : Rat t) : Int × Int × Int := (x.num.val, 0, x.den.val)

def sign {t} (x : Rat t) : Rat t :=
  ⟨JInt.lit t (if x.num.val < 0 then -1 else if x.num.val > 0 then 1 else 0),
   JInt.lit t 1⟩

def ispow2 {t} (ispow2 : JInt t → Bool) (x : Rat t) : Bool :=
  ispow2 x.num && ispow2 x.den

def negUnchecked {t} (x : Rat t) : Rat t := ⟨-x.num, x.den⟩
def negWrap {t} (x : Rat t) : Rat t := ⟨-x.num, x.den⟩

/-- Explicit wrapping rational addition and subtraction; `base/rational.jl:424-449`. -/
def addWrap {t} (x y : Rat t) : Jl (Rat t) := do
  if x.den.val = 0 ∧ eq x y = true then return x
  let p ← divgcd x.den y.den
  ofInts (x.num * p.2 + y.num * p.1) (x.den * p.2)

def subWrap {t} (x y : Rat t) : Jl (Rat t) := do
  if x.den.val = 0 then
    let ny := negUnchecked y
    if eq x ny then return x
  let p ← divgcd x.den y.den
  ofInts (x.num * p.2 - y.num * p.1) (x.den * p.2)

def boolMul {t} (b : Bool) (x : Rat t) : Rat t :=
  if b then x
  else ⟨JInt.lit t 0, JInt.lit t 1⟩

def fma {t} (x y z : Rat t) : Jl (Rat t) := do
  let p ← mul x y
  add p z

/-- Promotion and widening of rational component types;
`base/rational.jl:230-234`. -/
def promoteComponent (promote : α → β → γ) (rationalType : γ → δ) (t : α) (s : β) : δ :=
  rationalType (promote t s)
def widenType (widen : α → β) (rationalType : β → γ) (t : α) : γ := rationalType (widen t)
def floatType (float : α → β) (t : α) : β := float t
def throwNegateUnsigned : Jl α := .error (.overflowError "cannot negate unsigned number")
def bottomRationalize : Jl α := .error (.methodError "rationalize")

/-- Rational/complex equality ambiguity methods; `base/rational.jl:583-584`. -/
def eqComplex (isreal : Pair α → Bool) (eq : α → β → Bool)
    (z : Pair α) (x : β) : Bool := isreal z && eq z.re x

/-- `==(::AbstractFloat,::Rational)`; `base/rational.jl:521-527`. -/
def eqFloat (isfinite : α → Bool) (countOnes : β → Nat)
    (ldexp : α → Int → α) (topBit : β → Int) (eqFloatInt : α → γ → Bool)
    (divide : γ → β → α) (eqFloat : α → α → Bool)
    (x : α) (num : γ) (den : β) : Bool :=
  if isfinite x then countOnes den == 1 && eqFloatInt (ldexp x (topBit den)) num
  else eqFloat x (divide num den)

/-- Componentwise rationalization wrappers; `base/rational.jl:320-343`. -/
def rationalizeComplex (rationalize : α → β) (z : Pair α) : Pair β :=
  ⟨rationalize z.re, rationalize z.im⟩

/-- Generic power forwarding wrappers; `base/rational.jl:628-639`. -/
def powerRationalExponent (div : α → α → β) (pow : γ → β → δ)
    (x : γ) (num den : α) : δ := pow x (div num den)
def powerBool (one : Pair α → Pair α)
    (z : Pair α) (n : Bool) : Pair α := if n then z else one z

def powerInteger (nonnegative : Int → Bool) (pow : α → Int → α)
    (inverse : α → α) (x : α) (n : Int) : α :=
  if nonnegative n then pow x n else pow (inverse x) (-n)

def convertVia (first : α → β) (second : β → γ) (x : α) : γ := second (first x)
def bigRat (big : α → β) (unsafeCtor : β → β → γ) (num den : α) : γ :=
  unsafeCtor (big num) (big den)

/-- Rational-input rationalize branch at `base/rational.jl:326-333`; booleans
are the observable results of the source range and tolerance predicates. -/
def rationalizeRat (convert : α → Jl β) (rationalizeFloat : Unit → Jl β) (x : α)
    (unsignedNegative fits toleranceSufficient : Bool) : Jl β :=
  if unsignedNegative then .error (.overflowError "cannot negate unsigned number")
  else if fits then convert x
  else if toleranceSufficient then rationalizeFloat ()
  else .error (.inexactError "rationalize")

def roundBool (targetIsInteger denominatorFalse : Bool) (convert : α → Jl β)
    (x : α) : Jl β :=
  if denominatorFalse && targetIsInteger then .error .divideError else convert x

/-- Linear rational interpolation; `base/rational.jl:644-646`. -/
def lerpi (sub mul div add : α → α → α) (j d a b : α) : α :=
  add (div (mul (sub d j) a) d) (div (mul j b) d)

/-- Rational gcd/lcm shapes; `base/rational.jl:650-661`. -/
def gcd (gcd lcm : α → α → α) (x y : α × α) : α × α :=
  (gcd x.1 y.1, lcm x.2 y.2)
def lcm (gcd lcm : α → α → α) (x y : α × α) : α × α :=
  (lcm x.1 y.1, gcd x.2 y.2)

/-- Rational gcd/lcm and extended gcd; `base/rational.jl:650-674`. -/
def gcdRat {t} (x y : Rat t) : Jl (Rat t) := do
  if (x.den.val = 0) != (y.den.val = 0) then
    throw (.argumentError "gcd finite/infinite")
  let n ← JuliaLean.IntArith.NumberTheory.gcd x.num y.num
  let d ← JuliaLean.IntArith.NumberTheory.lcm x.den y.den
  return ⟨n, d⟩

def lcmRat {t} (x y : Rat t) : Jl (Rat t) := do
  if (x.den.val = 0) != (y.den.val = 0) then
    throw (.argumentError "lcm finite/infinite")
  let n ← JuliaLean.IntArith.NumberTheory.lcm x.num y.num
  let d ← JuliaLean.IntArith.NumberTheory.gcd x.den y.den
  return ⟨n, d⟩

def idivRat {t} (x c : Rat t) : Jl (JInt t) := do
  let a ← JInt.div x.num c.num
  let b ← JInt.div c.den x.den
  return a * b

def gcdxRat {t} (x y : Rat t) : Jl (Rat t × JInt t × JInt t) := do
  let c ← gcdRat x y
  if c.num.val = 0 then return (c, JInt.lit t 0, c.num)
  if c.den.val = 0 then
    return (c, if x.den.val = 0 then JInt.lit t 1 else c.den,
      if y.den.val = 0 then JInt.lit t 1 else c.den)
  let ix ← idivRat x c
  let iy ← idivRat y c
  let g ← JuliaLean.IntArith.NumberTheory.gcdx ix iy
  return (c, g.2.1, g.2.2)

/-- `typemin` and `typemax` rational values; `base/rational.jl:392-394`. -/
def typemin (t : IntTy) : Rat t :=
  if t.signed then ⟨JInt.lit t (-1), JInt.lit t 0⟩
  else ⟨JInt.lit t 0, JInt.lit t 1⟩
def typemax (t : IntTy) : Rat t := ⟨JInt.lit t 1, JInt.lit t 0⟩

/-- Rational range `length`; `base/rational.jl:707-712`. -/
def rangeLength {t} (first last : Rat t) : Jl (JInt t) := do
  let d ← JInt.div (last.num - first.num + first.den) first.den
  return d

/-- `checked_length`; `base/rational.jl:713-720`. -/
def checkedRangeLength {t} (first last : Rat t) (empty : Bool) : Jl (JInt t) :=
  if empty then .ok (first.num - first.num)
  else do
    let d ← JuliaLean.IntArith.Checked.checkedSub last.num first.num
    let n ← JuliaLean.IntArith.Checked.checkedAdd d first.den
    JInt.div n first.den

end RationalModel

/-! ## Generic complex component methods -/

namespace ComplexModel

structure Cx (α : Type) where
  re : α
  im : α
  deriving DecidableEq, Repr

structure ScalarOps (α : Type) extends GenericOps α where
  identical : α → α → Bool
  ofInt : Int → α
  sin : α → α
  cos : α → α
  sinpi : α → α
  cospi : α → α
  sinh : α → α
  cosh : α → α
  tan : α → α
  tanh : α → α
  asinh : α → α
  muladd : α → α → α → α
  exp : α → α
  expm1 : α → α
  exp2 : α → α
  exp10 : α → α
  log : α → α
  log1p : α → α
  sqrt : α → α
  abs : α → α
  copysign : α → α → α
  round : α → α
  eps : α → α
  nextfloat : α → α
  prevfloat : α → α
  exponent : α → Int
  ldexp : α → Int → α
  floatmin : α
  floatmax : α
  pi : α

/-- Constructors and accessors; `base/complex.jl:17-18,42-47,72-124`. -/
def make (x y : α) : Cx α := ⟨x, y⟩
def ofReal (o : GenericOps α) (x : α) : Cx α := ⟨x, o.zero x⟩
def real (z : Cx α) : α := z.re
def imag (z : Cx α) : α := z.im
def reim (z : Cx α) : α × α := (z.re, z.im)

def constructPromoted (promote : α → β → γ × γ) (x : α) (y : β) : Cx γ :=
  let p := promote x y
  ⟨p.1, p.2⟩
def constructTypedReal (convert : α → β) (zero : β) (x : α) : Cx β :=
  ⟨convert x, zero⟩
def constructTypedComplex (convert : α → β) (z : Cx α) : Cx β :=
  ⟨convert z.re, convert z.im⟩
def realConvert (isreal : Cx α → Bool) (convert : α → β)
    (typeName : String) (z : Cx α) : Jl β :=
  if isreal z then .ok (convert z.re) else .error (.inexactError typeName)
def complexIdentity (z : Cx α) : Cx α := z
def realOfReal (x : α) : α := x
def imagOfReal (zero : α → α) (x : α) : α := zero x
def reimGeneric (real imag : α → β) (z : α) : β × β := (real z, imag z)

/-- Type-level promotion, widening, and real/complex component selection;
`base/complex.jl:49-57,120-124,190-195`. -/
def promoteType (promote : α → β → γ) (complexType : γ → δ) (a : α) (b : β) : δ :=
  complexType (promote a b)
def mapType (f : α → β) (complexType : β → γ) (t : α) : γ := complexType (f t)
def realTypeGeneric (zero : α → β) (real : β → γ) (typeOf : γ → δ) (t : α) : δ :=
  typeOf (real (zero t))
def realTypeIdentity (t : α) : α := t
def realTypeComplex (fieldType : α → β) (t : α) : β := fieldType t
def bottomType : Jl α := .error (.methodError "bottom type")

/-- Predicates; `base/complex.jl:148-155`. -/
def isreal (o : GenericOps α) (z : Cx α) : Bool := o.eq z.im (o.zero z.im)
def isinteger (o : GenericOps α) (integer : α → Bool) (z : Cx α) : Bool :=
  isreal o z && integer z.re
def isfinite (o : GenericOps α) (z : Cx α) : Bool := o.isfinite z.re && o.isfinite z.im
def isnan (o : GenericOps α) (z : Cx α) : Bool := o.isnan z.re || o.isnan z.im
def isinf (o : GenericOps α) (z : Cx α) : Bool := o.isinf z.re || o.isinf z.im
def iszero (o : GenericOps α) (z : Cx α) : Bool := o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im)
def isone (o : GenericOps α) (z : Cx α) : Bool := o.eq z.re (o.one z.re) && o.eq z.im (o.zero z.im)

/-- Equality, total equality, and range membership; `base/complex.jl:246-254`. -/
def eq (o : GenericOps α) (z w : Cx α) : Bool := o.eq z.re w.re && o.eq z.im w.im
def eqReal (o : GenericOps α) (z : Cx α) (x : α) : Bool := isreal o z && o.eq z.re x
def eqRealLeft (o : GenericOps α) (x : α) (z : Cx α) : Bool := isreal o z && o.eq z.re x
def isequal (eq : α → α → Bool) (z w : Cx α) : Bool := eq z.re w.re && eq z.im w.im
def isequalComplexReal (eq : α → α → Bool) (zero : α → α)
    (z : Cx α) (x : α) : Bool := eq z.re x && eq z.im (zero x)
def isequalRealComplex (eq : α → α → Bool) (zero : α → α)
    (x : α) (z : Cx α) : Bool := eq x z.re && eq (zero x) z.im
def memRealRange (o : GenericOps α) (mem : α → β → Bool) (z : Cx α) (r : β) : Bool :=
  isreal o z && mem z.re r

def flipsign (o : GenericOps α) (z : Cx α) (y : α) : Cx α :=
  if NumberModel.signbit o y then ⟨o.neg z.re, o.neg z.im⟩ else z

/-- Observable display and binary I/O shapes; `base/complex.jl:199-242`. -/
def showParts (realText imagText : String) (compact needsStar : Bool) : String :=
  let negative := imagText.startsWith "-"
  let imagText := if negative then (imagText.drop 1).toString else imagText
  realText ++
    (if negative then (if compact then "-" else " - ")
     else if compact then "+" else " + ") ++
    imagText ++ (if needsStar then "*" else "") ++ "im"
def showBool (isImaginaryUnit : Bool) (re im : Bool) : String :=
  if isImaginaryUnit then "im" else s!"Complex({re},{im})"
def showUnquoted (render : α → String) (needsParens : Bool) (z : α) : String :=
  if needsParens then "(" ++ render z ++ ")" else render z
def readPair (read : Unit → α × α) : Cx α :=
  let p := read (); ⟨p.1, p.2⟩
def writePair (write : α → α → β) (z : Cx α) : β := write z.re z.im
def bswap (swap : α → α) (z : Cx α) : Cx α := ⟨swap z.re, swap z.im⟩
def hash (hashScalar : α → Nat → Nat) (hImag hashZero : Nat) (z : Cx α) (h : Nat) : Nat :=
  hashScalar z.re (Nat.xor h (Nat.xor (hashScalar z.im hImag) hashZero))

/-- Componentwise arithmetic; `base/complex.jl:280-355`. -/
def conj (o : GenericOps α) (z : Cx α) : Cx α := ⟨z.re, o.neg z.im⟩
def abs2 (o : GenericOps α) (z : Cx α) : α := o.add (o.mul z.re z.re) (o.mul z.im z.im)
def pos (o : GenericOps α) (z : Cx α) : Cx α := ⟨o.pos z.re, o.pos z.im⟩
def neg (o : GenericOps α) (z : Cx α) : Cx α := ⟨o.neg z.re, o.neg z.im⟩
def add (o : GenericOps α) (z w : Cx α) : Cx α := ⟨o.add z.re w.re, o.add z.im w.im⟩
def sub (o : GenericOps α) (z w : Cx α) : Cx α := ⟨o.sub z.re w.re, o.sub z.im w.im⟩
def mul (o : GenericOps α) (z w : Cx α) : Cx α :=
  ⟨o.sub (o.mul z.re w.re) (o.mul z.im w.im),
   o.add (o.mul z.re w.im) (o.mul z.im w.re)⟩
def addReal (o : GenericOps α) (x : α) (z : Cx α) : Cx α := ⟨o.add x z.re, z.im⟩
def subRealComplex (o : GenericOps α) (x : α) (z : Cx α) : Cx α :=
  ⟨o.sub x z.re, o.neg z.im⟩
def subComplexReal (o : GenericOps α) (z : Cx α) (x : α) : Cx α := ⟨o.sub z.re x, z.im⟩
def mulReal (o : GenericOps α) (x : α) (z : Cx α) : Cx α := ⟨o.mul x z.re, o.mul x z.im⟩
def divReal (o : GenericOps α) (z : Cx α) (x : α) : Cx α := ⟨o.div z.re x, o.div z.im x⟩

def invGeneric (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.isinf z.re || o.isinf z.im then
    ⟨o.copysign (o.zero z.re) z.re, o.neg (o.copysign (o.zero z.im) z.im)⟩
  else
    divReal o.toGenericOps ⟨z.re, o.neg z.im⟩
      (o.add (o.mul z.re z.re) (o.mul z.im z.im))

def invInteger (float : Cx α → Cx β) (inv : Cx β → Cx β) (z : Cx α) : Cx β :=
  inv (float z)

def mulsub (muladd : α → α → α → α) (neg : α → α) (a b c : α) : α :=
  muladd a b (neg c)
def mulsubPromoted (promote : α → β → γ → δ × δ × δ)
    (mulsub : δ → δ → δ → ε) (a : α) (b : β) (c : γ) : ε :=
  let p := promote a b c
  mulsub p.1 p.2.1 p.2.2

def muladdComplex (muladd : α → α → α → α) (mulsub : α → α → α → α)
    (neg : α → α) (z w x : Cx α) : Cx α :=
  ⟨muladd z.re w.re (neg (mulsub z.im w.im x.re)),
   muladd z.re w.im (muladd z.im w.re x.im)⟩

def muladdComplexReal (muladd : α → α → α → α) (mul : α → α → α)
    (z : Cx α) (x y : α) : Cx α :=
  ⟨muladd z.re x y, mul z.im x⟩
def muladdComplexScalar (muladd : α → α → α → α) (z : Cx α) (x : α)
    (w : Cx α) : Cx α := ⟨muladd z.re x w.re, muladd z.im x w.im⟩
def muladdRealRealComplex (muladd : α → α → α → α) (x y : α) (z : Cx α) : Cx α :=
  ⟨muladd x y z.re, z.im⟩
def muladdSwap (muladd : Cx α → α → β → γ) (x : α) (z : Cx α) (y : β) : γ :=
  muladd z x y
def muladdComplexComplexReal (muladd : α → α → α → α)
    (mulsub : α → α → α → α) (neg : α → α) (mul : α → α → α)
    (z w : Cx α) (x : α) : Cx α :=
  ⟨muladd z.re w.re (neg (mulsub z.im w.im x)),
   muladd z.re w.im (mul z.im w.re)⟩

def realDivComplex (promote : α → Cx β → γ × Cx γ) (mul : γ → Cx γ → Cx γ)
    (inv : Cx γ → Cx γ) (a : α) (z : Cx β) : Cx γ :=
  let p := promote a z
  mul p.1 (inv p.2)

/-- Generic same-component complex division; `base/complex.jl:360-377`. -/
def divGeneric (o : ScalarOps α) (a b : Cx α) : Cx α :=
  if o.isinf b.re || o.isinf b.im then
    if isfinite o.toGenericOps a then
      ⟨o.mul (o.mul (o.zero a.re) (NumberModel.signReal o.toGenericOps a.re))
          (NumberModel.signReal o.toGenericOps b.re),
       o.mul (o.neg (o.mul (o.zero a.im) (NumberModel.signReal o.toGenericOps a.im)))
          (NumberModel.signReal o.toGenericOps b.im)⟩
    else
      let nan := o.div (o.zero a.re) (o.zero a.re)
      ⟨nan, nan⟩
  else if o.le (o.abs b.re) (o.abs b.im) then
    let r := o.div b.re b.im
    let den := o.add b.im (o.mul r b.re)
    ⟨o.div (o.add (o.mul a.re r) a.im) den,
     o.div (o.sub (o.mul a.im r) a.re) den⟩
  else
    let r := o.div b.im b.re
    let den := o.add b.re (o.mul r b.im)
    ⟨o.div (o.add a.re (o.mul a.im r)) den,
     o.div (o.sub a.im (o.mul a.re r)) den⟩

/-- Widened Float16/Float32 division; `base/complex.jl:379-392`. -/
def divSmall (small : ScalarOps α) (wide : ScalarOps β)
    (widen : Cx α → Cx β) (narrow : Cx β → Cx α) (z w : Cx α) : Cx α :=
  let ww := widen w
  let zz := widen z
  if wide.isinf ww.re || wide.isinf ww.im then
    if isfinite small.toGenericOps z then
      ⟨small.mul (small.mul (small.zero z.re) (NumberModel.signReal small.toGenericOps z.re))
          (NumberModel.signReal small.toGenericOps w.re),
       small.mul (small.neg (small.mul (small.zero z.im) (NumberModel.signReal small.toGenericOps z.im)))
          (NumberModel.signReal small.toGenericOps w.im)⟩
    else
      let nan := small.div (small.zero z.re) (small.zero z.re)
      ⟨nan, nan⟩
  else
    let mag := wide.div (wide.one ww.re)
      (wide.muladd ww.re ww.re (wide.mul ww.im ww.im))
    let re := wide.muladd zz.re ww.re (wide.mul zz.im ww.im)
    let im := wide.muladd zz.im ww.re (wide.neg (wide.mul zz.re ww.im))
    narrow ⟨wide.mul re mag, wide.mul im mag⟩

def invSmall (small : ScalarOps α) (wide : ScalarOps β)
    (widen : Cx α → Cx β) (narrow : Cx β → Cx α) (z : Cx α) : Cx α :=
  let w := widen z
  if wide.isinf w.re || wide.isinf w.im then
    ⟨small.copysign (small.zero z.re) z.re,
     small.neg (small.copysign (small.zero z.im) z.im)⟩
  else
    let mag := wide.div (wide.one w.re)
      (wide.muladd w.re w.re (wide.mul w.im w.im))
    narrow ⟨wide.mul w.re mag, wide.neg (wide.mul w.im mag)⟩

/-- Generic `ssqs`; `base/complex.jl:519-531`. -/
def ssqs (o : ScalarOps α) (x y : α) : α × Int :=
  let rho0 := o.add (o.mul x x) (o.mul y y)
  let inf := o.div (o.one x) (o.zero x)
  if !o.isfinite rho0 && (o.isinf x || o.isinf y) then (inf, 0)
  else
    let threshold := o.div (o.nextfloat (o.zero x))
      (o.mul (o.ofInt 2) (o.mul (o.eps x) (o.eps x)))
    if o.isinf rho0 ||
        (o.eq rho0 (o.zero rho0) && (!o.eq x (o.zero x) || !o.eq y (o.zero y))) ||
        o.lt rho0 threshold then
      let m := if o.lt (o.abs x) (o.abs y) then o.abs y else o.abs x
      let k := if o.eq m (o.zero m) then 0 else o.exponent m
      let xk := o.ldexp x (-k)
      let yk := o.ldexp y (-k)
      (o.add (o.mul xk xk) (o.mul yk yk), k)
    else (rho0, 0)

/-- Main dispatch skeleton of `_cpow`; integer real exponents take the exact
power path and every other input takes the polar/logarithmic path. The supplied
callbacks implement the corresponding source blocks at `base/complex.jl:792-881`. -/
def cpow (float : Cx α → Cx α) (isreal : Cx α → Bool) (isinteger : α → Bool)
    (integerPower : Cx α → α → Cx α) (generalPower : Cx α → Cx α → Cx α)
    (z p : Cx α) : Cx α :=
  let z := float z
  let p := float p
  if isreal p && isinteger p.re then integerPower z p.re else generalPower z p

def cscale (o : GenericOps α) (r : α) (z : Cx α) : Cx α :=
  ⟨o.mul r z.re, o.mul r z.im⟩

def polarFinish (o : ScalarOps α) (cisF : α → Cx α) (r phi : α) : Cx α :=
  if o.isfinite phi then cscale o.toGenericOps r (cisF phi)
  else if o.eq r (o.zero r) then ⟨o.zero r, o.zero r⟩
  else
    let nan := o.div (o.zero r) (o.zero r)
    ⟨nan, nan⟩

def polarMagnitude (o : ScalarOps α) (r pr reLog imPhase : α) : α :=
  let lim := o.sub (o.log o.floatmax) (o.one o.floatmax)
  if o.lt (o.abs reLog) lim && o.lt (o.abs imPhase) lim then
    o.mul (o.pow r pr) (o.exp (o.neg imPhase))
  else o.exp (o.sub reLog imPhase)

/-- `_cpow` at `base/complex.jl:792-881`. Real Julia operands are represented
as complex values with zero imaginary component; `zWasReal` retains the source
union arm needed for the signed-zero rule at line 828. -/
def cpowFull (o : ScalarOps α) (float : Cx α → Cx α)
    (isinteger : α → Bool) (toInt : α → Int)
    (powerC : Cx α → Int → Cx α) (invC : Cx α → Cx α)
    (absC : Cx α → α) (cisF : α → Cx α) (angleF : Cx α → α)
    (zWasReal : Bool) (z0 p0 : Cx α) : Cx α :=
  let z := float z0
  let p := float p0
  let nan := o.div (o.zero z.re) (o.zero z.re)
  if isreal o.toGenericOps p then
    let pr := p.re
    if isinteger pr && o.lt (o.abs pr) (o.ofInt 2147483647) then
      if o.eq pr (o.zero pr) then
        let zi := if NumberModel.signbit o.toGenericOps p.re != NumberModel.signbit o.toGenericOps z.im
          then o.neg (o.zero z.im) else o.zero z.im
        ⟨o.one z.re, zi⟩
      else
        let ip := toInt pr
        if isreal o.toGenericOps z then
          if ip < 0 then
            if iszero o.toGenericOps z then ⟨nan, nan⟩
            else
              let re := o.pow (o.div (o.one z.re) z.re) (o.ofInt (-ip))
              let im := o.neg z.im
              ⟨re, if decide (ip % 2 = 0) && NumberModel.signbit o.toGenericOps z.re
                then o.neg im else im⟩
          else
            let re := o.pow z.re (o.ofInt ip)
            ⟨re, if decide (ip % 2 = 0) && NumberModel.signbit o.toGenericOps z.re
              then o.neg z.im else z.im⟩
        else if ip < 0 then powerC (invC z) (-ip) else powerC z ip
    else if isreal o.toGenericOps z then
      if o.eq z.re (o.zero z.re) then
        if o.lt (o.zero pr) pr then z else ⟨nan, nan⟩
      else if o.lt (o.zero z.re) z.re then
        let im := if zWasReal then
          (if o.lt z.re (o.one z.re) then o.neg p.im else p.im)
          else if NumberModel.signbit o.toGenericOps pr then o.neg z.im else z.im
        ⟨o.pow z.re pr, im⟩
      else
        let rp := o.pow (o.neg z.re) pr
        if o.isfinite pr then
          cscale o.toGenericOps rp
            ⟨o.cospi pr, if NumberModel.signbit o.toGenericOps z.im then o.neg (o.sinpi pr) else o.sinpi pr⟩
        else if o.eq rp (o.zero rp) then ⟨o.zero rp, o.zero rp⟩ else ⟨nan, nan⟩
    else
      let rp := o.pow (absC z) pr
      let phi := o.mul pr (angleF z)
      polarFinish o cisF rp phi
  else if isreal o.toGenericOps z then
    if iszero o.toGenericOps z then
      if o.lt (o.zero p.re) p.re then z else ⟨nan, nan⟩
    else if o.lt (o.zero z.re) z.re then
      let rp := o.pow z.re p.re
      let phi := o.mul p.im (o.log z.re)
      polarFinish o cisF rp phi
    else
      let r := o.neg z.re
      let theta := o.copysign o.pi z.im
      let logr := o.log r
      let reLog := o.mul p.re logr
      let imPhase := o.mul p.im theta
      let rp := polarMagnitude o r p.re reLog imPhase
      let phi := o.add (o.mul p.re theta) (o.mul p.im logr)
      polarFinish o cisF rp phi
  else
    let r := absC z
    let theta := angleF z
    let logr := o.log r
    let reLog := o.mul p.re logr
    let imPhase := o.mul p.im theta
    let rp := polarMagnitude o r p.re reLog imPhase
    let phi := o.add (o.mul p.re theta) (o.mul p.im logr)
    polarFinish o cisF rp phi

def powerBool (one : Cx α → Cx α) (z : Cx α) (n : Bool) : Cx α :=
  if n then z else one z
def powerCpow (cpow : Cx α → Cx β → Cx γ) (z : Cx α) (p : Cx β) : Cx γ :=
  cpow z p
def powerViaComplexExponent (toComplex : Int → Cx α)
    (pow : Cx α → Cx α → Cx α) (z : Cx α) (n : Int) : Cx α :=
  pow z (toComplex n)
def powerPromotedComplexReal (promote : α → β → γ)
    (convertComplex : γ → Cx α → Cx δ) (convertReal : γ → β → δ)
    (pow : Cx δ → δ → Cx δ) (component : α) (z : Cx α) (p : β) : Cx δ :=
  let t := promote component p
  pow (convertComplex t z) (convertReal t p)
def powerPromotedRealComplex (promote : α → β → γ)
    (convertReal : γ → α → δ) (convertComplex : γ → Cx β → Cx δ)
    (pow : δ → Cx δ → Cx δ) (z : α) (component : β) (p : Cx β) : Cx δ :=
  let t := promote z component
  pow (convertReal t z) (convertComplex t p)

/-- `cis` and `cispi`; `base/complex.jl:587-624`. -/
def cis (o : ScalarOps α) (theta : α) : Cx α := ⟨o.cos theta, o.sin theta⟩
def cisComplex (o : ScalarOps α) (z : Cx α) : Cx α :=
  let v := o.exp (o.neg z.im)
  ⟨o.mul v (o.cos z.re), o.mul v (o.sin z.re)⟩
def cispi (o : ScalarOps α) (theta : α) : Cx α :=
  ⟨o.cospi theta, o.sinpi theta⟩

def cispiComplex (o : ScalarOps α) (z : Cx α) : Cx α :=
  let v := o.exp (o.neg (o.mul o.pi z.im))
  ⟨o.mul v (o.cospi z.re), o.mul v (o.sinpi z.re)⟩

/-- Complex angle; `base/complex.jl:651`. -/
def angle (o : ScalarOps α) (z : Cx α) : α := o.atan2 z.im z.re

/-- Complex logarithm; `ssqs` supplies the source helper from
`base/complex.jl:519-531`; `base/complex.jl:653-674`. -/
def log (o : ScalarOps α) (ssqs : α → α → α × Int) (z : Cx α) : Cx α :=
  let p := ssqs z.re z.im
  let rho := p.1
  let k := p.2
  let ax := o.abs z.re
  let ay := o.abs z.im
  let theta := if o.lt ax ay then ax else ay
  let beta := if o.lt ax ay then ay else ax
  let one := o.ofInt 1
  let half := o.div one (o.ofInt 2)
  let near := o.lt half (o.mul beta beta) &&
    (!o.lt (o.div (o.ofInt 5) (o.ofInt 4)) beta || o.lt rho (o.ofInt 3))
  let mag := if k = 0 && near then
      o.div (o.log1p (o.add (o.mul (o.sub beta one) (o.add beta one)) (o.mul theta theta))) (o.ofInt 2)
    else o.add (o.div (o.log rho) (o.ofInt 2)) (o.mul (o.ofInt k) (o.log (o.ofInt 2)))
  ⟨mag, angle o z⟩

/-- Complex exponential, including source special-value branches;
`base/complex.jl:704-725`. -/
def exp (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.isnan z.re then ⟨z.re, if o.eq z.im (o.zero z.im) then z.im else z.re⟩
  else if !o.isfinite z.im then
    if o.isinf z.re && !NumberModel.signbit o.toGenericOps z.re then
      ⟨o.neg z.re, o.div (o.zero z.re) (o.zero z.re)⟩
    else if o.isinf z.re then ⟨o.neg (o.zero z.re), o.copysign (o.zero z.im) z.im⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
  else
    let er := o.exp z.re
    if o.eq z.im (o.zero z.im) then ⟨er, z.im⟩
    else ⟨o.mul er (o.cos z.im), o.mul er (o.sin z.im)⟩

/-- Complex `expm1`; `base/complex.jl:727-755`. -/
def expm1 (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.isnan z.re then ⟨z.re, if o.eq z.im (o.zero z.im) then z.im else z.re⟩
  else if !o.isfinite z.im then
    if o.isinf z.re && !NumberModel.signbit o.toGenericOps z.re then
      ⟨o.neg z.re, o.div (o.zero z.re) (o.zero z.re)⟩
    else if o.isinf z.re then ⟨o.neg (o.one z.re), o.copysign (o.zero z.im) z.im⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
  else
    let em1 := o.expm1 z.re
    if o.eq z.im (o.zero z.im) then ⟨em1, z.im⟩
    else
      let er := o.add em1 (o.one em1)
      if o.isfinite er then
        let half := o.div (o.one z.im) (o.ofInt 2)
        ⟨o.sub em1 (o.mul (o.ofInt 2) (o.mul er (o.mul (o.sin (o.mul half z.im)) (o.sin (o.mul half z.im))))),
         o.mul er (o.sin z.im)⟩
      else ⟨o.mul er (o.cos z.im), o.mul er (o.sin z.im)⟩

/-- Complex `log1p`; `base/complex.jl:757-773`. -/
def log1p (o : ScalarOps α) (logC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isfinite z.re then
    if o.isinf z.im then logC z
    else
      let u := add o.toGenericOps ⟨o.one z.re, o.zero z.im⟩ z
      if eq o.toGenericOps u ⟨o.one z.re, o.zero z.im⟩ then z
      else if !o.lt (o.zero u.re) u.re then logC u
      else mul o.toGenericOps (logC u) (divReal o.toGenericOps z (o.sub u.re (o.one u.re)))
  else if o.isnan z.re then ⟨z.re, z.re⟩
  else if o.isfinite z.im then
    ⟨o.div (o.one z.re) (o.zero z.re), o.copysign (if o.lt (o.zero z.re) z.re then o.zero z.re else o.pi) z.im⟩
  else ⟨o.div (o.one z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩

/-- Complex `exp2` and `exp10`; `base/complex.jl:775-789`. -/
def exp2 (o : ScalarOps α) (z : Cx α) : Cx α :=
  let er := o.exp2 z.re
  let theta := o.mul z.im (o.log (o.ofInt 2))
  ⟨o.mul er (o.cos theta), o.mul er (o.sin theta)⟩
def exp10 (o : ScalarOps α) (z : Cx α) : Cx α :=
  let er := o.exp10 z.re
  let theta := o.mul z.im (o.log (o.ofInt 10))
  ⟨o.mul er (o.cos theta), o.mul er (o.sin theta)⟩

/-- Complex sine and cosine; `base/complex.jl:905-940`. -/
def sin (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.eq z.re (o.zero z.re) then ⟨z.re, o.sinh z.im⟩
  else if !o.isfinite z.re then
    if o.eq z.im (o.zero z.im) || o.isinf z.im then
      ⟨o.div (o.zero z.re) (o.zero z.re), z.im⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩
  else ⟨o.mul (o.sin z.re) (o.cosh z.im), o.mul (o.cos z.re) (o.sinh z.im)⟩

def cos (o : ScalarOps α) (z : Cx α) : Cx α :=
  if o.eq z.re (o.zero z.re) then
    ⟨o.cosh z.im, if o.isnan z.im then z.re else o.neg (o.copysign z.re z.im)⟩
  else if !o.isfinite z.re then
    if o.eq z.im (o.zero z.im) then
      ⟨o.div (o.zero z.re) (o.zero z.re), if o.isnan z.re then o.zero z.re else o.neg (o.copysign z.im z.re)⟩
    else if o.isinf z.im then ⟨o.div (o.one z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.re) (o.zero z.re)⟩
  else ⟨o.mul (o.cos z.re) (o.cosh z.im), o.neg (o.mul (o.sin z.re) (o.sinh z.im))⟩

/-- Complex inverse sine; `base/complex.jl:949-961`. -/
def asin (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isinf z.re && o.isinf z.im then
    ⟨o.copysign (o.div o.pi (o.ofInt 4)) z.re, z.im⟩
  else if o.isnan z.im && o.isinf z.re then
    ⟨z.im, o.div (o.one z.re) (o.zero z.re)⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let oneMinus := sub o.toGenericOps one z
    let onePlus := add o.toGenericOps one z
    let a := sqrtC oneMinus
    let b := sqrtC onePlus
    let xi := if o.eq z.re (o.zero z.re) then z.re
      else if !o.isfinite z.re then o.mul (o.div o.pi (o.ofInt 2)) (if o.lt z.re (o.zero z.re) then o.neg (o.one z.re) else o.one z.re)
      else o.atan2 z.re (mul o.toGenericOps a b).re
    let etaTerm := mul o.toGenericOps (sqrtC (conj o.toGenericOps oneMinus)) b
    let eta := o.asinh (o.copysign etaTerm.im z.im)
    ⟨xi, eta⟩

/-- Complex inverse cosine; `base/complex.jl:963-984`. -/
def acos (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isnan z.re then
    if o.isinf z.im then ⟨z.re, o.neg z.im⟩ else ⟨z.re, z.re⟩
  else if o.isnan z.im then
    if o.isinf z.re then ⟨z.im, o.abs z.re⟩
    else if o.eq z.re (o.zero z.re) then ⟨o.div o.pi (o.ofInt 2), z.im⟩ else ⟨z.im, z.im⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps one z)
    let b := sqrtC (add o.toGenericOps one z)
    let xi := o.mul (o.ofInt 2) (o.atan2 a.re b.re)
    let eta := o.asinh (mul o.toGenericOps (conj o.toGenericOps b) a).im
    ⟨xi, eta⟩

/-- Full `acos` including signed-zero and infinite branches;
`base/complex.jl:963-984`. -/
def acosFull (o : ScalarOps α) (float : Cx α → Cx α)
    (sqrtC : Cx α → Cx α) (z0 : Cx α) : Cx α :=
  let z := float z0
  if o.isnan z.re then
    if o.isinf z.im then ⟨z.re, o.neg z.im⟩ else ⟨z.re, z.re⟩
  else if o.isnan z.im then
    if o.isinf z.re then ⟨z.im, o.abs z.re⟩
    else if o.eq z.re (o.zero z.re) then ⟨o.div o.pi (o.ofInt 2), z.im⟩
    else ⟨z.im, z.im⟩
  else if o.eq z.re (o.zero z.re) && o.eq z.im (o.zero z.im) then
    ⟨o.div o.pi (o.ofInt 2), o.neg z.im⟩
  else if o.isinf z.re && !NumberModel.signbit o.toGenericOps z.re &&
      o.identical z.im (o.zero z.im) then
    ⟨z.im, o.neg z.re⟩
  else if o.isinf z.re && NumberModel.signbit o.toGenericOps z.re &&
      o.identical z.im (o.neg (o.zero z.im)) then
    ⟨o.pi, o.neg z.re⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps one z)
    let b := sqrtC (add o.toGenericOps one z)
    let xi0 := o.mul (o.ofInt 2) (o.atan2 a.re b.re)
    let eta := o.asinh (mul o.toGenericOps (conj o.toGenericOps b) a).im
    let xi := if o.isinf z.re && o.isinf z.im then
      o.sub xi0 (o.mul (o.div o.pi (o.ofInt 4))
        (if o.lt z.re (o.zero z.re) then o.neg (o.one z.re) else o.one z.re))
      else xi0
    ⟨xi, eta⟩

/-- Complex hyperbolic tangent, retaining the source overflow split;
`base/complex.jl:1002-1022`. -/
def tanh (o : ScalarOps α) (overflowThreshold : α) (z : Cx α) : Cx α :=
  if o.isnan z.re && o.eq z.im (o.zero z.im) then z
  else if o.lt overflowThreshold (o.mul (o.ofInt 4) (o.abs z.re)) then
    ⟨o.copysign (o.one z.re) z.re,
     o.copysign (o.zero z.im) (o.mul z.im (if o.isfinite z.im then o.sin (o.mul (o.ofInt 2) (o.abs z.im)) else o.one z.im))⟩
  else
    let t := o.tan z.im
    let beta := o.add (o.one t) (o.mul t t)
    let s := o.sinh z.re
    let rho := o.sqrt (o.add (o.one s) (o.mul s s))
    if o.isinf t then ⟨o.div rho s, o.div (o.one t) t⟩
    else divReal o.toGenericOps ⟨o.mul beta (o.mul rho s), t⟩
      (o.add (o.one s) (o.mul beta (o.mul s s)))

/-- Complex inverse hyperbolic cosine; `base/complex.jl:1029-1046`. -/
def acosh (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  if o.isnan z.re || o.isnan z.im then
    if o.isinf z.re || o.isinf z.im then
      ⟨o.div (o.one z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
    else ⟨o.div (o.zero z.re) (o.zero z.re), o.div (o.zero z.im) (o.zero z.im)⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps z one)
    let b := sqrtC (add o.toGenericOps z one)
    ⟨o.asinh (mul o.toGenericOps (conj o.toGenericOps a) b).re,
     o.mul (o.ofInt 2) (o.atan2 a.im b.re)⟩

def acoshFull (o : ScalarOps α) (sqrtC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let nan := o.div (o.zero z.re) (o.zero z.re)
  if o.isnan z.re || o.isnan z.im then
    if o.isinf z.re || o.isinf z.im then
      ⟨o.div (o.one z.re) (o.zero z.re), nan⟩ else ⟨nan, nan⟩
  else if o.isinf z.re && NumberModel.signbit o.toGenericOps z.re &&
      o.identical z.im (o.neg (o.zero z.im)) then
    ⟨o.div (o.one z.re) (o.zero z.re), o.neg o.pi⟩
  else
    let one : Cx α := ⟨o.one z.re, o.zero z.im⟩
    let a := sqrtC (sub o.toGenericOps z one)
    let b := sqrtC (add o.toGenericOps z one)
    let xi := o.asinh (mul o.toGenericOps (conj o.toGenericOps a) b).re
    let eta0 := o.mul (o.ofInt 2) (o.atan2 a.im b.re)
    let eta := if o.isinf z.re && o.isinf z.im then
      o.sub eta0 (o.mul (o.div o.pi (o.ofInt 4))
        (o.mul (if o.lt z.im (o.zero z.im) then o.neg (o.one z.im) else o.one z.im)
          (if o.lt z.re (o.zero z.re) then o.neg (o.one z.re) else o.one z.re)))
      else eta0
    ⟨xi, eta⟩

/-- Complex inverse hyperbolic tangent; `base/complex.jl:1048-1089`. -/
def atanh (o : ScalarOps α) (large : α) (invC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let ax := o.abs z.re
  let ay := o.abs z.im
  if o.lt large ax || o.lt large ay then
    if o.isnan z.im then
      if o.isinf z.re then ⟨o.copysign (o.zero z.re) z.re, z.im⟩ else ⟨(invC z).re, z.im⟩
    else ⟨(invC z).re, o.copysign (o.div o.pi (o.ofInt 2)) z.im⟩
  else
    let beta := o.copysign (o.one z.re) z.re
    let x := o.mul z.re beta
    let y := o.mul z.im beta
    let ysq := o.mul (o.abs y) (o.abs y)
    let xi := if o.eq x (o.zero x) then x
      else o.div (o.log1p (o.div (o.mul (o.ofInt 4) x)
        (o.add (o.mul (o.sub (o.one x) x) (o.sub (o.one x) x)) ysq))) (o.ofInt 4)
    let eta := o.div (o.atan2 (o.mul (o.ofInt 2) y)
      (o.sub (o.mul (o.sub (o.one x) x) (o.add (o.one x) x)) ysq)) (o.ofInt 2)
    ⟨o.mul beta xi, o.mul beta eta⟩

def atanhFull (o : ScalarOps α) (large : α) (invC : Cx α → Cx α)
    (z : Cx α) : Cx α :=
  let ax := o.abs z.re
  let ay := o.abs z.im
  if o.lt large ax || o.lt large ay then
    if o.isnan z.im then
      if o.isinf z.re then ⟨o.copysign (o.zero z.re) z.re, z.im⟩
      else ⟨(invC z).re, z.im⟩
    else if o.isinf z.im then
      ⟨o.copysign (o.zero z.re) z.re, o.copysign (o.div o.pi (o.ofInt 2)) z.im⟩
    else ⟨(invC z).re, o.copysign (o.div o.pi (o.ofInt 2)) z.im⟩
  else
    let beta := o.copysign (o.one z.re) z.re
    let x := o.mul z.re beta
    let y := o.mul z.im beta
    let xiEta :=
      if o.eq x (o.one x) then
        if o.eq y (o.zero y) then
          (o.div (o.one x) (o.zero x), y)
        else
          let xi := o.log (o.div (o.sqrt (o.sqrt (o.add (o.mul y y) (o.ofInt 4))))
            (o.sqrt ay))
          let eta := o.div (o.copysign
            (o.add (o.div o.pi (o.ofInt 2)) (o.atan2 ay (o.ofInt 2))) y) (o.ofInt 2)
          (xi, eta)
      else
        let ysq := o.mul ay ay
        let xi := if o.eq x (o.zero x) then x
          else o.div (o.log1p (o.div (o.mul (o.ofInt 4) x)
            (o.add (o.mul (o.sub (o.one x) x) (o.sub (o.one x) x)) ysq))) (o.ofInt 4)
        let eta := o.div (o.atan2 (o.mul (o.ofInt 2) y)
          (o.sub (o.mul (o.sub (o.one x) x) (o.add (o.one x) x)) ysq)) (o.ofInt 2)
        (xi, eta)
    ⟨o.mul beta xiEta.1, o.mul beta xiEta.2⟩

/-- Analytic identities used by the short wrapper methods;
`base/complex.jl:695-702,943-1000,1024-1027`. -/
def logBase (o : ScalarOps α) (base : α) (logz : Cx α) : Cx α := divReal o.toGenericOps logz (o.log base)
def tanFromTanh (o : ScalarOps α) (tanhC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := tanhC ⟨o.neg z.im, z.re⟩
  ⟨w.im, o.neg w.re⟩
def atanFromAtanh (o : ScalarOps α) (atanhC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := atanhC ⟨o.neg z.im, z.re⟩
  ⟨w.im, o.neg w.re⟩
def sinhFromSin (_o : ScalarOps α) (sinC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := sinC ⟨z.im, z.re⟩
  ⟨w.im, w.re⟩
def coshFromCos (o : ScalarOps α) (cosC : Cx α → Cx α) (z : Cx α) : Cx α :=
  cosC ⟨z.im, o.neg z.re⟩
def asinhFromAsin (o : ScalarOps α) (asinC : Cx α → Cx α) (z : Cx α) : Cx α :=
  let w := asinC ⟨o.neg z.im, z.re⟩
  ⟨w.im, o.neg w.re⟩

/-- Componentwise rounding and conversions; `base/complex.jl:1123-1166`. -/
def round (rr ri : α → α) (z : Cx α) : Cx α := ⟨rr z.re, ri z.im⟩
def mapComponents (f : α → β) (z : Cx α) : Cx β := ⟨f z.re, f z.im⟩
def floatIdentity (z : Cx α) : Cx α := z
def bigType (big : α → β) (complexType : β → γ) (t : α) : γ := complexType (big t)
def bigValue (big : α → β) (convert : β → Cx α → Cx γ)
    (t : α) (z : Cx α) : Cx γ := convert (big t) z
def arrayComplexIdentity (xs : α) : α := xs
def arrayComplexConvert (isConcrete : Bool) (convert : α → β) (xs : α) : Jl β :=
  if isConcrete then .ok (convert xs)
  else .error (.argumentError "complex abstractly typed array")
def epsValue (o : ScalarOps α) (z : Cx α) : α :=
  o.sqrt (o.add (o.mul (o.eps z.re) (o.eps z.re)) (o.mul (o.eps z.im) (o.eps z.im)))
def epsType (o : ScalarOps α) (sample : α) : α :=
  o.mul (o.sqrt (o.add (o.one sample) (o.one sample))) (o.eps sample)

end ComplexModel

end JuliaLean.NumbersCov
