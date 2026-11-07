import JuliaLean.base.float
import JuliaLean.base.complex
import JuliaLean.base.floatfuncs
import JuliaLean.base.promotion
import JuliaLean.Runtime.Collections
import JuliaLean.base.error
import JuliaLean.base.checked
namespace JuliaLean.base.math

open JuliaLean JuliaLean.base.float
open JuliaLean.Promotion hiding FV FTy
/--
Julia source: base/math.jl:32-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_complex_domainerror(f::Symbol, x)
    throw(DomainError(x,
        LazyString(f," was called with a negative real argument but will only return a complex result if called with a complex argument. Try ", f,"(Complex(x)).")))
end
```
-/
def throwComplexDomainError {α : Type} (f : String) (_x : α) : Jl α :=
  .error (.domainError (f ++ " was called with a negative real argument but will only return a complex result if called with a complex argument. Try " ++ f ++ "(Complex(x))."))
/--
Julia source: base/math.jl:1265-1265 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
muladd(x,y,z) = x*y+z
```
-/
def muladdSource {m : Type → Type} [Monad m] {X Y P Z R : Type}
    (mul : X → Y → m P) (add : P → Z → m R)
    (x : X) (y : Y) (z : Z) : m R := do
  let product ← mul x y
  add product z

-- Source: base/math.jl:1265
def muladd {X Y P Z R : Type} (mul : X → Y → P) (add : P → Z → R)
    (x : X) (y : Y) (z : Z) : R :=
  muladdSource (m := Id) (fun x y => pure (mul x y)) (fun p z => pure (add p z)) x y z



structure IEEEOps (T : FTy) where
  sqrtLlvm : FV T → FV T
  eps : FV T
  floatmin : FV T
  floatmax : FV T
  invFloatmin : FV T
  pi : FV T
  fma : FV T → FV T → FV T → FV T
  twoMul : FV T → FV T → FV T × FV T
  trunc : FV T → FV T
  rem : FV T → FV T → FV T
  flipsign : FV T → FV T → FV T
  minFloat : FV T → FV T → FV T
  maxFloat : FV T → FV T → FV T
  clampUnsigned : Nat → Nat → Nat → Nat
  addFast : FV T → FV T → FV T
  oneunit : FV T → FV T
  inverse : FV T → FV T
  greater : FV T → FV T → Bool
  muladd : FV T → FV T → FV T → FV T
  abs2 : FV T → FV T
  haveFma : Bool

structure GenericHypotOps (α β : Type) where
  abs : α → β
  oneunit : β → β
  isinf : β → Bool
  isnan : β → Bool
  iszero : β → Bool
  isless : β → β → Bool
  lt : β → β → Bool
  greater : β → β → Bool
  le : β → β → Bool
  zero : β
  one : β
  infinity : β
  eps : β
  floatmin : β
  floatmax : β
  two : β
  four : β
  inverse : β → β
  sqrt : β → Jl β
  mul : β → β → β
  div : β → β → β
  add : β → β → β
  sub : β → β → β
  muladd : β → β → β → β
  fma : β → β → β → β
  divideInput : α → β → α
  abs2 : α → β
  haveFma : Bool
  neg : β → β := fun x => sub zero x
structure HypotDispatch (α β : Type) where
  pair : α → α → Jl β
  tuple : List α → Jl β

abbrev HypotArg := Σ α : Type, α

def packHypotArg {α : Type} (x : α) : HypotArg := ⟨α, x⟩

def packHypotArgs {α : Type} (xs : List α) : List HypotArg :=
  xs.map packHypotArg
structure AbstractFloatOps (α : Type) where
  typeName : String
  ofInt : Int → α
  pi : α
  mul : α → α → α
  div : α → α → α
  pow : α → α → α
  abs : α → α
  isnan : α → Bool
  signbit : α → Bool
  lt : α → α → Bool

structure HypotFloatReductionOps (T : FTy) where
  iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
    JuliaLean.base.reduce.EltypeStatus
  booleanOr : JuliaLean.base.reduce.Reducer Bool Bool
  Signed : Type
  reinterpretSigned : FV T → Signed
  reinterpretFloat : Signed → FV T
  maximumReducer : JuliaLean.base.reduce.Reducer Signed Signed
  sumReducer : JuliaLean.base.reduce.Reducer (FV T) (FV T)

structure IntegerStepOps (Unsigned : Type) (Shift : Type := Int) where
  one : Unsigned
  add : Unsigned → Unsigned → Unsigned
  mul : Unsigned → Unsigned → Unsigned
  ge : Unsigned → Unsigned → Bool
  shiftRight : Unsigned → Shift → Unsigned
  shiftOne : Shift
  addShift : Shift → Shift → Shift
  checkedAdd : Int → Shift → Jl Int

structure IntegerExponentOps (Integer Unsigned : Type) where
  iszero : Integer → Bool
  uabs : Integer → Unsigned
  step : IntegerStepOps Unsigned
abbrev Cx (T : FTy) := JuliaLean.base.complex.Complex (FV T)
inductive EvalpolyResult (T : FTy) (Coefficient : Type := FV T)
    (ComplexValue : Type := Cx T) where
  | real (value : Coefficient)
  | complex (value : ComplexValue)
structure JuliaSyntax where
  source : String
  deriving DecidableEq, Repr

inductive JuliaQuote where
  | escaped (node : JuliaSyntax)
  | tupleSplat (items : List JuliaQuote)
  | call (callee : String) (args : List JuliaQuote)
  | invoke (callee signature : String) (args : List JuliaQuote)


abbrev add {T : FTy} := JuliaLean.base.float.add_float (T := T)
abbrev sub {T : FTy} := JuliaLean.base.float.sub_float (T := T)
abbrev mul {T : FTy} := JuliaLean.base.float.mul_float (T := T)
abbrev div {T : FTy} := JuliaLean.base.float.div_float (T := T)
abbrev fzero (T : FTy) := JuliaLean.base.float.zero_float T
abbrev fone (T : FTy) := JuliaLean.base.float.one_float T
abbrev finf (T : FTy) := JuliaLean.base.float.inf_float T
abbrev fnan (T : FTy) := JuliaLean.base.float.nan_float T
abbrev fabs {T : FTy} := JuliaLean.base.float.abs_float (T := T)
abbrev fneg {T : FTy} := JuliaLean.base.float.neg_float (T := T)
abbrev feq {T : FTy} := JuliaLean.base.float.eq_float (T := T)
abbrev flt {T : FTy} := JuliaLean.base.float.lt_float (T := T)
abbrev fle {T : FTy} := JuliaLean.base.float.le_float (T := T)
abbrev fisnan {T : FTy} := JuliaLean.base.float.isnan_callee (T := T)
abbrev fisinf {T : FTy} := JuliaLean.base.float.isinf_callee (T := T)
abbrev fisfinite {T : FTy} := JuliaLean.base.float.isfinite_callee (T := T)
abbrev fiszero {T : FTy} := JuliaLean.base.float.iszero_float (T := T)
abbrev fsignbit {T : FTy} := JuliaLean.base.float.signbit_float (T := T)

private def bitMask (width : Nat) : Nat := 2 ^ width - 1
def signMask (T : FTy) : Nat := 2 ^ (T.fmt.eb + T.fmt.sb)
def exponentMask (T : FTy) : Nat := T.fmt.emax * 2 ^ T.fmt.sb
private def exponentRawMax (T : FTy) : Nat := T.fmt.emax
private def significandBits (T : FTy) : Nat := T.fmt.sb
private def exponentBits (T : FTy) : Nat := T.fmt.eb
private def exponentBias (T : FTy) : Nat := T.fmt.bias
def leadingZeros (width bits : Nat) : Nat :=
  if bits = 0 then width else width - bits.log2 - 1
def withoutBits (value mask width : Nat) : Nat := Nat.land value (bitMask width - mask)

theorem withoutSignBitMagnitude {T : FTy} (x : FV T) :
    withoutBits x.toBits (2 ^ (T.fmt.eb + T.fmt.sb)) T.fmt.width = x.magnitude := by
  have hwidth : T.fmt.width = T.fmt.eb + T.fmt.sb + 1 := by
    simp [JuliaLean.Promotion.Fmt.width]
    omega
  have hmask :
      (2 ^ (T.fmt.eb + T.fmt.sb + 1) - 1) -
        2 ^ (T.fmt.eb + T.fmt.sb) =
        2 ^ (T.fmt.eb + T.fmt.sb) - 1 := by
    have hp : 0 < 2 ^ (T.fmt.eb + T.fmt.sb) := Nat.two_pow_pos _
    rw [Nat.pow_succ]
    omega
  unfold withoutBits bitMask
  rw [hwidth, hmask]
  change Nat.land x.toBits (2 ^ (T.fmt.eb + T.fmt.sb) - 1) =
    x.toBits % 2 ^ (T.fmt.eb + T.fmt.sb)
  exact Nat.and_two_pow_sub_one_eq_mod _ _
private def hornerLoop {α : Type} (mul add : α → α → α) (x acc : α) : List α → α
  | [] => acc
  | c :: cs => hornerLoop mul add x (muladd mul add x acc c) cs

private def hornerValue {α : Type} (mul add : α → α → α) (x : α) (p : List α) : Option α :=
  match p.reverse with
  | [] => none
  | c :: cs => some (hornerLoop mul add x c cs)

def mixedHornerValue {X C R : Type}
    (muladdFirst : X → C → C → R) (muladdNext : X → R → C → R)
    (x : X) (p : List C) : Option (C ⊕ R) :=
  match p.reverse with
  | [] => none
  | [c] => some (.inl c)
  | c :: d :: cs => some (.inr
      (cs.foldl (fun acc coefficient => muladdNext x acc coefficient)
        (muladdFirst x c d)))


private def maximumBy {α : Type} (isless : α → α → Bool) (xs : List α) : Option α :=
  match xs with
  | [] => none
  | x :: rest => some (rest.foldl (fun m y => if isless m y then y else m) x)



/--
Julia source: base/math.jl:90-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _evalpoly(x, p)
    Base.require_one_based_indexing(p)
    N = length(p)
    ex = p[end]
    for i in N-1:-1:1
        ex = muladd(x, ex, p[i])
    end
    ex
end
```
-/
-- Source: base/math.jl:90-98
private def polynomialListIndex {C : Type} (p : List C) (i : JInt .i64) : Jl C :=
  if i.val < 1 then .error .boundsError
  else match p[(i.val - 1).toNat]? with
    | some coefficient => .ok coefficient
    | none => .error .boundsError

theorem polynomialListIndex_empty {C : Type} (i : JInt .i64) :
    polynomialListIndex ([] : List C) i = .error .boundsError := by
  simp [polynomialListIndex]

-- Source: base/math.jl:90-98
private def polynomialRealLoop {m : Type → Type} [Monad m] {P X C R : Type}
    (getindex : P → JInt .i64 → m C)
    (first : X → C → C → m R) (next : X → R → C → m R)
    (x : X) (p : P) : Nat → C ⊕ R → m (C ⊕ R)
  | 0, value => pure value
  | remaining + 1, value => do
    let coefficient ← getindex p (JInt.wrap .i64 (remaining + 1))
    let value ← match value with
      | .inl initial => first x initial coefficient
      | .inr accumulated => next x accumulated coefficient
    polynomialRealLoop getindex first next x p remaining (.inr value)

-- Source: base/math.jl:90-98
def evalpolyRealSource {m : Type → Type} [Monad m] {P X C R : Type}
    (requireOneBased : P → m Unit) (length lastindex : P → m (JInt .i64))
    (getindex : P → JInt .i64 → m C)
    (first : X → C → C → m R) (next : X → R → C → m R)
    (x : X) (p : P) : m (C ⊕ R) := do
  let _ ← requireOneBased p
  let n ← length p
  let last ← lastindex p
  let initial ← getindex p last
  polynomialRealLoop getindex first next x p
    (JuliaLean.base.int.sub_int n (JInt.lit .i64 1)).val.toNat (.inl initial)

def evalpolyReal {X C R : Type}
    (muladdFirst : X → C → C → R) (muladdNext : X → R → C → R)
    (requireOneBased : List C → Jl Unit) (x : X) (p : List C) :
    Jl (C ⊕ R) :=
  evalpolyRealSource requireOneBased (fun p => .ok (JInt.wrap .i64 p.length))
    (fun p => .ok (JInt.wrap .i64 p.length)) polynomialListIndex
    (fun x a b => .ok (muladdFirst x a b)) (fun x a b => .ok (muladdNext x a b)) x p

/--
Julia source: base/math.jl:88-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
evalpoly(x, p::AbstractVector) = _evalpoly(x, p)
```
-/
-- Source: base/math.jl:88
def evalpolyVectorSource {m : Type → Type} {P X Result : Type}
    (evalpoly : X → P → m Result) (x : X) (p : P) : m Result := evalpoly x p

def evalpolyVector {X C R : Type}
    (muladdFirst : X → C → C → R) (muladdNext : X → R → C → R)
    (requireOneBased : List C → Jl Unit) (x : X) (p : List C) :
    Jl (C ⊕ R) :=
  evalpolyVectorSource (evalpolyReal muladdFirst muladdNext requireOneBased) x p

/--
Julia source: base/math.jl:75-86 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function evalpoly(x, p::Tuple)
    if @generated
        N = length(p.parameters::Core.SimpleVector)
        ex = :(p[end])
        for i in N-1:-1:1
            ex = :(muladd(x, $ex, p[$i]))
        end
        ex
    else
        _evalpoly(x, p)
    end
end
```
-/
-- Source: base/math.jl:75-86
def evalpolyTupleSource {m : Type → Type} [Monad m] [MonadExceptOf JlError m] {X C R : Type}
    (first : X → C → C → m R) (next : X → R → C → m R)
    (requireOneBased : List C → m Unit) (generated : Bool) (x : X) (p : List C) :
    m (C ⊕ R) :=
  evalpolyRealSource (if generated then fun _ => pure () else requireOneBased)
    (fun p => pure (JInt.wrap .i64 p.length)) (fun p => pure (JInt.wrap .i64 p.length))
    (fun p i => match polynomialListIndex p i with
      | .ok value => pure value
      | .error error => throw error)
    first next x p

def evalpolyTuple {X C R : Type}
    (muladdFirst : X → C → C → R) (muladdNext : X → R → C → R)
    (requireOneBased : List C → Jl Unit) (generated : Bool) (x : X) (p : List C) :
    Jl (C ⊕ R) :=
  evalpolyTupleSource (fun x a b => .ok (muladdFirst x a b))
    (fun x a b => .ok (muladdNext x a b)) requireOneBased generated x p

theorem evalpolyTuple_generated_empty {X C R : Type}
    (first : X → C → C → R) (next : X → R → C → R)
    (require : List C → Jl Unit) (x : X) :
    evalpolyTuple first next require true x [] = .error .boundsError := by
  simp only [evalpolyTuple, evalpolyTupleSource, evalpolyRealSource, if_true,
    bind, Except.bind, pure, Except.pure, polynomialListIndex_empty]
  rfl

-- Source: base/math.jl:100-148
private def polynomialComplexLoop {m : Type → Type} [Monad m] {P A C R : Type}
    (getindex : P → JInt .i64 → m C) (neg : A → m A)
    (first : A → C → C → m R) (accum : A → R → R → m R)
    (next : A → R → C → m R) (r s : A) (p : P) :
    Nat → (C × C) ⊕ (R × R) → m ((C × C) ⊕ (R × R))
  | 0, state => pure state
  | remaining + 1, .inl (a, b) => do
    let nextA ← first r a b
    let minusS ← neg s
    let coefficient ← getindex p (JInt.wrap .i64 (remaining + 1))
    let nextB ← first minusS a coefficient
    polynomialComplexLoop getindex neg first accum next r s p remaining (.inr (nextA, nextB))
  | remaining + 1, .inr (a, b) => do
    let nextA ← accum r a b
    let minusS ← neg s
    let coefficient ← getindex p (JInt.wrap .i64 (remaining + 1))
    let nextB ← next minusS a coefficient
    polynomialComplexLoop getindex neg first accum next r s p remaining (.inr (nextA, nextB))

-- Source: base/math.jl:100-148
private def polynomialComplexEvaluate {m : Type → Type} [Monad m] {P A C R O : Type}
    (lastindex : P → m (JInt .i64)) (getindex : P → JInt .i64 → m C)
    (double : A → m A) (mul : A → A → m A) (muladd : A → A → A → m A)
    (neg : A → m A) (first : A → C → C → m R)
    (accum : A → R → R → m R) (next : A → R → C → m R)
    (complexFirst : C → JuliaLean.base.complex.Complex A → C → m O)
    (complexNext : R → JuliaLean.base.complex.Complex A → R → m O)
    (n : JInt .i64) (z : JuliaLean.base.complex.Complex A) (p : P) : m (C ⊕ O) := do
  let last ← lastindex p
  let a ← getindex p last
  let last ← lastindex p
  let b ← getindex p (JuliaLean.base.int.sub_int last (JInt.lit .i64 1))
  let x := JuliaLean.base.complex.real_Complex z
  let y := JuliaLean.base.complex.imag_Complex z
  let r ← double x
  let yy ← mul y y
  let s ← muladd x x yy
  let state ← polynomialComplexLoop getindex neg first accum next r s p
    (JuliaLean.base.int.sub_int n (JInt.lit .i64 2)).val.toNat (.inl (a, b))
  match state with
  | .inl (a, b) => return .inr (← complexFirst a z b)
  | .inr (a, b) => return .inr (← complexNext a z b)

-- Source: base/math.jl:130-148
def evalpolyComplexSource {m : Type → Type} [Monad m] {P A C R O : Type}
    (requireOneBased : P → m Unit) (length lastindex : P → m (JInt .i64))
    (getindex : P → JInt .i64 → m C)
    (mulInt : JInt .i64 → A → m A) (mul : A → A → m A)
    (muladd : A → A → A → m A) (neg : A → m A)
    (first : A → C → C → m R) (accum : A → R → R → m R)
    (next : A → R → C → m R)
    (complexFirst : C → JuliaLean.base.complex.Complex A → C → m O)
    (complexNext : R → JuliaLean.base.complex.Complex A → R → m O)
    (z : JuliaLean.base.complex.Complex A) (p : P) : m (C ⊕ O) := do
  let _ ← requireOneBased p
  let n ← length p
  if n.val == 1 then return .inl (← getindex p (JInt.lit .i64 1))
  let n ← length p
  polynomialComplexEvaluate lastindex getindex (mulInt (JInt.lit .i64 2))
    mul muladd neg first accum next complexFirst complexNext n z p

-- Source: base/math.jl:100-124
private def polynomialComplexGeneratedLoop {m : Type → Type} [Monad m] {P A C R O : Type}
    (getindex : P → JInt .i64 → m C) (neg : A → m A)
    (first : A → C → C → m R) (accum : A → R → R → m R)
    (next : A → R → C → m R)
    (complexFirst : C → JuliaLean.base.complex.Complex A → C → m O)
    (complexNext : R → JuliaLean.base.complex.Complex A → R → m O)
    (r s : A) (z : JuliaLean.base.complex.Complex A) (p : P) :
    Nat → (C × (Unit → m C)) ⊕ (R × (Unit → m R)) → m O
  | 0, .inl (a, b) => do complexFirst a z (← b ())
  | 0, .inr (a, b) => do complexNext a z (← b ())
  | remaining + 1, .inl (a, b) => do
    let nextA ← first r a (← b ())
    let nextB := fun _ : Unit => do
      let minusS ← neg s
      first minusS a (← getindex p (JInt.wrap .i64 (remaining + 1)))
    polynomialComplexGeneratedLoop getindex neg first accum next complexFirst complexNext
      r s z p remaining (.inr (nextA, nextB))
  | remaining + 1, .inr (a, b) => do
    let nextA ← accum r a (← b ())
    let nextB := fun _ : Unit => do
      let minusS ← neg s
      next minusS a (← getindex p (JInt.wrap .i64 (remaining + 1)))
    polynomialComplexGeneratedLoop getindex neg first accum next complexFirst complexNext
      r s z p remaining (.inr (nextA, nextB))

-- Source: base/math.jl:100-124
def evalpolyComplexTupleSource {m : Type → Type} [Monad m] {P A C R O : Type}
    (length lastindex : P → m (JInt .i64)) (getindex : P → JInt .i64 → m C)
    (add mul : A → A → m A) (muladd : A → A → A → m A)
    (neg : A → m A) (first : A → C → C → m R)
    (accum : A → R → R → m R) (next : A → R → C → m R)
    (complexFirst : C → JuliaLean.base.complex.Complex A → C → m O)
    (complexNext : R → JuliaLean.base.complex.Complex A → R → m O)
    (runtime : JuliaLean.base.complex.Complex A → P → m (C ⊕ O))
    (generated : Bool) (z : JuliaLean.base.complex.Complex A) (p : P) : m (C ⊕ O) := do
  if generated then
    let n ← length p
    let x := JuliaLean.base.complex.real_Complex z
    let y := JuliaLean.base.complex.imag_Complex z
    let r ← add x x
    let yy ← mul y y
    let s ← muladd x x yy
    let last ← lastindex p
    let a ← getindex p last
    let b := fun _ : Unit => do
      let last ← lastindex p
      getindex p (JuliaLean.base.int.sub_int last (JInt.lit .i64 1))
    return .inr (← polynomialComplexGeneratedLoop getindex neg first accum next
      complexFirst complexNext r s z p
      (JuliaLean.base.int.sub_int n (JInt.lit .i64 2)).val.toNat (.inl (a, b)))
  else runtime z p

-- Source: base/math.jl:125
def evalpolyComplexOneSource {A C : Type} (_z : JuliaLean.base.complex.Complex A) (c : C) : C := c

-- Source: base/math.jl:128
def evalpolyComplexVectorSource {m : Type → Type} {P A Result : Type}
    (evalpoly : JuliaLean.base.complex.Complex A → P → m Result)
    (z : JuliaLean.base.complex.Complex A) (p : P) : m Result :=
  evalpoly z p
def evalpolyComplexBody {T : FTy}
    (complexMuladd : FV T → Cx T → FV T → Cx T)
    (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) := do
  let kernel := fun x a b => .ok (JuliaLean.base.float.muladd_IEEEFloat x a b)
  let result ← evalpolyComplexTupleSource
    (fun p => .ok (JInt.wrap .i64 p.length)) (fun p => .ok (JInt.wrap .i64 p.length))
    polynomialListIndex (fun a b => .ok (add a b)) (fun a b => .ok (mul a b))
    kernel (fun x => .ok (fneg x)) kernel kernel kernel
    (fun a z b => .ok (complexMuladd a z b)) (fun a z b => .ok (complexMuladd a z b))
    (evalpolyComplexSource (fun _ => .ok ())
      (fun p => .ok (JInt.wrap .i64 p.length)) (fun p => .ok (JInt.wrap .i64 p.length))
      polynomialListIndex (fun n x => .ok (mul (Fl.ofInt n.val) x))
      (fun a b => .ok (mul a b)) kernel (fun x => .ok (fneg x)) kernel kernel kernel
      (fun a z b => .ok (complexMuladd a z b)) (fun a z b => .ok (complexMuladd a z b)))
    true z p
  return match result with | .inl c => .real c | .inr value => .complex value


def evalpolyComplexGenericBody {T : FTy} {C R O : Type}
    (muladdFirst : FV T → C → C → R)
    (muladdAccum : FV T → R → R → R)
    (muladdNext : FV T → R → C → R)
    (complexMuladdFirst : C → Cx T → C → O)
    (complexMuladdNext : R → Cx T → R → O)
    (z : Cx T) (p : List C) : Jl (EvalpolyResult T C O) := do
  let result ← evalpolyComplexSource (fun _ => .ok ())
    (fun p => .ok (JInt.wrap .i64 p.length)) (fun p => .ok (JInt.wrap .i64 p.length))
    polynomialListIndex (fun n x => .ok (mul (Fl.ofInt n.val) x))
    (fun a b => .ok (mul a b))
    (fun x a b => .ok (JuliaLean.base.float.muladd_IEEEFloat x a b))
    (fun x => .ok (fneg x))
    (fun x a b => .ok (muladdFirst x a b)) (fun x a b => .ok (muladdAccum x a b))
    (fun x a b => .ok (muladdNext x a b))
    (fun a z b => .ok (complexMuladdFirst a z b))
    (fun a z b => .ok (complexMuladdNext a z b)) z p
  return match result with | .inl c => .real c | .inr value => .complex value


/--
Julia source: base/math.jl:130-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _evalpoly(z::Complex, p)
    Base.require_one_based_indexing(p)
    length(p) == 1 && return p[1]
    N = length(p)
    a = p[end]
    b = p[end-1]

    x = real(z)
    y = imag(z)
    r = 2x
    s = muladd(x, x, y*y)
    for i in N-2:-1:1
        ai = a
        a = muladd(r, ai, b)
        b = muladd(-s, ai, p[i])
    end
    ai = a
    muladd(ai, z, b)
end
```
-/
def evalpolyComplex {T : FTy} {C R O : Type}
    (muladdFirst : FV T → C → C → R)
    (muladdAccum : FV T → R → R → R)
    (muladdNext : FV T → R → C → R)
    (complexMuladdFirst : C → Cx T → C → O)
    (complexMuladdNext : R → Cx T → R → O)
    (requireOneBased : List C → Jl Unit) (z : Cx T) (p : List C) :
    Jl (EvalpolyResult T C O) := do
  let result ← evalpolyComplexSource requireOneBased
    (fun p => .ok (JInt.wrap .i64 p.length)) (fun p => .ok (JInt.wrap .i64 p.length))
    polynomialListIndex (fun n x => .ok (mul (Fl.ofInt n.val) x))
    (fun a b => .ok (mul a b))
    (fun x a b => .ok (JuliaLean.base.float.muladd_IEEEFloat x a b))
    (fun x => .ok (fneg x))
    (fun x a b => .ok (muladdFirst x a b)) (fun x a b => .ok (muladdAccum x a b))
    (fun x a b => .ok (muladdNext x a b))
    (fun a z b => .ok (complexMuladdFirst a z b))
    (fun a z b => .ok (complexMuladdNext a z b)) z p
  return match result with | .inl c => .real c | .inr value => .complex value


/--
Julia source: base/math.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
evalpoly(z::Complex, p::AbstractVector) = _evalpoly(z, p)
```
-/
def evalpolyComplexVector {T : FTy} {C R O : Type}
    (muladdFirst : FV T → C → C → R)
    (muladdAccum : FV T → R → R → R)
    (muladdNext : FV T → R → C → R)
    (complexMuladdFirst : C → Cx T → C → O)
    (complexMuladdNext : R → Cx T → R → O)
    (requireOneBased : List C → Jl Unit) (z : Cx T) (p : List C) :
    Jl (EvalpolyResult T C O) :=
  evalpolyComplexVectorSource
    (evalpolyComplex muladdFirst muladdAccum muladdNext complexMuladdFirst
      complexMuladdNext requireOneBased) z p

/--
Julia source: base/math.jl:100-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function evalpoly(z::Complex, p::Tuple)
    if @generated
        N = length(p.parameters)
        a = :(p[end])
        b = :(p[end-1])
        as = []
        for i in N-2:-1:1
            ai = Symbol("a", i)
            push!(as, :($ai = $a))
            a = :(muladd(r, $ai, $b))
            b = :(muladd(-s, $ai, p[$i]))
        end
        ai = :a0
        push!(as, :($ai = $a))
        Expr(:block,
             :(x = real(z)),
             :(y = imag(z)),
             :(r = x + x),
             :(s = muladd(x, x, y*y)),
             as...,
             :(muladd($ai, z, $b)))
    else
        _evalpoly(z, p)
    end
end
```
-/
def evalpolyComplexTuple {T : FTy}
    (complexMuladd : FV T → Cx T → FV T → Cx T)
    (requireOneBased : List (FV T) → Jl Unit) (generated : Bool)
    (z : Cx T) (p : List (FV T)) : Jl (EvalpolyResult T) :=
  match p with
  | [coefficient] => .ok (.real (evalpolyComplexOneSource z coefficient))
  | _ =>
    if generated then evalpolyComplexBody complexMuladd z p
    else evalpolyComplexVector
      (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
      (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
      (fun x a b => JuliaLean.base.float.muladd_IEEEFloat x a b)
      complexMuladd complexMuladd requireOneBased z p

/--
Julia source: base/math.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
evalpoly(z::Complex, p::Tuple{<:Any}) = p[1]
```
-/
def evalpolyComplexOne {T : FTy} {C : Type} (z : Cx T) (c : C) : C :=
  evalpolyComplexOneSource z c

/--
Julia source: base/math.jl:157-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro horner(x, p...)
     xesc, pesc = esc(x), esc.(p)
    :(invoke(evalpoly, Tuple{Any, Tuple}, $xesc, ($(pesc...),)))
end
```
-/
def hornerMacro (x : JuliaSyntax) (p : List JuliaSyntax) : JuliaQuote :=
  .invoke "evalpoly" "Tuple{Any, Tuple}"
    [.escaped x, .tupleSplat (p.map JuliaQuote.escaped)]

/--
Julia source: base/math.jl:189-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro evalpoly(z, p...)
    zesc, pesc = esc(z), esc.(p)
    :(evalpoly($zesc, ($(pesc...),)))
end
```
-/
def evalpolyMacro (z : JuliaSyntax) (p : List JuliaSyntax) : JuliaQuote :=
  .call "evalpoly" [.escaped z, .tupleSplat (p.map JuliaQuote.escaped)]

/--
Julia source: base/math.jl:203-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _exthorner(i::Int, x::T, p::Tuple{T,T,T}, hi::T, lo::T) where T<:Union{Float32,Float64}
    i == 2 || i == 1 || error("unexpected index")
    pi = p[i]
    prod, err = two_mul(hi,x)
    hi = pi+prod
    lo = fma(lo, x, prod - (hi - pi) + err)
    return hi, lo
end
```
-/
def exthornerStepSource {T : FTy} (_wide : T = .f32 ∨ T = .f64)
    (o : IEEEOps T) (i : Int) (x : FV T)
    (p : FV T × FV T × FV T) (hi lo : FV T) :
    Except JuliaLean.base.error.JuliaException (FV T × FV T) := do
  if i != 2 && i != 1 then
    JuliaLean.base.error.errorVararg [.abstractString "unexpected index"]
  else
    let pi := if i = 2 then p.2.1 else p.1
    let (prod, err) := o.twoMul hi x
    let hi := add pi prod
    let lo := o.fma lo x (add (sub prod (sub hi pi)) err)
    pure (hi, lo)

def exthornerStep {T : FTy} (wide : T = .f32 ∨ T = .f64)
    (o : IEEEOps T) (i : Int) (x : FV T)
    (p : FV T × FV T × FV T) (hi lo : FV T) :
    Except JuliaLean.base.error.JuliaException (FV T × FV T) :=
  exthornerStepSource wide o i x p hi lo
/--
Julia source: base/math.jl:196-201 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function exthorner(x::T, p::Tuple{T,T,T}) where T<:Union{Float32,Float64}
    hi, lo = p[lastindex(p)], zero(x)
    hi, lo = _exthorner(2, x, p, hi, lo)
    hi, lo = _exthorner(1, x, p, hi, lo)
    return hi, lo
end
```
-/
def exthorner {T : FTy} (wide : T = .f32 ∨ T = .f64)
    (o : IEEEOps T) (x : FV T) (p : FV T × FV T × FV T) :
    Except JuliaLean.base.error.JuliaException (FV T × FV T) := do
  let hi := p.2.2
  let lo := fzero T
  let (hi, lo) ← exthornerStep wide o 2 x p hi lo
  exthornerStep wide o 1 x p hi lo

/--
Julia source: base/math.jl:937-937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline throw1(x) = throw(DomainError(x, "Cannot be NaN or Inf."))
```
-/
def exponentThrow1 {T : FTy} (_x : FV T) : Jl Int := .error (.domainError "Cannot be NaN or Inf.")

/--
Julia source: base/math.jl:938-938 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @noinline throw2(x) = throw(DomainError(x, "Cannot be ±0.0."))
```
-/
def exponentThrow2 {T : FTy} (_x : FV T) : Jl Int := .error (.domainError "Cannot be ±0.0.")

/--
Julia source: base/math.jl:936-950 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::T) where T<:IEEEFloat
    @noinline throw1(x) = throw(DomainError(x, "Cannot be NaN or Inf."))
    @noinline throw2(x) = throw(DomainError(x, "Cannot be ±0.0."))
    xs = reinterpret(Unsigned, x) & ~sign_mask(T)
    xs >= exponent_mask(T) && throw1(x)
    # use `% Int` instead of `Int(...)` to preserve `:nothrow` (the shifted value
    # always fits in `exponent_bits(T)` bits, well below `typemax(Int)`)
    k = (xs >> significand_bits(T)) % Int
    if k == 0 # x is subnormal
        xs == 0 && throw2(x)
        m = leading_zeros(xs) - exponent_bits(T)
        k = 1 - m
    end
    return k - exponent_bias(T)
end
```
-/
def exponentFloat {T : FTy} (x : FV T) : Jl Int :=
  let xs := withoutBits x.toBits (signMask T) T.fmt.width
  if xs >= exponentMask T then exponentThrow1 x
  else
    let k : Int := (xs / 2 ^ significandBits T : Nat)
    if k == 0 then
      if xs == 0 then exponentThrow2 x
      else
        let m := leadingZeros T.fmt.width xs - exponentBits T
        .ok ((1 - (m : Int)) - exponentBias T)
    else .ok (k - exponentBias T)

/--
Julia source: base/math.jl:629-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sqrt(x::IEEEFloat)
    x < zero(x) && throw_complex_domainerror(:sqrt, x)
    sqrt_llvm(x)
end
```
-/
def sqrtIEEE {T : FTy} (o : IEEEOps T) (x : FV T) : Jl (FV T) :=
  if flt x (fzero T) then throwComplexDomainError "sqrt" x else .ok (o.sqrtLlvm x)

/--
Julia source: base/math.jl:1100-1111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scaleinv(x::T) where T<:IEEEFloat
    # by removing the sign and significand and restricting values to a limited range,
    # we can invert a number using bit-twiddling instead of division
    U = uinttype(T)
    umin = reinterpret(U, floatmin(T))
    umax = reinterpret(U, inv(floatmin(T)))
    emask = exponent_mask(T) # used to strip sign and significand
    u = clamp(reinterpret(U, x) & emask, umin, umax)
    scale = reinterpret(T, u)
    invscale = reinterpret(T, umin + umax - u) # inv(scale)
    return scale, invscale
end
```
-/
def scaleinv {T : FTy} (o : IEEEOps T) (x : FV T) : FV T × FV T :=
  let umin := o.floatmin.toBits
  let umax := o.invFloatmin.toBits
  let e := (x.toBits / 2 ^ significandBits T % 2 ^ exponentBits T) * 2 ^ significandBits T
  let u := o.clampUnsigned e umin umax
  (Fl.ofBits u, Fl.ofBits (umin + umax - u))

/--
Julia source: base/math.jl:826-826 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    add_fast(x, y) = Core.Intrinsics.add_float_fast(x, y) # @fastmath is not available during bootstrap
```
-/
def addFast {T : FTy} (o : IEEEOps T) (x y : FV T) : FV T := o.addFast x y

def hypotOpsOfIEEE {T : FTy} (o : IEEEOps T) : GenericHypotOps (FV T) (FV T) :=
  { abs := fabs
    oneunit := o.oneunit
    isinf := fisinf
    isnan := fisnan
    iszero := fiszero
    isless := Fl.isless
    lt := flt
    greater := o.greater
    le := fle
    zero := fzero T
    one := fone T
    infinity := finf T
    eps := o.eps
    floatmin := o.floatmin
    floatmax := o.floatmax
    two := Fl.ofInt 2
    four := Fl.ofInt 4
    inverse := o.inverse
    sqrt := sqrtIEEE o
    mul := mul
    div := div
    add := add
    sub := sub
    muladd := o.muladd
    fma := o.fma
    divideInput := div
    abs2 := o.abs2
    haveFma := o.haveFma
    neg := fneg }
/--
Julia source: base/math.jl:732-786 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hypot(x, y)
    # preserves unit
    axu = abs(x)
    ayu = abs(y)

    # unitless
    ax = axu / oneunit(axu)
    ay = ayu / oneunit(ayu)

    # Return Inf if either or both inputs is Inf (Compliance with IEEE754)
    if isinf(ax) || isinf(ay)
        return typeof(axu)(Inf)
    end

    # Order the operands
    if ay > ax
        axu = ayu
        ax, ay = ay, ax
    end

    # Widely varying operands
    if ay <= ax*sqrt(eps(typeof(ax))/2)  #Note: This also gets ay == 0
        return axu
    end

    # Operands do not vary widely
    scale = eps(typeof(ax))*sqrt(floatmin(ax))  #Rescaling constant
    if ax > sqrt(floatmax(ax)/2)
        ax = ax*scale
        ay = ay*scale
        scale = inv(scale)
    elseif ay < sqrt(floatmin(ax))
        ax = ax/scale
        ay = ay/scale
    else
        scale = oneunit(scale)
    end
    h = sqrt(muladd(ax, ax, ay*ay))
    # This branch is correctly rounded but requires a native hardware fma.
    if Core.Intrinsics.have_fma(typeof(h))
        hsquared = h*h
        axsquared = ax*ax
        h -= (fma(-ay, ay, hsquared-axsquared) + fma(h, h,-hsquared) - fma(ax, ax, -axsquared))/(2*h)
    # This branch is within one ulp of correctly rounded.
    else
        if h <= 2*ay
            delta = h-ay
            h -= muladd(delta, delta-2*(ax-ay), ax*(2*delta - ax))/(2*h)
        else
            delta = h-ax
            h -= muladd(delta, delta, muladd(ay, (4*delta - ay), 2*delta*(ax - 2*ay)))/(2*h)
        end
    end
    return h*scale*oneunit(axu)
end
```
-/
def hypotGenericSource {α γ β : Type} (o : GenericHypotOps α β)
    (absRight : γ → β) (x : α) (y : γ) : Jl β := do
  let axu0 := o.abs x
  let ayu := absRight y
  let ax0 := o.div axu0 (o.oneunit axu0)
  let ay0 := o.div ayu (o.oneunit ayu)
  if o.isinf ax0 || o.isinf ay0 then return o.infinity
  let (axu, ax, ay) :=
    if o.greater ay0 ax0 then (ayu, ay0, ax0) else (axu0, ax0, ay0)
  let cutoff ← o.sqrt (o.div o.eps o.two)
  if o.le ay (o.mul ax cutoff) then return axu
  let minRoot ← o.sqrt o.floatmin
  let scale0 := o.mul o.eps minRoot
  let bigRoot ← o.sqrt (o.div o.floatmax o.two)
  let (ax, ay, scale) :=
    if o.greater ax bigRoot then
      (o.mul ax scale0, o.mul ay scale0, o.inverse scale0)
    else if o.lt ay minRoot then
      (o.div ax scale0, o.div ay scale0, scale0)
    else (ax, ay, o.oneunit scale0)
  let h0 ← o.sqrt (o.muladd ax ax (o.mul ay ay))
  let h :=
    if o.haveFma then
      let hsquared := o.mul h0 h0
      let axsquared := o.mul ax ax
      let correction := o.sub
        (o.add (o.fma (o.neg ay) ay (o.sub hsquared axsquared))
          (o.fma h0 h0 (o.neg hsquared)))
        (o.fma ax ax (o.neg axsquared))
      o.sub h0 (o.div correction (o.mul o.two h0))
    else if o.le h0 (o.mul o.two ay) then
      let delta := o.sub h0 ay
      o.sub h0 (o.div
        (o.muladd delta (o.sub delta (o.mul o.two (o.sub ax ay)))
          (o.mul ax (o.sub (o.mul o.two delta) ax)))
        (o.mul o.two h0))
    else
      let delta := o.sub h0 ax
      let inner := o.muladd ay
        (o.sub (o.mul o.four delta) ay)
        (o.mul (o.mul o.two delta) (o.sub ax (o.mul o.two ay)))
      o.sub h0 (o.div (o.muladd delta delta inner) (o.mul o.two h0))
  return o.mul (o.mul h scale) (o.oneunit axu)

def hypotGeneric {α γ β : Type} (o : GenericHypotOps α β)
    (absRight : γ → β) (x : α) (y : γ) : Jl β :=
  hypotGenericSource o absRight x y

section

variable (mapreduce maximum_f sum_f :
  ∀ {Input Output F Acc : Type} [JuliaLean.base.reduce.MapCallable F Input Output],
    ({I : Type} → JuliaLean.base.reduce.JIterator I → JuliaLean.base.reduce.EltypeStatus) →
    F → JuliaLean.base.reduce.Reducer Acc Output → JuliaLean.base.reduce.JIterator Input →
    JuliaLean.base.reduce.FoldInit Acc → Jl Acc)
/--
Julia source: base/math.jl:805-814 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hypot(x::NTuple{N,<:Number}) where {N}
    maxabs = maximum(abs, x)
    if isnan(maxabs) && any(isinf, x)
        return typeof(maxabs)(Inf)
    elseif (iszero(maxabs) || isinf(maxabs))
        return maxabs
    else
        return maxabs * sqrt(sum(y -> abs2(y / maxabs), x))
    end
end
```
-/

def hypotTupleGeneric {α β : Type} (o : GenericHypotOps α β)
    (iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
      JuliaLean.base.reduce.EltypeStatus)
    (maximumReducer sumReducer : JuliaLean.base.reduce.Reducer β β)
    (isinfInput : α → Bool) (xs : List α) : Jl β := do
  let maxabs ← maximum_f iteratorEltype o.abs maximumReducer
    (.values xs) .initial
  if o.isnan maxabs && xs.any isinfInput then return o.infinity
  else if o.iszero maxabs || o.isinf maxabs then return maxabs
  else
    let sum ← sum_f iteratorEltype
      (fun y => o.abs2 (o.divideInput y maxabs)) sumReducer (.values xs) .initial
    let root ← o.sqrt sum
    pure (o.mul maxabs root)
/--
Julia source: base/math.jl:816-828 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _hypot(x::NTuple{N,<:IEEEFloat}) where {N}
    T = eltype(x)
    infT = convert(T, Inf)
    x = abs.(x) # doesn't change result but enables computational shortcuts
    # note: any() was causing this to not inline for N=3 but mapreduce() was not
    mapreduce(==(infT), |, x) && return infT # return Inf even if an argument is NaN
    maxabs = reinterpret(T, maximum(z -> reinterpret(Signed, z), x)) # for abs(::IEEEFloat) values, a ::BitInteger cast does not change the result
    maxabs > zero(T) || return maxabs # catch NaN before the @fastmath below, but also shortcut 0 since we can (remove if no more @fastmath below)
    scale,invscale = scaleinv(maxabs)
     # @fastmath(+) to allow reassociation (see #48129)
    add_fast(x, y) = Core.Intrinsics.add_float_fast(x, y) # @fastmath is not available during bootstrap
    return scale * sqrt(mapreduce(y -> abs2(y * invscale), add_fast, x))
end
```
-/
def hypotTupleIEEE {T : FTy} (o : IEEEOps T)
    (ops : HypotFloatReductionOps T) (xs : List (FV T)) : Jl (FV T) := do
  let xs := xs.map fabs
  let hasInfinity ← mapreduce ops.iteratorEltype
    (fun x => feq x (finf T)) ops.booleanOr (.values xs) .initial
  if hasInfinity then return finf T
  let maxSigned ← maximum_f ops.iteratorEltype
    ops.reinterpretSigned ops.maximumReducer (.values xs) .initial
  let maxabs := ops.reinterpretFloat maxSigned
  if !flt (fzero T) maxabs then return maxabs
  let (scale, invscale) := scaleinv o maxabs
  let sum ← mapreduce ops.iteratorEltype
    (fun y => o.abs2 (mul y invscale)) ops.sumReducer (.values xs) .initial
  let root ← sqrtIEEE o sum
  pure (mul scale root)

/--
Julia source: base/math.jl:789-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow @inline function _hypot(x::Float32, y::Float32)
    if isinf(x) || isinf(y)
        return Inf32
    end
    _x, _y = Float64(x), Float64(y)
    return Float32(sqrt(muladd(_x, _x, _y*_y)))
end
```
-/
def hypot32 (o64 : IEEEOps .f64) (x y : FV .f32) : Jl (FV .f32) := do
  if fisinf x || fisinf y then return finf .f32
  let x64 := Fl.convert x
  let y64 := Fl.convert y
  let r ← sqrtIEEE o64 (JuliaLean.base.float.muladd_IEEEFloat x64 x64 (mul y64 y64))
  pure (Fl.convert r)

/--
Julia source: base/math.jl:796-802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@assume_effects :nothrow @inline function _hypot(x::Float16, y::Float16)
    if isinf(x) || isinf(y)
        return Inf16
    end
    _x, _y = Float32(x), Float32(y)
    return Float16(sqrt(muladd(_x, _x, _y*_y)))
end
```
-/
def hypot16 (o32 : IEEEOps .f32) (x y : FV .f16) : Jl (FV .f16) := do
  if fisinf x || fisinf y then return finf .f16
  let x32 := Fl.convert x
  let y32 := Fl.convert y
  let r ← sqrtIEEE o32 (JuliaLean.base.float.muladd_IEEEFloat x32 x32 (mul y32 y32))
  pure (Fl.convert r)

/--
Julia source: base/math.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_hypot(x::ComplexF16, y::ComplexF16) = Float16(_hypot(ComplexF32(x), ComplexF32(y)))
```
-/
def hypotComplex16 (o32 : GenericHypotOps (Cx .f32) (FV .f32))
    (x y : Cx .f16) : Jl (FV .f16) := do
  let x32 : Cx .f32 := ⟨Fl.convert x.re, Fl.convert x.im⟩
  let y32 : Cx .f32 := ⟨Fl.convert y.re, Fl.convert y.im⟩
  let r ← hypotGeneric o32 o32.abs x32 y32
  pure (Fl.convert r)
def hypotDispatchFloat16 (o16 : IEEEOps .f16) (o32 : IEEEOps .f32)
    (reduce16 : HypotFloatReductionOps .f16) :
    HypotDispatch (FV .f16) (FV .f16) :=
  { pair := hypot16 o32, tuple := hypotTupleIEEE mapreduce maximum_f o16 reduce16 }

def hypotDispatchFloat32 (o32 : IEEEOps .f32) (o64 : IEEEOps .f64)
    (reduce32 : HypotFloatReductionOps .f32) :
    HypotDispatch (FV .f32) (FV .f32) :=
  { pair := hypot32 o64, tuple := hypotTupleIEEE mapreduce maximum_f o32 reduce32 }

def hypotDispatchFloat64 (o64 : IEEEOps .f64)
    (reduce64 : HypotFloatReductionOps .f64) :
    HypotDispatch (FV .f64) (FV .f64) :=
  { pair := fun x y =>
      hypotGeneric (hypotOpsOfIEEE o64) (hypotOpsOfIEEE o64).abs x y
    tuple := hypotTupleIEEE mapreduce maximum_f o64 reduce64 }

def hypotDispatchComplex16
    (iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
      JuliaLean.base.reduce.EltypeStatus)
    (maximumReducer sumReducer : JuliaLean.base.reduce.Reducer (FV .f16) (FV .f16))
    (isinfInput : Cx .f16 → Bool)
    (pairOps : GenericHypotOps (Cx .f32) (FV .f32))
    (tupleOps : GenericHypotOps (Cx .f16) (FV .f16)) :
    HypotDispatch (Cx .f16) (FV .f16) :=
  { pair := hypotComplex16 pairOps
    tuple := hypotTupleGeneric maximum_f sum_f tupleOps iteratorEltype maximumReducer sumReducer isinfInput }

end

/--
Julia source: base/math.jl:729-729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hypot(x::Number) = abs(float(x))
```
-/
def hypotOne {α β γ : Type} (float : α → β) (abs : β → γ) (x : α) : γ :=
  abs (float x)

/--
Julia source: base/math.jl:730-730 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hypot(x::Number, y::Number) = _hypot(float.(promote(x, y))...)
```
-/
def hypotTwo {α β γ δ ε : Type} (promote : α → β → Jl (γ × γ)) (float : γ → δ)
    (dispatch : HypotDispatch δ ε) (x : α) (y : β) : Jl ε := do
  let (xp, yp) ← promote x y
  dispatch.pair (float xp) (float yp)

/--
Julia source: base/math.jl:731-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
hypot(x::Number, y::Number, xs::Number...) = _hypot(float.(promote(x, y, xs...)))
```
-/
def hypotMany {α : Type _} {β γ δ : Type} (promote : List α → Jl (List β)) (float : β → γ)
    (dispatch : HypotDispatch γ δ) (xs : List α) : Jl δ := do
  dispatch.tuple ((← promote xs).map float)

/--
Julia source: base/math.jl:854-897 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ldexp(x::T, e::Integer) where T<:IEEEFloat
    xu = reinterpret(Unsigned, x)
    xs = xu & ~sign_mask(T)
    xs >= exponent_mask(T) && return x # NaN or Inf
    k = (xs >> significand_bits(T)) % Int
    if k == 0 # x is subnormal
        xs == 0 && return x # +-0
        m = leading_zeros(xs) - exponent_bits(T)
        ys = xs << unsigned(m)
        xu = ys | (xu & sign_mask(T))
        k = 1 - m
        # underflow, otherwise may have integer underflow in the following n + k
        e < -50000 && return flipsign(T(0.0), x)
    end
    # For cases where e of an Integer larger than Int make sure we properly
    # overflow/underflow; this is optimized away otherwise.
    if e > typemax(Int)
        return flipsign(T(Inf), x)
    elseif e < typemin(Int)
        return flipsign(T(0.0), x)
    end
    n = e % Int
    k = k +% n
    # overflow, if k is larger than maximum possible exponent
    if k >= exponent_raw_max(T)
        return flipsign(T(Inf), x)
    end
    if k > 0 # normal case
        xu = (xu & ~exponent_mask(T)) | (rem(k, uinttype(T)) << significand_bits(T))
        return reinterpret(T, xu)
    else # subnormal case
        # results with k == -significand_bits(T) are at least nextfloat(zero(T))/2, so may round up
        if k <= -significand_bits(T) - 1 # underflow
            # overflow, for the case of integer overflow in n + k
            e > 50000 && return flipsign(T(Inf), x)
            return flipsign(T(0.0), x)
        end
        k += significand_bits(T) + 1
        # z = T(2.0) ^ (-significand_bits(T) - 1)
        z = reinterpret(T, rem(exponent_bias(T)-significand_bits(T)-1, uinttype(T)) << significand_bits(T))
        xu = (xu & ~exponent_mask(T)) | (rem(k, uinttype(T)) << significand_bits(T))
        return z*reinterpret(T, xu)
    end
end
```
-/
def ldexpSource {m : Type → Type} [Monad m] {E : Type} {T : FTy}
    (o : IEEEOps T) (lt gt : E → Int → m Bool) (remInt : E → m (JInt .i64))
    (x : FV T) (e : E) : m (FV T) := do
  let xu0 := x.toBits
  let xs := withoutBits xu0 (signMask T) T.fmt.width
  if xs >= exponentMask T then return x
  let mut xu := xu0
  let mut k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    if xs == 0 then return x
    let m := leadingZeros T.fmt.width xs - exponentBits T
    let ys := xs * 2 ^ m
    xu := ys + (if fsignbit x then signMask T else 0)
    k := 1 - (m : Int)
    if ← lt e (-50000) then return o.flipsign (fzero T) x
  if ← gt e (IntTy.max .i64) then return o.flipsign (finf T) x
  else if ← lt e (IntTy.min .i64) then return o.flipsign (fzero T) x
  let n := (← remInt e).val
  k := wrapInt .i64 (k + n)
  if k >= exponentRawMax T then return o.flipsign (finf T) x
  if k > 0 then
    xu := withoutBits xu (exponentMask T) T.fmt.width + k.toNat * 2 ^ significandBits T
    return Fl.ofBits xu
  else
    if k <= -(significandBits T : Int) - 1 then
      if ← gt e 50000 then return o.flipsign (finf T) x
      return o.flipsign (fzero T) x
    k := k + significandBits T + 1
    let z : FV T := Fl.ofBits ((exponentBias T - significandBits T - 1) * 2 ^ significandBits T)
    xu := withoutBits xu (exponentMask T) T.fmt.width + k.toNat * 2 ^ significandBits T
    return mul z (Fl.ofBits xu)

-- Source: base/math.jl:854-897
def ldexp {T : FTy} (o : IEEEOps T) (x : FV T) (e : Int) : FV T :=
  ldexpSource (m := Id) o (fun e n => pure (decide (e < n)))
    (fun e n => pure (decide (e > n))) (fun e => pure (JInt.wrap .i64 e)) x e

/--
Julia source: base/math.jl:898-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ldexp(x::Float16, q::Integer) = Float16(ldexp(Float32(x), q))
```
-/
def ldexp16Source {m : Type → Type} [Monad m] {E : Type}
    (ldexp : FV .f32 → E → m (FV .f32)) (x : FV .f16) (q : E) : m (FV .f16) := do
  return Fl.convert (← ldexp (Fl.convert x) q)

-- Source: base/math.jl:898
def ldexp16 (o32 : IEEEOps .f32) (x : FV .f16) (q : Int) : FV .f16 :=
  ldexp16Source (m := Id) (fun x q => pure (ldexp o32 x q)) x q

/--
Julia source: base/math.jl:967-978 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _ilog2_step(y::T, d::T, s) where {T<:Integer}
    if (y >> s) >= d
        y, n = _ilog2_step(y, d*d, s+s)
    else
        n = 0
    end
    if y >= d
        y >>= s
        n = Base.checked_add(n, s)
    end
    return y, n
end
```
-/
def ilog2StepSource {T Shift : Type} (o : IntegerStepOps T Shift) (y d : T) (s : Shift)
    (continuation : Jl (T × Int) → Jl (T × Int) := id) :
    Option (Jl (T × Int)) :=
  let finish := fun result => continuation (do
    let (y, n) ← result
    if o.ge y d then
      let y := o.shiftRight y s
      let n ← o.checkedAdd n s
      pure (y, n)
    else pure (y, n))
  if o.ge (o.shiftRight y s) d then
    ilog2StepSource o y (o.mul d d) (o.addShift s s) finish
  else some (finish (.ok (y, 0)))
partial_fixpoint

-- Source: base/math.jl:967-978
def ilog2Step {T Shift : Type} (o : IntegerStepOps T Shift) (y d : T) (s : Shift)
    (continuation : Jl (T × Int) → Jl (T × Int) := id) : Option (Jl (T × Int)) :=
  ilog2StepSource o y d s continuation

/--
Julia source: base/math.jl:980-985 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::Integer)
    iszero(x) && throw(DomainError(x, "cannot be zero"))
    ux = Base.uabs(x)
    _, n = _ilog2_step(ux, one(ux) + one(ux), 1)
    return n
end
```
-/
def exponentIntegerSource {X U : Type} (o : IntegerExponentOps X U) (x : X) :
    Option (Jl Int) :=
  if o.iszero x then some (.error (.domainError "cannot be zero"))
  else
    let ux := o.uabs x
    let step := { o.step with
      shiftOne := 1
      addShift := fun a b => (JuliaLean.base.int.add_int
        (JInt.wrap .i64 a) (JInt.wrap .i64 b)).val
      checkedAdd := fun n s => (JuliaLean.base.checked.checkedAddBits
        (JInt.wrap .i64 n) (JInt.wrap .i64 s)).map (·.val) }
    (ilog2Step step ux (o.step.add o.step.one o.step.one) 1).map
      (fun result => result.map Prod.snd)

-- Source: base/math.jl:980-985
def exponentInteger {X U : Type} (o : IntegerExponentOps X U) (x : X) : Option (Jl Int) :=
  exponentIntegerSource o x

/--
Julia source: base/math.jl:987-991 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::Base.BitInteger)
    iszero(x) && throw(DomainError(x, "cannot be zero"))
    ux = Base.uabs(x)
    return 8sizeof(ux) - leading_zeros(ux) - 1
end
```
-/
def exponentBitInteger {t : IntTy} (x : JInt t) : Jl Int :=
  if x.val == 0 then .error (.domainError "cannot be zero")
  else .ok ((t.bits : Int) - leadingZeros t.bits x.val.natAbs - 1)

/--
Julia source: base/math.jl:993-999 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exponent(x::Bool)
    if x
        0
    else
        throw(DomainError(x, "cannot be zero"))
    end
end
```
-/
def exponentBool (x : Bool) : Jl Int :=
  if x then .ok 0 else .error (.domainError "cannot be zero")

/--
Julia source: base/math.jl:1276-1276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline highword(x::UInt64)  = (x >>> 32) % UInt32
```
-/
def highwordUInt64 (x : JInt .u64) : JInt .u32 :=
  JInt.wrap .u32 (x.val.toNat / 2 ^ 32)

/--
Julia source: base/math.jl:1275-1275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline highword(x::Float64) = highword(reinterpret(UInt64, x))
```
-/
def highword64 (x : FV .f64) : JInt .u32 :=
  highwordUInt64 (JInt.wrap .u64 x.toBits)

/--
Julia source: base/math.jl:1277-1277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline highword(x::Float32) = reinterpret(UInt32, x)
```
-/
def highword32 (x : FV .f32) : JInt .u32 := JInt.wrap .u32 x.toBits

/--
Julia source: base/math.jl:1289-1289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline poshighword(x::UInt64)  = highword(x) & 0x7fffffff
```
-/
def poshighwordUInt64 (x : JInt .u64) : JInt .u32 :=
  JInt.wrap .u32 (Nat.land (x.val.toNat / 2 ^ 32) 0x7fffffff)

/--
Julia source: base/math.jl:1288-1288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline poshighword(x::Float64) = poshighword(reinterpret(UInt64, x))
```
-/
def poshighword64 (x : FV .f64) : JInt .u32 :=
  poshighwordUInt64 (JInt.wrap .u64 x.toBits)

/--
Julia source: base/math.jl:1279-1279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline fromhighword(::Type{Float64}, u::UInt32) = reinterpret(Float64, UInt64(u) << 32)
```
-/
def fromhighword64 (u : JInt .u32) : FV .f64 := Fl.ofBits (u.val.toNat * 2 ^ 32)

/--
Julia source: base/math.jl:1280-1280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline fromhighword(::Type{Float32}, u::UInt32) = reinterpret(Float32, u)
```
-/
def fromhighword32 (u : JInt .u32) : FV .f32 := Fl.ofBits u.val.toNat

/--
Julia source: base/math.jl:1290-1290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline poshighword(x::Float32) = highword(x) & 0x7fffffff
```
-/
def poshighword32 (x : FV .f32) : JInt .u32 :=
  JInt.wrap .u32 (Nat.land x.toBits 0x7fffffff)


/--
Julia source: base/math.jl:36-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_complex_domainerror_neg1(f::Symbol, x)
    throw(DomainError(x,
        LazyString(f," was called with a real argument < -1 but will only return a complex result if called with a complex argument. Try ", f,"(Complex(x)).")))
end
```
-/
def throwComplexDomainErrorNeg1 {α : Type} (f : String) (_x : α) : Jl α :=
  .error (.domainError (f ++ " was called with a real argument < -1 but will only return a complex result if called with a complex argument. Try " ++ f ++ "(Complex(x))."))

/--
Julia source: base/math.jl:40-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_finite_domainerror(f::Symbol, x)
    throw(DomainError(x, LazyString("`", f, "(x)` is only defined for finite `x`.")))
end
```
-/
def throwFiniteDomainError {α : Type} (f : String) (_x : α) : Jl α :=
  .error (.domainError ("`" ++ f ++ "(x)` is only defined for finite `x`."))

/--
Julia source: base/math.jl:43-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function throw_exp_domainerror(x)
    throw(DomainError(x, LazyString(
        "Exponentiation yielding a complex result requires a ",
        "complex argument.\nReplace x^y with (x+0im)^y, ",
        "Complex(x)^y, or similar.")))
end
```
-/
def throwExpDomainError {α : Type} (_x : α) : Jl α :=
  .error (.domainError "Exponentiation yielding a complex result requires a complex argument.\nReplace x^y with (x+0im)^y, Complex(x)^y, or similar.")

/--
Julia source: base/math.jl:213-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _180_over_pi(z::AbstractFloat)
    180 / oftype(z, pi)
end
```
-/
def oneEightyOverPiSource {m : Type → Type} [Monad m] {Z Pi Result : Type}
    (oftypePi : Z → m Pi) (div : JInt .i64 → Pi → m Result) (z : Z) : m Result := do
  let pi ← oftypePi z
  div (JInt.lit .i64 180) pi

-- Source: base/math.jl:213-215
def oneEightyOverPi {α : Type} (o : AbstractFloatOps α) (z : α) : α :=
  oneEightyOverPiSource (m := Id) (fun _ => pure o.pi)
    (fun n pi => pure (o.div (o.ofInt n.val) pi)) z

/--
Julia source: base/math.jl:216-218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _pi_over_180(z::AbstractFloat)
    oftype(z, pi) / 180
end
```
-/
def piOverOneEightySource {m : Type → Type} [Monad m] {Z Pi Result : Type}
    (oftypePi : Z → m Pi) (div : Pi → JInt .i64 → m Result) (z : Z) : m Result := do
  let pi ← oftypePi z
  div pi (JInt.lit .i64 180)

-- Source: base/math.jl:216-218
def piOverOneEighty {α : Type} (o : AbstractFloatOps α) (z : α) : α :=
  piOverOneEightySource (m := Id) (fun _ => pure o.pi)
    (fun pi n => pure (o.div pi (o.ofInt n.val))) z

/--
Julia source: base/math.jl:221-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_180_over_pi(::Float16) = Float16(57.28)
```
-/
def oneEightyOverPi16 : FV .f16 := Fl.convert (Fl.roundRat 5728 100 false : FV .f64)

/--
Julia source: base/math.jl:222-222 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_180_over_pi(::Float32) = 57.29578f0
```
-/
def oneEightyOverPi32 : FV .f32 := Fl.roundRat 5729578 100000 false

/--
Julia source: base/math.jl:223-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_pi_over_180(::Float16) = Float16(0.01746)
```
-/
def piOverOneEighty16 : FV .f16 := Fl.convert (Fl.roundRat 1746 100000 false : FV .f64)
def oneEightyOverPiDispatch : (T : FTy) → IEEEOps T → FV T → FV T
  | .f16, _, _ => oneEightyOverPi16
  | .f32, _, _ => oneEightyOverPi32
  | .f64, o, _ => div (Fl.ofInt 180) o.pi

def piOverOneEightyDispatch : (T : FTy) → IEEEOps T → FV T → FV T
  | .f16, _, _ => piOverOneEighty16
  | .f32, o, _ => div o.pi (Fl.ofInt 180)
  | .f64, o, _ => div o.pi (Fl.ofInt 180)
/--
Julia source: base/math.jl:238-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rad2deg(z::AbstractFloat) = z * _180_over_pi(z)
```
-/
def rad2degFloatSource {m : Type → Type} [Monad m] {Z Factor Result : Type}
    (mul : Z → Factor → m Result) (factor : Z → m Factor) (z : Z) : m Result := do
  mul z (← factor z)

-- Source: base/math.jl:238
def rad2degFloat {α : Type} (mul : α → α → α) (factor : α → α) (z : α) : α :=
  rad2degFloatSource (m := Id) (fun a b => pure (mul a b)) (fun z => pure (factor z)) z

/--
Julia source: base/math.jl:253-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deg2rad(z::AbstractFloat) = z * _pi_over_180(z)
```
-/
def deg2radFloatSource {m : Type → Type} [Monad m] {Z Factor Result : Type}
    (mul : Z → Factor → m Result) (factor : Z → m Factor) (z : Z) : m Result := do
  mul z (← factor z)

-- Source: base/math.jl:253
def deg2radFloat {α : Type} (mul : α → α → α) (factor : α → α) (z : α) : α :=
  deg2radFloatSource (m := Id) (fun a b => pure (mul a b)) (fun z => pure (factor z)) z

/--
Julia source: base/math.jl:254-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rad2deg(z::Real) = rad2deg(float(z))
```
-/
def rad2degRealSource {m : Type → Type} [Monad m] {Z Float Result : Type}
    (rad2deg : Float → m Result) (float : Z → m Float) (z : Z) : m Result := do
  rad2deg (← float z)

-- Source: base/math.jl:254
def rad2degReal {α β : Type} (rad2deg : β → β) (float : α → β) (z : α) : β :=
  rad2degRealSource (m := Id) (fun x => pure (rad2deg x)) (fun x => pure (float x)) z

/--
Julia source: base/math.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deg2rad(z::Real) = deg2rad(float(z))
```
-/
def deg2radRealSource {m : Type → Type} [Monad m] {Z Float Result : Type}
    (deg2rad : Float → m Result) (float : Z → m Float) (z : Z) : m Result := do
  deg2rad (← float z)

-- Source: base/math.jl:255
def deg2radReal {α β : Type} (deg2rad : β → β) (float : α → β) (z : α) : β :=
  deg2radRealSource (m := Id) (fun x => pure (deg2rad x)) (fun x => pure (float x)) z

/--
Julia source: base/math.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rad2deg(z::Number) = (z/pi)*180
```
-/
def rad2degNumberSource {m : Type → Type} [Monad m] {Z Pi Quotient Result : Type}
    (div : Z → Pi → m Quotient) (mul : Quotient → JInt .i64 → m Result)
    (pi : Pi) (z : Z) : m Result := do
  mul (← div z pi) (JInt.lit .i64 180)

-- Source: base/math.jl:256
def rad2degNumber {Z Pi Quotient Scale Result : Type}
    (div : Z → Pi → Quotient) (mul : Quotient → Scale → Result)
    (pi : Pi) (z : Z) (oneEighty : Scale) : Result :=
  rad2degNumberSource (m := Id) (fun x y => pure (div x y))
    (fun x _ => pure (mul x oneEighty)) pi z

/--
Julia source: base/math.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
deg2rad(z::Number) = (z*pi)/180
```
-/
def deg2radNumberSource {m : Type → Type} [Monad m] {Z Pi Product Result : Type}
    (mul : Z → Pi → m Product) (div : Product → JInt .i64 → m Result)
    (pi : Pi) (z : Z) : m Result := do
  div (← mul z pi) (JInt.lit .i64 180)

-- Source: base/math.jl:257
def deg2radNumber {Z Pi Product Scale Result : Type}
    (mul : Z → Pi → Product) (div : Product → Scale → Result)
    (pi : Pi) (z : Z) (oneEighty : Scale) : Result :=
  deg2radNumberSource (m := Id) (fun x y => pure (mul x y))
    (fun x _ => pure (div x oneEighty)) pi z

/--
Julia source: base/math.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
log(b::T, x::T) where {T<:Number} = log(x)/log(b)
```
-/
def logBase {α β : Type} (logFn : α → Jl β) (divFn : β → β → β) (b x : α) : Jl β := do
  return divFn (← logFn x) (← logFn b)

/--
Julia source: base/math.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
log(b::Number, x::Number) = log(promote(b,x)...)
```
-/
def logBaseNumber {α β γ : Type} (promote : α → β → Jl (γ × γ))
    (logFn : γ → Jl γ) (divFn : γ → γ → γ) (b : α) (x : β) : Jl γ := do
  let (b, x) ← promote b x
  logBase logFn divFn b x

/--
Julia source: base/math.jl:399-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline nan_dom_err(out, x) = isnan(out) & !isnan(x) ? throw(DomainError(x, "NaN result for non-NaN input.")) : out
```
-/
def nanDomErrSource {Output Input : Type}
    (isnanOut : Output → Jl Bool) (isnanInput : Input → Jl Bool)
    (out : Output) (x : Input) : Jl Output := do
  let outNaN ← isnanOut out
  let inputNaN ← isnanInput x
  if outNaN && !inputNaN then
    .error (.domainError "NaN result for non-NaN input.")
  else pure out

-- Source: base/math.jl:399
def nanDomErr {T S : FTy} (out : FV T) (x : FV S) : Jl (FV T) :=
  nanDomErrSource (fun value => .ok (fisnan value)) (fun value => .ok (fisnan value)) out x

/--
Julia source: base/math.jl:685-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fourthroot(x::Number) = sqrt(sqrt(x))
```
-/
def fourthroot {Input Middle Result : Type}
    (firstSqrt : Input → Jl Middle) (secondSqrt : Middle → Jl Result)
    (x : Input) : Jl Result := do
  secondSqrt (← firstSqrt x)

/--
Julia source: base/math.jl:830-830 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atan(y::Real, x::Real) = atan(promote(float(y),float(x))...)
```
-/
def atanReal {α β γ : Type} (float : α → β) (float2 : γ → β)
    (promote : β → β → β × β) (atanFloat : β → β → Jl β) (y : α) (x : γ) : Jl β :=
  let (yp, xp) := promote (float y) (float2 x)
  atanFloat yp xp

/--
Julia source: base/math.jl:831-831 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atan(y::T, x::T) where {T<:AbstractFloat} = Base.no_op_err("atan", T)
```
-/
def atanNoOp {α : Type} (typeName : String) : Except
    JuliaLean.base.error.JuliaException α :=
  JuliaLean.base.promotion.noOpErr (fun (_ : Unit) => typeName)
    (fun message => JuliaLean.base.error.errorVararg [.abstractString message]) "atan" ()

/--
Julia source: base/math.jl:833-833 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isless(x::T, y::T) where {T<:AbstractFloat} = (x < y) || (signbit(x) > signbit(y))
```
-/
def islessFloat {α : Type} (o : AbstractFloatOps α) (x y : α) : Bool :=
  o.lt x y || (o.signbit x && !o.signbit y)

/--
Julia source: base/math.jl:834-834 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::T, y::T) where {T<:AbstractFloat} = isnan(x) || ~isnan(y) && _isless(x, y) ? x : y
```
-/
def minGeneric {α : Type} (o : AbstractFloatOps α) (x y : α) : α :=
  if o.isnan x || (!o.isnan y && islessFloat o x y) then x else y

/--
Julia source: base/math.jl:835-835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::T, y::T) where {T<:AbstractFloat} = isnan(x) || ~isnan(y) && _isless(y, x) ? x : y
```
-/
def maxGeneric {α : Type} (o : AbstractFloatOps α) (x y : α) : α :=
  if o.isnan x || (!o.isnan y && islessFloat o y x) then x else y


/--
Julia source: base/math.jl:838-838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min(x::T, y::T) where {T<:IEEEFloat} = min_float(x, y)
```
-/
def minIEEE {T : FTy} (o : IEEEOps T) (x y : FV T) : FV T := o.minFloat x y

/--
Julia source: base/math.jl:839-839 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max(x::T, y::T) where {T<:IEEEFloat} = max_float(x, y)
```
-/
def maxIEEE {T : FTy} (o : IEEEOps T) (x y : FV T) : FV T := o.maxFloat x y

/--
Julia source: base/math.jl:836-836 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax(x::T, y::T) where {T<:AbstractFloat} = min(x, y), max(x, y)
```
-/
def minmaxGeneric {α : Type} (minFn maxFn : α → α → α) (x y : α) : α × α :=
  (minFn x y, maxFn x y)
/--
Julia source: base/math.jl:956-965 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _exponent_finite_nonzero(x::T) where T<:IEEEFloat
    # @precond :nothrow !isnan(x) && !isinf(x) && !iszero(x)
    xs = reinterpret(Unsigned, x) & ~sign_mask(T)
    k = rem(xs >> significand_bits(T), Int)
    if k == 0 # x is subnormal
        m = leading_zeros(xs) - exponent_bits(T)
        k = 1 - m
    end
    return k - exponent_bias(T)
end
```
-/
def exponentFiniteNonzero {T : FTy} (x : FV T) : Int :=
  let xs := withoutBits x.toBits (signMask T) T.fmt.width
  let k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    let m := leadingZeros T.fmt.width xs - exponentBits T
    (1 - (m : Int)) - exponentBias T
  else k - exponentBias T

/--
Julia source: base/math.jl:1026-1038 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function significand(x::T) where T<:IEEEFloat
    xu = reinterpret(Unsigned, x)
    xs = xu & ~sign_mask(T)
    xs >= exponent_mask(T) && return x # NaN or Inf
    if xs <= (~exponent_mask(T) & ~sign_mask(T)) # x is subnormal
        xs == 0 && return x # +-0
        m = unsigned(leading_zeros(xs) - exponent_bits(T))
        xs <<= m
        xu = xs | (xu & sign_mask(T))
    end
    xu = (xu & ~exponent_mask(T)) | exponent_one(T)
    return reinterpret(T, xu)
end
```
-/
def significand {T : FTy} (x : FV T) : FV T := Id.run do
  let xu0 := x.toBits
  let mut xu := xu0
  let xs := withoutBits xu0 (signMask T) T.fmt.width
  if xs >= exponentMask T then return x
  if xs <= bitMask T.fmt.width - exponentMask T - signMask T then
    if xs == 0 then return x
    let m := leadingZeros T.fmt.width xs - exponentBits T
    let xs := xs * 2 ^ m
    xu := xs + (if fsignbit x then signMask T else 0)
  xu := withoutBits xu (exponentMask T) T.fmt.width + exponentBias T * 2 ^ significandBits T
  return Fl.ofBits xu

/--
Julia source: base/math.jl:1060-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function frexp(x::T) where T<:IEEEFloat
    xu = reinterpret(Unsigned, x)
    xs = xu & ~sign_mask(T)
    xs >= exponent_mask(T) && return x, 0 # NaN or Inf
    # use `% Int` instead of `Int(...)` to preserve `:nothrow` (after masking the sign
    # bit, xs >> significand_bits(T) is at most 2^exponent_bits(T)-1, which always fits in Int)
    k = (xs >> significand_bits(T)) % Int
    if k == 0 # x is subnormal
        xs == 0 && return x, 0 # +-0
        m = leading_zeros(xs) - exponent_bits(T)
        xs <<= unsigned(m)
        xu = xs | (xu & sign_mask(T))
        k = 1 - m
    end
    k -= (exponent_bias(T) - 1)
    xu = (xu & ~exponent_mask(T)) | exponent_half(T)
    return reinterpret(T, xu), k
end
```
-/
def frexp {T : FTy} (x : FV T) : FV T × Int := Id.run do
  let xu0 := x.toBits
  let mut xu := xu0
  let xs := withoutBits xu0 (signMask T) T.fmt.width
  if xs >= exponentMask T then return (x, 0)
  let mut k : Int := (xs / 2 ^ significandBits T : Nat)
  if k == 0 then
    if xs == 0 then return (x, 0)
    let m := leadingZeros T.fmt.width xs - exponentBits T
    let xs := xs * 2 ^ m
    xu := xs + (if fsignbit x then signMask T else 0)
    k := 1 - m
  k := k - (exponentBias T - 1)
  xu := withoutBits xu (exponentMask T) T.fmt.width + (exponentBias T - 1) * 2 ^ significandBits T
  return (Fl.ofBits xu, k)

/--
Julia source: base/math.jl:1122-1145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem(x::T, p::T, ::RoundingMode{:Nearest}) where T<:IEEEFloat
    (iszero(p) || !isfinite(x) || isnan(p)) && return T(NaN)
    x == p && return copysign(zero(T), x)
    oldx = x
    x = abs(rem(x, 2p))  # 2p may overflow but that's okay
    p = abs(p)
    if p < 2 * floatmin(T)  # Check whether dividing p by 2 will underflow
        if 2x > p
            x -= p
            if 2x >= p
                x -= p
            end
        end
    else
        p_half = p / 2
        if x > p_half
            x -= p
            if x >= p_half
                x -= p
            end
        end
    end
    return flipsign(x, oldx)
end
```
-/
def remNearestSource {T : FTy} (o : IEEEOps T) (x0 p0 : FV T) : FV T := Id.run do
  if fiszero p0 || !fisfinite x0 || fisnan p0 then return fnan T
  if feq x0 p0 then return JuliaLean.base.float.copysign_float (fzero T) x0
  let oldx := x0
  let mut x := fabs (o.rem x0 (mul (Fl.ofInt 2) p0))
  let p := fabs p0
  if flt p (mul (Fl.ofInt 2) o.floatmin) then
    if flt p (mul (Fl.ofInt 2) x) then
      x := sub x p
      if fle p (mul (Fl.ofInt 2) x) then x := sub x p
  else
    let pHalf := div p (Fl.ofInt 2)
    if flt pHalf x then
      x := sub x p
      if fle pHalf x then x := sub x p
  return o.flipsign x oldx

-- Source: base/math.jl:1122-1145
def remNearest {T : FTy} (o : IEEEOps T) (x0 p0 : FV T) : FV T :=
  remNearestSource o x0 p0

/--
Julia source: base/math.jl:1163-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
modf(x) = isinf(x) ? (flipsign(zero(x), x), x) : (rem(x, one(x)), trunc(x))
```
-/
def modfGeneric {α : Type} (isinf : α → Bool) (zero one trunc : α → α)
    (flip rem : α → α → α) (x : α) : α × α :=
  if isinf x then (flip (zero x) x, x) else (rem x (one x), trunc x)

/--
Julia source: base/math.jl:1165-1170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function modf(x::T) where T<:IEEEFloat
    isinf(x) && return (copysign(zero(T), x), x)
    ix = trunc(x)
    rx = copysign(x - ix, x)
    return (rx, ix)
end
```
-/
def modfIEEE {T : FTy} (o : IEEEOps T) (x : FV T) : FV T × FV T :=
  if fisinf x then (JuliaLean.base.float.copysign_float (fzero T) x, x)
  else
    let ix := o.trunc x
    let rx := JuliaLean.base.float.copysign_float (sub x ix) x
    (rx, ix)

/--
Julia source: base/math.jl:1176-1185 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function add22condh(xh::Float64, xl::Float64, yh::Float64, yl::Float64)
    # This algorithm, due to Dekker, computes the sum of two
    # double-double numbers and returns the high double. References:
    # [1] http://www.digizeitschriften.de/en/dms/img/?PID=GDZPPN001170007
    # [2] https://doi.org/10.1007/BF01397083
    r = xh+yh
    s = (abs(xh) > abs(yh)) ? (xh-r+yh+yl+xl) : (yh-r+xh+xl+yl)
    zh = r+s
    return zh
end
```
-/
def add22condh (xh xl yh yl : FV .f64) : FV .f64 :=
  let r := add xh yh
  let s := if flt (fabs yh) (fabs xh)
    then add (add (add (sub xh r) yh) yl) xl
    else add (add (add (sub yh r) xh) xl) yl
  let zh := add r s
  zh

/--
Julia source: base/math.jl:1241-1241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mod2pi(x) = rem2pi(x,RoundDown)
```
-/
def mod2pi {α : Type} (rem2pi : α → JuliaLean.base.float.RoundingMode → α) (x : α) : α :=
  rem2pi x .Down

/--
Julia source: base/math.jl:1309-1309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $func(a::Float16) = Float16($func(Float32(a)))
```
-/
def float16Via32 (f : FV .f32 → Jl (FV .f32)) (a : FV .f16) : Jl (FV .f16) := do
  return Fl.convert (← f (Fl.convert a))

/--
Julia source: base/math.jl:1310-1310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $func(a::ComplexF16) = ComplexF16($func(ComplexF32(a)))
```
-/
def complex16Via32 (f : Cx .f32 → Jl (Cx .f32)) (a : Cx .f16) : Jl (Cx .f16) := do
  let result ← f ⟨Fl.convert a.re, Fl.convert a.im⟩
  return ⟨Fl.convert result.re, Fl.convert result.im⟩

/--
Julia source: base/math.jl:1315-1315 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
     @eval $func(a::ComplexF16) = ComplexF16($func(ComplexF32(a)))
```
-/
def complex16Via32Second (f : Cx .f32 → Jl (Cx .f32)) (a : Cx .f16) : Jl (Cx .f16) := do
  let result ← f ⟨Fl.convert a.re, Fl.convert a.im⟩
  return ⟨Fl.convert result.re, Fl.convert result.im⟩

/--
Julia source: base/math.jl:1319-1319 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atan(a::Float16,b::Float16) = Float16(atan(Float32(a),Float32(b)))
```
-/
def atan16 (atan32 : FV .f32 → FV .f32 → Jl (FV .f32))
    (a b : FV .f16) : Jl (FV .f16) := do
  return Fl.convert (← atan32 (Fl.convert a) (Fl.convert b))

/--
Julia source: base/math.jl:1320-1320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos(a::Float16) = Float16.(sincos(Float32(a)))
```
-/
def sincos16 (sincos32 : FV .f32 → Jl (FV .f32 × FV .f32))
    (a : FV .f16) : Jl (FV .f16 × FV .f16) := do
  let result ← sincos32 (Fl.convert a)
  return (Fl.convert result.1, Fl.convert result.2)

/--
Julia source: base/math.jl:1326-1330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function ($f)(x::Real)
        xf = float(x)
        xf isa typeof(x) && throw(MethodError($f, (x,)))
        return ($f)(xf)
    end
```
-/
-- Source: base/math.jl:1326-1330
def realFallbackCall {α β γ : Type} (float : α → Jl β) (sameType : β → Bool)
    (fName : String) (f : β → Jl γ) (x : α) : Jl γ := do
  let xf ← float x
  if sameType xf then .error (.methodError fName) else f xf

def realFallback {α β γ : Type} (float : α → β) (sameType : α → Bool)
    (fName : String) (f : β → Jl γ) (x : α) : Jl γ :=
  realFallbackCall (fun x => .ok (float x)) (fun _ => sameType x) fName f x

/--
Julia source: base/math.jl:1331-1331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Missing) = missing
```
-/
def missingUnary {α : Type} (_x : Option α) : Option α := none

/--
Julia source: base/math.jl:1335-1335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Missing, ::Missing) = missing
```
-/
def missingBoth {α β γ : Type} (_x : Option α) (_y : Option β) : Option γ := none

/--
Julia source: base/math.jl:1336-1336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Number, ::Missing) = missing
```
-/
def missingRight {α β γ : Type} (_x : α) (_y : Option β) : Option γ := none

/--
Julia source: base/math.jl:1337-1337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval $(f)(::Missing, ::Number) = missing
```
-/
def missingLeft {α β γ : Type} (_x : Option α) (_y : β) : Option γ := none

/--
Julia source: base/math.jl:1340-1340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exp2(x::AbstractFloat) = 2^x
```
-/
def exp2Float {α : Type} (o : AbstractFloatOps α) (x : α) : α :=
  o.pow (o.ofInt 2) x

/--
Julia source: base/math.jl:1341-1341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exp10(x::AbstractFloat) = 10^x
```
-/
def exp10Float {α : Type} (o : AbstractFloatOps α) (x : α) : α :=
  o.pow (o.ofInt 10) x

/--
Julia source: base/math.jl:1342-1342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
fourthroot(::Missing) = missing
```
-/
def fourthrootMissing {α : Type} (_x : Option α) : Option α := none


end JuliaLean.base.math

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- Horner loop of `evalpoly(x, p::Tuple)` for a nonempty coefficient list: start from
`p[end]`, then `muladd(x, ex, p[i])` for `i = N-1:-1:1`; `base/math.jl:75-86`. -/
def horner (x : F64) : List F64 → F64
  | [] => F64.zero
  | [c] => c
  | c :: cs => F64.muladd x (horner x cs) c

/-- `evalpoly(x::Float64, p)` for a tuple or vector `p`; an empty `p` makes `p[end]`
throw `BoundsError`; `base/math.jl:75-98`. -/
def evalpoly (x : F64) (p : List F64) : Jl F64 :=
  if p.isEmpty then .error .boundsError else .ok (horner x p)

end JuliaLean.MathFuncs

namespace JuliaLean.FloatRanges

open JuliaLean.Float

/-- `_isless`, `base/math.jl:833`. -/
private def fisless (x y : F64) : Bool :=
  F64.lt x y || (F64.signbit x && !F64.signbit y)

/-- `max(x, y)` on Float64 (`max_float`); semantics of `base/math.jl:835`. -/
def fmax (x y : F64) : F64 :=
  if F64.isnan x || (!F64.isnan y && fisless y x) then x else y

/-- `min(x, y)` on Float64 (`min_float`); semantics of `base/math.jl:834`. -/
def fmin (x y : F64) : F64 :=
  if F64.isnan x || (!F64.isnan y && fisless x y) then x else y

end JuliaLean.FloatRanges

/-!
Short `base/math.jl` functions on Float64 (master `bbfa0ce4150`): `min`, `max`,
`minmax`, `clamp`, `hypot`, `scaleinv`, `deg2rad`, `rad2deg`, `fourthroot`,
`exponent(::Real)` for `Rational{Int64}`, and the generic and `BitSigned`
`copysign`/`flipsign` methods.
-/

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- LLVM `minimum`, the `min_float` intrinsic behind `min(::Float64, ::Float64)`;
`base/math.jl:838`. A NaN operand gives NaN; `-0.0` is below `+0.0`. -/
def fmin (x y : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isnan y then y
  else if F64.lt x y || (F64.iszero x && F64.iszero y && F64.signbit x) then x
  else y

/-- LLVM `maximum`, the `max_float` intrinsic behind `max(::Float64, ::Float64)`;
`base/math.jl:839`. -/
def fmax (x y : F64) : F64 :=
  if F64.isnan x then x
  else if F64.isnan y then y
  else if F64.lt y x || (F64.iszero x && F64.iszero y && F64.signbit y) then x
  else y

/-- `minmax(x::T, y::T) where {T<:AbstractFloat} = min(x, y), max(x, y)`; `base/math.jl:836`. -/
def fminmax (x y : F64) : F64 × F64 := (fmin x y, fmax x y)

/-- `sqrt(eps(Float64)/2)`, the constant at `base/math.jl:753`. -/
def hypotTiny : F64 := lit 0x3E46A09E667F3BCD
/-- `eps(Float64)*sqrt(floatmin(Float64))`, `base/math.jl:758`. -/
def hypotScale : F64 := lit 0x1CC0000000000000
/-- `sqrt(floatmax(Float64)/2)`, `base/math.jl:759`. -/
def hypotBig : F64 := lit 0x5FE6A09E667F3BCC
/-- `sqrt(floatmin(Float64))`, `base/math.jl:763`. -/
def hypotSmall : F64 := lit 0x2000000000000000

/-- `_hypot(x, y)` for Float64 on a machine with hardware fma (`have_fma` true);
`base/math.jl:732-776`. -/
def hypot (x y : F64) : F64 :=
  let axu := F64.abs x
  let ayu := F64.abs y
  let ax := F64.div axu F64.one
  let ay := F64.div ayu F64.one
  if F64.isinf ax || F64.isinf ay then F64.inf
  else
    let swap := F64.lt ax ay
    let axu := if swap then ayu else axu
    let (ax, ay) := if swap then (ay, ax) else (ax, ay)
    if F64.le ay (F64.mul ax hypotTiny) then axu
    else
      let (ax, ay, scale) :=
        if F64.lt hypotBig ax then
          (F64.mul ax hypotScale, F64.mul ay hypotScale, F64.div F64.one hypotScale)
        else if F64.lt ay hypotSmall then
          (F64.div ax hypotScale, F64.div ay hypotScale, hypotScale)
        else (ax, ay, F64.one)
      let h0 := match F64.sqrt (F64.muladd ax ax (F64.mul ay ay)) with
        | .ok v => v
        | .error _ => F64.nan
      let hsquared := F64.mul h0 h0
      let axsquared := F64.mul ax ax
      let num := F64.sub
        (F64.add (F64.fma (F64.neg ay) ay (F64.sub hsquared axsquared))
          (F64.fma h0 h0 (F64.neg hsquared)))
        (F64.fma ax ax (F64.neg axsquared))
      let h := F64.sub h0 (F64.div num (F64.mul (F64.ofInt 2) h0))
      F64.mul (F64.mul h scale) F64.one

/-- `scaleinv(x::Float64)`; `base/math.jl:1100-1111`. -/
def scaleinv (x : F64) : F64 × F64 :=
  let umin := 0x0010000000000000
  let umax := 0x7FD0000000000000
  let e := bitsOf x / 2^52 % 2048 * 2^52
  let u := if e > umax then umax else if e < umin then umin else e
  (F64.ofBits u, F64.ofBits (umin + umax - u))

/-- Maximum of the bit patterns of nonnegative values,
`reinterpret(T, maximum(z -> reinterpret(Signed, z), x))`; `base/math.jl:822`. -/
def maxBits : List F64 → Nat
  | [] => 0
  | x :: xs => max (bitsOf x) (maxBits xs)

/-- `mapreduce(y -> abs2(y * invscale), add_fast, x)` folded from the left, the order the
compiler emits for three arguments; `add_fast` lets it reassociate longer sums;
`base/math.jl:826-827`. -/
def sumScaledSquares (invscale : F64) : F64 → List F64 → F64
  | acc, [] => acc
  | acc, y :: ys =>
    let t := F64.mul y invscale
    sumScaledSquares invscale (F64.add acc (F64.mul t t)) ys

/-- `_hypot(x::NTuple{N,<:IEEEFloat})` for `N ≥ 3` Float64 arguments; `base/math.jl:816-828`. -/
def hypotN (xs : List F64) : F64 :=
  let xs := xs.map F64.abs
  if xs.any (fun z => F64.eq z F64.inf) then F64.inf
  else
    let maxabs := F64.ofBits (maxBits xs)
    if !(F64.lt F64.zero maxabs) then maxabs
    else
      let (scale, invscale) := scaleinv maxabs
      match xs with
      | [] => maxabs
      | y :: ys =>
        let t := F64.mul y invscale
        match F64.sqrt (sumScaledSquares invscale (F64.mul t t) ys) with
        | .ok s => F64.mul scale s
        | .error _ => F64.nan

/-- `deg2rad(z::AbstractFloat) = z * _pi_over_180(z)`, `_pi_over_180(z) = oftype(z, pi)/180`;
`base/math.jl:216-218,253`. -/
def deg2rad (z : F64) : F64 := F64.mul z (F64.div piF64 (F64.ofInt 180))

/-- `rad2deg(z::AbstractFloat) = z * _180_over_pi(z)`, `_180_over_pi(z) = 180/oftype(z, pi)`;
`base/math.jl:213-215,238`. -/
def rad2deg (z : F64) : F64 := F64.mul z (F64.div (F64.ofInt 180) piF64)

/-- `fourthroot(x::Number) = sqrt(sqrt(x))`; `base/math.jl:685`. -/
def fourthroot (x : F64) : Jl F64 := do
  let s ← F64.sqrt x
  F64.sqrt s

/-- `exponent(x::Real)` on a `Rational{Int64}` `num//den`: `float(x)` is
`float(x.num)/float(x.den)` (`base/rational.jl:204`), then `exponent(::Float64)`;
`base/math.jl:1322-1331`. -/
def exponentRat (num den : JInt .i64) : Jl Int :=
  F64.exponent (F64.div (F64.ofJInt num) (F64.ofJInt den))

end JuliaLean.MathFuncs

/-!
Bit-level methods of `base/math.jl` and `base/floatfuncs.jl` at Julia master
`bbfa0ce4150`, generic over the three IEEE formats (`T : FTy`): `ldexp`, `exponent`,
`_exponent_finite_nonzero`, `scaleinv`, the integer `exponent` methods, `highword` and
friends, `copysign`/`flipsign`/`signbit`, `maxintfloat`, `min`/`max`, IEEE `rem` with
`RoundNearest`, `modf`, and `add22condh`.
-/

namespace JuliaLean.MathCov.Bits

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP
open JuliaLean.FloatIntCov.Float (signMask exponentMask exponentOne significandBits
  exponentBits exponentBias exponentRawMax leadingZeros uintTy)

variable {T : FTy}

/-- `_ilog2_step(y, d, s)` on nonnegative integers (`BigInt`); `base/math.jl:967-978`.
`fuel` bounds the recursion, which deepens only while `y >= d^2`. -/
def ilog2Step : Nat → Nat → Nat → Nat → Nat × Nat
  | 0, y, _, _ => (y, 0)
  | fuel + 1, y, d, s =>
    let (y1, n1) := if y / 2 ^ s ≥ d then ilog2Step fuel y (d * d) (s + s) else (y, 0)
    if y1 ≥ d then (y1 / 2 ^ s, n1 + s) else (y1, n1)

/-- `exponent(x::Integer)` for unbounded integers; `base/math.jl:980-985`. -/
def exponentInteger (x : Int) : Jl Int :=
  if x == 0 then .error (.domainError "cannot be zero")
  else .ok (ilog2Step (x.natAbs + 1) x.natAbs 2 1).2

/-- `exponent(x::Base.BitInteger)`; `base/math.jl:987-991`. `uabs` of `typemin` is its
magnitude, which fits the unsigned type. -/
def exponentBitInteger {t : IntTy} (x : JInt t) : Jl Int :=
  if x.val == 0 then .error (.domainError "cannot be zero")
  else
    let ux := x.val.natAbs
    .ok ((t.bits : Int) - leadingZeros t.bits ux - 1)

/-- `exponent(x::Bool)`; `base/math.jl:993-999`. -/
def exponentBool (x : Bool) : Jl Int :=
  if x then .ok 0 else .error (.domainError "cannot be zero")

/-- `scaleinv(x::T)`; `base/math.jl:1100-1111`. Returns `(scale, invscale)`. -/
def scaleinv (x : FV T) : FV T × FV T :=
  let umin := (floatminT T : FV T).toBits
  let umax := (div (one T) (floatminT T) : FV T).toBits
  let e := (x.toBits / 2 ^ significandBits T % 2 ^ exponentBits T) * 2 ^ significandBits T
  let u := Nat.min (Nat.max e umin) umax
  (Fl.ofBits u, Fl.ofBits (umin + umax - u))

/-- `highword(x::UInt64) = (x >>> 32) % UInt32`; `base/math.jl:1276`. -/
def highwordU64 (u : Nat) : Nat := u / 2 ^ 32 % 2 ^ 32
/-- `highword(x::Float64)`; `base/math.jl:1275`. -/
def highword64 (x : FV .f64) : Nat := highwordU64 x.toBits
/-- `highword(x::Float32) = reinterpret(UInt32, x)`; `base/math.jl:1277`. -/
def highword32 (x : FV .f32) : Nat := x.toBits
/-- `fromhighword(Float64, u)`; `base/math.jl:1279`. -/
def fromhighword64 (u : Nat) : FV .f64 := Fl.ofBits (u % 2 ^ 32 * 2 ^ 32)
/-- `fromhighword(Float32, u)`; `base/math.jl:1280`. -/
def fromhighword32 (u : Nat) : FV .f32 := Fl.ofBits (u % 2 ^ 32)
/-- `poshighword(x::UInt64) = highword(x) & 0x7fffffff`; `base/math.jl:1288-1290`. -/
def poshighwordU64 (u : Nat) : Nat := highwordU64 u % 2 ^ 31
def poshighword64 (x : FV .f64) : Nat := poshighwordU64 x.toBits
def poshighword32 (x : FV .f32) : Nat := highword32 x % 2 ^ 31

/-- `_isless(x, y) = (x < y) || (signbit(x) > signbit(y))`; `base/math.jl:833`. -/
def isless_ (x y : FV T) : Bool := lt x y || (x.signbit && !y.signbit)

/-- Generic `min`/`max` for `AbstractFloat`; `base/math.jl:834-835`. -/
def minGeneric (x y : FV T) : FV T := if x.isnan || (!y.isnan && isless_ x y) then x else y
def maxGeneric (x y : FV T) : FV T := if x.isnan || (!y.isnan && isless_ y x) then x else y

/-- `min_float`/`max_float` (LLVM `minimum`/`maximum`: NaN-propagating, `-0.0 < 0.0`);
`base/math.jl:838-839`. -/
def minFloat (x y : FV T) : FV T :=
  if x.isnan then x else if y.isnan then y else if isless_ y x then y else x
def maxFloat (x y : FV T) : FV T :=
  if x.isnan then x else if y.isnan then y else if isless_ x y then y else x

/-- `rem(x::T, p::T, ::RoundingMode{:Nearest})`; `base/math.jl:1122-1145`. `rem(x, 2p)` is
the `base/float.jl` remainder (`FloatIntCov.Float.rem`). -/
def remNearest (x p : FV T) : FV T := Id.run do
  if p.iszero || !x.isfinite || p.isnan then return nan T
  if eq x p then return copysign (zero T) x
  let oldx := x
  let mut x := abs (FloatIntCov.Float.rem x (mul (ofInt T 2) p))
  let p := abs p
  if lt p (mul (ofInt T 2) (floatminT T)) then
    if lt p (mul (ofInt T 2) x) then
      x := sub x p
      if le p (mul (ofInt T 2) x) then
        x := sub x p
  else
    let pHalf := div p (ofInt T 2)
    if lt pHalf x then
      x := sub x p
      if le pHalf x then
        x := sub x p
  return flipsign x oldx

/-- `modf(x::T) where T<:IEEEFloat`; `base/math.jl:1165-1170`. -/
def modf (x : FV T) : FV T × FV T :=
  if x.isinf then (copysign (zero T) x, x)
  else
    let ix := trunc x
    (copysign (sub x ix) x, ix)

/-- Generic `modf(x)` for a float `x`: `isinf(x) ? (flipsign(zero(x), x), x) :
(rem(x, one(x)), trunc(x))`; `base/math.jl:1163`. -/
def modfGeneric (x : FV T) : FV T × FV T :=
  if x.isinf then (flipsign (zero T) x, x)
  else (FloatIntCov.Float.rem x (one T), trunc x)

/-- `add22condh(xh, xl, yh, yl)`; `base/math.jl:1176-1185`. -/
def add22condh (xh xl yh yl : FV .f64) : FV .f64 :=
  let r := add xh yh
  let s := if lt (abs yh) (abs xh) then add (add (add (sub xh r) yh) yl) xl
    else add (add (add (sub yh r) xh) xl) yl
  add r s

end JuliaLean.MathCov.Bits

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `_exthorner(i, x, p, hi, lo)` with `pi = p[i]`; `base/math.jl:203-210`. -/
def exthornerStep (twoMul : F64 → F64 → F64 × F64) (p x hi lo : F64) : F64 × F64 :=
  let (prod, err) := twoMul hi x
  let hi' := F64.add p prod
  (hi', F64.fma lo x (F64.add (F64.sub prod (F64.sub hi' p)) err))

/-- `exthorner(x, (p1, p2, p3))`; `base/math.jl:196-201`. -/
def exthorner (twoMul : F64 → F64 → F64 × F64)
    (x : F64) (p : F64 × F64 × F64) : F64 × F64 :=
  let (hi, lo) := exthornerStep twoMul p.2.1 x p.2.2 F64.zero
  exthornerStep twoMul p.1 x hi lo

end JuliaLean.MathFuncs

namespace JuliaLean.MathCov.Exp

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP

/-- `evalpoly(x, p)` for a coefficient tuple: Horner with `muladd`; `base/math.jl:75-86`. -/
def horner {T : FTy} (x : FV T) : List (FV T) → FV T
  | [] => zero T
  | [c] => c
  | c :: cs => muladd x (horner x cs) c

/-- `_exthorner(i, x, p, hi, lo)` with `pi = p[i]`, after the index check
`i == 2 || i == 1 || error(...)`; `base/math.jl:203-210`. -/
def exthornerStep {T : FTy} (twoMulG : FV T → FV T → FV T × FV T)
    (i : Nat) (x : FV T) (p : FV T × FV T × FV T) (hi lo : FV T) :
    Jl (FV T × FV T) :=
  if !(i == 2 || i == 1) then .error (.argumentError "unexpected index")
  else
    let pi := if i == 1 then p.1 else p.2.1
    let (prod, err) := twoMulG hi x
    let hi' := add pi prod
    .ok (hi', fma lo x (add (sub prod (sub hi' pi)) err))

/-- `exthorner(x, p::Tuple{T,T,T})`; `base/math.jl:196-201`. -/
def exthorner {T : FTy} (twoMulG : FV T → FV T → FV T × FV T)
    (x : FV T) (p : FV T × FV T × FV T) : Jl (FV T × FV T) := do
  let (hi, lo) ← exthornerStep twoMulG 2 x p p.2.2 (zero T)
  exthornerStep twoMulG 1 x p hi lo

end JuliaLean.MathCov.Exp

namespace JuliaLean.NumMisc

def nf32Horner (x : NF32) : List NF32 → NF32
  | [] => JuliaLean.Promotion.Fl.zero
  | [c] => c
  | c :: cs => nf32Fma x (nf32Horner x cs) c

end JuliaLean.NumMisc

namespace JuliaLean.MathCov.Trig

open JuliaLean JuliaLean.Promotion

/-- `@horner(x, c...)`, i.e. `evalpoly`; `base/math.jl:157-160`. -/
abbrev horner {T : FTy} := @Exp.horner T

/-- `throw_finite_domainerror(f, x)`; `base/math.jl:40-42`. -/
def finiteDomainError {α : Type} (f : String) : Jl α := .error (.domainError f)

end JuliaLean.MathCov.Trig

namespace JuliaLean.MathCov.TrigMisc

open JuliaLean JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C

/-- `deg2rad(z::AbstractFloat) = z * _pi_over_180(z)`; `base/math.jl:216-223,253`. -/
def deg2rad (T : FTy) (z : FV T) : FV T :=
  match T with
  | .f16 => mul z deg2rad16
  | .f32 => mul z deg2rad32
  | .f64 => mul z deg2rad64

/-- `rad2deg(z::AbstractFloat) = z * _180_over_pi(z)`; `base/math.jl:213-222,238`. -/
def rad2deg (T : FTy) (z : FV T) : FV T :=
  match T with
  | .f16 => mul z rad2deg16
  | .f32 => mul z rad2deg32
  | .f64 => mul z rad2deg64

/-- `_180_over_pi(z) = 180 / oftype(z, pi)`, `_pi_over_180(z) = oftype(z, pi) / 180` for a
float type without a specialised constant; `base/math.jl:213-218`. -/
def oneEightyOverPi (T : FTy) : FV T := div (ofInt T 180) (Trig.piT T)
def piOverOneEighty (T : FTy) : FV T := div (Trig.piT T) (ofInt T 180)

end JuliaLean.MathCov.TrigMisc

namespace JuliaLean.MathFuncs

open JuliaLean.Float

/-- `add22condh(xh, xl, yh, yl)`: high part of Dekker's double-double sum;
`base/math.jl:1176-1186`. -/
def add22condh (xh xl yh yl : F64) : F64 :=
  let r := F64.add xh yh
  let s :=
    if F64.lt (F64.abs yh) (F64.abs xh) then
      F64.add (F64.add (F64.add (F64.sub xh r) yh) yl) xl
    else
      F64.add (F64.add (F64.add (F64.sub yh r) xh) xl) yl
  F64.add r s

/-- `mod2pi(x) = rem2pi(x, RoundDown)`; `base/math.jl:1241`. -/
def mod2pi (rem2piDown : F64 → F64) (x : F64) : F64 := rem2piDown x

end JuliaLean.MathFuncs

/-!
The remaining methods of `base/math.jl` at Julia master `bbfa0ce4150`: the error
helpers, the complex `evalpoly`, `log(b, x)`, `nan_dom_err`, `sqrt`, `fourthroot`, the
`hypot` family, the `atan` and `muladd` fallbacks, and the method-generating loops for
`Float16`, `ComplexF16`, `Real` and `Missing` arguments.
-/

namespace JuliaLean.MathCov.MathMisc

open JuliaLean JuliaLean.Float JuliaLean.Promotion JuliaLean.MathCov.FP JuliaLean.MathCov.C
open JuliaLean.MathCov.TrigPi (Cx)

/-- `throw_complex_domainerror(f, x)`, `throw_complex_domainerror_neg1(f, x)`,
`throw_finite_domainerror(f, x)` and `throw_exp_domainerror(x)` all throw `DomainError`;
`base/math.jl:32-48`. -/
def throwComplexDomainError {α : Type} (f : String) : Jl α := .error (.domainError f)
def throwComplexDomainErrorNeg1 {α : Type} (f : String) : Jl α := .error (.domainError f)
def throwFiniteDomainError {α : Type} (f : String) : Jl α := .error (.domainError f)
def throwExpDomainError {α : Type} : Jl α := .error (.domainError "Exponentiation yielding a complex result requires a complex argument.")

/-- `_evalpoly(x, p)` for a real `x` and coefficient vector `p`; `base/math.jl:90-98`.
`p[end]` of an empty vector throws `BoundsError`. The `@horner` macro expands to
`invoke(evalpoly, Tuple{Any, Tuple}, x, p)`, the same Horner loop (`base/math.jl:157-160`),
and `@evalpoly(z, p...)` to `evalpoly(z, (p...,))` (`base/math.jl:189-192`). -/
def evalpolyReal {T : FTy} (x : FV T) (p : List (FV T)) : Jl (FV T) :=
  if p.isEmpty then .error .boundsError else .ok (Exp.horner x p)

/-- `_evalpoly(z::Complex, p)` for real coefficients (the Goertzel-style recurrence);
`base/math.jl:130-148`. The generated `evalpoly(z::Complex, p::Tuple)` (`base/math.jl:100-124`)
unrolls the same recurrence, and `evalpoly(z::Complex, p::Tuple{<:Any}) = p[1]`
(`base/math.jl:125`). -/
def evalpolyComplex {T : FTy} (z : Cx T) (p : List (FV T)) : Jl (Cx T) :=
  match p.reverse with
  | [] => .error .boundsError
  | [c] => .ok ⟨c, zero T⟩
  | a :: b :: rest =>
    let x := z.re
    let y := z.im
    let r := add x x
    let s := muladd x x (mul y y)
    let (a, b) := rest.foldl (fun (ab : FV T × FV T) pi =>
      let ai := ab.1
      (muladd r ai ab.2, muladd (neg s) ai pi)) (a, b)
    .ok (muladdCR a z b)

/-- `evalpoly(z::Complex, p::Tuple{<:Any}) = p[1]`, a real coefficient as is. -/
def evalpolyComplex1 {T : FTy} (_z : Cx T) (c : FV T) : FV T := c

/-- `rad2deg(z::Real) = rad2deg(float(z))`, `deg2rad(z::Real)`, and for other numbers
`rad2deg(z) = (z/pi)*180`, `deg2rad(z) = (z*pi)/180`; `base/math.jl:254-257`. -/
def rad2degNumber {T : FTy} (z : Cx T) : Cx T :=
  let p := Trig.piT T
  ⟨mul (div z.re p) (ofInt T 180), mul (div z.im p) (ofInt T 180)⟩
def deg2radNumber {T : FTy} (z : Cx T) : Cx T :=
  let p := Trig.piT T
  ⟨div (mul z.re p) (ofInt T 180), div (mul z.im p) (ofInt T 180)⟩

/-- `log(b::T, x::T) = log(x)/log(b)` for a float type with its `log`; `base/math.jl:259`.
`log(b::Number, x::Number) = log(promote(b,x)...)` (`base/math.jl:304`). -/
def logBase {α : Type} (logf : α → Jl α) (divα : α → α → α) (b x : α) : Jl α := do
  return divα (← logf x) (← logf b)

/-- `nan_dom_err(out, x)`; `base/math.jl:399`. -/
def nanDomErr {T S : FTy} (out : FV T) (x : FV S) : Jl (FV T) :=
  if out.isnan && !x.isnan then .error (.domainError "NaN result for non-NaN input.") else .ok out

/-- `sqrt(x::IEEEFloat)`; `base/math.jl:629-632`. -/
def sqrt {T : FTy} (x : FV T) : Jl (FV T) :=
  if lt x (zero T) then throwComplexDomainError "sqrt" else .ok (sqrtLlvm x)

/-- `fourthroot(x::Number) = sqrt(sqrt(x))`; `base/math.jl:685`. -/
def fourthroot {T : FTy} (x : FV T) : Jl (FV T) := do sqrt (← sqrt x)

/-- `hypot(x::Number) = abs(float(x))`; `base/math.jl:729`. -/
def hypot1 {T : FTy} (x : FV T) : FV T := abs x

/-- `_hypot(x, y)` for real floats `x`, `y` of type `T` on a machine with fma;
`base/math.jl:732-786`. -/
def hypotGeneric {T : FTy} (x y : FV T) : FV T := Id.run do
  let mut axu := abs x
  let ayu := abs y
  let mut ax := axu
  let mut ay := ayu
  if ax.isinf || ay.isinf then return inf T
  if lt ax ay then
    axu := ayu
    let t := ax
    ax := ay
    ay := t
  let epsT' := epsT T
  if le ay (mul ax (sqrtLlvm (div epsT' (ofInt T 2)))) then return axu
  let mut scale := mul epsT' (sqrtLlvm (floatminT T))
  if lt (sqrtLlvm (div (floatmaxT T) (ofInt T 2))) ax then
    ax := mul ax scale
    ay := mul ay scale
    scale := div (one T) scale
  else if lt ay (sqrtLlvm (floatminT T)) then
    ax := div ax scale
    ay := div ay scale
  else scale := one T
  let mut h := sqrtLlvm (muladd ax ax (mul ay ay))
  let hsquared := mul h h
  let axsquared := mul ax ax
  h := sub h (div (sub (add (fma (neg ay) ay (sub hsquared axsquared)) (fma h h (neg hsquared)))
    (fma ax ax (neg axsquared))) (mul (ofInt T 2) h))
  return mul (mul h scale) (one T)

/-- `_hypot(x::Float32, y::Float32)`; `base/math.jl:789-795`. -/
def hypot32 (x y : FV .f32) : FV .f32 :=
  if x.isinf || y.isinf then inf .f32
  else
    let x' : FV .f64 := conv x
    let y' : FV .f64 := conv y
    conv (sqrtLlvm (muladd x' x' (mul y' y')))

/-- `_hypot(x::Float16, y::Float16)`; `base/math.jl:796-802`. -/
def hypot16 (x y : FV .f16) : FV .f16 :=
  if x.isinf || y.isinf then inf .f16
  else
    let x' : FV .f32 := conv x
    let y' : FV .f32 := conv y
    conv (sqrtLlvm (muladd x' x' (mul y' y')))

/-- `abs(z::Complex) = hypot(real(z), imag(z))` for `ComplexF32`. -/
def absC32 (z : Cx .f32) : FV .f32 := hypot32 z.re z.im

/-- `_hypot(x::ComplexF16, y::ComplexF16) = Float16(_hypot(ComplexF32(x), ComplexF32(y)))`,
where the complex generic `_hypot` starts from `abs` of each argument; `base/math.jl:803`. -/
def hypotC16 (x y : Cx .f16) : FV .f16 :=
  conv (hypotGeneric (absC32 ⟨conv x.re, conv x.im⟩) (absC32 ⟨conv y.re, conv y.im⟩))

/-- `hypot(x, y)` on the two-argument IEEE method of the promoted type;
`base/math.jl:730` with `_hypot` at `base/math.jl:732,789,796`. -/
def hypot2 : (T : FTy) → FV T → FV T → FV T
  | .f16, x, y => hypot16 x y
  | .f32, x, y => hypot32 x y
  | .f64, x, y => of64 (MathFuncs.hypot (to64 x) (to64 y))

/-- `hypot(x::Number, y::Number) = _hypot(float.(promote(x, y))...)` for floats of two
formats: both are converted (exactly) to the wider one; `base/math.jl:730`. -/
def promoteTy (T S : FTy) : FTy :=
  match T, S with
  | .f64, _ | _, .f64 => .f64
  | .f32, _ | _, .f32 => .f32
  | _, _ => .f16
def hypotMixed {T S : FTy} (x : FV T) (y : FV S) : FV (promoteTy T S) :=
  hypot2 (promoteTy T S) (conv x) (conv y)

/-- `_hypot(x::NTuple{N,<:Number})` for real floats; `base/math.jl:805-814`. -/
def hypotTupleGeneric {T : FTy} (xs : List (FV T)) : FV T :=
  let maxabs := xs.foldl (fun m v => if lt m (abs v) || (abs v).isnan then abs v else m) (zero T)
  if maxabs.isnan && xs.any (·.isinf) then inf T
  else if maxabs.iszero || maxabs.isinf then maxabs
  else mul maxabs (sqrtLlvm (xs.foldl (fun s v => let q := div v maxabs; add s (mul q q)) (zero T)))

/-- `_hypot(x::NTuple{N,<:IEEEFloat})`, with `add_fast` an ordinary addition (it is
`add_float_fast`, whose only licence is reassociation); `base/math.jl:816-828`. -/
def hypotTupleIEEE {T : FTy} (xs : List (FV T)) : FV T :=
  let xs := xs.map abs
  if xs.any (fun v => eq v (inf T)) then inf T
  else
    let maxabs : FV T := Fl.ofBits (xs.foldl (fun m v => Nat.max m v.toBits) 0)
    if !(lt (zero T) maxabs) then maxabs
    else
      let (scale, invscale) := Bits.scaleinv maxabs
      match xs.map (fun v => let q := mul v invscale; mul q q) with
      | [] => maxabs
      | q :: qs => mul scale (sqrtLlvm (qs.foldl add q))

/-- `add_fast(x, y)`; `base/math.jl:826`. -/
def addFast {T : FTy} (x y : FV T) : FV T := add x y

/-- `atan(y::Real, x::Real) = atan(promote(float(y), float(x))...)`; `base/math.jl:830`. -/
def atanMixed (atan2 : (U : FTy) → FV U → FV U → FV U)
    {T S : FTy} (y : FV T) (x : FV S) : FV (promoteTy T S) :=
  match promoteTy T S with
  | .f16 => conv (atan2 .f32 (conv y) (conv x))
  | U => atan2 U (conv y) (conv x)

/-- `atan(y::T, x::T) where {T<:AbstractFloat} = Base.no_op_err("atan", T)` for a float type
without its own method; `base/math.jl:831`. -/
def atanNoOp {α : Type} : Jl α := .error (.methodError "atan")

/-- `muladd(x, y, z) = x*y+z` for a fixed-width integer type; `base/math.jl:1265`. -/
def muladdInt {t : IntTy} (x y z : JInt t) : JInt t := JInt.wrap t (wrapInt t (x.val * y.val) + z.val)

/-- Generic `muladd(x,y,z) = x*y+z`; `base/math.jl:1265`. -/
def muladdGeneric {α : Type} (mul add : α → α → α) (x y z : α) : α := add (mul x y) z

/-- `$func(a::Float16) = Float16($func(Float32(a)))` for the fifteen functions of the loop;
`base/math.jl:1306-1312`. -/
def viaF32 (f : FV .f32 → Jl (FV .f32)) (a : FV .f16) : Jl (FV .f16) := do
  return conv (← f (conv a))

/-- `$func(a::ComplexF16) = ComplexF16($func(ComplexF32(a)))`; `base/math.jl:1310,1315`. -/
def viaC32 (f : Cx .f32 → Jl (Cx .f32)) (a : Cx .f16) : Jl (Cx .f16) := do
  let r ← f ⟨conv a.re, conv a.im⟩
  return ⟨conv r.re, conv r.im⟩

/-- `atan(a::Float16, b::Float16) = Float16(atan(Float32(a), Float32(b)))`; `base/math.jl:1319`. -/
def atan16 (atan2 : (U : FTy) → FV U → FV U → FV U)
    (a b : FV .f16) : FV .f16 := conv (atan2 .f32 (conv a) (conv b))

/-- `sincos(a::Float16) = Float16.(sincos(Float32(a)))`; `base/math.jl:1320`. -/
def sincos16 (f : FV .f32 → Jl (FV .f32 × FV .f32))
    (a : FV .f16) : Jl (FV .f16 × FV .f16) := do
  let r ← f (conv a)
  return (conv r.1, conv r.2)

/-- `($f)(x::Real)`: `xf = float(x)`; a float `x` already of type `float(x)` has no method
(`MethodError`); otherwise `f(xf)`; `base/math.jl:1326-1330`. -/
def realFallback {α β : Type} (float : α → β) (isFloat : Bool) (f : β → Jl β) (x : α) : Jl β :=
  if isFloat then .error (.methodError "f") else f (float x)

/-- `f(::Missing) = missing` and the two-argument `Missing` methods; `base/math.jl:1331-1337`. -/
def missing1 {α : Type} (_x : Option α) : Option α := none
def missing2 {α β γ : Type} (_x : Option α) (_y : Option β) : Option γ := none

/-- `exp2(x::AbstractFloat) = 2^x` and `exp10(x::AbstractFloat) = 10^x` for a float type with
power `pow`; `base/math.jl:1340-1341`. -/
def exp2Abstract {α : Type} (two : α) (pow : α → α → α) (x : α) : α := pow two x
def exp10Abstract {α : Type} (ten : α) (pow : α → α → α) (x : α) : α := pow ten x

/-- `mod2pi(x) = rem2pi(x, RoundDown)`; `base/math.jl:1241`. -/
def mod2pi (rem2pi64 : FV .f64 → FloatFuncs.Mode → FV .f64)
    (rem2piNarrow : {U : FTy} → FV U → FloatFuncs.Mode → FV U)
    {T : FTy} (x : FV T) : FV T :=
  match T, x with
  | .f64, x => rem2pi64 x .Down
  | _, x => rem2piNarrow x .Down

end JuliaLean.MathCov.MathMisc

namespace JuliaLean.Reduce.Val

open JuliaLean.Float

/-- `_isless(x, y)` on floats, `base/math.jl:833`. -/
def fisless (x y : F64) : Bool := F64.lt x y || (F64.signbit x && !F64.signbit y)

/-- `max(x, y)` on `Float64` (`max_float`), semantics of `base/math.jl:835`. -/
def fmax (x y : F64) : F64 := if F64.isnan x || (!F64.isnan y && fisless y x) then x else y

/-- `min(x, y)` on `Float64` (`min_float`), semantics of `base/math.jl:834`. -/
def fmin (x y : F64) : F64 := if F64.isnan x || (!F64.isnan y && fisless x y) then x else y

end JuliaLean.Reduce.Val
