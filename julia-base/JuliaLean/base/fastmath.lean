import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.Runtime.Float
import JuliaLean.base.float
import JuliaLean.src.runtime_intrinsics_c

/-!
# Model of `base/fastmath.jl`

Typed fast-math wrappers are generic over IEEE formats and complex Float32/Float64 values. Fast
intrinsics, Base math calls, AST construction, promotion, and reductions remain explicit operation
interfaces where Julia calls outside this file. Generated fallback dispatch uses typed generic
models with explicit Base operation and promotion callbacks.
-/

-- Source: base/fastmath.jl:1-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Support for @fastmath
-- 
-- # This module provides versions of math functions that may violate
-- # strict IEEE semantics.
-- 
-- # This allows the following transformations. For more information see
-- # https://llvm.org/docs/LangRef.html#fast-math-flags:
-- # nnan: No NaNs - Allow optimizations to assume the arguments and
-- #       result are not NaN. Such optimizations are required to retain
-- #       defined behavior over NaNs, but the value of the result is
-- #       undefined.
-- # ninf: No Infs - Allow optimizations to assume the arguments and
-- #       result are not +/-Inf. Such optimizations are required to
-- #       retain defined behavior over +/-Inf, but the value of the
-- #       result is undefined.
-- # nsz:  No Signed Zeros - Allow optimizations to treat the sign of a
-- #       zero argument or result as insignificant.
-- # arcp: Allow Reciprocal - Allow optimizations to use the reciprocal
-- #       of an argument rather than perform division.
-- # fast: Fast - Allow algebraically equivalent transformations that may
-- #       dramatically change results in floating point (e.g.
-- #       reassociate). This flag implies all the others.
-- 
-- module FastMath
-- 
-- export @fastmath
-- 
-- import Core.Intrinsics: sqrt_llvm_fast, neg_float_fast,
--     add_float_fast, sub_float_fast, mul_float_fast, div_float_fast, min_float_fast, max_float_fast,
--     eq_float_fast, ne_float_fast, lt_float_fast, le_float_fast
-- import Base: afoldl
-- 
-- /Source


namespace JuliaLean.base.fastmath

open JuliaLean JuliaLean.base.float JuliaLean.ExprReflect
open JuliaLean.Promotion hiding FV FTy

/--
Julia source: base/fastmath.jl:35-94 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const fast_op =
    Dict(# basic arithmetic
         :+ => :add_fast,
         :- => :sub_fast,
         :* => :mul_fast,
         :/ => :div_fast,
         :(==) => :eq_fast,
         :!= => :ne_fast,
         :< => :lt_fast,
         :<= => :le_fast,
         :> => :gt_fast,
         :>= => :ge_fast,
         :abs => :abs_fast,
         :abs2 => :abs2_fast,
         :cmp => :cmp_fast,
         :conj => :conj_fast,
         :inv => :inv_fast,
         :rem => :rem_fast,
         :sign => :sign_fast,
         :isfinite => :isfinite_fast,
         :isinf => :isinf_fast,
         :isnan => :isnan_fast,
         :issubnormal => :issubnormal_fast,
         # math functions
         :^ => :pow_fast,
         :acos => :acos_fast,
         :acosh => :acosh_fast,
         :angle => :angle_fast,
         :asin => :asin_fast,
         :asinh => :asinh_fast,
         :atan => :atan_fast,
         :atanh => :atanh_fast,
         :cbrt => :cbrt_fast,
         :cis => :cis_fast,
         :cos => :cos_fast,
         :cosh => :cosh_fast,
         :exp10 => :exp10_fast,
         :exp2 => :exp2_fast,
         :exp => :exp_fast,
         :expm1 => :expm1_fast,
         :hypot => :hypot_fast,
         :log10 => :log10_fast,
         :log1p => :log1p_fast,
         :log2 => :log2_fast,
         :log => :log_fast,
         :max => :max_fast,
         :min => :min_fast,
         :minmax => :minmax_fast,
         :sin => :sin_fast,
         :sincos => :sincos_fast,
         :sinh => :sinh_fast,
         :sqrt => :sqrt_fast,
         :tan => :tan_fast,
         :tanh => :tanh_fast,
         # reductions
         :maximum => :maximum_fast,
         :minimum => :minimum_fast,
         :maximum! => :maximum!_fast,
         :minimum! => :minimum!_fast)

```
-/
def fastOpMappings : List (String × String) := [
  ("+", "add_fast"), ("-", "sub_fast"), ("*", "mul_fast"), ("/", "div_fast"),
  ("==", "eq_fast"), ("!=", "ne_fast"), ("<", "lt_fast"), ("<=", "le_fast"),
  (">", "gt_fast"), (">=", "ge_fast"), ("abs", "abs_fast"), ("abs2", "abs2_fast"),
  ("cmp", "cmp_fast"), ("conj", "conj_fast"), ("inv", "inv_fast"), ("rem", "rem_fast"),
  ("sign", "sign_fast"), ("isfinite", "isfinite_fast"), ("isinf", "isinf_fast"),
  ("isnan", "isnan_fast"), ("issubnormal", "issubnormal_fast"), ("^", "pow_fast"),
  ("acos", "acos_fast"), ("acosh", "acosh_fast"), ("angle", "angle_fast"),
  ("asin", "asin_fast"), ("asinh", "asinh_fast"), ("atan", "atan_fast"),
  ("atanh", "atanh_fast"), ("cbrt", "cbrt_fast"), ("cis", "cis_fast"),
  ("cos", "cos_fast"), ("cosh", "cosh_fast"), ("exp10", "exp10_fast"),
  ("exp2", "exp2_fast"), ("exp", "exp_fast"), ("expm1", "expm1_fast"),
  ("hypot", "hypot_fast"), ("log10", "log10_fast"), ("log1p", "log1p_fast"),
  ("log2", "log2_fast"), ("log", "log_fast"), ("max", "max_fast"),
  ("min", "min_fast"), ("minmax", "minmax_fast"), ("sin", "sin_fast"),
  ("sincos", "sincos_fast"), ("sinh", "sinh_fast"), ("sqrt", "sqrt_fast"),
  ("tan", "tan_fast"), ("tanh", "tanh_fast"), ("maximum", "maximum_fast"),
  ("minimum", "minimum_fast"), ("maximum!", "maximum!_fast"), ("minimum!", "minimum!_fast")]

/--
Julia source: base/fastmath.jl:95-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const rewrite_op =
    Dict(:+= => :+,
         :-= => :-,
         :*= => :*,
         :/= => :/,
         :^= => :^)

```
-/
def rewriteOpMappings : List (String × String) :=
  [("+=", "+"), ("-=", "-"), ("*=", "*"), ("/=", "/"), ("^=", "^")]

private def lookupName : String → List (String × String) → Option String
  | _, [] => none
  | key, (name, value) :: rest => if key == name then some value else lookupName key rest

private def fastOpName (name : String) : Option String :=
  lookupName name fastOpMappings

private def makeFastmathName (name : String) : String :=
  match fastOpName name with
  | none => name
  | some fastName => "Base.FastMath." ++ fastName

private def rewriteOpName (name : String) : Option String :=
  lookupName name rewriteOpMappings

abbrev FastMathResult (α : Type) := Jl α

private def makeFastmathSymbolHelper (name : String) : Ast :=
  .atom (makeFastmathName name)

private def makeFastmathOtherHelper {A : Type} (value : A) : A := value

private structure FastLiteralPower (args : List Ast) where
  base : Ast
  exponent : Int
  baseMem : base ∈ args

private def fastLiteralPower : (args : List Ast) → Option (FastLiteralPower args)
  | .atom "^" :: base :: .int exponent :: _ => some ⟨base, exponent, by simp⟩
  | _ => none

private structure FastRewriteArguments (args : List Ast) where
  lhs : Ast
  rhs : Ast
  lhsMem : lhs ∈ args
  rhsMem : rhs ∈ args

private def fastRewriteArguments : (args : List Ast) → Except JlError (FastRewriteArguments args)
  | [] => .error .boundsError
  | lhs :: [] => .error .boundsError
  | lhs :: rhs :: _ => .ok ⟨lhs, rhs, by simp, by simp⟩

private theorem fastMathExprChildSize {head : String} {args : List Ast} {child : Ast}
    (member : child ∈ args) : sizeOf child < sizeOf (Ast.expr head args) := by
  have h := List.sizeOf_lt_of_mem member
  simp_wf
  omega

/--
Julia source: base/fastmath.jl:102-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_fastmath(expr::Expr)
    if expr.head === :quote
        return expr
    elseif expr.head === :call && expr.args[1] === :^
        ea = expr.args
        if length(ea) >= 3 && isa(ea[3], Int)
            # mimic Julia's literal_pow lowering of literal integer powers
            return Expr(:call, :(Base.FastMath.pow_fast), make_fastmath(ea[2]), Val(ea[3]))
        end
    end
    op = get(rewrite_op, expr.head, :nothing)
    if op !== :nothing
        var = expr.args[1]
        rhs = expr.args[2]
        if isa(var, Symbol)
            # simple assignment
            expr = :($var = $op($var, $rhs))
        end
        # It is hard to optimize array[i += 1] += 1
        # and array[end] += 1 without bugs. (#47241)
        # We settle for not optimizing the op= call.
    end
    Base.exprarray(make_fastmath(expr.head), Base.mapany(make_fastmath, expr.args))
end
```
-/
def makeFastmath : Ast → FastMathResult Ast
  | .atom name => pure (makeFastmathSymbolHelper name)
  | .expr "quote" args => pure (Ast.expr "quote" args)
  | .expr "call" args =>
      if args.isEmpty then .error .boundsError
      else
        match fastLiteralPower args with
        | some power => do
            let base ← makeFastmath power.base
            pure (.expr "call" [
              .atom "Base.FastMath.pow_fast", base,
              .expr "call" [.atom "Val", .int power.exponent]])
        | none => do
            let mappedArgs ← args.mapM makeFastmath
            pure (.expr "call" mappedArgs)
  | .expr head args =>
      match rewriteOpName head with
      | none => do
          let mappedArgs ← args.mapM makeFastmath
          pure (.expr (makeFastmathName head) mappedArgs)
      | some op =>
          match fastRewriteArguments args with
          | .error error => .error error
          | .ok assignment =>
              match assignment.lhs with
              | .atom variableName => do
                  let mappedRhs ← makeFastmath assignment.rhs
                  let mappedVariable := makeFastmathSymbolHelper variableName
                  let mappedOp := makeFastmathSymbolHelper op
                  pure (.expr "=" [mappedVariable,
                    .expr "call" [mappedOp, mappedVariable, mappedRhs]])
              | _ => do
                  let mappedArgs ← args.mapM makeFastmath
                  pure (.expr (makeFastmathName head) mappedArgs)
  | other => pure (makeFastmathOtherHelper other)
termination_by node => sizeOf node
decreasing_by
  all_goals
    first
    | exact fastMathExprChildSize (head := "call") (args := args) (child := power.base) power.baseMem
    | exact fastMathExprChildSize (head := head) (args := args) (child := assignment.rhs) assignment.rhsMem
    | exact fastMathExprChildSize (head := _) (args := _) (child := _) ‹_ ∈ _›

/--
Julia source: base/fastmath.jl:126-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_fastmath(symb::Symbol)
    fast_symb = get(fast_op, symb, :nothing)
    if fast_symb === :nothing
        return symb
    end
    :(Base.FastMath.$fast_symb)
end
```
-/
def makeFastmathSymbol (name : String) : Ast :=
  makeFastmathSymbolHelper name

/--
Julia source: base/fastmath.jl:133-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
make_fastmath(expr) = expr

```
-/
def makeFastmathOther {A : Type} (value : A) : A := makeFastmathOtherHelper value

/--
Julia source: base/fastmath.jl:135-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @fastmath expr

Execute a transformed version of the expression, which calls functions that
may violate strict IEEE semantics. This allows the fastest possible operation,
but results are undefined -- be careful when doing this, as it may change numerical
results.

This sets the [LLVM Fast-Math flags](https://llvm.org/docs/LangRef.html#fast-math-flags),
and corresponds to the `-ffast-math` option in clang. See [the notes on performance
annotations](@ref man-performance-annotations) for more details.

# Examples
```jldoctest
julia> @fastmath 1+2
3

julia> @fastmath(sin(3))
0.1411200080598672
```
"""
macro fastmath(expr)
    make_fastmath(esc(expr))
end


````
-/
def fastmathMacro (escape : Ast → FastMathResult Ast) (expr : Ast) : FastMathResult Ast := do
  makeFastmath (← escape expr)

/--
Julia source: base/fastmath.jl:161-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Basic arithmetic

const FloatTypes = Union{Float16,Float32,Float64}
```
-/
def floatTypes : List FTy := [.f16, .f32, .f64]

inductive FastFloatUnary where
  | abs | abs2 | inv | sign
  | acos | acosh | asin | asinh | atan | atanh | cbrt
  | cos | cosh | exp10 | exp2 | exp | expm1
  | log10 | log1p | log2 | log | sin | sinh | sqrt | tan | tanh
  deriving Repr, DecidableEq

inductive FastFloatBinary where
  | add | sub | mul | div | max | min | hypot | atan2 | remInternal | copysign
  deriving Repr, DecidableEq

inductive FastFloatPredicate where
  | eq | ne | lt | le
  deriving Repr, DecidableEq

structure FastFloatOps (T : FTy) where
  negFloatFast : FV T → FV T
  unary : FastFloatUnary → FV T → FV T
  binary : FastFloatBinary → FV T → FV T → FV T
  predicate : FastFloatPredicate → FV T → FV T → Bool
  minmax : FV T → FV T → FV T × FV T
  sincos : FV T → FV T × FV T
  powInt32 : FV T → JInt .i32 → FV T
  toInt32 : {I : Type} → I → JInt .i32
  int32EqualsInteger : {I : Type} → JInt .i32 → I → Bool
  powInteger : {I : Type} → FV T → I → FV T
  zero : FV T
  one : FV T
  two : FV T
  ten : FV T
  pi : FV T

structure ComplexFloatType where
  scalar : FTy
  supported : scalar = .f32 ∨ scalar = .f64

def complexFloat32 : ComplexFloatType := ⟨.f32, Or.inl rfl⟩
def complexFloat64 : ComplexFloatType := ⟨.f64, Or.inr rfl⟩
/--
Julia source: base/fastmath.jl:192-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# complex numbers

ComplexTypes = Union{ComplexF32, ComplexF64}

@fastmath begin
```
-/
def complexTypes : List ComplexFloatType := [complexFloat32, complexFloat64]

structure FastComplex (T : ComplexFloatType) where
  re : FV T.scalar
  im : FV T.scalar

private def fastComplex {T : ComplexFloatType} (re im : FV T.scalar) : FastComplex T :=
  ⟨re, im⟩

private def fastComplexZero {T : ComplexFloatType} (ops : FastFloatOps T.scalar) : FastComplex T :=
  fastComplex ops.zero ops.zero

private def fastComplexOne {T : ComplexFloatType} (ops : FastFloatOps T.scalar) : FastComplex T :=
  fastComplex ops.one ops.zero

private def fastImaginaryUnit {T : ComplexFloatType} (ops : FastFloatOps T.scalar) : FastComplex T :=
  fastComplex ops.zero ops.one

private def fastRealComplex {T : ComplexFloatType} (ops : FastFloatOps T.scalar)
    (x : FV T.scalar) : FastComplex T := fastComplex x ops.zero

private def fastComplexNeg {T : ComplexFloatType} (ops : FastFloatOps T.scalar)
    (x : FastComplex T) : FastComplex T :=
  fastComplex (ops.negFloatFast x.re) (ops.negFloatFast x.im)

private def fastComplexDivReal {T : ComplexFloatType} (ops : FastFloatOps T.scalar)
    (x : FastComplex T) (y : FV T.scalar) : FastComplex T :=
  fastComplex (ops.binary .div x.re y) (ops.binary .div x.im y)

private def fastComplexMulReal {T : ComplexFloatType} (ops : FastFloatOps T.scalar)
    (x : FastComplex T) (y : FV T.scalar) : FastComplex T :=
  fastComplex (ops.binary .mul x.re y) (ops.binary .mul x.im y)

inductive FastComplexUnary where
  | acos | acosh | asin | asinh | atan | atanh | cos | cosh | exp | log | sin | sinh | sqrt | tan | tanh
  deriving Repr, DecidableEq

structure FastReductionOps (Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type) where
  maxOp : Op
  minOp : Op
  maxFast : Op
  minFast : Op
  identity : Mapper
  reduce : Op → Collection → Keywords → Jl ScalarOutput
  mapreduce : Mapper → Op → Collection → Keywords → Jl ScalarOutput
  reducedimInit : Mapper → Op → Collection → Region → Jl ArrayOutput
  initArray : ArrayOutput → Mapper → Op → Bool → Collection → Jl ArrayOutput
  mapreducedim : Mapper → Op → ArrayOutput → Collection → Jl ArrayOutput
  maxBangDispatch : Mapper → ArrayOutput → Collection → Keywords → Jl ArrayOutput
  minBangDispatch : Mapper → ArrayOutput → Collection → Keywords → Jl ArrayOutput

/--
Julia source: base/fastmath.jl:164-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

sub_fast(x::FloatTypes) = neg_float_fast(x)
```
-/
def fastNegFloat {T : FTy} (ops : FastFloatOps T) (x : FV T) : FV T :=
  ops.negFloatFast x

/--
Julia source: base/fastmath.jl:166-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

add_fast(x::T, y::T) where {T<:FloatTypes} = add_float_fast(x, y)
```
-/
def fastAddFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  ops.binary .add x y

/--
Julia source: base/fastmath.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sub_fast(x::T, y::T) where {T<:FloatTypes} = sub_float_fast(x, y)
```
-/
def fastSubFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  ops.binary .sub x y

/--
Julia source: base/fastmath.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mul_fast(x::T, y::T) where {T<:FloatTypes} = mul_float_fast(x, y)
```
-/
def fastMulFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  ops.binary .mul x y

/--
Julia source: base/fastmath.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
div_fast(x::T, y::T) where {T<:FloatTypes} = div_float_fast(x, y)
```
-/
def fastDivFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  ops.binary .div x y

/--
Julia source: base/fastmath.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
max_fast(x::T, y::T) where {T<:FloatTypes} = max_float_fast(x, y)
```
-/
def fastMaxFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  ops.binary .max x y

/--
Julia source: base/fastmath.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min_fast(x::T, y::T) where {T<:FloatTypes} = min_float_fast(x, y)
```
-/
def fastMinFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  ops.binary .min x y

/--
Julia source: base/fastmath.jl:173-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minmax_fast(x::T, y::T) where {T<:FloatTypes} = (min_fast(x, y), max_fast(x, y))

```
-/
def fastMinmaxFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T × FV T :=
  (fastMinFloat ops x y, fastMaxFloat ops x y)

/--
Julia source: base/fastmath.jl:175-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@fastmath begin
    cmp_fast(x::T, y::T) where {T<:FloatTypes} = ifelse(x==y, 0, ifelse(x<y, -1, +1))
```
-/
def fastCmpFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : JInt .i64 :=
  if ops.predicate .eq x y then JInt.lit .i64 0
  else if ops.predicate .lt x y then JInt.lit .i64 (-1)
  else JInt.lit .i64 1

/--
Julia source: base/fastmath.jl:177-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    log_fast(b::T, x::T) where {T<:FloatTypes} = log_fast(x)/log_fast(b)
end

```
-/
def fastLogBaseFloat {T : FTy} (ops : FastFloatOps T) (base x : FV T) : FV T :=
  ops.binary .div (ops.unary .log x) (ops.unary .log base)

/--
Julia source: base/fastmath.jl:180-180 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eq_fast(x::T, y::T) where {T<:FloatTypes} = eq_float_fast(x, y)
```
-/
def fastEqFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : Bool :=
  ops.predicate .eq x y

/--
Julia source: base/fastmath.jl:181-181 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ne_fast(x::T, y::T) where {T<:FloatTypes} = ne_float_fast(x, y)
```
-/
def fastNeFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : Bool :=
  ops.predicate .ne x y

/--
Julia source: base/fastmath.jl:182-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
lt_fast(x::T, y::T) where {T<:FloatTypes} = lt_float_fast(x, y)
```
-/
def fastLtFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : Bool :=
  ops.predicate .lt x y

/--
Julia source: base/fastmath.jl:183-183 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
le_fast(x::T, y::T) where {T<:FloatTypes} = le_float_fast(x, y)
```
-/
def fastLeFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : Bool :=
  ops.predicate .le x y

/--
Julia source: base/fastmath.jl:184-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gt_fast(x, y) = lt_fast(y, x)
```
-/
def fastGt {A : Type} (lt : A → A → Bool) (x y : A) : Bool := lt y x

/--
Julia source: base/fastmath.jl:185-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
ge_fast(x, y) = le_fast(y, x)

```
-/
def fastGe {A : Type} (le : A → A → Bool) (x y : A) : Bool := le y x

/--
Julia source: base/fastmath.jl:187-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isinf_fast(x) = false
```
-/
def isInfFast {_A : Type} (_x : _A) : Bool := false
/--
Julia source: base/fastmath.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isfinite_fast(x) = true
```
-/
def isFiniteFast {_A : Type} (_x : _A) : Bool := true
/--
Julia source: base/fastmath.jl:189-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isnan_fast(x) = false
```
-/
def isNanFast {_A : Type} (_x : _A) : Bool := false
/--
Julia source: base/fastmath.jl:190-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issubnormal_fast(x) = false

```
-/
def isSubnormalFast {_A : Type} (_x : _A) : Bool := false

/--
Julia source: base/fastmath.jl:300-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function pow_fast(x::T, y::Integer) where T <: Base.IEEEFloat
    z = y % Int32
    z == y ? pow_fast(x, z) : x^y
end
```
-/
def powFastInteger {T : FTy} {I : Type} (ops : FastFloatOps T) (x : FV T) (y : I) : FV T :=
  let z := ops.toInt32 y
  if ops.int32EqualsInteger z y then ops.powInt32 x z else ops.powInteger x y

/--
Julia source: base/fastmath.jl:304-304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pow_fast(x::Float16, y::Int32) = ccall("llvm.powi", llvmcall, Float16, (Float16, Int32), x, y)
```
-/
def powFastFloat16 (ops : FastFloatOps .f16) (x : FV .f16) (y : JInt .i32) : FV .f16 :=
  ops.powInt32 x y

/--
Julia source: base/fastmath.jl:305-305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pow_fast(x::Float32, y::Int32) = ccall("llvm.powi", llvmcall, Float32, (Float32, Int32), x, y)
```
-/
def powFastFloat32 (ops : FastFloatOps .f32) (x : FV .f32) (y : JInt .i32) : FV .f32 :=
  ops.powInt32 x y

/--
Julia source: base/fastmath.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pow_fast(x::Float64, y::Int32) = ccall("llvm.powi", llvmcall, Float64, (Float64, Int32), x, y)
```
-/
def powFastFloat64 (ops : FastFloatOps .f64) (x : FV .f64) (y : JInt .i32) : FV .f64 :=
  ops.powInt32 x y

/--
Julia source: base/fastmath.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
pow_fast(x::FloatTypes, ::Val{p}) where {p} = pow_fast(x, p) # inlines already via llvm.powi
```
-/
def powFastVal {T : FTy} {I : Type} (ops : FastFloatOps T) (x : FV T) (power : I) : FV T :=
  powFastInteger ops x power

/--
Julia source: base/fastmath.jl:308-309 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline pow_fast(x, v::Val) = Base.literal_pow(^, x, v)

```
-/
def powFastLiteral {X V : Type} (literalPow : X → V → X) (x : X) (value : V) : X :=
  literalPow x value

/--
Julia source: base/fastmath.jl:310-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sqrt_fast(x::FloatTypes) = sqrt_llvm_fast(x)
```
-/
def sqrtFastFloat {T : FTy} (x : FV T) : FV T :=
  JuliaLean.C.jlSqrtLlvmFast x

/--
Julia source: base/fastmath.jl:293-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Math functions
exp2_fast(x::Union{Float32,Float64})  = Base.Math.exp2_fast(x)
```
-/
def exp2Fast {T : FTy} (_notHalf : T ≠ .f16) (ops : FastFloatOps T) (x : FV T) : FV T :=
  ops.unary .exp2 x

/--
Julia source: base/fastmath.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exp_fast(x::Union{Float32,Float64})   = Base.Math.exp_fast(x)
```
-/
def expFast {T : FTy} (_notHalf : T ≠ .f16) (ops : FastFloatOps T) (x : FV T) : FV T :=
  ops.unary .exp x

/--
Julia source: base/fastmath.jl:296-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
exp10_fast(x::Union{Float32,Float64}) = Base.Math.exp10_fast(x)

# builtins

```
-/
def exp10Fast {T : FTy} (_notHalf : T ≠ .f16) (ops : FastFloatOps T) (x : FV T) : FV T :=
  ops.unary .exp10 x

/--
Julia source: base/fastmath.jl:311-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos_fast(v::FloatTypes) = sincos(v)

```
-/
def sincosFastFloat {T : FTy} (ops : FastFloatOps T) (x : FV T) : FV T × FV T :=
  ops.sincos x

/--
Julia source: base/fastmath.jl:313-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function sincos_fast(v::Float16)
    s, c = sincos_fast(Float32(v))
    return Float16(s), Float16(c)
end
```
-/
def sincosFastFloat16 (toFloat32 : FV .f16 → FV .f32) (toFloat16 : FV .f32 → FV .f16)
    (ops : FastFloatOps .f32) (x : FV .f16) : FV .f16 × FV .f16 :=
  let (s, c) := ops.sincos (toFloat32 x)
  (toFloat16 s, toFloat16 c)

/--
Julia source: base/fastmath.jl:317-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos_fast(v::AbstractFloat) = (sin_fast(v), cos_fast(v))
```
-/
def sincosFastAbstract {A : Type} (sinFast cosFast : A → A) (x : A) : A × A :=
  (sinFast x, cosFast x)

/--
Julia source: base/fastmath.jl:318-318 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos_fast(v::Real) = sincos_fast(float(v)::AbstractFloat)
```
-/
def sincosFastReal {R A : Type} (toFloat : R → A) (sincosFast : A → A × A)
    (x : R) : A × A := sincosFast (toFloat x)

/--
Julia source: base/fastmath.jl:319-321 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sincos_fast(v) = (sin_fast(v), cos_fast(v))


```
-/
def sincosFastAny {A : Type} (sinFast cosFast : A → A) (x : A) : A × A :=
  (sinFast x, cosFast x)

/--
Julia source: base/fastmath.jl:322-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rem_fast(x::T, y::T) where {T<:FloatTypes}
    return @fastmath copysign(Base.rem_internal(abs(x), abs(y)), x)
end
```
-/
def remFastFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  let rx := ops.unary .abs x
  let ry := ops.unary .abs y
  let remainder := ops.binary .remInternal rx ry
  ops.binary .copysign remainder x

/--
Julia source: base/fastmath.jl:325-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

@fastmath begin
    hypot_fast(x::T, y::T) where {T<:FloatTypes} = sqrt(x*x + y*y)
```
-/
def hypotFastFloat {T : FTy} (ops : FastFloatOps T) (x y : FV T) : FV T :=
  let xx := ops.binary .mul x x
  let yy := ops.binary .mul y y
  sqrtFastFloat (ops.binary .add xx yy)

/--
Julia source: base/fastmath.jl:203-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    add_fast(x::T, y::T) where {T<:ComplexTypes} =
        T(real(x)+real(y), imag(x)+imag(y))
```
-/
def complexAddFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : FastComplex C :=
  fastComplex (ops.binary .add x.re y.re) (ops.binary .add x.im y.im)

/--
Julia source: base/fastmath.jl:205-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    add_fast(x::Complex{T}, b::T) where {T<:FloatTypes} =
        Complex{T}(real(x)+b, imag(x))
```
-/
def complexAddRealFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) (y : FV C.scalar) : FastComplex C :=
  fastComplex (ops.binary .add x.re y) x.im

/--
Julia source: base/fastmath.jl:207-208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    add_fast(a::T, y::Complex{T}) where {T<:FloatTypes} =
        Complex{T}(a+real(y), imag(y))
```
-/
def realAddComplexFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) (y : FastComplex C) : FastComplex C :=
  fastComplex (ops.binary .add x y.re) y.im

/--
Julia source: base/fastmath.jl:209-211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    sub_fast(x::T, y::T) where {T<:ComplexTypes} =
        T(real(x)-real(y), imag(x)-imag(y))
```
-/
def complexSubFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : FastComplex C :=
  fastComplex (ops.binary .sub x.re y.re) (ops.binary .sub x.im y.im)

/--
Julia source: base/fastmath.jl:212-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    sub_fast(x::Complex{T}, b::T) where {T<:FloatTypes} =
        Complex{T}(real(x)-b, imag(x))
```
-/
def complexSubRealFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) (y : FV C.scalar) : FastComplex C :=
  fastComplex (ops.binary .sub x.re y) x.im

/--
Julia source: base/fastmath.jl:214-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    sub_fast(a::T, y::Complex{T}) where {T<:FloatTypes} =
        Complex{T}(a-real(y), -imag(y))
```
-/
def realSubComplexFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) (y : FastComplex C) : FastComplex C :=
  fastComplex (ops.binary .sub x y.re) (ops.negFloatFast y.im)

/--
Julia source: base/fastmath.jl:216-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    mul_fast(x::T, y::T) where {T<:ComplexTypes} =
        T(real(x)*real(y) - imag(x)*imag(y),
          real(x)*imag(y) + imag(x)*real(y))
```
-/
def complexMulFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : FastComplex C :=
  let rr := ops.binary .mul x.re y.re
  let ii := ops.binary .mul x.im y.im
  let ri := ops.binary .mul x.re y.im
  let ir := ops.binary .mul x.im y.re
  fastComplex (ops.binary .sub rr ii) (ops.binary .add ri ir)

/--
Julia source: base/fastmath.jl:220-221 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    mul_fast(x::Complex{T}, b::T) where {T<:FloatTypes} =
        Complex{T}(real(x)*b, imag(x)*b)
```
-/
def complexMulRealFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) (y : FV C.scalar) : FastComplex C :=
  fastComplex (ops.binary .mul x.re y) (ops.binary .mul x.im y)

/--
Julia source: base/fastmath.jl:222-223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    mul_fast(a::T, y::Complex{T}) where {T<:FloatTypes} =
        Complex{T}(a*real(y), a*imag(y))
```
-/
def realMulComplexFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) (y : FastComplex C) : FastComplex C :=
  fastComplex (ops.binary .mul x y.re) (ops.binary .mul x y.im)

/--
Julia source: base/fastmath.jl:228-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    div_fast(x::Complex{T}, b::T) where {T<:FloatTypes} =
        Complex{T}(real(x)/b, imag(x)/b)
```
-/
def complexDivRealFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) (y : FV C.scalar) : FastComplex C :=
  fastComplex (ops.binary .div x.re y) (ops.binary .div x.im y)

/--
Julia source: base/fastmath.jl:230-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    div_fast(a::T, y::Complex{T}) where {T<:FloatTypes} =
        Complex{T}(a*real(y), -a*imag(y)) / abs2(y)
```
-/
def realDivComplexFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) (y : FastComplex C) : FastComplex C :=
  let magnitude := ops.binary .add (ops.binary .mul y.re y.re) (ops.binary .mul y.im y.im)
  let re := ops.binary .div (ops.binary .mul x y.re) magnitude
  let im := ops.binary .div (ops.negFloatFast (ops.binary .mul x y.im)) magnitude
  fastComplex re im

/--
Julia source: base/fastmath.jl:198-198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    abs2_fast(x::ComplexTypes) = real(x)*real(x) + imag(x)*imag(x)
```
-/
def complexAbs2Fast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FV C.scalar :=
  let rr := ops.binary .mul x.re x.re
  let ii := ops.binary .mul x.im x.im
  ops.binary .add rr ii

/--
Julia source: base/fastmath.jl:197-197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    abs_fast(x::ComplexTypes) = hypot(real(x), imag(x))
```
-/
def complexAbsFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FV C.scalar :=
  hypotFastFloat ops x.re x.im

/--
Julia source: base/fastmath.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    angle_fast(x::ComplexTypes) = atan(imag(x), real(x))
```
-/
def complexAngleFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FV C.scalar :=
  ops.binary .atan2 x.im x.re

private def complexIsZeroFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : Bool :=
  ops.predicate .eq x.re ops.zero && ops.predicate .eq x.im ops.zero

/--
Julia source: base/fastmath.jl:232-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    eq_fast(x::T, y::T) where {T<:ComplexTypes} =
        (real(x)==real(y)) & (imag(x)==imag(y))
```
-/
def complexEqualFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : Bool :=
  ops.predicate .eq x.re y.re && ops.predicate .eq x.im y.im

/--
Julia source: base/fastmath.jl:235-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eq_fast(x::Complex{T}, b::T) where {T<:FloatTypes} =
        (real(x)==b) & (imag(x)==T(0))
```
-/
def complexEqualRealFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) (y : FV C.scalar) : Bool :=
  ops.predicate .eq x.re y && ops.predicate .eq x.im ops.zero

/--
Julia source: base/fastmath.jl:237-238 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    eq_fast(a::T, y::Complex{T}) where {T<:FloatTypes} =
        (a==real(y)) & (T(0)==imag(y))
```
-/
def realEqualComplexFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) (y : FastComplex C) : Bool :=
  ops.predicate .eq x y.re && ops.predicate .eq ops.zero y.im

/--
Julia source: base/fastmath.jl:239-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    ne_fast(x::T, y::T) where {T<:ComplexTypes} = !(x==y)

end
```
-/
def complexNeFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : Bool := !complexEqualFast ops x y

/--
Julia source: base/fastmath.jl:199-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    conj_fast(x::T) where {T<:ComplexTypes} = T(real(x), -imag(x))
```
-/
def complexConjFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  fastComplex x.re (ops.negFloatFast x.im)

/--
Julia source: base/fastmath.jl:200-200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    inv_fast(x::ComplexTypes) = conj(x) / abs2(x)
```
-/
def complexInvFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  complexDivRealFast ops (complexConjFast ops x) (complexAbs2Fast ops x)

/--
Julia source: base/fastmath.jl:201-202 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    sign_fast(x::ComplexTypes) = x == 0 ? float(zero(x)) : x/abs(x)

```
-/
def complexSignFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  if complexIsZeroFast ops x then fastComplexZero ops else complexDivRealFast ops x (complexAbsFast ops x)

/--
Julia source: base/fastmath.jl:224-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    @inline div_fast(x::T, y::T) where {T<:ComplexTypes} =
        T(real(x)*real(y) + imag(x)*imag(y),
          imag(x)*real(y) - real(x)*imag(y)) / abs2(y)
```
-/
def complexDivFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : FastComplex C :=
  let re1 := ops.binary .mul x.re y.re
  let im1 := ops.binary .mul x.im y.im
  let im2 := ops.binary .mul x.im y.re
  let re2 := ops.binary .mul x.re y.im
  let numerator := fastComplex (ops.binary .add re1 im1) (ops.binary .sub im2 re2)
  complexDivRealFast ops numerator (complexAbs2Fast ops y)

/--
Julia source: base/fastmath.jl:328-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    # complex numbers

    function cis_fast(x::T) where {T<:FloatTypes}
        s, c = sincos_fast(x)
        Complex{T}(c, s)
    end
```
-/
def complexCisFloatFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) : FastComplex C :=
  let (s, c) := ops.sincos x
  fastComplex c s

/--
Julia source: base/fastmath.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    log_fast(x::T) where {T<:ComplexTypes} = T(log(abs2(x))/2, angle(x))
```
-/
def complexLogFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  fastComplex (ops.binary .div (ops.unary .log (complexAbs2Fast ops x)) ops.two)
    (complexAngleFast ops x)

/--
Julia source: base/fastmath.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    exp_fast(x::ComplexTypes) = exp(real(x)) * cis(imag(x))
```
-/
def complexExpFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  realMulComplexFast ops (ops.unary .exp x.re) (complexCisFloatFast ops x.im)

/--
Julia source: base/fastmath.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    sqrt_fast(x::ComplexTypes) = sqrt(abs(x)) * cis(angle(x)/2)
```
-/
def complexSqrtFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let halfAngle := ops.binary .div (complexAngleFast ops x) ops.two
  realMulComplexFast ops (sqrtFastFloat (complexAbsFast ops x)) (complexCisFloatFast ops halfAngle)

/--
Julia source: base/fastmath.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    sinh_fast(x::T) where {T<:ComplexTypes} = convert(T,1)/2*(exp(x) - exp(-x))
```
-/
def complexSinhFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let positive := complexExpFast ops x
  let negative := complexExpFast ops (fastComplexNeg ops x)
  let half := fastComplexDivReal ops (fastComplexOne ops) ops.two
  complexMulFast ops half (complexSubFast ops positive negative)

/--
Julia source: base/fastmath.jl:350-350 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    cosh_fast(x::T) where {T<:ComplexTypes} = convert(T,1)/2*(exp(x) + exp(-x))
```
-/
def complexCoshFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let positive := complexExpFast ops x
  let negative := complexExpFast ops (fastComplexNeg ops x)
  let half := fastComplexDivReal ops (fastComplexOne ops) ops.two
  complexMulFast ops half (complexAddFast ops positive negative)

/--
Julia source: base/fastmath.jl:345-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    asinh_fast(x::ComplexTypes) = log(x + sqrt(1+x*x))
```
-/
def complexAsinhFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let square := complexMulFast ops x x
  let inside := complexAddFast ops (fastComplexOne ops) square
  complexLogFast ops (complexAddFast ops x (complexSqrtFast ops inside))

/--
Julia source: base/fastmath.jl:347-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    atanh_fast(x::T) where {T<:ComplexTypes} = convert(T,1)/2*(log(1+x) - log(1-x))
```
-/
def complexAtanhFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let onePlus := complexAddFast ops (fastComplexOne ops) x
  let oneMinus := complexSubFast ops (fastComplexOne ops) x
  let logs := complexSubFast ops (complexLogFast ops onePlus) (complexLogFast ops oneMinus)
  let half := fastComplexDivReal ops (fastComplexOne ops) ops.two
  complexMulFast ops half logs

/--
Julia source: base/fastmath.jl:346-346 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    atan_fast(x::ComplexTypes) = -im*atanh(im*x)
```
-/
def complexAtanFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let product := complexMulFast ops (fastImaginaryUnit ops) x
  fastComplexNeg ops (complexMulFast ops (fastImaginaryUnit ops) (complexAtanhFast ops product))

/--
Julia source: base/fastmath.jl:335-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

    # See <https://en.cppreference.com/w/cpp/numeric/complex>
    pow_fast(x::T, y::T) where {T<:ComplexTypes} = exp(y*log(x))
```
-/
def powFastComplexComplex {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x y : FastComplex C) : FastComplex C :=
  complexExpFast ops (complexMulFast ops y (complexLogFast ops x))

/--
Julia source: base/fastmath.jl:338-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    pow_fast(x::T, y::Complex{T}) where {T<:FloatTypes} = exp(y*log(x))
```
-/
def powFastFloatComplex {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FV C.scalar) (y : FastComplex C) : FastComplex C :=
  complexExpFast ops (complexMulRealFast ops y (ops.unary .log x))

/--
Julia source: base/fastmath.jl:339-339 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    pow_fast(x::Complex{T}, y::T) where {T<:FloatTypes} = exp(y*log(x))
```
-/
def powFastComplexFloat {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) (y : FV C.scalar) : FastComplex C :=
  complexExpFast ops (realMulComplexFast ops y (complexLogFast ops x))

/--
Julia source: base/fastmath.jl:340-341 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    acos_fast(x::T) where {T<:ComplexTypes} =
        convert(T,π)/2 + im*log(im*x + sqrt(1-x*x))
```
-/
def complexAcosFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let imaginary := fastImaginaryUnit ops
  let xx := complexMulFast ops x x
  let root := complexSqrtFast ops (complexSubFast ops (fastComplexOne ops) xx)
  let inside := complexAddFast ops (complexMulFast ops imaginary x) root
  let product := complexMulFast ops imaginary (complexLogFast ops inside)
  let halfPi := complexDivRealFast ops (fastRealComplex ops ops.pi) ops.two
  complexAddFast ops halfPi product

/--
Julia source: base/fastmath.jl:342-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    acosh_fast(x::ComplexTypes) = log(x + sqrt(x+1) * sqrt(x-1))
```
-/
def complexAcoshFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let plusOne := complexAddFast ops x (fastComplexOne ops)
  let minusOne := complexSubFast ops x (fastComplexOne ops)
  let product := complexMulFast ops (complexSqrtFast ops plusOne) (complexSqrtFast ops minusOne)
  complexLogFast ops (complexAddFast ops x product)

/--
Julia source: base/fastmath.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    asin_fast(x::ComplexTypes) = -im*asinh(im*x)
```
-/
def complexAsinFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let product := complexMulFast ops (fastImaginaryUnit ops) x
  fastComplexNeg ops (complexMulFast ops (fastImaginaryUnit ops) (complexAsinhFast ops product))

/--
Julia source: base/fastmath.jl:349-349 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    cos_fast(x::ComplexTypes) = cosh(im*x)
```
-/
def complexCosFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  complexCoshFast ops (complexMulFast ops (fastImaginaryUnit ops) x)

/--
Julia source: base/fastmath.jl:366-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    tanh_fast(x::ComplexTypes) = (a=exp(x); b=exp(-x); (a-b)/(a+b))
end
```
-/
def complexTanhFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let positive := complexExpFast ops x
  let negative := complexExpFast ops (fastComplexNeg ops x)
  complexDivFast ops (complexSubFast ops positive negative) (complexAddFast ops positive negative)

/--
Julia source: base/fastmath.jl:365-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    tan_fast(x::ComplexTypes) = -im*tanh(im*x)
```
-/
def complexTanFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  fastComplexNeg ops (complexMulFast ops (fastImaginaryUnit ops)
    (complexTanhFast ops (complexMulFast ops (fastImaginaryUnit ops) x)))

/--
Julia source: base/fastmath.jl:348-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    cis_fast(x::ComplexTypes) = exp(-imag(x)) * cis(real(x))
```
-/
def complexCisComplexFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let scale := ops.unary .exp (ops.negFloatFast x.im)
  realMulComplexFast ops scale (complexCisFloatFast ops x.re)

/--
Julia source: base/fastmath.jl:351-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    exp10_fast(x::T) where {T<:ComplexTypes} =
        exp10(real(x)) * cis(imag(x)*log(convert(T,10)))
```
-/
def complexExp10Fast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let logBase := complexLogFast ops (fastRealComplex ops ops.ten)
  let angle := realMulComplexFast ops x.im logBase
  realMulComplexFast ops (ops.unary .exp10 x.re) (complexCisComplexFast ops angle)

/--
Julia source: base/fastmath.jl:353-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    exp2_fast(x::T) where {T<:ComplexTypes} =
        exp2(real(x)) * cis(imag(x)*log(convert(T,2)))
```
-/
def complexExp2Fast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  let logBase := complexLogFast ops (fastRealComplex ops ops.two)
  let angle := realMulComplexFast ops x.im logBase
  realMulComplexFast ops (ops.unary .exp2 x.re) (complexCisComplexFast ops angle)

/--
Julia source: base/fastmath.jl:356-356 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    expm1_fast(x::ComplexTypes) = exp(x)-1
```
-/
def complexExpm1Fast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  complexSubFast ops (complexExpFast ops x) (fastComplexOne ops)

/--
Julia source: base/fastmath.jl:357-357 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    log10_fast(x::T) where {T<:ComplexTypes} = log(x) / log(convert(T,10))
```
-/
def complexLog10Fast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  complexDivFast ops (complexLogFast ops x) (complexLogFast ops (fastRealComplex ops ops.ten))

/--
Julia source: base/fastmath.jl:358-358 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    log1p_fast(x::ComplexTypes) = log(1+x)
```
-/
def complexLog1pFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  complexLogFast ops (complexAddFast ops (fastComplexOne ops) x)

/--
Julia source: base/fastmath.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    log2_fast(x::T) where {T<:ComplexTypes} = log(x) / log(convert(T,2))
```
-/
def complexLog2Fast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  complexDivFast ops (complexLogFast ops x) (complexLogFast ops (fastRealComplex ops ops.two))

/--
Julia source: base/fastmath.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    log_fast(b::T, x::T) where {T<:ComplexTypes} = T(log(x)/log(b))
```
-/
def complexLogBaseFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (base x : FastComplex C) : FastComplex C :=
  complexDivFast ops (complexLogFast ops x) (complexLogFast ops base)

/--
Julia source: base/fastmath.jl:362-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    sin_fast(x::ComplexTypes) = -im*sinh(im*x)
```
-/
def complexSinFast {C : ComplexFloatType} (ops : FastFloatOps C.scalar)
    (x : FastComplex C) : FastComplex C :=
  fastComplexNeg ops (complexMulFast ops (fastImaginaryUnit ops)
    (complexSinhFast ops (complexMulFast ops (fastImaginaryUnit ops) x)))


/--
Julia source: base/fastmath.jl:397-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Reductions

maximum_fast(a; kw...) = Base.reduce(max_fast, a; kw...)
```
-/
def maximumFast {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (values : Collection) (keywords : Keywords) : Jl ScalarOutput :=
  ops.reduce ops.maxFast values keywords

/--
Julia source: base/fastmath.jl:400-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum_fast(a; kw...) = Base.reduce(min_fast, a; kw...)
```
-/
def minimumFast {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (values : Collection) (keywords : Keywords) : Jl ScalarOutput :=
  ops.reduce ops.minFast values keywords

/--
Julia source: base/fastmath.jl:401-402 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

maximum_fast(f, a; kw...) = Base.mapreduce(f, max_fast, a; kw...)
```
-/
def maximumFastMap {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (f : Mapper) (values : Collection) (keywords : Keywords) : Jl ScalarOutput :=
  ops.mapreduce f ops.maxFast values keywords

/--
Julia source: base/fastmath.jl:403-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum_fast(f, a; kw...) = Base.mapreduce(f, min_fast, a; kw...)

```
-/
def minimumFastMap {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (f : Mapper) (values : Collection) (keywords : Keywords) : Jl ScalarOutput :=
  ops.mapreduce f ops.minFast values keywords

/--
Julia source: base/fastmath.jl:405-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.reducedim_init(f, ::typeof(max_fast), A::AbstractArray, region) =
    Base.reducedim_init(f, max, A::AbstractArray, region)
```
-/
def reducedimInitMax {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (f : Mapper) (values : Collection) (region : Region) : Jl ArrayOutput :=
  ops.reducedimInit f ops.maxOp values region

/--
Julia source: base/fastmath.jl:407-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.reducedim_init(f, ::typeof(min_fast), A::AbstractArray, region) =
    Base.reducedim_init(f, min, A::AbstractArray, region)
```
-/
def reducedimInitMin {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (f : Mapper) (values : Collection) (region : Region) : Jl ArrayOutput :=
  ops.reducedimInit f ops.minOp values region

/--
Julia source: base/fastmath.jl:409-411 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

maximum!_fast(r::AbstractArray, A::AbstractArray; kw...) =
    maximum!_fast(identity, r, A; kw...)
```
-/
def maximumBangFast {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (result : ArrayOutput) (values : Collection) (keywords : Keywords) : Jl ArrayOutput :=
  ops.maxBangDispatch ops.identity result values keywords

/--
Julia source: base/fastmath.jl:412-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum!_fast(r::AbstractArray, A::AbstractArray; kw...) =
    minimum!_fast(identity, r, A; kw...)
```
-/
def minimumBangFast {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (result : ArrayOutput) (values : Collection) (keywords : Keywords) : Jl ArrayOutput :=
  ops.minBangDispatch ops.identity result values keywords

/--
Julia source: base/fastmath.jl:414-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

maximum!_fast(f::Function, r::AbstractArray, A::AbstractArray; init::Bool=true) =
    Base.mapreducedim!(f, max_fast, Base.initarray!(r, f, max, init, A), A)
```
-/
def maximumBangFastMap {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (f : Mapper) (result : ArrayOutput) (values : Collection) (init : Bool := true) :
    Jl ArrayOutput := do
  let initialized ← ops.initArray result f ops.maxOp init values
  ops.mapreducedim f ops.maxFast initialized values

/--
Julia source: base/fastmath.jl:417-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum!_fast(f::Function, r::AbstractArray, A::AbstractArray; init::Bool=true) =
    Base.mapreducedim!(f, min_fast, Base.initarray!(r, f, min, init, A), A)

end
```
-/
def minimumBangFastMap {Op Mapper Collection Region ScalarOutput ArrayOutput Keywords : Type}
    (ops : FastReductionOps Op Mapper Collection Region ScalarOutput ArrayOutput Keywords)
    (f : Mapper) (result : ArrayOutput) (values : Collection) (init : Bool := true) :
    Jl ArrayOutput := do
  let initialized ← ops.initArray result f ops.minOp init values
  ops.mapreducedim f ops.minFast initialized values

-- Source: base/fastmath.jl:243-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # fall-back implementations and type promotion
-- 
-- for op in (:abs, :abs2, :conj, :inv, :sign)
--     op_fast = fast_op[op]
--     @eval begin
--         # fall-back implementation for non-numeric types
--         $op_fast(xs...) = $op(xs...)
--     end
-- end
-- 
-- for op in (:-, :/, :(==), :!=, :<, :<=, :cmp, :rem, :minmax)
--     op_fast = fast_op[op]
--     @eval begin
--         # fall-back implementation for non-numeric types
--         $op_fast(xs...) = $op(xs...)
--         # type promotion
--         $op_fast(x::Number, y::Number, zs::Number...) =
--             $op_fast(promote(x,y,zs...)...)
--         # fall-back implementation that applies after promotion
--         $op_fast(x::T,ys::T...) where {T<:Number} = $op(x,ys...)
--     end
-- end
-- 
-- for op in (:+, :*, :min, :max)
--     op_fast = fast_op[op]
--     @eval begin
--         $op_fast(x) = $op(x)
--         # fall-back implementation for non-numeric types
--         $op_fast(x, y) = $op(x, y)
--         # type promotion
--         $op_fast(x::Number, y::Number) =
--             $op_fast(promote(x,y)...)
--         # fall-back implementation that applies after promotion
--         $op_fast(x::T,y::T) where {T<:Number} = $op(x,y)
--         # note: these definitions must not cause a dispatch loop when +(a,b) is
--         # not defined, and must only try to call 2-argument definitions, so
--         # that defining +(a,b) is sufficient for full functionality.
--         ($op_fast)(a, b, c, xs...) = (@inline; afoldl($op_fast, ($op_fast)(($op_fast)(a,b),c), xs...))
--         # a further concern is that it's easy for a type like (Int,Int...)
--         # to match many definitions, so we need to keep the number of
--         # definitions down to avoid losing type information.
--         # type promotion
--         $op_fast(a::Number, b::Number, c::Number, xs::Number...) =
--             $op_fast(promote(a,b,c,xs...)...)
--         # fall-back implementation that applies after promotion
--         $op_fast(a::T, b::T, c::T, xs::T...) where {T<:Number} = (@inline; afoldl($op_fast, ($op_fast)(($op_fast)(a,b),c), xs...))
--     end
-- end
-- 
-- /Source

-- Source: base/fastmath.jl:368-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # fall-back implementations and type promotion
-- 
-- for f in (:acos, :acosh, :angle, :asin, :asinh, :atan, :atanh, :cbrt,
--           :cis, :cos, :cosh, :exp10, :exp2, :exp, :expm1,
--           :log10, :log1p, :log2, :log, :sin, :sinh, :sqrt, :tan,
--           :tanh)
--     f_fast = fast_op[f]
--     @eval begin
--         $f_fast(x) = $f(x)
--     end
-- end
-- 
-- for f in (:^, :atan, :hypot, :log)
--     f_fast = fast_op[f]
--     @eval begin
--         # fall-back implementation for non-numeric types
--         $f_fast(x, y) = $f(x, y)
--         # type promotion
--         $f_fast(x::Number, y::Number) = $f_fast(promote(x, y)...)
--         # fall-back implementation that applies after promotion
--         $f_fast(x::T, y::T) where {T<:Number} = $f(x, y)
--     end
--     # Issue 53886 - avoid promotion of Int128 etc to be consistent with non-fastmath
--     if f === :^
--         @eval $f_fast(x::Number, y::Integer) = $f(x, y)
--     end
-- end
-- 
-- /Source
structure FastFallbackOps (Value Error : Type) where
  baseCall : String → List Value → Except Error Value
  fastCall : String → List Value → Except Error Value
  promote : List Value → Except Error (List Value)

/--
Julia source: base/fastmath.jl:250-250 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(xs...) = $op(xs...)
```
-/
def fallbackUnaryGroup {Value Error : Type} (ops : FastFallbackOps Value Error)
    (op : String) (xs : List Value) : Except Error Value :=
  ops.baseCall op xs

/--
Julia source: base/fastmath.jl:258-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(xs...) = $op(xs...)
```
-/
def fallbackVariadicGroup {Value Error : Type} (ops : FastFallbackOps Value Error)
    (op : String) (xs : List Value) : Except Error Value :=
  ops.baseCall op xs

/--
Julia source: base/fastmath.jl:260-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(x::Number, y::Number, zs::Number...) =
            $op_fast(promote(x,y,zs...)...)
```
-/
def fallbackPromoteVariadicNumbers {Value Error : Type}
    (ops : FastFallbackOps Value Error) (op : String) (xs : List Value) :
    Except Error Value := do
  ops.fastCall op (← ops.promote xs)

/--
Julia source: base/fastmath.jl:263-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(x::T,ys::T...) where {T<:Number} = $op(x,ys...)
```
-/
def fallbackSameTypeNumbers {Value Error : Type} (ops : FastFallbackOps Value Error)
    (op : String) (xs : List Value) : Except Error Value :=
  ops.baseCall op xs

/--
Julia source: base/fastmath.jl:270-270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(x) = $op(x)
```
-/
def fallbackUnaryBasic {Value Error : Type} (ops : FastFallbackOps Value Error)
    (op : String) (x : Value) : Except Error Value :=
  ops.baseCall op [x]

/--
Julia source: base/fastmath.jl:272-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(x, y) = $op(x, y)
```
-/
def fallbackBinaryBasic {Value Error : Type} (ops : FastFallbackOps Value Error)
    (op : String) (x y : Value) : Except Error Value :=
  ops.baseCall op [x, y]

/--
Julia source: base/fastmath.jl:274-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(x::Number, y::Number) =
            $op_fast(promote(x,y)...)
```
-/
def fallbackPromoteBinaryNumbers {Value Error : Type}
    (ops : FastFallbackOps Value Error) (op : String) (x y : Value) :
    Except Error Value := do
  ops.fastCall op (← ops.promote [x, y])

/--
Julia source: base/fastmath.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(x::T,y::T) where {T<:Number} = $op(x,y)
```
-/
def fallbackSameTypeBinaryNumbers {Value Error : Type}
    (ops : FastFallbackOps Value Error) (op : String) (x y : Value) :
    Except Error Value :=
  ops.baseCall op [x, y]

/--
Julia source: base/fastmath.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($op_fast)(a, b, c, xs...) = (@inline; afoldl($op_fast, ($op_fast)(($op_fast)(a,b),c), xs...))
```
-/
def fallbackFoldBasic {Value Error : Type} (ops : FastFallbackOps Value Error)
    (op : String) (a b c : Value) (xs : List Value) : Except Error Value := do
  let ab ← ops.fastCall op [a, b]
  let abc ← ops.fastCall op [ab, c]
  xs.foldlM (fun acc x => ops.fastCall op [acc, x]) abc

/--
Julia source: base/fastmath.jl:286-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(a::Number, b::Number, c::Number, xs::Number...) =
            $op_fast(promote(a,b,c,xs...)...)
```
-/
def fallbackPromoteFoldNumbers {Value Error : Type}
    (ops : FastFallbackOps Value Error) (op : String)
    (a b c : Value) (xs : List Value) : Except Error Value := do
  ops.fastCall op (← ops.promote (a :: b :: c :: xs))

/--
Julia source: base/fastmath.jl:289-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $op_fast(a::T, b::T, c::T, xs::T...) where {T<:Number} = (@inline; afoldl($op_fast, ($op_fast)(($op_fast)(a,b),c), xs...))
```
-/
def fallbackSameTypeFoldNumbers {Value Error : Type}
    (ops : FastFallbackOps Value Error) (op : String)
    (a b c : Value) (xs : List Value) : Except Error Value := do
  let ab ← ops.fastCall op [a, b]
  let abc ← ops.fastCall op [ab, c]
  xs.foldlM (fun acc x => ops.fastCall op [acc, x]) abc

/--
Julia source: base/fastmath.jl:377-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f_fast(x) = $f(x)
```
-/
def fallbackMathUnary {Value Error : Type} (ops : FastFallbackOps Value Error)
    (fn : String) (x : Value) : Except Error Value :=
  ops.baseCall fn [x]

/--
Julia source: base/fastmath.jl:385-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f_fast(x, y) = $f(x, y)
```
-/
def fallbackMathBinary {Value Error : Type} (ops : FastFallbackOps Value Error)
    (fn : String) (x y : Value) : Except Error Value :=
  ops.baseCall fn [x, y]

/--
Julia source: base/fastmath.jl:387-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f_fast(x::Number, y::Number) = $f_fast(promote(x, y)...)
```
-/
def fallbackPromoteMathBinary {Value Error : Type}
    (ops : FastFallbackOps Value Error) (fn : String) (x y : Value) :
    Except Error Value := do
  ops.fastCall fn (← ops.promote [x, y])

/--
Julia source: base/fastmath.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        $f_fast(x::T, y::T) where {T<:Number} = $f(x, y)
```
-/
def fallbackSameTypeMathBinary {Value Error : Type}
    (ops : FastFallbackOps Value Error) (fn : String) (x y : Value) :
    Except Error Value :=
  ops.baseCall fn [x, y]

/--
Julia source: base/fastmath.jl:393-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        @eval $f_fast(x::Number, y::Integer) = $f(x, y)
```
-/
def fallbackIntegerExponent {Value Error : Type} (ops : FastFallbackOps Value Error)
    (fn : String) (x y : Value) : Except Error Value :=
  ops.baseCall fn [x, y]

end JuliaLean.base.fastmath

namespace JuliaLean.NumMisc.Coverage

open JuliaLean

/-! ## `base/fastmath.jl:102-158` -/

def fastOpPairs : List (String × String) := [
  ("+", "Base.FastMath.add_fast"), ("-", "Base.FastMath.sub_fast"),
  ("*", "Base.FastMath.mul_fast"), ("/", "Base.FastMath.div_fast"),
  ("==", "Base.FastMath.eq_fast"), ("!=", "Base.FastMath.ne_fast"),
  ("<", "Base.FastMath.lt_fast"), ("<=", "Base.FastMath.le_fast"),
  (">", "Base.FastMath.gt_fast"), (">=", "Base.FastMath.ge_fast"),
  ("abs", "Base.FastMath.abs_fast"), ("abs2", "Base.FastMath.abs2_fast"),
  ("cmp", "Base.FastMath.cmp_fast"), ("conj", "Base.FastMath.conj_fast"),
  ("inv", "Base.FastMath.inv_fast"), ("rem", "Base.FastMath.rem_fast"),
  ("sign", "Base.FastMath.sign_fast"), ("isfinite", "Base.FastMath.isfinite_fast"),
  ("isinf", "Base.FastMath.isinf_fast"), ("isnan", "Base.FastMath.isnan_fast"),
  ("issubnormal", "Base.FastMath.issubnormal_fast"), ("^", "Base.FastMath.pow_fast"),
  ("acos", "Base.FastMath.acos_fast"), ("acosh", "Base.FastMath.acosh_fast"),
  ("angle", "Base.FastMath.angle_fast"), ("asin", "Base.FastMath.asin_fast"),
  ("asinh", "Base.FastMath.asinh_fast"), ("atan", "Base.FastMath.atan_fast"),
  ("atanh", "Base.FastMath.atanh_fast"), ("cbrt", "Base.FastMath.cbrt_fast"),
  ("cis", "Base.FastMath.cis_fast"), ("cos", "Base.FastMath.cos_fast"),
  ("cosh", "Base.FastMath.cosh_fast"), ("exp10", "Base.FastMath.exp10_fast"),
  ("exp2", "Base.FastMath.exp2_fast"), ("exp", "Base.FastMath.exp_fast"),
  ("expm1", "Base.FastMath.expm1_fast"), ("hypot", "Base.FastMath.hypot_fast"),
  ("log10", "Base.FastMath.log10_fast"), ("log1p", "Base.FastMath.log1p_fast"),
  ("log2", "Base.FastMath.log2_fast"), ("log", "Base.FastMath.log_fast"),
  ("max", "Base.FastMath.max_fast"), ("min", "Base.FastMath.min_fast"),
  ("minmax", "Base.FastMath.minmax_fast"), ("sin", "Base.FastMath.sin_fast"),
  ("sincos", "Base.FastMath.sincos_fast"), ("sinh", "Base.FastMath.sinh_fast"),
  ("sqrt", "Base.FastMath.sqrt_fast"), ("tan", "Base.FastMath.tan_fast"),
  ("tanh", "Base.FastMath.tanh_fast"), ("maximum", "Base.FastMath.maximum_fast"),
  ("minimum", "Base.FastMath.minimum_fast"), ("maximum!", "Base.FastMath.maximum!_fast"),
  ("minimum!", "Base.FastMath.minimum!_fast")]

def rewriteOpPairs : List (String × String) :=
  [("+=", "+"), ("-=", "-"), ("*=", "*"), ("/=", "/"), ("^=", "^")]

def lookupName (fallback : String) : List (String × String) → String
  | [] => fallback
  | (source, target) :: rest => if source == fallback then target else lookupName fallback rest

def makeFastSymbol (symbol : String) : String := lookupName symbol fastOpPairs
def rewrittenAssignmentOp (head : String) : Option String :=
  let found := lookupName head rewriteOpPairs
  if found == head then none else some found

inductive FMExpr where
  | opaque (id : Nat)
  | symbol (name : String)
  | int (value : Int)
  | valInt (value : Int)
  | quote (body : FMExpr)
  | call (name : String) (args : List FMExpr)
  | node (head : String) (args : List FMExpr)

mutual
  def makeFastMath : FMExpr → FMExpr
    | .opaque id => .opaque id
    | .symbol name => .symbol (makeFastSymbol name)
    | .int value => .int value
    | .valInt value => .valInt value
    | .quote body => .quote body
    | .call "^" [base, .int power] =>
        .call "Base.FastMath.pow_fast" [makeFastMath base, .valInt power]
    | .call name args => .call (makeFastSymbol name) (makeFastList args)
    | .node head (lhs :: rhs :: rest) =>
        match rewrittenAssignmentOp head, lhs with
        | some op, .symbol name =>
            .node "=" [.symbol name,
              .call (makeFastSymbol op) [.symbol name, makeFastMath rhs]]
        | _, _ => .node (makeFastSymbol head) (makeFastList (lhs :: rhs :: rest))
    | .node head args => .node (makeFastSymbol head) (makeFastList args)

  def makeFastList : List FMExpr → List FMExpr
    | [] => []
    | expression :: rest => makeFastMath expression :: makeFastList rest
end

def fastmathMacro (expression : FMExpr) : FMExpr :=
  makeFastMath (.node "escape" [expression])

/-! ## `base/fastmath.jl:165-327` -/

inductive FastTerm where
  | var (id : Nat)
  | int (value : Int)
  | bool (value : Bool)
  | val (value : Int)
  | call (name : String) (args : List FastTerm)
  | pair (first second : FastTerm)
  | ite (condition yes no : FastTerm)
  | eagerIf (condition yes no : FastTerm)
  | list (items : List FastTerm)

def ftCall1 (name : String) (x : FastTerm) : FastTerm := .call name [x]
def ftCall2 (name : String) (x y : FastTerm) : FastTerm := .call name [x, y]

def subFastUnaryTerm (x : FastTerm) : FastTerm := ftCall1 "neg_float_fast" x
def addFastTerm (x y : FastTerm) : FastTerm := ftCall2 "add_float_fast" x y
def subFastTerm (x y : FastTerm) : FastTerm := ftCall2 "sub_float_fast" x y
def mulFastTerm (x y : FastTerm) : FastTerm := ftCall2 "mul_float_fast" x y
def divFastTerm (x y : FastTerm) : FastTerm := ftCall2 "div_float_fast" x y
def maxFastTerm (x y : FastTerm) : FastTerm := ftCall2 "max_float_fast" x y
def minFastTerm (x y : FastTerm) : FastTerm := ftCall2 "min_float_fast" x y

def cmpFastTerm (x y : FastTerm) : FastTerm :=
  .eagerIf (ftCall2 "Base.FastMath.eq_fast" x y) (.int 0)
    (.eagerIf (ftCall2 "Base.FastMath.lt_fast" x y) (.int (-1)) (.int 1))

def logBaseFastTerm (base x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" base)

def eqFastTerm (x y : FastTerm) : FastTerm := ftCall2 "eq_float_fast" x y
def neFastTerm (x y : FastTerm) : FastTerm := ftCall2 "ne_float_fast" x y
def ltFastTerm (x y : FastTerm) : FastTerm := ftCall2 "lt_float_fast" x y
def leFastTerm (x y : FastTerm) : FastTerm := ftCall2 "le_float_fast" x y
def gtFastTerm (x y : FastTerm) : FastTerm := ftCall2 "Base.FastMath.lt_fast" y x
def geFastTerm (x y : FastTerm) : FastTerm := ftCall2 "Base.FastMath.le_fast" y x
def isinfFastTerm (_x : FastTerm) : FastTerm := .bool false
def isfiniteFastTerm (_x : FastTerm) : FastTerm := .bool true
def isnanFastTerm (_x : FastTerm) : FastTerm := .bool false
def issubnormalFastTerm (_x : FastTerm) : FastTerm := .bool false

def forwardingTerm (name : String) (args : List FastTerm) : FastTerm := .call name args

def promoteRedispatchTerm (fastName : String) (args : List FastTerm) : FastTerm :=
  .call fastName [.call "promote" args]

def naryFoldTerm (fastName : String) (a b c : FastTerm) (rest : List FastTerm) : FastTerm :=
  .call "afoldl" [symbol fastName,
    ftCall2 fastName (ftCall2 fastName a b) c, .list rest]
where
  symbol (name : String) : FastTerm := .call "symbol" [.call name []]

def fallbackVarargsTerm (baseName : String) (args : List FastTerm) : FastTerm :=
  .call baseName args

def promoteVarargsTerm (fastName : String) (args : List FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" args]]

def promoteBinaryTerm (fastName : String) (x y : FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" [x, y]]]

def promoteNaryTerm (fastName : String) (a b c : FastTerm) (rest : List FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" (a :: b :: c :: rest)]]

def exp2FastTerm (x : FastTerm) : FastTerm := ftCall1 "Base.Math.exp2_fast" x
def expFastTerm (x : FastTerm) : FastTerm := ftCall1 "Base.Math.exp_fast" x
def exp10FastTerm (x : FastTerm) : FastTerm := ftCall1 "Base.Math.exp10_fast" x

def powIntegerFastTerm (x : FastTerm) (y : Int) : FastTerm :=
  let z := (JInt.wrap .i32 y).val
  if z == y then ftCall2 "Base.FastMath.pow_fast" x (.int z)
  else ftCall2 "Base.^" x (.int y)

def powiFastTerm (floatType : String) (x y : FastTerm) : FastTerm :=
  .call "ccall:llvm.powi" [.call floatType [], x, y]

def powValFastTerm (x : FastTerm) (power : Int) : FastTerm :=
  ftCall2 "Base.FastMath.pow_fast" x (.int power)

def powLiteralFallbackTerm (x value : FastTerm) : FastTerm :=
  .call "Base.literal_pow" [.call "Base.^" [], x, value]

def sqrtFastTerm (x : FastTerm) : FastTerm := ftCall1 "sqrt_llvm_fast" x
def sincosPrimitiveFastTerm (x : FastTerm) : FastTerm := ftCall1 "sincos" x

def sincosFloat16FastTerm (x : FastTerm) : FastTerm :=
  let widened := ftCall1 "Float32" x
  let result := ftCall1 "Base.FastMath.sincos_fast" widened
  .pair (ftCall1 "Float16" (.call "first" [result]))
    (ftCall1 "Float16" (.call "second" [result]))

def sincosRealFastTerm (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.sincos_fast"
    (.call "typeassert:AbstractFloat" [ftCall1 "float" x])

def remFastTerm (x y : FastTerm) : FastTerm :=
  ftCall2 "copysign"
    (ftCall2 "Base.rem_internal" (ftCall1 "Base.FastMath.abs_fast" x)
      (ftCall1 "Base.FastMath.abs_fast" y)) x

def hypotFastTerm (x y : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.sqrt_fast"
    (ftCall2 "Base.FastMath.add_fast"
      (ftCall2 "Base.FastMath.mul_fast" x x)
      (ftCall2 "Base.FastMath.mul_fast" y y))

structure ScalarFastOps where
  neg : Int → Int
  add : Int → Int → Int
  sub : Int → Int → Int
  mul : Int → Int → Int
  div : Int → Int → Int
  min : Int → Int → Int
  max : Int → Int → Int
  rem : Int → Int → Int
  pow : Int → Int → Int
  sqrt : Int → Int
  eq : Int → Int → Bool
  lt : Int → Int → Bool

def fastCmp (ops : ScalarFastOps) (x y : Int) : Int :=
  if ops.eq x y then 0 else if ops.lt x y then -1 else 1

def fastMinmax (ops : ScalarFastOps) (x y : Int) : Int × Int :=
  (ops.min x y, ops.max x y)

def promoteThen (promote : Int → Int → Int × Int) (op : Int → Int → Int) (x y : Int) : Int :=
  let pair := promote x y
  op pair.1 pair.2

def foldFast (op : Int → Int → Int) (x : Int) (xs : List Int) : Int := xs.foldl op x

def powFastPath (fitsInt32 : Bool) (fast normal : Int) : Int := if fitsInt32 then fast else normal

def sincosFast (sin cos : Int → Int) (x : Int) : Int × Int := (sin x, cos x)

def fastUnary (operation : Int → Int) (x : Int) : Int := operation x
def fastBinary (operation : Int → Int → Int) (x y : Int) : Int := operation x y
def fastClassification (kind : Nat) (_x : Int) : Bool := kind == 1
def fastRemainder (abs rem copySign : Int → Int → Int) (x y : Int) : Int :=
  copySign (rem (abs x 0) (abs y 0)) x
def fastHypot (mul add sqrt : Int → Int → Int) (x y : Int) : Int :=
  sqrt (add (mul x x) (mul y y)) 0

/-! ## `base/fastmath.jl:331-418` -/

structure ComplexInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr

structure ComplexOps where
  add : Int → Int → Int
  sub : Int → Int → Int
  mul : Int → Int → Int
  div : Int → Int → Int
  exp : Int → Int
  log : Int → Int
  sqrt : Int → Int
  sincos : Int → Int × Int
  neg : Int → Int

def complexAdd (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.add x.re y.re, o.add x.im y.im⟩

def complexSub (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.sub x.re y.re, o.sub x.im y.im⟩

def complexMul (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.sub (o.mul x.re y.re) (o.mul x.im y.im),
   o.add (o.mul x.re y.im) (o.mul x.im y.re)⟩

def complexEq (o : ScalarFastOps) (x y : ComplexInt) : Bool :=
  o.eq x.re y.re && o.eq x.im y.im

def complexConj (neg : Int → Int) (x : ComplexInt) : ComplexInt := ⟨x.re, neg x.im⟩

def complexAbs2 (mul add : Int → Int → Int) (x : ComplexInt) : Int :=
  add (mul x.re x.re) (mul x.im x.im)

def complexDivNumerator (o : ComplexOps) (x y : ComplexInt) : ComplexInt :=
  ⟨o.add (o.mul x.re y.re) (o.mul x.im y.im),
   o.sub (o.mul x.im y.re) (o.mul x.re y.im)⟩

inductive ComplexFormulaTag where
  | pow | acos | acosh | angle | asin | asinh | atan | atanh | cis | cos | cosh
  | exp10 | exp2 | exp | expm1 | log10 | log1p | log2 | log | sin | sinh | sqrt | tan | tanh
  deriving DecidableEq, Repr

def complexFormulaCode : ComplexFormulaTag → Nat
  | .pow => 1 | .acos => 2 | .acosh => 3 | .angle => 4 | .asin => 5 | .asinh => 6
  | .atan => 7 | .atanh => 8 | .cis => 9 | .cos => 10 | .cosh => 11 | .exp10 => 12
  | .exp2 => 13 | .exp => 14 | .expm1 => 15 | .log10 => 16 | .log1p => 17
  | .log2 => 18 | .log => 19 | .sin => 20 | .sinh => 21 | .sqrt => 22
  | .tan => 23 | .tanh => 24

def reduceFast (op : Int → Int → Int) (values : List Int) (init : Int) : Int :=
  values.foldl op init

def cReal (x : FastTerm) : FastTerm := ftCall1 "real" x
def cImag (x : FastTerm) : FastTerm := ftCall1 "imag" x
def cMake (re im : FastTerm) : FastTerm := .call "Complex" [re, im]
def cOne (x : FastTerm) : FastTerm := .call "convert" [.call "typeof" [x], .int 1]
def cConst (x : FastTerm) (n : Int) : FastTerm := .call "convert" [.call "typeof" [x], .int n]
def cIm : FastTerm := .call "im" []

def cAbsFast (x : FastTerm) : FastTerm := ftCall2 "Base.FastMath.hypot_fast" (cReal x) (cImag x)
def cInvFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.div_fast" (ftCall1 "Base.FastMath.conj_fast" x)
    (ftCall1 "Base.FastMath.abs2_fast" x)
def cSignFast (x : FastTerm) : FastTerm :=
  .ite (ftCall2 "Base.FastMath.eq_fast" x (.int 0)) (.call "float" [.call "zero" [x]])
    (ftCall2 "Base.FastMath.div_fast" x (ftCall1 "Base.FastMath.abs_fast" x))

def cAddScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.add_fast" (cReal x) b) (cImag x)
def cAddScalarLeft (a y : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.add_fast" a (cReal y)) (cImag y)
def cSubScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.sub_fast" (cReal x) b) (cImag x)
def cSubScalarLeft (a y : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.sub_fast" a (cReal y))
    (ftCall1 "Base.FastMath.sub_fast" (cImag y))
def cMulScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.mul_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.mul_fast" (cImag x) b)
def cMulScalarLeft (a y : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
    (ftCall2 "Base.FastMath.mul_fast" a (cImag y))

def cDivFast (x y : FastTerm) : FastTerm :=
  let numerator := cMake
    (ftCall2 "Base.FastMath.add_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cReal y))
      (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cImag y)))
    (ftCall2 "Base.FastMath.sub_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cImag x) (cReal y))
      (ftCall2 "Base.FastMath.mul_fast" (cReal x) (cImag y)))
  ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)

def cDivScalarRight (x b : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.div_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.div_fast" (cImag x) b)

def cDivScalarLeft (a y : FastTerm) : FastTerm :=
  let numerator := cMake
    (ftCall2 "Base.FastMath.mul_fast" a (cReal y))
    (ftCall1 "Base.FastMath.sub_fast" (ftCall2 "Base.FastMath.mul_fast" a (cImag y)))
  ftCall2 "Base.FastMath.div_fast" numerator (ftCall1 "Base.FastMath.abs2_fast" y)

def cEqFast (x y : FastTerm) : FastTerm :=
  ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (cImag y))
def cEqScalarRight (x b : FastTerm) : FastTerm :=
  ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" (cReal x) b)
    (ftCall2 "Base.FastMath.eq_fast" (cImag x) (.int 0))
def cEqScalarLeft (a y : FastTerm) : FastTerm :=
  ftCall2 "&" (ftCall2 "Base.FastMath.eq_fast" a (cReal y))
    (ftCall2 "Base.FastMath.eq_fast" (.int 0) (cImag y))
def cNeFast (x y : FastTerm) : FastTerm := ftCall1 "!" (ftCall2 "Base.FastMath.eq_fast" x y)

def cCisFastReal (x : FastTerm) : FastTerm :=
  let sc := ftCall1 "Base.FastMath.sincos_fast" x
  cMake (.call "second" [sc]) (.call "first" [sc])
def cPowFast (x y : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.exp_fast"
    (ftCall2 "Base.FastMath.mul_fast" y (ftCall1 "Base.FastMath.log_fast" x))
def cAcosFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.add_fast"
    (ftCall2 "Base.FastMath.div_fast" (.call "convertπ" [.call "typeof" [x]]) (.int 2))
    (ftCall2 "Base.FastMath.mul_fast" cIm
      (ftCall1 "Base.FastMath.log_fast"
        (ftCall2 "Base.FastMath.add_fast"
          (ftCall2 "Base.FastMath.mul_fast" cIm x)
          (ftCall1 "Base.FastMath.sqrt_fast"
            (ftCall2 "Base.FastMath.sub_fast" (.int 1)
              (ftCall2 "Base.FastMath.mul_fast" x x))))))
def cAcoshFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x
      (ftCall2 "Base.FastMath.mul_fast"
        (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.add_fast" x (.int 1)))
        (ftCall1 "Base.FastMath.sqrt_fast" (ftCall2 "Base.FastMath.sub_fast" x (.int 1)))))
def cAngleFast (x : FastTerm) : FastTerm := .call "atan" [cImag x, cReal x]
def cAsinFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.asinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cAsinhFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.log_fast"
    (ftCall2 "Base.FastMath.add_fast" x
      (ftCall1 "Base.FastMath.sqrt_fast"
        (ftCall2 "Base.FastMath.add_fast" (.int 1)
          (ftCall2 "Base.FastMath.mul_fast" x x))))
def cAtanFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.atanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cAtanhFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast"
    (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast"
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast" (.int 1) x))
      (ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.sub_fast" (.int 1) x)))
def cCisFastComplex (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" (cImag x)))
    (ftCall1 "Base.FastMath.cis_fast" (cReal x))
def cCosFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.cosh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x)
def cCoshFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.add_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))
def cExpBaseFast (name : String) (base : Int) (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 name (cReal x))
    (ftCall1 "Base.FastMath.cis_fast"
      (ftCall2 "Base.FastMath.mul_fast" (cImag x)
        (ftCall1 "Base.FastMath.log_fast" (cConst x base))))
def cExp10Fast (x : FastTerm) : FastTerm := cExpBaseFast "Base.FastMath.exp10_fast" 10 x
def cExp2Fast (x : FastTerm) : FastTerm := cExpBaseFast "Base.FastMath.exp2_fast" 2 x
def cExpFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "Base.FastMath.exp_fast" (cReal x))
    (ftCall1 "Base.FastMath.cis_fast" (cImag x))
def cExpm1Fast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.sub_fast" (ftCall1 "Base.FastMath.exp_fast" x) (.int 1)
def cLogBaseFast (base : Int) (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.div_fast" (ftCall1 "Base.FastMath.log_fast" x)
    (ftCall1 "Base.FastMath.log_fast" (cConst x base))
def cLog10Fast (x : FastTerm) : FastTerm := cLogBaseFast 10 x
def cLog2Fast (x : FastTerm) : FastTerm := cLogBaseFast 2 x
def cLog1pFast (x : FastTerm) : FastTerm :=
  ftCall1 "Base.FastMath.log_fast" (ftCall2 "Base.FastMath.add_fast" (.int 1) x)
def cLogFast (x : FastTerm) : FastTerm :=
  cMake (ftCall2 "Base.FastMath.div_fast"
      (ftCall1 "Base.FastMath.log_fast" (ftCall1 "Base.FastMath.abs2_fast" x)) (.int 2))
    (ftCall1 "Base.FastMath.angle_fast" x)
def cLogTwoFast (base x : FastTerm) : FastTerm :=
  .call "Complex" [ftCall2 "Base.FastMath.div_fast"
    (ftCall1 "Base.FastMath.log_fast" x) (ftCall1 "Base.FastMath.log_fast" base)]
def cSinFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.sinh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cSinhFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall2 "Base.FastMath.div_fast" (cOne x) (.int 2))
    (ftCall2 "Base.FastMath.sub_fast" (ftCall1 "Base.FastMath.exp_fast" x)
      (ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)))
def cSqrtFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "Base.FastMath.sqrt_fast"
    (ftCall1 "Base.FastMath.abs_fast" x))
    (ftCall1 "Base.FastMath.cis_fast" (ftCall2 "Base.FastMath.div_fast"
      (ftCall1 "Base.FastMath.angle_fast" x) (.int 2)))
def cTanFast (x : FastTerm) : FastTerm :=
  ftCall2 "Base.FastMath.mul_fast" (ftCall1 "-" cIm)
    (ftCall1 "Base.FastMath.tanh_fast" (ftCall2 "Base.FastMath.mul_fast" cIm x))
def cTanhFast (x : FastTerm) : FastTerm :=
  let a := ftCall1 "Base.FastMath.exp_fast" x
  let b := ftCall1 "Base.FastMath.exp_fast" (ftCall1 "-" x)
  ftCall2 "Base.FastMath.div_fast" (ftCall2 "Base.FastMath.sub_fast" a b)
    (ftCall2 "Base.FastMath.add_fast" a b)

def unaryMathFallbackTerm (baseName : String) (x : FastTerm) : FastTerm := ftCall1 baseName x
def binaryMathFallbackTerm (baseName : String) (x y : FastTerm) : FastTerm := ftCall2 baseName x y
def binaryMathPromoteTerm (fastName : String) (x y : FastTerm) : FastTerm :=
  .call fastName [.call "splat" [.call "promote" [x, y]]]
def powerNumberIntegerFallbackTerm (x y : FastTerm) : FastTerm := ftCall2 "Base.^" x y

def maximumFastTerm (array kwargs : FastTerm) : FastTerm :=
  .call "Base.reduce" [.call "Base.FastMath.max_fast" [], array, kwargs]
def minimumFastTerm (array kwargs : FastTerm) : FastTerm :=
  .call "Base.reduce" [.call "Base.FastMath.min_fast" [], array, kwargs]
def maximumMapFastTerm (f array kwargs : FastTerm) : FastTerm :=
  .call "Base.mapreduce" [f, .call "Base.FastMath.max_fast" [], array, kwargs]
def minimumMapFastTerm (f array kwargs : FastTerm) : FastTerm :=
  .call "Base.mapreduce" [f, .call "Base.FastMath.min_fast" [], array, kwargs]
def reducedimInitFastTerm (f reducer array region : FastTerm) : FastTerm :=
  .call "Base.reducedim_init" [f, reducer, array, region]
def maxReducedimInitFastTerm (f array region : FastTerm) : FastTerm :=
  reducedimInitFastTerm f (.call "max" []) array region
def minReducedimInitFastTerm (f array region : FastTerm) : FastTerm :=
  reducedimInitFastTerm f (.call "min" []) array region
def maximumBangWrapperTerm (result array kwargs : FastTerm) : FastTerm :=
  .call "Base.FastMath.maximum!_fast" [.call "identity" [], result, array, kwargs]
def minimumBangWrapperTerm (result array kwargs : FastTerm) : FastTerm :=
  .call "Base.FastMath.minimum!_fast" [.call "identity" [], result, array, kwargs]
def maximumBangTerm (f result array init : FastTerm) : FastTerm :=
  .call "Base.mapreducedim!" [f, .call "Base.FastMath.max_fast" [],
    .call "Base.initarray!" [result, f, .call "max" [], init, array], array]
def minimumBangTerm (f result array init : FastTerm) : FastTerm :=
  .call "Base.mapreducedim!" [f, .call "Base.FastMath.min_fast" [],
    .call "Base.initarray!" [result, f, .call "min" [], init, array], array]

end JuliaLean.NumMisc.Coverage
