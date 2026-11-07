import JuliaLean.base.generator
import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.base.range

/-!
# Model of `base/simdloop.jl`

The `Base.SimdLoop` module of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`: the `@simd`
macro and the `simd_outer_range`/`simd_inner_length`/`simd_index` functions its expansion calls.
Syntax is the installed `base/expr.jl` model (`JuliaLean.base.expr.Value`); as there, a macro is a
function of its arguments returning the expansion. The `quote` block of `compile` is the
`Expr(:block, ...)` the parser builds for it, with a `LineNumberNode` for each statement line;
Base records this file as `simdloop.jl`. The `length`, `firstindex`, `+` and in-bounds
`getindex` that the runtime functions call on a user's range are typed operations with no
assumed laws.
-/

namespace JuliaLean.base.simdloop

open JuliaLean
open JuliaLean.base.expr (Value LeafOps ExprError esc i64)

section
variable {L : Type}

/-- The `LineNumberNode` the parser records for a line of this file. -/
def lnn (line : Int) : Value L := .lineNumberNode (i64 line) (.symbol "simdloop.jl")

/-- `Base.name`: `Expr(:., :Base, QuoteNode(:name))`. -/
def baseDot (name : String) : Value L := .expr "." [.symbol "Base", .quoteNode (.symbol name)]

/-- `f(args...)`. -/
def call (f : Value L) (args : List (Value L)) : Value L := .expr "call" (f :: args)

/-- Operations on the range value `r` of a `@simd` loop, with exception type `E`. -/
structure SimdRangeOps (R I V E : Type) where
  length : R → Except E I
  firstindex : R → Except E I
  /-- `i + j`. -/
  add : I → I → Except E I
  /-- `@inbounds r[k]`. -/
  getindex : R → I → Except E V

-- Reason: The opening comments, module header and export list are load-time structure.
-- UNTRANSLATED
-- Source: base/simdloop.jl:1-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Support for @simd for
-- 
-- module SimdLoop
-- 
-- export @simd, simd_outer_range, simd_inner_length, simd_index
-- 
-- /Source

/--
Julia source: base/simdloop.jl:9-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Error thrown from ill-formed uses of @simd
struct SimdError <: Exception
    msg::String
end
```
-/
inductive SimdError where
  | mk (msg : String)

/-- Exceptions thrown by the modelled methods. -/
inductive Error where
  | simd (e : SimdError)
  | expr (e : ExprError)

def simdError (msg : String) : Error := .simd (.mk msg)
/--
Julia source: base/simdloop.jl:13-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Parse iteration space expression
#       symbol '=' range
#       symbol 'in' range
function parse_iteration_space(x)
    (isa(x, Expr) && (x.head === :(=) || x.head === :in)) || throw(SimdError("= or in expected"))
    length(x.args) == 2 || throw(SimdError("simd range syntax is wrong"))
    isa(x.args[1], Symbol) || throw(SimdError("simd loop index must be a symbol"))
    x.args # symbol, range
end
```
-/
-- The loop index and range: the two elements of `x.args`.
def parse_iteration_space (x : Value L) : Except Error (Value L × Value L) := do
  match x with
  | .expr head args =>
    if !(head == "=" || head == "in") then throw (simdError "= or in expected")
    if args.length != 2 then throw (simdError "simd range syntax is wrong")
    match args with
    | [.symbol s, range] => pure (.symbol s, range)
    | _ => throw (simdError "simd loop index must be a symbol")
  | _ => throw (simdError "= or in expected")
mutual
/--
Julia source: base/simdloop.jl:23-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# reject invalid control flow statements in @simd loop body
function check_body!(x::Expr)
    if x.head === :break || x.head === :continue
        throw(SimdError("$(x.head) is not allowed inside a @simd loop body"))
    elseif x.head === :macrocall && x.args[1] === Symbol("@goto")
        throw(SimdError("@goto is not allowed inside a @simd loop body"))
    end
    for arg in x.args
        check_body!(arg)
    end
    return true
end
check_body!(x::QuoteNode) = check_body!(x.value)
check_body!(x) = true
```
-/
def check_body : Value L → Except Error Bool
  | .expr head args => do
    if head == "break" || head == "continue" then
      throw (simdError (head ++ " is not allowed inside a @simd loop body"))
    else if head == "macrocall" then
      match args with
      | [] => throw (.expr (.jl .boundsError))
      | a1 :: _ =>
        if a1 matches .symbol "@goto" then
          throw (simdError "@goto is not allowed inside a @simd loop body")
    check_body_args args
    return true
  | .quoteNode value => check_body value
  | _ => pure true
/-- `for arg in x.args; check_body!(arg); end`. -/
def check_body_args : List (Value L) → Except Error Unit
  | [] => pure ()
  | arg :: rest => do
    let _ ← check_body arg
    check_body_args rest
end
/--
Julia source: base/simdloop.jl:38-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# @simd splits a for loop into two loops: an outer scalar loop and
# an inner loop marked with :loopinfo. The simd_... functions define
# the splitting.
# Custom iterators that do not support random access cannot support
# vectorization. In order to be compatible with `@simd` annotated loops,
#they should override `simd_inner_length(v::MyIter, j) = 1`,
#`simd_outer_range(v::MyIter) = v`, and `simd_index(v::MyIter, j, i) = j`.

# Get range for outer loop.
simd_outer_range(r) = 0:0
```
-/
def simd_outer_range {R : Type} (_r : R) : JuliaLean.base.range.UnitRange JInt64 := ⟨i64 0, i64 0⟩
/--
Julia source: base/simdloop.jl:49-51 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Get trip count for inner loop.
@inline simd_inner_length(r, j) = Base.length(r)
```
-/
def simd_inner_length {R I V E : Type} (ops : SimdRangeOps R I V E) (r : R) (_j : I) : Except E I :=
  ops.length r
/--
Julia source: base/simdloop.jl:52-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Construct user-level element from original range, outer loop index j, and inner loop index i.
@inline simd_index(r, j, i) = (@inbounds ret = r[i+firstindex(r)]; ret)
```
-/
def simd_index {R I V E : Type} (ops : SimdRangeOps R I V E) (r : R) (_j i : I) : Except E V := do
  let first ← ops.firstindex r
  let k ← ops.add i first
  ops.getindex r k
/--
Julia source: base/simdloop.jl:55-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Compile Expr x in context of @simd.
function compile(x, ivdep)
    (isa(x, Expr) && x.head === :for) || throw(SimdError("for loop expected"))
    length(x.args) == 2 || throw(SimdError("1D for loop expected"))
    check_body!(x)

    var,range = parse_iteration_space(x.args[1])
    # r: Range value
    # j: Iteration variable for outer loop
    # n: Trip count for inner loop
    # i: Trip index for inner loop
    return quote
        # Evaluate range value once, to enhance type and data flow analysis by optimizers.
        let r = $(esc(range))
            for j in Base.simd_outer_range(r)
                let n = Base.simd_inner_length(r,j)
                    if zero(n) < n
                        # Lower loop in way that seems to work best for LLVM 3.3 vectorizer.
                        let i = zero(n)
                            while i < n
                                local $(esc(var)) = Base.simd_index(r,j,i)
                                $(esc(x.args[2]))        # Body of loop
                                i += 1
                                $(Expr(:loopinfo, Symbol("julia.simdloop"), ivdep))  # Mark loop as SIMD loop
                            end
                        end
                    end
                end
            end
        end
        nothing
    end
end
```
-/
def compile (lo : LeafOps L) (x ivdep : Value L) : Except Error (Value L) := do
  let args ← match x with
    | .expr "for" args => pure args
    | _ => throw (simdError "for loop expected")
  if args.length != 2 then throw (simdError "1D for loop expected")
  let _ ← check_body x
  match args with
  | [spec, body] =>
    let (var, range) ← parse_iteration_space spec
    -- r: Range value; j: outer iteration variable; n: inner trip count; i: inner trip index
    return .expr "block" [lnn 69,
      .expr "let" [.expr "=" [.symbol "r", esc range],
        .expr "block" [lnn 70,
          .expr "for" [.expr "=" [.symbol "j", call (baseDot "simd_outer_range") [.symbol "r"]],
            .expr "block" [lnn 71,
              .expr "let" [.expr "=" [.symbol "n",
                  call (baseDot "simd_inner_length") [.symbol "r", .symbol "j"]],
                .expr "block" [lnn 72,
                  .expr "if" [call (.symbol "<") [call (.symbol "zero") [.symbol "n"], .symbol "n"],
                    .expr "block" [lnn 74,
                      .expr "let" [.expr "=" [.symbol "i", call (.symbol "zero") [.symbol "n"]],
                        .expr "block" [lnn 75,
                          .expr "while" [call (.symbol "<") [.symbol "i", .symbol "n"],
                            .expr "block" [lnn 76,
                              .expr "local" [.expr "=" [esc var,
                                call (baseDot "simd_index") [.symbol "r", .symbol "j", .symbol "i"]]],
                              lnn 77, esc body,
                              lnn 78, .expr "+=" [.symbol "i", .leaf (lo.ofInt (i64 1))],
                              lnn 79, .expr "loopinfo" [.symbol "julia.simdloop", ivdep],
                              lnn 80]]]]]]]],
              lnn 84]]]],
      lnn 86, .symbol "nothing"]
  | _ => throw (simdError "1D for loop expected")
/--
Julia source: base/simdloop.jl:89-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @simd

Annotate a `for` loop to allow the compiler to take extra liberties to allow loop re-ordering

!!! warning
    This feature is experimental and could change or disappear in future versions of Julia.
    Incorrect use of the `@simd` macro may cause unexpected results.

The object iterated over in a `@simd for` loop should be a one-dimensional range.
By using `@simd`, you are asserting several properties of the loop:

* It is safe to execute iterations in arbitrary or overlapping order, with special consideration for reduction variables.
* Floating-point operations on reduction variables can be reordered or contracted, possibly causing different results than without `@simd`.

In many cases, Julia is able to automatically vectorize inner for loops without the use of `@simd`.
Using `@simd` gives the compiler a little extra leeway to make it possible in more situations. In
either case, your inner loop should have the following properties to allow vectorization:

* The loop must be an innermost loop
* The loop body must be straight-line code. Therefore, [`@inbounds`](@ref) is
    currently needed for all array accesses. The compiler can sometimes turn
    short `&&`, `||`, and `?:` expressions into straight-line code if it is safe
    to evaluate all operands unconditionally. Consider using the [`ifelse`](@ref)
    function instead of `?:` in the loop if it is safe to do so.
* Accesses must have a stride pattern and cannot be "gathers" (random-index
    reads) or "scatters" (random-index writes).
* The stride should be unit stride.

!!! note
    The `@simd` does not assert by default that the loop is completely free of loop-carried
    memory dependencies, which is an assumption that can easily be violated in generic code.
    If you are writing non-generic code, you can use `@simd ivdep for ... end` to also assert that:

* There exists no loop-carried memory dependencies
* No iteration ever waits on a previous iteration to make forward progress.
"""
macro simd(forloop)
    compile(forloop, nothing)
end
```
-/
def macro_simd (lo : LeafOps L) (forloop : Value L) : Except Error (Value L) :=
  compile lo forloop (.leaf lo.nothing)
/--
Julia source: base/simdloop.jl:130-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

macro simd(ivdep, forloop)
    if ivdep === :ivdep
        compile(forloop, Symbol("julia.ivdep"))
    else
        throw(SimdError("Only ivdep is valid as the first argument to @simd"))
    end
end
```
-/
def macro_simd_ivdep (lo : LeafOps L) (ivdep forloop : Value L) : Except Error (Value L) :=
  if ivdep matches .symbol "ivdep" then compile lo forloop (.symbol "julia.ivdep")
  else throw (simdError "Only ivdep is valid as the first argument to @simd")
-- Reason: The module end is load-time structure.
-- UNTRANSLATED
-- Source: base/simdloop.jl:138-139 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end # module SimdLoop
-- /Source

end

end JuliaLean.base.simdloop



/-!
# `@simd` syntax processing (`base/simdloop.jl`)
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

inductive SExpr where
  | atom (name : String)
  | symbol (name : String)
  | quote (value : SExpr)
  | expr (head : String) (args : List SExpr)
  deriving Repr

/-- `parse_iteration_space`, `base/simdloop.jl:17-22`. -/
def parseIterationSpace : SExpr → R (String × SExpr)
  | .expr head args =>
      if head ≠ "=" ∧ head ≠ "in" then .error (.simdError "= or in expected")
      else match args with
      | [.symbol var, range] => .ok (var, range)
      | [_, _] => .error (.simdError "simd loop index must be a symbol")
      | _ => .error (.simdError "simd range syntax is wrong")
  | _ => .error (.simdError "= or in expected")

mutual
/-- The recursive search performed by `check_body!`, lines 25-37. -/
def forbidden : SExpr → Bool
  | .atom _ | .symbol _ => false
  | .quote value => forbidden value
  | .expr head args =>
      head == "break" || head == "continue" ||
      (head == "macrocall" && isGotoArgs args) ||
      forbiddenArgs args

def forbiddenArgs : List SExpr → Bool
  | [] => false
  | arg :: rest => forbidden arg || forbiddenArgs rest

def isGotoArgs : List SExpr → Bool
  | .symbol name :: _ => name == "@goto"
  | _ => false
end

/-- `check_body!` succeeds exactly when the recursive source-order scan finds
no break, continue or @goto. -/
def checkSimdBody (x : SExpr) : R Bool :=
  if forbidden x then .error (.simdError "invalid control flow inside a @simd loop body")
  else .ok true

/-- The three overridable range helpers, `base/simdloop.jl:48-54`. Lists use
zero-based Lean positions; Julia's `i + firstindex(r)` selects that element. -/
def simdOuterRange (_ : List α) : List Nat := [0]
def simdInnerLength (r : List α) (_j : Nat) : Nat := r.length
def simdIndex (r : List α) (_j i : Nat) : R α :=
  match r[i]? with | some value => .ok value | none => jthrow .boundsError

structure SimdCompiled where
  varName : String
  range : SExpr
  body : SExpr
  ivdep : Option String
  deriving Repr

/-- `compile(x, ivdep)`, `base/simdloop.jl:57-88`. `SimdCompiled` records
the variable, once-evaluated range, loop body and loopinfo dependency flag of
the returned quote; the scalar/inner loop skeleton is fixed. -/
def compileSimd (x : SExpr) (ivdep : Option String) : R SimdCompiled :=
  match x with
  | .expr head args =>
      if head ≠ "for" then .error (.simdError "for loop expected")
      else match args with
      | [iteration, body] => do
          let _ ← checkSimdBody x
          let (varName, range) ← parseIterationSpace iteration
          pure { varName, range, body, ivdep }
      | _ => .error (.simdError "1D for loop expected")
  | _ => .error (.simdError "for loop expected")

/-- The two `@simd` macro methods, lines 127-137. -/
def simdMacro (forloop : SExpr) : R SimdCompiled := compileSimd forloop none
def simdIvdepMacro (tag : String) (forloop : SExpr) : R SimdCompiled :=
  if tag = "ivdep" then compileSimd forloop (some "julia.ivdep")
  else .error (.simdError "Only ivdep is valid as the first argument to @simd")
end JuliaLean.IteratorsCov
