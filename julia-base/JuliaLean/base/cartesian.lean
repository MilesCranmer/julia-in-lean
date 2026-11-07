import JuliaLean.Core
import JuliaLean.base.expr

/-!
# Model of `base/cartesian.jl`

The `Base.Cartesian` macros of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`, over the
installed `base/expr.jl` model (`JuliaLean.base.expr.Value`). As in that model, a macro is a
function of its arguments returning the expansion, and the mutable `Expr` is represented by its
contents: a method that mutates a copy returns the updated value.

* A `quote` block of this file is the `Expr(:block, ...)` the parser builds for it, with a
  `LineNumberNode` for each source line it covers; Base records this file as `cartesian.jl`.
* Values that are not syntax nodes (numbers, arrays, `nothing`, ...) are leaves of type `L`.
  The Base methods applied to them (`+`, `<`, `==`, `getindex`, `string`, the `Int`
  conversion of `LReplace`) are the typed operations of `CartOps`, with no assumed laws.
* A `Symbol` name is a Lean `String`, so `lreplace_string!` walks characters; on valid UTF-8 its
  index arithmetic (`nextind`, `prevind`, `str[i:end]`) is character arithmetic.
* Julia exceptions are `CartError`: those of the `expr` model, `UndefVarError`, and an exception
  object thrown by a leaf operation.
-/

namespace JuliaLean.base.cartesian

open JuliaLean
open JuliaLean.base.expr (Value LeafOps ExprError Sym esc i64)

/-- Exceptions thrown by the modelled methods. -/
inductive CartError (L : Type) where
  | expr (e : ExprError)
  /-- `UndefVarError(name)` of reading an unassigned local. -/
  | undefVarError (name : Sym)
  /-- An exception thrown by a Base method applied to leaf values. -/
  | thrown (exception : L)

abbrev CartResult (L α : Type) := Except (CartError L) α

/-- Base methods on non-syntax values. -/
structure CartOps (L : Type) where
  lo : LeafOps L
  /-- `x::Int`; `none` when `x` is not an `Int`. -/
  asInt : L → Option JInt64
  /-- The `Int` conversion of `LReplace(sym, val::Integer)`; `none` when `val` is not an
  `Integer` (no `LReplace` method applies). -/
  toInt : L → Option (CartResult L JInt64)
  /-- `x isa Number`. -/
  isNumber : L → Bool
  /-- `x isa Real`. -/
  isReal : L → Bool
  /-- `x isa Array`. -/
  isArray : L → Bool
  /-- `string(x)`. -/
  string : Value L → CartResult L String
  /-- `f(args...)` for `f` the function `exprresolve_arith_dict` maps the symbol to. -/
  arith : Sym → List L → CartResult L (Value L)
  /-- `f(a, b)` for `f` the function `exprresolve_cond_dict` maps the symbol to; `none` when
  the result is not a `Bool`. -/
  compare : Sym → L → L → CartResult L (Option Bool)
  /-- `x == 0`; `none` when the result is not a `Bool`. -/
  eqZero : L → CartResult L (Option Bool)
  /-- `A[i...]`. -/
  getindex : L → List L → CartResult L (Value L)
  /-- The elements of `N-1:-1:1` for an `N` that is not an `Int`. -/
  countdown : Value L → CartResult L (List (Value L))

/-- The value `inlineanonymous` substitutes: an `Int`, or another value. -/
inductive Ext (L : Type) where
  | int (i : JInt64)
  | other (v : Value L)

section
variable {L : Type} (ops : CartOps L)

def argumentError (msg : String) : CartError L := .expr (.jl (.argumentError msg))
def methodError (fn : String) : CartError L := .expr (.jl (.methodError fn))
def typeError : CartError L := .expr .typeError

/-- `args[i]` (1-based). -/
def argAt (args : List (Value L)) (i : Nat) : CartResult L (Value L) :=
  match JuliaLean.base.expr.argAt args i with
  | .ok v => .ok v
  | .error e => .error (.expr e)

/-- An `Int` leaf. -/
def intV (i : JInt64) : Value L := .leaf (ops.lo.ofInt i)

/-- The `nothing` leaf. -/
def nothingV : Value L := .leaf ops.lo.nothing

/-- `x === nothing`. -/
def isNothingV : Value L → Bool
  | .leaf x => ops.lo.isNothing x
  | _ => false

/-- The `LineNumberNode` the parser records for a line of this file. -/
def lnn (line : Int) : Value L := .lineNumberNode (i64 line) (.symbol "cartesian.jl")

/-- `Symbol(name)`. -/
def mkSymbol (name : String) : CartResult L (Value L) :=
  if name.contains '\x00' then throw (argumentError "Symbol name may not contain \\0")
  else pure (.symbol name)

/-- The elements of `1:N`. -/
def oneTo (n : JInt64) : List JInt64 := (List.range n.val.toNat).map (fun (k : Nat) => i64 (k + 1))

/-- `x::Int` for a macro argument. -/
def intArg (fn : String) : Value L → CartResult L JInt64
  | .leaf x => match ops.asInt x with
    | some i => pure i
    | none => throw (methodError fn)
  | _ => throw (methodError fn)

/-- An `Expr` argument, for a method whose signature requires `Expr`. -/
def exprArg (fn : String) : Value L → CartResult L (Sym × List (Value L))
  | .expr h a => pure (h, a)
  | _ => throw (methodError fn)

/-- A `Symbol` argument, for a method whose signature requires `Symbol`. -/
def symArg (fn : String) : Value L → CartResult L Sym
  | .symbol s => pure s
  | _ => throw (methodError fn)

/-- `x isa Number`. -/
def isNumberV : Value L → Bool
  | .leaf x => ops.isNumber x
  | _ => false

/-- `x isa Real`. -/
def isRealV : Value L → Bool
  | .leaf x => ops.isReal x
  | _ => false

/-- `x == 0`: values that are not leaves use the fallback `===`, which is `false`. -/
def eqZeroV : Value L → CartResult L (Option Bool)
  | .leaf x => ops.eqZero x
  | _ => pure (some false)

/-- The leaf values of a list whose elements are all leaves. -/
def leaves : List (Value L) → Option (List L)
  | [] => some []
  | .leaf x :: rest => (leaves rest).map (x :: ·)
  | _ :: _ => none

/-- `a isa LineNumberNode || a isa Expr && a.head === :line`. -/
def isLine : Value L → Bool
  | .lineNumberNode .. => true
  | .expr "line" _ => true
  | _ => false

-- Reason: The module header and export list are load-time structure.
-- UNTRANSLATED
-- Source: base/cartesian.jl:1-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module Cartesian
-- 
-- export @nloops, @nref, @ncall, @ncallkw, @nexprs, @nextract, @nall, @nany, @ntuple, @nif
-- 
-- ### Cartesian-specific macros
-- 
-- /Source

/--
Julia source: base/cartesian.jl:280-292 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Replace a symbol by a value or a "coded" symbol
# E.g., for d = 3,
#    lreplace(:d, :d, 3) -> 3
#    lreplace(:i_d, :d, 3) -> :i_3
#    lreplace(:i_{d-1}, :d, 3) -> :i_2
# This follows LaTeX notation.
struct LReplace{S<:AbstractString}
    pat_sym::Symbol
    pat_str::S
    val::Int
end
LReplace(sym::Symbol, val::Integer) = LReplace(sym, string(sym), val)
```
-/
-- `LReplace(pat_sym, pat_str, val)`.
structure LReplace where
  pat_sym : Sym
  pat_str : String
  val : JInt64

/-- `LReplace(sym::Symbol, val::Integer)`, with `val` converted to `Int`. -/
def LReplace.ofSym (sym : Sym) (val : JInt64) : LReplace := ⟨sym, sym, val⟩
mutual
/--
Julia source: base/cartesian.jl:301-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function lreplace_string!(str::String, r::LReplace)
    i = firstindex(str)
    pat = r.pat_str
    j = firstindex(pat)
    matching = false
    local istart::Int
    while i <= ncodeunits(str)
        cstr = str[i]
        i = nextind(str, i)
        if !matching
            if cstr != '_' || i > ncodeunits(str)
                continue
            end
            istart = i
            cstr = str[i]
            i = nextind(str, i)
        end
        if j <= lastindex(pat)
            cr = pat[j]
            j = nextind(pat, j)
            if cstr == cr
                matching = true
            else
                matching = false
                j = firstindex(pat)
                i = istart
                continue
            end
        end
        if matching && j > lastindex(pat)
            if i > lastindex(str) || str[i] == '_'
                # We have a match
                return string(str[1:prevind(str, istart)], r.val, lreplace_string!(str[i:end], r))
            end
            matching = false
            j = firstindex(pat)
            i = istart
        end
    end
    str
end
```
-/
-- The loop of `lreplace_string!` while `matching` is false (then `j` is `firstindex(pat)`):
-- `i` is the 1-based character index of the next read.
def lreplace_scan (s pat : List Char) (val : JInt64) (i j : Nat) : String :=
  if h : i ≤ s.length then
    -- `cstr = str[i]; i = nextind(str, i)`
    if hc : s.getD (i - 1) ' ' != '_' then lreplace_scan s pat val (i + 1) j
    else if hi : i + 1 > s.length then lreplace_scan s pat val (i + 1) j
    else
      -- `istart = i; cstr = str[i]; i = nextind(str, i)`, with `istart = i + 1`
      let cstr := s.getD i ' '
      if j ≤ pat.length then
        if cstr == pat.getD (j - 1) ' ' then
          if j + 1 > pat.length then
            if i + 2 > s.length || s.getD (i + 1) ' ' == '_' then
              String.ofList (s.take i) ++ toString val.val ++ lreplace_string_chars (s.drop (i + 1)) pat val
            else lreplace_scan s pat val (i + 1) 1
          else lreplace_match s pat val (i + 2) (j + 1) (i + 1) (by omega)
        else lreplace_scan s pat val (i + 1) 1
      else lreplace_scan s pat val (i + 2) j
  else String.ofList s
termination_by (s.length, s.length + 1 - i, s.length + 2 - i)
/-- The loop of `lreplace_string!` while `matching` is true; `istart` is the index after the
`'_'` that began the match. -/
def lreplace_match (s pat : List Char) (val : JInt64) (i j istart : Nat)
    (hstart : 1 ≤ istart ∧ istart ≤ i) : String :=
  if h : i ≤ s.length then
    let cstr := s.getD (i - 1) ' '
    if j ≤ pat.length then
      if cstr == pat.getD (j - 1) ' ' then
        if j + 1 > pat.length then
          if i + 1 > s.length || s.getD i ' ' == '_' then
            String.ofList (s.take (istart - 1)) ++ toString val.val ++
              lreplace_string_chars (s.drop i) pat val
          else lreplace_scan s pat val istart 1
        else lreplace_match s pat val (i + 1) (j + 1) istart (by omega)
      else lreplace_scan s pat val istart 1
    else
      if i + 1 > s.length || s.getD i ' ' == '_' then
        String.ofList (s.take (istart - 1)) ++ toString val.val ++ lreplace_string_chars (s.drop i) pat val
      else lreplace_scan s pat val istart 1
  else String.ofList s
termination_by (s.length, s.length + 2 - istart, s.length + 2 - i)
/-- `lreplace_string!(str, r)` on the characters of `str`. -/
def lreplace_string_chars (s pat : List Char) (val : JInt64) : String :=
  lreplace_scan s pat val 1 1
termination_by (s.length, s.length + 3, 0)
end

/-- `lreplace_string!(str, r)`. -/
def lreplace_string (str : String) (r : LReplace) : String :=
  lreplace_string_chars str.toList r.pat_str.toList r.val
/--
Julia source: base/cartesian.jl:295-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function lreplace!(sym::Symbol, r::LReplace, in_quote_context::Bool, escs::Int)
    escs == 0 || return sym
    sym == r.pat_sym && return r.val
    Symbol(lreplace_string!(string(sym), r))
end
```
-/
def lreplace_sym (s : Sym) (r : LReplace) (escs : Nat) : CartResult L (Value L) :=
  if escs != 0 then pure (.symbol s)
  else if s == r.pat_sym then pure (intV ops r.val)
  else mkSymbol (lreplace_string s r)
/--
Julia source: base/cartesian.jl:380-399 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia


# If a block expression contains one non-linenode arg, extract it
poplinenum(arg) = arg
function poplinenum(ex::Expr)
    if ex.head === :block
        arg_out = nothing
        for i in 1:length(ex.args)
            a = ex.args[i]
            if !(a isa LineNumberNode || a isa Expr && a.head === :line)
                if arg_out === nothing
                    arg_out = a
                else
                    return ex
                end
            end
        end
    end
    return arg_out === nothing ? ex : arg_out
end
```
-/
-- The scan of a `:block`'s arguments for its one non-line argument.
def poplinenum_loop (ex : Value L) (arg_out : Value L) : List (Value L) → Value L
  | [] => if isNothingV ops arg_out then ex else arg_out
  | a :: rest =>
    if !isLine a then
      if isNothingV ops arg_out then poplinenum_loop ex a rest else ex
    else poplinenum_loop ex arg_out rest

/-- `poplinenum(ex)`. For an `Expr` whose head is not `:block` the local `arg_out` is never
assigned, so reading it throws `UndefVarError(:arg_out)`. -/
def poplinenum : Value L → CartResult L (Value L)
  | .expr "block" args => pure (poplinenum_loop ops (.expr "block" args) (nothingV ops) args)
  | .expr _ _ => throw (.undefVarError "arg_out")
  | v => pure v
/--
Julia source: base/cartesian.jl:400-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## Resolve expressions at parsing time ##

const exprresolve_arith_dict = IdDict{Symbol,Function}(:+ => +,
    :- => -, :* => *, :/ => /, :^ => ^, :div => div)
const exprresolve_cond_dict = IdDict{Symbol,Function}(:(==) => ==,
    :(<) => <, :(>) => >, :(<=) => <=, :(>=) => >=)
```
-/
-- The keys of `exprresolve_arith_dict`; each maps to the Base function of that name.
def exprresolve_arith_dict : List Sym := ["+", "-", "*", "/", "^", "div"]
/-- The keys of `exprresolve_cond_dict`; each maps to the Base function of that name. -/
def exprresolve_cond_dict : List Sym := ["==", "<", ">", "<=", ">="]
/--
Julia source: base/cartesian.jl:407-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function exprresolve_arith(ex::Expr)
    if ex.head === :call
        callee = ex.args[1]
        if isa(callee, Symbol)
            if haskey(exprresolve_arith_dict, callee) && all(Bool[isa(ex.args[i], Number) for i = 2:length(ex.args)])
                return true, exprresolve_arith_dict[callee](ex.args[2:end]...)
            end
        end
    end
    false, 0
end
exprresolve_arith(arg) = false, 0
```
-/
def exprresolve_arith : Value L → CartResult L (Bool × Value L)
  | .expr "call" args => do
    let callee ← argAt args 1
    match callee with
    | .symbol c =>
      if exprresolve_arith_dict.contains c && (args.drop 1).all (isNumberV ops) then
        match leaves (args.drop 1) with
        | some xs => return (true, ← ops.arith c xs)
        | none => return (false, intV ops (i64 0))
      else return (false, intV ops (i64 0))
    | _ => return (false, intV ops (i64 0))
  | _ => pure (false, intV ops (i64 0))
/--
Julia source: base/cartesian.jl:420-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

exprresolve_conditional(b::Bool) = true, b
function exprresolve_conditional(ex::Expr)
    if ex.head === :call
        callee = ex.args[1]
        if isa(callee, Symbol)
            if callee ∈ keys(exprresolve_cond_dict) && isa(ex.args[2], Number) && isa(ex.args[3], Number)
                return true, exprresolve_cond_dict[callee](ex.args[2], ex.args[3])
            end
        end
    elseif Meta.isexpr(ex, :block, 2) && ex.args[1] isa LineNumberNode
        return exprresolve_conditional(ex.args[2])
    end
    false, false
end
exprresolve_conditional(arg) = false, false
```
-/
-- `exprresolve_conditional(ex)`: whether the condition can be evaluated, and its value (`none`
-- when that value is not a `Bool`).
def exprresolve_conditional : Value L → CartResult L (Bool × Option Bool)
  | .leaf x => match ops.lo.asBool x with
    | some b => pure (true, some b)
    | none => pure (false, some false)
  | .expr "call" args => do
    let callee ← argAt args 1
    match callee with
    | .symbol c =>
      if exprresolve_cond_dict.contains c then
        let a2 ← argAt args 2
        if !isNumberV ops a2 then return (false, some false)
        let a3 ← argAt args 3
        if !isNumberV ops a3 then return (false, some false)
        match a2, a3 with
        | .leaf a, .leaf b => return (true, ← ops.compare c a b)
        | _, _ => return (false, some false)
      else return (false, some false)
    | _ => return (false, some false)
  | .expr "block" [.lineNumberNode _ _, a2] => exprresolve_conditional a2
  | _ => pure (false, some false)
/--
Julia source: base/cartesian.jl:436-473 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

exprresolve(arg) = arg
function exprresolve(ex::Expr)
    for i = 1:length(ex.args)
        ex.args[i] = exprresolve(ex.args[i])
    end
    # Handle simple arithmetic
    can_eval, result = exprresolve_arith(ex)
    if can_eval
        return result
    elseif ex.head === :call && (ex.args[1] === :+ || ex.args[1] === :-) && length(ex.args) == 3 && ex.args[3] == 0
        # simplify x+0 and x-0
        return ex.args[2]
    end
    # Resolve array references
    if ex.head === :ref && isa(ex.args[1], Array)
        for i = 2:length(ex.args)
            if !isa(ex.args[i], Real)
                return ex
            end
        end
        return ex.args[1][ex.args[2:end]...]
    end
    # Resolve conditionals
    if ex.head === :if || ex.head === :elseif
        can_eval, tf = exprresolve_conditional(ex.args[1])
        if can_eval
            if tf
                return ex.args[2]
            elseif length(ex.args) == 3
                return ex.args[3]
            else
                return nothing
            end
        end
    end
    ex
end
```
-/
-- `exprresolve` of an `Expr` whose arguments are already resolved.
def exprresolve_node (head : Sym) (args : List (Value L)) : CartResult L (Value L) := do
  let ex : Value L := .expr head args
  -- Handle simple arithmetic
  let (can_eval, result) ← exprresolve_arith ops ex
  if can_eval then return result
  if head == "call" then
    let a1 ← argAt args 1
    if (a1 matches .symbol "+" || a1 matches .symbol "-") && args.length == 3 then
      match ← eqZeroV ops (← argAt args 3) with
      | some true => return (← argAt args 2)
      | some false => pure ()
      | none => throw typeError
  -- Resolve array references
  if head == "ref" then
    match ← argAt args 1 with
    | .leaf a =>
      if ops.isArray a then
        if !(args.drop 1).all (isRealV ops) then return ex
        match leaves (args.drop 1) with
        | some is => return (← ops.getindex a is)
        | none => return ex
    | _ => pure ()
  -- Resolve conditionals
  if head == "if" || head == "elseif" then
    let (can_eval, tf) ← exprresolve_conditional ops (← argAt args 1)
    if can_eval then
      match tf with
      | some true => return (← argAt args 2)
      | some false => return (← if args.length == 3 then argAt args 3 else pure (nothingV ops))
      | none => throw typeError
  return ex

mutual
def exprresolve : Value L → CartResult L (Value L)
  | .expr head args => do exprresolve_node ops head (← exprresolve_args args)
  | v => pure v
def exprresolve_args : List (Value L) → CartResult L (List (Value L))
  | [] => pure []
  | a :: rest => do
    let a ← exprresolve a
    return a :: (← exprresolve_args rest)
end
mutual
/--
Julia source: base/cartesian.jl:343-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function lreplace!(ex::Expr, r::LReplace, in_quote_context::Bool, escs::Int)
    # Curly-brace notation, which acts like parentheses
    if !in_quote_context && ex.head === :curly && length(ex.args) == 2 && isa(ex.args[1], Symbol) && endswith(string(ex.args[1]::Symbol), "_")
        excurly = exprresolve(lreplace!(ex.args[2], r, in_quote_context, escs))
        if isa(excurly, Int)
            return Symbol(ex.args[1]::Symbol, excurly)
        else
            ex.args[2] = excurly
            return ex
        end
    elseif ex.head === :meta || ex.head === :inert
        return ex
    elseif ex.head === :$
        # no longer an executable expression (handle all equivalent forms of :inert, :quote, and QuoteNode the same way)
        in_quote_context = false
    elseif ex.head === :quote
        # executable again
        in_quote_context = true
    elseif ex.head === :var"hygienic-scope"
        # no longer our expression
        escs += 1
    elseif ex.head === :escape
        # our expression again once zero
        escs == 0 && return ex
        escs -= 1
    elseif ex.head === :macrocall
        # n.b. blithely go about altering arguments to macros also, assuming that is at all what the user intended
        # it is probably the user's fault if they put a macro inside here and didn't mean for it to get rewritten
    end
    for i in 1:length(ex.args)
        ex.args[i] = lreplace!(ex.args[i], r, in_quote_context, escs)
    end
    ex
end

lreplace!(@nospecialize(arg), r::LReplace, in_quote_context::Bool, escs::Int) = arg
```
-/
-- `lreplace!(ex, r, in_quote_context, escs)`.
def lreplace_v (r : LReplace) (in_quote_context : Bool) (escs : Nat) :
    Value L → CartResult L (Value L)
  | .symbol s => lreplace_sym ops s r escs
  | .expr head args =>
    -- Curly-brace notation, which acts like parentheses
    match args with
    | [.symbol a1, a2] =>
      if !in_quote_context && head == "curly" && a1.endsWith "_" then do
        let excurly ← exprresolve ops (← lreplace_v r in_quote_context escs a2)
        match excurly with
        | .leaf x => match ops.asInt x with
          | some k => mkSymbol (a1 ++ toString k.val)
          | none => pure (.expr head [.symbol a1, excurly])
        | _ => pure (.expr head [.symbol a1, excurly])
      else lreplace_node r in_quote_context escs head [.symbol a1, a2]
    | args => lreplace_node r in_quote_context escs head args
  | v => pure v
termination_by v => (sizeOf v, 1)
/-- `lreplace!` of an `Expr` that is not the curly-brace notation. -/
def lreplace_node (r : LReplace) (in_quote_context : Bool) (escs : Nat) (head : Sym)
    (args : List (Value L)) : CartResult L (Value L) :=
  if head == "meta" || head == "inert" then pure (.expr head args)
  else if head == "$" then do
    -- no longer an executable expression
    return .expr head (← lreplace_args r false escs args)
  else if head == "quote" then do
    -- executable again
    return .expr head (← lreplace_args r true escs args)
  else if head == "hygienic-scope" then do
    -- no longer our expression
    return .expr head (← lreplace_args r in_quote_context (escs + 1) args)
  else if head == "escape" then
    -- our expression again once zero
    if escs == 0 then pure (.expr head args)
    else do return .expr head (← lreplace_args r in_quote_context (escs - 1) args)
  else do
    return .expr head (← lreplace_args r in_quote_context escs args)
termination_by (1 + sizeOf head + sizeOf args, 0)
def lreplace_args (r : LReplace) (in_quote_context : Bool) (escs : Nat) :
    List (Value L) → CartResult L (List (Value L))
  | [] => pure []
  | a :: rest => do
    let a ← lreplace_v r in_quote_context escs a
    return a :: (← lreplace_args r in_quote_context escs rest)
termination_by as => (sizeOf as, 0)
end
/--
Julia source: base/cartesian.jl:293-294 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

lreplace(ex::Expr, sym::Symbol, val) = lreplace!(copy(ex), LReplace(sym, val), false, 0)
```
-/
-- `lreplace(ex, sym, val)` for an `Expr` `ex`, after the `Int` conversion of `val`.
def lreplace (head : Sym) (args : List (Value L)) (sym : Sym) (val : JInt64) :
    CartResult L (Value L) :=
  lreplace_v ops (LReplace.ofSym sym val) false 0 (.expr head args)
/--
Julia source: base/cartesian.jl:260-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

## Utilities

# Simplify expressions like :(d->3:size(A,d)-3) given an explicit value for d
function inlineanonymous(ex::Expr, val)
    if ex.head !== :->
        throw(ArgumentError("not an anonymous function"))
    end
    if !isa(ex.args[1], Symbol)
        throw(ArgumentError("not a single-argument anonymous function"))
    end
    sym = ex.args[1]::Symbol
    ex = ex.args[2]::Expr
    exout = lreplace(ex, sym, val)
    exout = poplinenum(exout)
    exprresolve(exout)
end

# Given :i and 3, this generates :i_3
inlineanonymous(base::Symbol, ext) = Symbol(base,'_',ext)
```
-/
-- The `Int` conversion `LReplace(sym, val::Integer)` applies to `val`.
def lreplaceVal : Ext L → CartResult L JInt64
  | .int i => pure i
  | .other (.leaf x) => match ops.toInt x with
    | some r => r
    | none => throw (methodError "LReplace")
  | .other _ => throw (methodError "LReplace")

/-- `string(ext)`. -/
def extString : Ext L → CartResult L String
  | .int i => pure (toString i.val)
  | .other v => ops.string v

/-- `inlineanonymous(ex, val)`, dispatching on `ex`. -/
def inlineanonymous (ex : Value L) (val : Ext L) : CartResult L (Value L) :=
  match ex with
  | .expr head args => do
    if head != "->" then throw (argumentError "not an anonymous function")
    match ← argAt args 1 with
    | .symbol sym =>
      match ← argAt args 2 with
      | .expr bh bargs => do
        let exout ← lreplace ops bh bargs sym (← lreplaceVal ops val)
        let exout ← poplinenum ops exout
        exprresolve ops exout
      | _ => throw typeError
    | _ => throw (argumentError "not a single-argument anonymous function")
  -- Given :i and 3, this generates :i_3
  | .symbol base => do mkSymbol (base ++ "_" ++ (← extString ops val))
  | _ => throw (methodError "inlineanonymous")
/--
Julia source: base/cartesian.jl:45-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _nloops(N::Int, itersym::Symbol, esc_rng::Bool, rangeexpr::Expr, args::Expr...)
    if rangeexpr.head !== :->
        throw(ArgumentError("second argument must be an anonymous function expression to compute the range"))
    end
    if !(1 <= length(args) <= 3)
        throw(ArgumentError("number of arguments must be 1 ≤ length(args) ≤ 3, got $(length(args))"))
    end
    body = args[end]
    ex = Expr(:escape, body)
    for dim = 1:N
        itervar = inlineanonymous(itersym, dim)
        itervar = esc(itervar)
        rng = inlineanonymous(rangeexpr, dim)
        esc_rng && (rng = esc(rng))
        preexpr = length(args) > 1 ? esc(inlineanonymous(args[1], dim)) : nothing
        postexpr = length(args) > 2 ? esc(inlineanonymous(args[2], dim)) : nothing
        ex = quote
            for $itervar = $rng
                $preexpr
                $ex
                $postexpr
            end
        end
    end
    ex
end
```
-/
def _nloops_expr (N : JInt64) (itersym : Sym) (esc_rng : Bool) (rh : Sym)
    (rargs : List (Value L)) (args : List (Value L)) : CartResult L (Value L) := do
  if rh != "->" then
    throw (argumentError "second argument must be an anonymous function expression to compute the range")
  if !(1 ≤ args.length ∧ args.length ≤ 3) then
    throw (argumentError
      ("number of arguments must be 1 ≤ length(args) ≤ 3, got " ++ toString args.length))
  let body ← argAt args args.length
  (oneTo N).foldlM (init := (Value.expr "escape" [body] : Value L)) fun ex dim => do
    let itervar ← inlineanonymous ops (.symbol itersym) (.int dim)
    let itervar := esc itervar
    let rng ← inlineanonymous ops (.expr rh rargs) (.int dim)
    let rng := if esc_rng then esc rng else rng
    let preexpr ← if args.length > 1 then
        pure (esc (← inlineanonymous ops (← argAt args 1) (.int dim)))
      else pure (nothingV ops)
    let postexpr ← if args.length > 2 then
        pure (esc (← inlineanonymous ops (← argAt args 2) (.int dim)))
      else pure (nothingV ops)
    return .expr "block" [lnn 63,
      .expr "for" [.expr "=" [itervar, rng],
        .expr "block" [lnn 64, preexpr, lnn 65, ex, lnn 66, postexpr, lnn 67]]]
/--
Julia source: base/cartesian.jl:41-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _nloops(N::Int, itersym::Symbol, esc_rng::Bool, arraysym::Symbol, args::Expr...)
    _nloops(N, itersym, false, :(d->axes($(esc(arraysym)), d)), args...)
end
```
-/
def _nloops_sym (N : JInt64) (itersym : Sym) (_esc_rng : Bool) (arraysym : Sym)
    (args : List (Value L)) : CartResult L (Value L) :=
  _nloops_expr ops N itersym false "->"
    [.symbol "d", .expr "block" [lnn 43, .expr "call" [.symbol "axes", esc (.symbol arraysym), .symbol "d"]]]
    args

/-- `_nloops(N, itersym, esc_rng, rangeexpr, args...)`, dispatching on the argument types. -/
def _nloops (N itersym : Value L) (esc_rng : Bool) (rangeexpr : Value L) (args : List (Value L)) :
    CartResult L (Value L) := do
  let N ← intArg ops "_nloops" N
  let itersym ← symArg "_nloops" itersym
  if !args.all (· matches .expr ..) then throw (methodError "_nloops")
  match rangeexpr with
  | .symbol arraysym => _nloops_sym ops N itersym esc_rng arraysym args
  | .expr rh rargs => _nloops_expr ops N itersym esc_rng rh rargs args
  | _ => throw (methodError "_nloops")
/--
Julia source: base/cartesian.jl:9-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @nloops N itersym rangeexpr bodyexpr
    @nloops N itersym rangeexpr preexpr bodyexpr
    @nloops N itersym rangeexpr preexpr postexpr bodyexpr

Generate `N` nested loops, using `itersym` as the prefix for the iteration variables.
`rangeexpr` may be an anonymous-function expression, or a simple symbol `var` in which case
the range is `axes(var, d)` for dimension `d`.

Optionally, you can provide "pre" and "post" expressions. These get executed first and last,
respectively, in the body of each loop. For example:

    @nloops 2 i A d -> j_d = min(i_d, 5) begin
        s += @nref 2 A j
    end

would generate:

    for i_2 = axes(A, 2)
        j_2 = min(i_2, 5)
        for i_1 = axes(A, 1)
            j_1 = min(i_1, 5)
            s += A[j_1, j_2]
        end
    end

If you want just a post-expression, supply [`nothing`](@ref) for the pre-expression. Using
parentheses and semicolons, you can supply multi-statement expressions.
"""
macro nloops(N, itersym, rangeexpr, args...)
    _nloops(N, itersym, true, rangeexpr, args...)
end
```
-/
def macro_nloops (N itersym rangeexpr : Value L) (args : List (Value L)) : CartResult L (Value L) :=
  _nloops ops N itersym true rangeexpr args
/--
Julia source: base/cartesian.jl:72-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @nref N A indexexpr

Generate expressions like `A[i_1, i_2, ...]`. `indexexpr` can either be an iteration-symbol
prefix, or an anonymous-function expression.

# Examples
```jldoctest
julia> @macroexpand Base.Cartesian.@nref 3 A i
:(A[i_1, i_2, i_3])
```
"""
macro nref(N::Int, A::Symbol, ex)
    vars = Any[ inlineanonymous(ex,i) for i = 1:N ]
    Expr(:escape, Expr(:ref, A, vars...))
end
````
-/
def macro_nref (N A ex : Value L) : CartResult L (Value L) := do
  let N ← intArg ops "@nref" N
  let A ← symArg "@nref" A
  let vars ← (oneTo N).mapM fun i => inlineanonymous ops ex (.int i)
  return .expr "escape" [.expr "ref" (.symbol A :: vars)]
/--
Julia source: base/cartesian.jl:89-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @ncall N f sym...

Generate a function call expression. `sym` represents any number of function arguments, the
last of which may be an anonymous-function expression and is expanded into `N` arguments.

For example, `@ncall 3 func a` generates

    func(a_1, a_2, a_3)

while `@ncall 2 func a b i->c[i]` yields

    func(a, b, c[1], c[2])

"""
macro ncall(N::Int, f, args...)
    pre = args[1:end-1]
    ex = args[end]
    vars = (inlineanonymous(ex, i) for i = 1:N)
    Expr(:escape, Expr(:call, f, pre..., vars...))
end
```
-/
def macro_ncall (N f : Value L) (args : List (Value L)) : CartResult L (Value L) := do
  let N ← intArg ops "@ncall" N
  let pre := args.take (args.length - 1)
  let ex ← argAt args args.length
  let vars ← (oneTo N).mapM fun i => inlineanonymous ops ex (.int i)
  return .expr "escape" [.expr "call" (f :: pre ++ vars)]
/--
Julia source: base/cartesian.jl:111-138 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @ncallkw N f kw sym...

Generate a function call expression with keyword arguments `kw...`. As
in the case of [`@ncall`](@ref), `sym` represents any number of function arguments, the
last of which may be an anonymous-function expression and is expanded into `N` arguments.

# Examples
```jldoctest
julia> using Base.Cartesian

julia> f(x...; a, b = 1, c = 2, d = 3) = +(x..., a, b, c, d);

julia> x_1, x_2 = (-1, -2); b = 0; kw = (c = 0, d = 0);

julia> @ncallkw 2 f (; a = 0, b, kw...) x
-3

```
"""
macro ncallkw(N::Int, f, kw, args...)
    pre = args[1:end-1]
    ex = args[end]
    vars = (inlineanonymous(ex, i) for i = 1:N)
    param = Expr(:parameters, Expr(:(...), kw))
    Expr(:escape, Expr(:call, f, param, pre..., vars...))
end
````
-/
def macro_ncallkw (N f kw : Value L) (args : List (Value L)) : CartResult L (Value L) := do
  let N ← intArg ops "@ncallkw" N
  let pre := args.take (args.length - 1)
  let ex ← argAt args args.length
  let vars ← (oneTo N).mapM fun i => inlineanonymous ops ex (.int i)
  let param : Value L := .expr "parameters" [.expr "..." [kw]]
  return .expr "escape" [.expr "call" (f :: param :: pre ++ vars)]
/--
Julia source: base/cartesian.jl:139-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @nexprs N expr

Generate `N` expressions. `expr` should be an anonymous-function expression.

# Examples
```jldoctest
julia> @macroexpand Base.Cartesian.@nexprs 4 i -> y[i] = A[i+j]
quote
    y[1] = A[1 + j]
    y[2] = A[2 + j]
    y[3] = A[3 + j]
    y[4] = A[4 + j]
end
```
"""
macro nexprs(N::Int, ex::Expr)
    exs = Any[ inlineanonymous(ex,i) for i = 1:N ]
    Expr(:escape, Expr(:block, exs...))
end
````
-/
def macro_nexprs (N ex : Value L) : CartResult L (Value L) := do
  let N ← intArg ops "@nexprs" N
  let _ ← exprArg "@nexprs" ex
  let exs ← (oneTo N).mapM fun i => inlineanonymous ops ex (.int i)
  return .expr "escape" [.expr "block" exs]
/--
Julia source: base/cartesian.jl:160-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @nextract N esym isym

Generate `N` variables `esym_1`, `esym_2`, ..., `esym_N` to extract values from `isym`.
`isym` can be either a `Symbol` or anonymous-function expression.

`@nextract 2 x y` would generate

    x_1 = y[1]
    x_2 = y[2]

while `@nextract 3 x d->y[2d-1]` yields

    x_1 = y[1]
    x_2 = y[3]
    x_3 = y[5]

"""
macro nextract(N::Int, esym::Symbol, isym::Symbol)
    aexprs = Any[ Expr(:escape, Expr(:(=), inlineanonymous(esym, i), :(($isym)[$i]))) for i = 1:N ]
    Expr(:block, aexprs...)
end

macro nextract(N::Int, esym::Symbol, ex::Expr)
    aexprs = Any[ Expr(:escape, Expr(:(=), inlineanonymous(esym, i), inlineanonymous(ex,i))) for i = 1:N ]
    Expr(:block, aexprs...)
end
```
-/
-- `@nextract N esym isym`, dispatching on `isym` (`Symbol` or `Expr`).
def macro_nextract (N esym isym : Value L) : CartResult L (Value L) := do
  let N ← intArg ops "@nextract" N
  let esym ← symArg "@nextract" esym
  match isym with
  | .symbol s => do
    let aexprs ← (oneTo N).mapM fun i => do
      return Value.expr "escape"
        [.expr "=" [← inlineanonymous ops (.symbol esym) (.int i), .expr "ref" [.symbol s, intV ops i]]]
    return .expr "block" aexprs
  | .expr .. => do
    let aexprs ← (oneTo N).mapM fun i => do
      let lhs ← inlineanonymous ops (.symbol esym) (.int i)
      return Value.expr "escape" [.expr "=" [lhs, ← inlineanonymous ops isym (.int i)]]
    return .expr "block" aexprs
  | _ => throw (methodError "@nextract")
/--
Julia source: base/cartesian.jl:188-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @nall N expr

Check whether all of the expressions generated by the anonymous-function expression `expr`
evaluate to `true`.

`@nall 3 d->(i_d > 1)` would generate the expression `(i_1 > 1 && i_2 > 1 && i_3 > 1)`. This
can be convenient for bounds-checking.
"""
macro nall(N::Int, criterion::Expr)
    if criterion.head !== :->
        throw(ArgumentError("second argument must be an anonymous function expression yielding the criterion"))
    end
    conds = Any[ Expr(:escape, inlineanonymous(criterion, i)) for i = 1:N ]
    Expr(:&&, conds...)
end
```
-/
def macro_nall (N criterion : Value L) : CartResult L (Value L) := do
  let N ← intArg ops "@nall" N
  let (head, _) ← exprArg "@nall" criterion
  if head != "->" then
    throw (argumentError "second argument must be an anonymous function expression yielding the criterion")
  let conds ← (oneTo N).mapM fun i => do return esc (← inlineanonymous ops criterion (.int i))
  return .expr "&&" conds
/--
Julia source: base/cartesian.jl:205-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @nany N expr

Check whether any of the expressions generated by the anonymous-function expression `expr`
evaluate to `true`.

`@nany 3 d->(i_d > 1)` would generate the expression `(i_1 > 1 || i_2 > 1 || i_3 > 1)`.
"""
macro nany(N::Int, criterion::Expr)
    if criterion.head !== :->
        error("Second argument must be an anonymous function expression yielding the criterion")
    end
    conds = Any[ Expr(:escape, inlineanonymous(criterion, i)) for i = 1:N ]
    Expr(:||, conds...)
end
```
-/
def macro_nany (N criterion : Value L) : CartResult L (Value L) := do
  let N ← intArg ops "@nany" N
  let (head, _) ← exprArg "@nany" criterion
  if head != "->" then
    throw (.expr (.errorException "Second argument must be an anonymous function expression yielding the criterion"))
  let conds ← (oneTo N).mapM fun i => do return esc (← inlineanonymous ops criterion (.int i))
  return .expr "||" conds
/--
Julia source: base/cartesian.jl:221-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @ntuple N expr

Generates an `N`-tuple. `@ntuple 2 i` would generate `(i_1, i_2)`, and `@ntuple 2 k->k+1`
would generate `(2,3)`.
"""
macro ntuple(N::Int, ex)
    vars = Any[ inlineanonymous(ex,i) for i = 1:N ]
    Expr(:escape, Expr(:tuple, vars...))
end
```
-/
def macro_ntuple (N ex : Value L) : CartResult L (Value L) := do
  let N ← intArg ops "@ntuple" N
  let vars ← (oneTo N).mapM fun i => inlineanonymous ops ex (.int i)
  return .expr "escape" [.expr "tuple" vars]
/--
Julia source: base/cartesian.jl:232-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

"""
    @nif N conditionexpr expr
    @nif N conditionexpr expr elseexpr

Generates a sequence of `if ... elseif ... else ... end` statements. For example:

    @nif 3 d->(i_d > size(A,d)) d->(error("Dimension ", d, " too big")) d->println("All OK")

would generate:

    if i_1 > size(A, 1)
        error("Dimension ", 1, " too big")
    elseif i_2 > size(A, 2)
        error("Dimension ", 2, " too big")
    else
        println("All OK")
    end
"""
macro nif(N, condition, operation...)
    # Handle the final "else"
    ex = esc(inlineanonymous(length(operation) > 1 ? operation[2] : operation[1], N))
    # Make the nested if statements
    for i = N-1:-1:1
        ex = Expr(:if, esc(inlineanonymous(condition,i)), esc(inlineanonymous(operation[1],i)), ex)
    end
    ex
end
```
-/
def macro_nif (N condition : Value L) (operation : List (Value L)) : CartResult L (Value L) := do
  let n : Ext L := match N with
    | .leaf x => match ops.asInt x with
      | some i => .int i
      | none => .other N
    | _ => .other N
  -- Handle the final "else"
  let last ← if operation.length > 1 then argAt operation 2 else argAt operation 1
  let ex := esc (← inlineanonymous ops last n)
  -- Make the nested if statements
  let is : List (Ext L) ← match n with
    | .int k => pure (((List.range (i64 (k.val - 1)).val.toNat).reverse).map fun (m : Nat) => Ext.int (i64 (m + 1)))
    | .other v => do pure ((← ops.countdown v).map Ext.other)
  is.foldlM (init := ex) fun ex i => do
    let c ← inlineanonymous ops condition i
    let o ← inlineanonymous ops (← argAt operation 1) i
    return .expr "if" [esc c, esc o, ex]
-- Reason: The module end is load-time structure.
-- UNTRANSLATED
-- Source: base/cartesian.jl:474-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end
-- /Source

end

end JuliaLean.base.cartesian


namespace JuliaLean.ExprReflect

open JuliaLean

/-! ### `Base.Cartesian` -/

def indexedName (stem : String) (dimension : Nat) : String :=
  stem ++ "_" ++ toString dimension

/-- `@nref`; `base/cartesian.jl:73-88`. -/
def nref (dimensions : Nat) (array stem : String) : Ast :=
  .expr "escape" [.expr "ref" (.atom array ::
    (List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

/-- `@ntuple`; `base/cartesian.jl:222-231`. -/
def ntuple (dimensions : Nat) (stem : String) : Ast :=
  .expr "escape" [.expr "tuple"
    ((List.range dimensions).map fun index => .atom (indexedName stem (index + 1)))]

def loopLayer (iterator array : String) (dimension : Nat) (body : Ast) : Ast :=
  .expr "for" [
    .expr "=" [.atom (indexedName iterator dimension),
      .expr "axes" [.atom array, .int dimension]],
    body]

/-- The documented normalized nest, built inner dimension first so dimension `N`
is outermost; `base/cartesian.jl:25-33,53-70`. -/
def documentedLoops (dimensions : Nat) (iterator array : String) (body : Ast) : Ast :=
  (List.range dimensions).foldl
    (fun nested index => loopLayer iterator array (index + 1) nested)
    (.expr "escape" [body])

def isCompound : Ast → Bool
  | .expr _ _ => true
  | _ => false

/-- Actual `@nloops` dispatch: `args::Expr...` rejects atomic bodies before the
loop builder runs; `base/cartesian.jl:38-70`. -/
def nloops (dimensions : Nat) (iterator array : String) (body : Ast) : Jl Ast :=
  if isCompound body then .ok (documentedLoops dimensions iterator array body)
  else .error (.methodError "Base.Cartesian._nloops")

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

inductive CartesianMacro where | nloops | nref | ncall | ncallkw | nexprs | nextract | nall | nany | ntuple | nif
  deriving Repr, DecidableEq, Inhabited

def cartesianGeneratedCount (kind : CartesianMacro) (dimensions : Nat) : Nat :=
  match kind with
  | .nif => if dimensions = 0 then 0 else dimensions
  | _ => dimensions

def cartesianIndexSequence (dimensions : Nat) : List Nat :=
  (List.range dimensions).map (· + 1)

def ncallArguments (dimensions : Nat) (fixed : List String) (stem : String) : List String :=
  fixed ++ (cartesianIndexSequence dimensions).map fun index => indexedName stem index

def ncallkwShape (dimensions : Nat) (keywords fixed : List String) (stem : String) : List String :=
  keywords ++ ncallArguments dimensions fixed stem

def nexprsShape (dimensions : Nat) (stem : String) : List String :=
  cartesianIndexSequence dimensions |>.map fun index => indexedName stem index

def nextractShape (dimensions : Nat) (stem source : String) : List (String × String) :=
  cartesianIndexSequence dimensions |>.map fun index =>
    (indexedName stem index, source ++ "[" ++ toString index ++ "]")

def nbooleanShape (dimensions : Nat) : List Nat := cartesianIndexSequence dimensions

def nifShape (dimensions : Nat) : List Nat :=
  if dimensions = 0 then [] else cartesianIndexSequence dimensions

inductive SymbolicExpr where
  | value (n : Int) | variable | add (a b : SymbolicExpr) | sub (a b : SymbolicExpr)
  | mul (a b : SymbolicExpr) | div (a b : SymbolicExpr) | neg (a : SymbolicExpr)
  deriving Repr, DecidableEq, Inhabited

def resolveArithmetic : SymbolicExpr → Option Int
  | .value n => some n
  | .variable => none
  | .add a b => do return (← resolveArithmetic a) + (← resolveArithmetic b)
  | .sub a b => do return (← resolveArithmetic a) - (← resolveArithmetic b)
  | .mul a b => do return (← resolveArithmetic a) * (← resolveArithmetic b)
  | .div a b => do
    let denominator ← resolveArithmetic b
    if denominator = 0 then none else return (← resolveArithmetic a).tdiv denominator
  | .neg a => do return -(← resolveArithmetic a)

def indexedSymbol (stem : String) (extension : Int) : String :=
  stem ++ "_" ++ toString extension

inductive ReplaceContext where | executable | quoted | foreignHygiene
  deriving Repr, DecidableEq, Inhabited

def replaceSymbolModel (context : ReplaceContext) (symbol pattern : String) (value : Int) : String :=
  match context with
  | .foreignHygiene => symbol
  | .quoted => symbol
  | .executable => if symbol == pattern then toString value else symbol

def popLineBlock (nonLineArguments : List String) : Option String :=
  match nonLineArguments with
  | [only] => some only
  | _ => none

def resolveConditional (condition : Option Bool) (whenTrue whenFalse : String) : Option String :=
  condition.map fun value => if value then whenTrue else whenFalse

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

def cartDimensions (count : Int) : List Int :=
  (List.range count.toNat).map fun index => (index + 1 : Nat)

def indexedNameInt (stem : String) (extension : Int) : String :=
  stem ++ "_" ++ toString extension

def replaceIndexedChars : Nat → List Char → List Char → List Char → List Char
  | 0, _, _, input => input
  | _fuel + 1, _pattern, _replacement, [] => []
  | fuel + 1, pattern, replacement, '_' :: rest =>
    if pattern.isEmpty then '_' :: replaceIndexedChars fuel pattern replacement rest
    else if pattern.isPrefixOf rest then
      let suffix := rest.drop pattern.length
      if suffix.isEmpty || suffix.head? = some '_' then
        '_' :: replacement ++ replaceIndexedChars fuel pattern replacement suffix
      else '_' :: replaceIndexedChars fuel pattern replacement rest
    else '_' :: replaceIndexedChars fuel pattern replacement rest
  | fuel + 1, pattern, replacement, character :: rest =>
    character :: replaceIndexedChars fuel pattern replacement rest

def replaceNameSegments (name pattern : String) (value : Int) : String :=
  String.ofList (replaceIndexedChars name.length pattern.toList (toString value).toList name.toList)

def cartResolveInt : Ast → Option Int
  | .int value => some value
  | .expr "call" [.atom "+", .int left, .int right] => some (left + right)
  | .expr "call" [.atom "-", .int left, .int right] => some (left - right)
  | .expr "call" [.atom "*", .int left, .int right] => some (left * right)
  | .expr "call" [.atom "div", .int left, .int right] =>
    if right = 0 then none else some (left.tdiv right)
  | _ => none

def cartReplaceCtx (pattern : String) (value : Int) (inQuote : Bool) (escapeDepth : Nat) : Ast → Ast
  | .atom name =>
    if escapeDepth != 0 then .atom name
    else if name == pattern then .int value else .atom (replaceNameSegments name pattern value)
  | .int number => .int number
  | .line => .line
  | .quoteNode quoted => .quoteNode quoted
  | .expr "meta" arguments => .expr "meta" arguments
  | .expr "inert" arguments => .expr "inert" arguments
  | .expr "curly" [.atom base, argument] =>
    if !inQuote && escapeDepth = 0 && base.endsWith "_" then
      let argument := cartReplaceCtx pattern value inQuote escapeDepth argument
      match cartResolveInt argument with
      | some result => .atom (base ++ toString result)
      | none => .expr "curly" [.atom base, argument]
    else .expr "curly" [.atom base, argument]
  | .expr "hygienic-scope" arguments =>
    .expr "hygienic-scope" (arguments.map (cartReplaceCtx pattern value inQuote (escapeDepth + 1)))
  | expression@(.expr "escape" arguments) =>
    if escapeDepth = 0 then expression
    else .expr "escape" (arguments.map (cartReplaceCtx pattern value inQuote (escapeDepth - 1)))
  | .expr "$" arguments =>
    .expr "$" (arguments.map (cartReplaceCtx pattern value false escapeDepth))
  | .expr "quote" arguments =>
    .expr "quote" (arguments.map (cartReplaceCtx pattern value true escapeDepth))
  | .expr head arguments =>
    .expr head (arguments.map (cartReplaceCtx pattern value inQuote escapeDepth))
termination_by expression => sizeOf expression

def cartReplace (pattern : String) (value : Int) (expression : Ast) : Ast :=
  cartReplaceCtx pattern value false 0 expression

def cartNonLine : Ast → Bool | .line => false | .expr "line" _ => false | _ => true

def cartPopLine : Ast → Ast
  | original@(.expr "block" arguments) =>
    match arguments.filter cartNonLine with | [only] => only | _ => original
  | value => value

def cartResolveSimple (expression : Ast) : Ast :=
  match cartResolveInt expression with | some value => .int value | none => expression

inductive InlineAnonymous where
  | prefix (stem : String)
  | lambda (parameter : String) (body : Ast)
  | invalid
  deriving Repr, Inhabited

def inlineAnonymousModel (source : InlineAnonymous) (value : Int) : Jl Ast :=
  match source with
  | .prefix stem => .ok (.atom (indexedNameInt stem value))
  | .lambda parameter body => .ok (cartResolveSimple (cartPopLine (cartReplace parameter value body)))
  | .invalid => .error (.argumentError "not an anonymous function")

def cartMapDimensions (count : Int) (source : InlineAnonymous) : Jl (List Ast) :=
  (cartDimensions count).mapM (inlineAnonymousModel source)

inductive CartesianRange where
  | arrayAxes (array : String)
  | anonymous (source : InlineAnonymous)
  | invalid
  deriving Repr, Inhabited

def rangeAt (range : CartesianRange) (dimension : Int) : Jl Ast :=
  match range with
  | .arrayAxes array => .ok (.expr "axes" [.atom array, .int dimension])
  | .anonymous source@(.lambda _ _) => inlineAnonymousModel source dimension
  | .anonymous _ => .error (.argumentError "range must be an anonymous function")
  | .invalid => .error (.argumentError "range must be an anonymous function")

def cartLoopLayer (iterator : String) (range : Ast) (pre post : Option Ast) (inner : Ast) : Ast :=
  .expr "for" [
    .expr "=" [.atom iterator, range],
    .expr "block" [pre.getD (.atom "nothing"), inner, post.getD (.atom "nothing")]]

def buildLoops (count : Int) (iterator : String) (range : CartesianRange)
    (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast := do
  let mut result := .expr "escape" [body]
  for dimension in cartDimensions count do
    let loopRange ← rangeAt range dimension
    let preExpr ← (match pre with
      | none => .ok none
      | some source => do let expression ← inlineAnonymousModel source dimension; return some expression : Jl (Option Ast))
    let postExpr ← (match post with
      | none => .ok none
      | some source => do let expression ← inlineAnonymousModel source dimension; return some expression : Jl (Option Ast))
    result := cartLoopLayer (indexedNameInt iterator dimension) loopRange preExpr postExpr result
  return result

/-- `@nloops`; `base/cartesian.jl:38-40`. -/

def cartRow38 (count : Int) (iterator : String) (range : CartesianRange)
    (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast :=
  buildLoops count iterator range pre post body

def cartRow42 (count : Int) (iterator array : String) (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast :=
  buildLoops count iterator (.arrayAxes array) pre post body

def cartRow46 (count : Int) (iterator : String) (range : InlineAnonymous)
    (argumentCount : Nat) (pre post : Option InlineAnonymous) (body : Ast) : Jl Ast :=
  if argumentCount < 1 || 3 < argumentCount then
    .error (.argumentError "number of arguments must be 1 through 3")
  else buildLoops count iterator (.anonymous range) pre post body

def cartRow85 (count : Int) (array : String) (source : InlineAnonymous) : Jl Ast := do
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok variables => .ok (.expr "escape" [.expr "ref" (.atom array :: variables)])

def splitLast {α : Type} : List α → Option (List α × α)
  | [] => none
  | [last] => some ([], last)
  | first :: rest => return (first :: (← splitLast rest).1, (← splitLast rest).2)

/-- `@ncall`; `base/cartesian.jl:105-110`. -/

def cartRow105 (count : Int) (functionName : String) (arguments : List Ast)
    (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok variables => .ok (.expr "escape" [.expr "call" (.atom functionName :: arguments ++ variables)])

def cartRow132 (count : Int) (functionName : String) (keywordTuple : Ast)
    (arguments : List Ast) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok variables =>
    let parameters := .expr "parameters" [.expr "..." [keywordTuple]]
    .ok (.expr "escape" [.expr "call" (.atom functionName :: parameters :: arguments ++ variables)])

def cartRow156 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok expressions => .ok (.expr "escape" [.expr "block" expressions])

def cartRow179 (count : Int) (external source : String) : Ast :=
  .expr "block" ((cartDimensions count).map fun dimension =>
    .expr "escape" [.expr "=" [
      .atom (indexedNameInt external dimension),
      .expr "ref" [.atom source, .int dimension]]])

def cartRow184 (count : Int) (external : String) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok values =>
    let assignments := List.zipWith (fun dimension value =>
      .expr "escape" [.expr "=" [.atom (indexedNameInt external dimension), value]])
      (cartDimensions count) values
    .ok (.expr "block" assignments)

def cartBooleanMacro (head : String) (count : Int) (source : InlineAnonymous) : Jl Ast := do
  let conditions ← cartMapDimensions count source
  return .expr head (conditions.map fun condition => .expr "escape" [condition])

/-- `@nall`; `base/cartesian.jl:198-204`. -/

def cartRow198 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match source with
  | .lambda _ _ => cartBooleanMacro "&&" count source
  | _ => .error (.argumentError "criterion must be an anonymous function")

def cartRow214 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match source with
  | .lambda _ _ => cartBooleanMacro "||" count source
  | _ => .error (.argumentError "criterion must be an anonymous function")

def cartRow228 (count : Int) (source : InlineAnonymous) : Jl Ast :=
  match cartMapDimensions count source with
  | .error error => .error error
  | .ok values => .ok (.expr "escape" [.expr "tuple" values])

def buildIfChain : List Int → InlineAnonymous → InlineAnonymous → Ast → Jl Ast
  | [], _, _, fallback => .ok fallback
  | dimension :: rest, condition, operation, fallback => do
    let tail ← buildIfChain rest condition operation fallback
    let condition ← inlineAnonymousModel condition dimension
    let operation ← inlineAnonymousModel operation dimension
    return .expr "if" [.expr "escape" [condition], .expr "escape" [operation], tail]

/-- `@nif`; `base/cartesian.jl:251-259`. -/

def cartRow251 (count : Int) (condition operation : InlineAnonymous) (otherwise : Option InlineAnonymous) : Jl Ast := do
  let last ← inlineAnonymousModel (otherwise.getD operation) count
  let dimensions := (cartDimensions count).dropLast.reverse
  buildIfChain dimensions condition operation (.expr "escape" [last])

def cartRow264 (source : InlineAnonymous) (value : Int) : Jl Ast := inlineAnonymousModel source value

def cartRow279 (base : String) (extension : Int) : String := indexedNameInt base extension

structure CartReplace where
  pattern : String
  value : Int
  deriving Repr, DecidableEq, Inhabited

/-- `LReplace(sym, val)`; `base/cartesian.jl:292`. -/

def cartRow292 (pattern : String) (value : Int) : CartReplace := ⟨pattern, value⟩

def cartRow294 (expression : Ast) (pattern : String) (value : Int) : Ast := cartReplace pattern value expression

def cartRow296 (symbol pattern : String) (value : Int) (escapeDepth : Nat) : String :=
  if escapeDepth != 0 then symbol else if symbol == pattern then toString value else replaceNameSegments symbol pattern value

def cartRow302 (name pattern : String) (value : Int) : String := replaceNameSegments name pattern value

def cartRow344 (expression : Ast) (pattern : String) (value : Int) : Ast := cartReplace pattern value expression

def cartRow379 (argument : Ast) : Ast := argument

def nonLineAst : Ast → Bool | .line => false | .expr "line" _ => false | _ => true

/-- Atomic `poplinenum`; `base/cartesian.jl:383`. -/

def cartRow383 (argument : Ast) : Ast := argument

def cartRow384 (expression : Ast) : Ast :=
  match expression with
  | .expr "block" arguments =>
    match arguments.filter nonLineAst with | [only] => only | _ => expression
  | _ => expression

inductive ResolveArithmetic where
  | value (number : Int)
  | call (operator : String) (arguments : List Int)
  | other
  deriving Repr, DecidableEq, Inhabited

def evaluateArithmetic (operator : String) (arguments : List Int) : Option Int :=
  match operator, arguments with
  | "+", [a,b] => some (a+b) | "-", [a,b] => some (a-b)
  | "*", [a,b] => some (a*b) | "div", [a,b] => if b = 0 then none else some (a.tdiv b)
  | _, _ => none

/-- Expr `exprresolve_arith`; `base/cartesian.jl:408-418`. -/

def cartRow408 : ResolveArithmetic → Bool × Int
  | .call operator arguments => match evaluateArithmetic operator arguments with | some value => (true,value) | none => (false,0)
  | _ => (false,0)

def cartRow419 (_ : Ast) : Bool × Int := (false,0)

def cartRow421 (condition : Bool) : Bool × Bool := (true,condition)

inductive ResolveCondition where | boolean (value : Bool) | comparison (operator : String) (left right : Int) | other
  deriving Repr, DecidableEq, Inhabited

def cartCompare : String → Int → Int → Option Bool
  | "==", a, b => some (a == b) | "<", a, b => some (a < b)
  | ">", a, b => some (a > b) | "<=", a, b => some (a ≤ b) | ">=", a, b => some (a ≥ b)
  | _, _, _ => none

/-- Expr `exprresolve_conditional`; `base/cartesian.jl:422-434`. -/

def cartRow422 : ResolveCondition → Bool × Bool
  | .boolean value => (true,value)
  | .comparison operator left right => match cartCompare operator left right with | some value => (true,value) | none => (false,false)
  | .other => (false,false)

def cartRow435 (_ : Ast) : Bool × Bool := (false,false)

def cartRow437 (argument : Ast) : Ast := argument

def cartRow438 : ResolveArithmetic → ResolveArithmetic
  | .call "+" [a,0] => .value a
  | .call "-" [a,0] => .value a
  | expression@(.call operator arguments) =>
    match evaluateArithmetic operator arguments with | some value => .value value | none => expression
  | expression => expression

end JuliaLean.ExprReflect
