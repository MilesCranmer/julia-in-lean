import JuliaLean.base.char
import JuliaLean.base.strings.unicode
import JuliaLean.Core
import JuliaLean.base.expr


section

/-!
# Julia values and `Expr` trees for the docsystem and `Base.Syntax` models

Model of the values that `base/docs/*.jl` and `base/syntax.jl` (master
`bbfa0ce4150`) take apart and build. A Julia `Expr` is `expr head args`, with
the head symbol's name as a `String`; `QuoteNode`, `GlobalRef`,
`LineNumberNode`, `Base.BaseDocs.Keyword` and the other atoms that these files
test with `isa` have their own constructors. Every other runtime value (a
module, a function, a type object) is `val name`, identified by a name.

Julia mutates `Expr` arguments in place in a few of these functions
(`x.args[i] = ...`); the models return the updated tree instead, which is
what the caller of each such function observes.
-/

namespace JuliaLean.DocsSyntaxCov

namespace JV

/-- `isexpr(x, h)`, `base/meta.jl` and `base/docs/core.jl:21`. -/
def isExpr (x : JV) (h : String) : Bool :=
  match x with
  | .expr h' _ => h' == h
  | _ => false

/-- `isexpr(x, heads)` for a collection of heads. -/
def isExprIn (x : JV) (hs : List String) : Bool :=
  match x with
  | .expr h' _ => hs.contains h'
  | _ => false

/-- `isexpr(x, h, n)`: head `h` and exactly `n` arguments. -/
def isExprN (x : JV) (h : String) (n : Nat) : Bool :=
  match x with
  | .expr h' as => h' == h && as.length == n
  | _ => false

end JV

/-- `Base.Meta.quot(ex)`: `Expr(:quote, ex)`. -/
def quot (x : JV) : JV := .expr "quote" [x]

/-- One iteration of the loops of `unblock`: `ex.args[1]` (or `nothing`). -/
def firstArg (x : JV) : JV := x.arg 1

/-- `Base.Meta.unblock(ex)`, `base/meta.jl:634-643`, with fuel bounding the loop and the
recursion (each step moves to a strict sub-expression). -/
def unblockF : Nat → JV → JV
  | 0, x => x
  | n + 1, x =>
    if x.isExpr "hygienic-scope" && (firstArg x).isExpr "escape" then
      unblockF n (firstArg (firstArg x))
    else if !x.isExpr "block" then x
    else
      match x.args.filter (fun a => !(a.isLnn || a.isExpr "line")) with
      | [a] => unblockF n a
      | _ => x

def unblock (x : JV) : JV := unblockF (x.size + 1) x

/-- The loop of `Base.Meta.unescape(ex)`, `base/meta.jl:651-657`. -/
def unescapeLoop : Nat → JV → JV
  | 0, x => x
  | n + 1, x =>
    if x.isExpr "escape" || x.isExpr "hygienic-scope" then unescapeLoop n (unblock (firstArg x))
    else x

/-- `Base.Meta.unescape(ex)`: peel `:escape`/`:var"hygienic-scope"` wrappers and
redundant blocks. -/
def unescape (x : JV) : JV := unescapeLoop (x.size + 1) (unblock x)

end JuliaLean.DocsSyntaxCov

end


/-!
# Model of `base/meta.jl`

Typed model of the module `Base.Meta` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a
64-bit platform. Each modelled method is a Lean definition whose docstring carries the method's
verbatim source; its body follows the Julia body call by call.

* Expressions and IR statements are the `Value L` ASTs of the `base/expr.jl` model, with value
  semantics: the in-place methods (`replace_sourceloc!`, `partially_inline!`) return the updated
  value.
* The parser's character and operator tables (`jl_id_start_char`, `jl_is_operator`, ...), the
  parser objects, `Core._lower` and `jl_instantiate_type_in_env` are typed primitives (`CharTables`,
  `OpTables`, `ParseOps`, `InlineOps`). Symbol names and `String` arguments of the operator
  predicates are Lean strings; other `AbstractString`s are a type parameter.
* Exceptions are `MetaError L`; methods that print or call the parser run in a monad `m`.
-/

namespace JuliaLean.base.meta
open JuliaLean
open JuliaLean.base.expr (Value LeafOps isexpr isexpr_n is_meta_expr_head)

abbrev Sym := String
abbrev JInt64 := JInt .i64

def i64 (z : Int) : JInt64 := JInt.wrap .i64 z
def addI (a b : JInt64) : JInt64 := JInt.wrap .i64 (a.val + b.val)

/-- `ParseError(msg, detail)`; `none` is a `nothing` detail. -/
structure ParseError (L : Type) where
  msg : String
  detail : Option (Value L)

/-- Exceptions thrown by the modelled methods. -/
inductive MetaError (L : Type) where
  | jl (e : JlError)
  | typeError
  | undefRefError
  | assertionError
  /-- `InvalidCharError` of converting a malformed character to `UInt32`. -/
  | invalidCharError
  | parseError (e : ParseError L)
  /-- `throw(err)` of another value. -/
  | thrown (x : Value L)

/-- The parser's character tables: `ccall(:jl_id_start_char, ...)`, `jl_id_char`,
`jl_op_suffix_char` on a code point. -/
structure CharTables where
  id_start_char : JInt .u32 → Bool
  id_char : JInt .u32 → Bool
  op_suffix_char : JInt .u32 → Bool

/-- The parser's operator tables on the bytes of a `Cstring` (`jl_is_operator`,
`jl_is_unary_operator`, `jl_is_unary_and_binary_operator`, `jl_is_syntactic_operator`). -/
structure OpTables where
  is_operator : String → Bool
  is_unary_operator : String → Bool
  is_unary_and_binary_operator : String → Bool
  is_syntactic_operator : String → Bool
  /-- `repr(s)` of a `String`, for the `Cstring` conversion error. -/
  reprStr : String → String

/-- A `Symbol` or a `String` argument. -/
inductive SymOrStr where
  | sym (s : Sym)
  | str (s : String)

-- UNTRANSLATED
-- license header, module docstring, `module Meta`, exports and `import Base: isexpr`; no method
-- Source: base/meta.jl:1-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
-- Convenience functions for metaprogramming.
-- """
-- module Meta
-- 
-- export quot,
--        isexpr,
--        isidentifier,
--        isoperator,
--        isunaryoperator,
--        isbinaryoperator,
--        ispostfixoperator,
--        replace_sourceloc!,
--        show_sexpr,
--        @dump
-- 
-- public parse
-- 
-- import Base: isexpr
-- 
-- ## AST decoding helpers ##
-- 
-- /Source

/--
Julia source: base/meta.jl:25-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_id_start_char(c::AbstractChar) = ccall(:jl_id_start_char, Cint, (UInt32,), c) != 0
is_id_char(c::AbstractChar) = ccall(:jl_id_char, Cint, (UInt32,), c) != 0

```
-/
/- `UInt32(c)` of a Lean character (always a valid code point). -/
def charCode (c : Char) : JInt .u32 := JInt.wrap .u32 c.val.toNat

def is_id_start_char (t : CharTables) (c : Char) : Bool := t.id_start_char (charCode c)
def is_id_char (t : CharTables) (c : Char) : Bool := t.id_char (charCode c)

/--
Julia source: base/meta.jl:28-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
     isidentifier(s) -> Bool

Return whether the symbol or string `s` contains characters that are parsed as
a valid ordinary identifier (not a binary/unary operator) in Julia code;
see also [`Base.isoperator`](@ref).

Internally Julia allows any sequence of characters in a `Symbol` (except `\\0`s),
and macros automatically use variable names containing `#` in order to avoid
naming collision with the surrounding code. In order for the parser to
recognize a variable, it uses a limited set of characters (greatly extended by
Unicode). `isidentifier()` makes it possible to query the parser directly
whether a symbol contains valid characters.

# Examples
```jldoctest
julia> Meta.isidentifier(:x), Meta.isidentifier("1x")
(true, false)
```
"""
function isidentifier(s::AbstractString)
    x = Iterators.peel(s)
    isnothing(x) && return false
    (s == "true" || s == "false") && return false
    c, rest = x
    is_id_start_char(c) || return false
    return all(is_id_char, rest)
end
isidentifier(s::Symbol) = isidentifier(string(s))

````
-/
/- `isidentifier(s::AbstractString)` over an `AbstractString` `S` iterating characters `C`;
`toUInt32` is `UInt32(c)`, and `eqLit s lit` is `s == lit`. -/
def isidentifier {S C L : Type} (t : CharTables) (chars : S → List C) (eqLit : S → String → Bool)
    (toUInt32 : C → Except (MetaError L) (JInt .u32)) (s : S) : Except (MetaError L) Bool := do
  match chars s with
  | [] => return false
  | c :: rest =>
    if eqLit s "true" || eqLit s "false" then return false
    if !t.id_start_char (← toUInt32 c) then return false
    for c' in rest do
      if !t.id_char (← toUInt32 c') then return false
    return true

/-- `isidentifier(s)` of a `String`. -/
def isidentifier_String {L : Type} (t : CharTables) (s : String) : Except (MetaError L) Bool :=
  isidentifier t String.toList (· == ·) (fun c => .ok (charCode c)) s

/-- `isidentifier(s::Symbol) = isidentifier(string(s))`. -/
def isidentifier_Symbol {L : Type} (t : CharTables) (s : Sym) : Except (MetaError L) Bool :=
  isidentifier_String t s

/--
Julia source: base/meta.jl:58-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_op_suffix_char(c::AbstractChar) = ccall(:jl_op_suffix_char, Cint, (UInt32,), c) != 0

```
-/
def is_op_suffix_char (t : CharTables) (c : Char) : Bool := t.op_suffix_char (charCode c)

/--
Julia source: base/meta.jl:60-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_isoperator(s) = ccall(:jl_is_operator, Cint, (Cstring,), s) != 0

```
-/
/- `Cstring` conversion: a `String` with an embedded NUL throws an `ArgumentError`. -/
def cstring {L : Type} (o : OpTables) : SymOrStr → Except (MetaError L) String
  | .sym s => .ok s
  | .str s =>
    if s.contains (Char.ofNat 0) then
      .error (.jl (.argumentError ("embedded NULs are not allowed in C strings: " ++ o.reprStr s)))
    else .ok s

def _isoperator {L : Type} (o : OpTables) (s : SymOrStr) : Except (MetaError L) Bool := do
  return o.is_operator (← cstring o s)

/--
Julia source: base/meta.jl:106-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    ispostfixoperator(s::Union{Symbol,AbstractString})

Return `true` if the symbol can be used as a postfix operator, `false` otherwise.

# Examples
```jldoctest
julia> Meta.ispostfixoperator(Symbol("'")), Meta.ispostfixoperator(Symbol("'ᵀ")), Meta.ispostfixoperator(:-)
(true, true, false)
```
"""
function ispostfixoperator(s::Union{Symbol,AbstractString})
    s = String(s)::String
    return startswith(s, '\'') && all(is_op_suffix_char, SubString(s, 2))
end

````
-/
/- `ispostfixoperator(s)`. -/
def ispostfixoperator (t : CharTables) (s : SymOrStr) : Bool :=
  let s := match s with | .sym x => x | .str x => x
  match s.toList with
  | '\'' :: rest => rest.all (is_op_suffix_char t)
  | _ => false

/--
Julia source: base/meta.jl:62-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isoperator(s::Symbol)

Return `true` if the symbol can be used as an operator, `false` otherwise.

# Examples
```jldoctest
julia> Meta.isoperator(:+), Meta.isoperator(:f)
(true, false)
```
"""
isoperator(s::Union{Symbol,AbstractString}) = _isoperator(s) || ispostfixoperator(s)

````
-/
def isoperator {L : Type} (t : CharTables) (o : OpTables) (s : SymOrStr) : Except (MetaError L) Bool := do
  return (← _isoperator o s) || ispostfixoperator t s

/--
Julia source: base/meta.jl:75-89 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isunaryoperator(s::Symbol)

Return `true` if the symbol can be used as a unary (prefix) operator, `false` otherwise.

# Examples
```jldoctest
julia> Meta.isunaryoperator(:-), Meta.isunaryoperator(:√), Meta.isunaryoperator(:f)
(true, true, false)
```
"""
isunaryoperator(s::Symbol) = ccall(:jl_is_unary_operator, Cint, (Cstring,), s) != 0
is_unary_and_binary_operator(s::Symbol) = ccall(:jl_is_unary_and_binary_operator, Cint, (Cstring,), s) != 0
is_syntactic_operator(s::Symbol) = ccall(:jl_is_syntactic_operator, Cint, (Cstring,), s) != 0

````
-/
def isunaryoperator (o : OpTables) (s : Sym) : Bool := o.is_unary_operator s
def is_unary_and_binary_operator (o : OpTables) (s : Sym) : Bool := o.is_unary_and_binary_operator s
def is_syntactic_operator (o : OpTables) (s : Sym) : Bool := o.is_syntactic_operator s

/--
Julia source: base/meta.jl:90-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    isbinaryoperator(s::Symbol)

Return `true` if the symbol can be used as a binary (infix) operator, `false` otherwise.

# Examples
```jldoctest
julia> Meta.isbinaryoperator(:-), Meta.isbinaryoperator(:√), Meta.isbinaryoperator(:f)
(true, false, false)
```
"""
function isbinaryoperator(s::Symbol)
    return _isoperator(s) && (!isunaryoperator(s) || is_unary_and_binary_operator(s)) &&
        s !== Symbol("'")
end

````
-/
def isbinaryoperator (o : OpTables) (s : Sym) : Bool :=
  o.is_operator s && (!isunaryoperator o s || is_unary_and_binary_operator o s) && s != "'"

/--
Julia source: base/meta.jl:122-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const keyword_syms = IdSet{Symbol}([
    :baremodule, :begin, :break, :catch, :const, :continue, :do, :else, :elseif,
    :end, :export, :var"false", :finally, :for, :function, :global, :if, :import,
    :let, :local, :macro, :module, :public, :quote, :return, :struct, :var"true",
    :try, :using, :while ])

function is_valid_identifier(sym)
    return (isidentifier(sym) && !(sym in keyword_syms)) ||
        (_isoperator(sym) &&
        !(sym in (Symbol("'"), :(::), :?)) &&
        !is_syntactic_operator(sym)
    )
end

```
-/
def keyword_syms : List Sym :=
  ["baremodule", "begin", "break", "catch", "const", "continue", "do", "else", "elseif",
   "end", "export", "false", "finally", "for", "function", "global", "if", "import",
   "let", "local", "macro", "module", "public", "quote", "return", "struct", "true",
   "try", "using", "while"]

/-- `is_valid_identifier(sym)` of a `Symbol`. -/
def is_valid_identifier {L : Type} (t : CharTables) (o : OpTables) (sym : Sym) : Except (MetaError L) Bool := do
  if (← isidentifier_Symbol t sym) && !keyword_syms.contains sym then return true
  return o.is_operator sym && !(["'", "::", "?"].contains sym) && !is_syntactic_operator o sym

/--
Julia source: base/meta.jl:136-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Meta.quot(ex)::Expr

Quote expression `ex` to produce an expression with head `quote`. This can for
instance be used to represent objects of type `Expr` in the AST. See also the
manual section about [QuoteNode](@ref man-quote-node).

# Examples
```jldoctest
julia> eval(Meta.quot(:x))
:x

julia> dump(Meta.quot(:x))
Expr
  head: Symbol quote
  args: Array{Any}((1,))
    1: Symbol x

julia> eval(Meta.quot(:(1+2)))
:(1 + 2)
```
"""
quot(ex) = Expr(:quote, ex)

````
-/
def quot {L : Type} (ex : Value L) : Value L := .expr "quote" [ex]

-- UNTRANSLATED
-- the docstring of `isexpr` (defined in `base/expr.jl`, modelled there); no method
-- Source: base/meta.jl:160-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     Meta.isexpr(ex, head[, n])::Bool
-- 
-- Return `true` if `ex` is an `Expr` with the given type `head` and optionally that
-- the argument list is of length `n`. `head` may be a `Symbol` or collection of
-- `Symbol`s. For example, to check that a macro was passed a function call
-- expression, you might use `isexpr(ex, :call)`.
-- 
-- # Examples
-- ```jldoctest
-- julia> ex = :(f(x))
-- :(f(x))
-- 
-- julia> Meta.isexpr(ex, :block)
-- false
-- 
-- julia> Meta.isexpr(ex, :call)
-- true
-- 
-- julia> Meta.isexpr(ex, [:block, :call]) # multiple possible heads
-- true
-- 
-- julia> Meta.isexpr(ex, :call, 1)
-- false
-- 
-- julia> Meta.isexpr(ex, :call, 2)
-- true
-- ```
-- """
-- isexpr
-- /Source

/--
Julia source: base/meta.jl:190-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    replace_sourceloc!(location, expr)

Overwrite the caller source location for each macro call in `expr`, returning
the resulting AST.  This is useful when you need to wrap a macro inside a
macro, and want the inner macro to see the `__source__` location of the outer
macro.  For example:

```
macro test_is_one(ex)
    replace_sourceloc!(__source__, :(@test \$(esc(ex)) == 1))
end
@test_is_one 2
```

`@test` now reports the location of the call `@test_is_one 2` to the user,
rather than line 2 where `@test` is used as an implementation detail.
"""
function replace_sourceloc!(sourceloc, @nospecialize(ex))
    if ex isa Expr
        if ex.head === :macrocall
            ex.args[2] = sourceloc
        end
        map!(e -> replace_sourceloc!(sourceloc, e), ex.args, ex.args)
    end
    return ex
end


````
-/
/- An `Except` result in the divergence-aware monad. -/
def liftE {ε α : Type} (x : Except ε α) : ExceptT ε Option α := ExceptT.mk (some x)

mutual
/-- `replace_sourceloc!(sourceloc, ex)`. Julia mutates `ex` in place; a `sourceloc` that is itself
an `Expr` is stored by reference and visited again, which diverges for a macro call. -/
def replace_sourceloc {L : Type} (sourceloc : Value L) : Value L → ExceptT (MetaError L) Option (Value L)
  | .expr head args => do
    let args ← if head == "macrocall" then
        if args.length ≥ 2 then pure (args.set 1 sourceloc) else throw (.jl .boundsError)
      else pure args
    return .expr head (← replace_sourceloc_args sourceloc args)
  | ex => pure ex
partial_fixpoint
/-- `map!(e -> replace_sourceloc!(sourceloc, e), ex.args, ex.args)`. -/
def replace_sourceloc_args {L : Type} (sourceloc : Value L) : List (Value L) → ExceptT (MetaError L) Option (List (Value L))
  | [] => pure []
  | a :: rest => do
    let a ← replace_sourceloc sourceloc a
    return a :: (← replace_sourceloc_args sourceloc rest)
partial_fixpoint
end

section show_sexpr
variable {m : Type → Type} [Monad m] {L : Type} [MonadExceptOf (MetaError L) m]

/-- Printing callees of `show_sexpr` over a stream `Io`: `stdout`, `show(io, x)` of a non-`Expr`,
non-`QuoteNode` value (and of a head `Symbol`), and `print(io, xs...)` of strings and characters. -/
structure SexprOps (n : Type → Type) (Io L : Type) where
  stdout : n Io
  showV : Io → Value L → n Unit
  printMany : Io → List String → n Unit

/-- `" "^n`. -/
def spaces (n : JInt64) : m String :=
  if n.val < 0 then throwThe (MetaError L) (.jl (.argumentError ("can't repeat a string " ++ toString n.val ++ " times")))
  else pure (String.ofList (List.replicate n.val.toNat ' '))

/--
Julia source: base/meta.jl:220-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Meta.show_sexpr([io::IO,], ex)

Show expression `ex` as a lisp style S-expression.

# Examples
```jldoctest
julia> Meta.show_sexpr(:(f(x, g(y,z))))
(:call, :f, :x, (:call, :g, :y, :z))
```
"""
show_sexpr(ex) = show_sexpr(stdout, ex)
show_sexpr(io::IO, ex) = show_sexpr(io, ex, 0)
show_sexpr(io::IO, ex, indent::Int) = show(io, ex)

const sexpr_indent_width = 2

function show_sexpr(io::IO, ex::QuoteNode, indent::Int)
    inner = indent + sexpr_indent_width
    print(io, "(:quote, #QuoteNode\n", " "^inner)
    show_sexpr(io, ex.value, inner)
    print(io, '\n', " "^indent, ')')
end
function show_sexpr(io::IO, ex::Expr, indent::Int)
    inner = indent + sexpr_indent_width
    print(io, '(')
    show_sexpr(io, ex.head, inner)
    for arg in ex.args
        print(io, ex.head === :block ? ",\n"*" "^inner : ", ")
        show_sexpr(io, arg, inner)
    end
    if isempty(ex.args)
        print(io, ",)")
    else
        print(io, (ex.head === :block ? "\n"*" "^indent : ""), ')')
    end
end

````
-/
def sexpr_indent_width : JInt64 := i64 2

mutual
/-- `show_sexpr(io, ex, indent)`: Julia selects the `QuoteNode` and `Expr` methods. -/
def show_sexpr_indent {Io : Type} (s : SexprOps m Io L) (io : Io) : Value L → JInt64 → m Unit
  | .quoteNode v, indent => do
    let inner := addI indent sexpr_indent_width
    s.printMany io ["(:quote, #QuoteNode\n", ← spaces (L := L) inner]
    show_sexpr_indent s io v inner
    s.printMany io ["\n", ← spaces (L := L) indent, ")"]
  | .expr head args, indent => do
    let inner := addI indent sexpr_indent_width
    s.printMany io ["("]
    s.showV io (.symbol head)
    show_sexpr_args s io head inner args
    if args.isEmpty then
      s.printMany io [",)"]
    else
      let t ← if head == "block" then do pure ("\n" ++ (← spaces (L := L) indent)) else pure ""
      s.printMany io [t, ")"]
  | ex, _ => s.showV io ex

/-- `for arg in ex.args; print(io, ex.head === :block ? ",\n"*" "^inner : ", "); show_sexpr(io, arg, inner); end`. -/
def show_sexpr_args {Io : Type} (s : SexprOps m Io L) (io : Io) (head : Sym) (inner : JInt64) :
    List (Value L) → m Unit
  | [] => pure ()
  | arg :: rest => do
    let t ← if head == "block" then do pure (",\n" ++ (← spaces (L := L) inner)) else pure ", "
    s.printMany io [t]
    show_sexpr_indent s io arg inner
    show_sexpr_args s io head inner rest
end

/-- `show_sexpr(io, ex) = show_sexpr(io, ex, 0)`. -/
def show_sexpr_io {Io : Type} (s : SexprOps m Io L) (io : Io) (ex : Value L) : m Unit :=
  show_sexpr_indent s io ex (i64 0)

/-- `show_sexpr(ex) = show_sexpr(stdout, ex)`. -/
def show_sexpr {Io : Type} (s : SexprOps m Io L) (ex : Value L) : m Unit := do
  show_sexpr_io s (← s.stdout) ex

end show_sexpr

/--
Julia source: base/meta.jl:258-267 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @dump expr

Show every part of the representation of the given expression. Equivalent to
[`dump(:(expr))`](@ref dump).
"""
macro dump(expr)
    return :(dump($(QuoteNode(expr))))
end

```
-/
/- `@dump expr` returns `:(dump($(QuoteNode(expr))))`. -/
def dump_macro {L : Type} (expr : Value L) : Value L := .expr "call" [.symbol "dump", .quoteNode expr]

section parse
variable {m : Type → Type} [Monad m] {L Mod P S Ty : Type} [MonadExceptOf (MetaError L) m]

/-- The runtime callees of `lower` and the parser interface: modules `Mod`, parser objects `P`,
strings `S` and the requested result type `Ty`. -/
structure ParseOps (n : Type → Type) (L Mod P S Ty : Type) where
  /-- `Core._lower(x, m, "none", 0, typemax(Csize_t), false)`: the returned `SimpleVector`. -/
  lower : Value L → Mod → n (List (Value L))
  /-- The module as an AST leaf value. -/
  modLeaf : Mod → L
  /-- `invokelatest(isdefined, mod, Symbol("#_internal_julia_parse"))` and `getglobal` of it. -/
  hasInternalParse : Mod → n Bool
  getInternalParse : Mod → n P
  /-- `Base.VersionedParse(Base.VERSION_EDITION)`. -/
  versionedParse : P
  /-- `_parse(text, filename, lineno, offset, options)` of a parser object, whose second result
  passed the `offset::Int` assertion. -/
  callParse : P → S → String → JInt64 → JInt64 → Sym → n (Value L × JInt64)
  ncodeunits : S → JInt64
  /-- `isdefined(Base, :Syntax)`, `ex isa Base.Syntax` of a leaf, `Base.head(ex)`,
  `Base.syntax_to_expr(ex)`, `Base.expr_to_syntax(ex, lno)`. -/
  syntaxDefined : n Bool
  isSyntax : L → Bool
  syntaxHead : L → Sym
  syntax_to_expr : L → n (Value L)
  expr_to_syntax : Value L → Value L → n (Value L)
  /-- `type == Expr`. -/
  isExprType : Ty → Bool
  /-- A `String` object as a leaf, and a leaf that is a `String`. -/
  ofString : String → L
  asString : L → Option String

/--
Julia source: base/meta.jl:268-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    lower(m, x)

Takes the expression `x` and returns an equivalent expression in lowered form
for executing in module `m`.
See also [`code_lowered`](@ref).
"""
lower(m::Module, @nospecialize(x)) = Core._lower(x, m, "none", 0, typemax(Csize_t), false)[1]

```
-/
def lower (o : ParseOps m L Mod P S Ty) (md : Mod) (x : Value L) : m (Value L) := do
  match ← o.lower x md with
  | v :: _ => pure v
  | [] => throwThe (MetaError L) (.jl .boundsError)

/--
Julia source: base/meta.jl:277-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @lower [m] x

Return lowered form of the expression `x` in module `m`.
By default `m` is the module in which the macro is called.
See also [`lower`](@ref).
"""
macro lower(code)
    return :(lower($__module__, $(QuoteNode(code))))
end
macro lower(mod, code)
    return :(lower($(esc(mod)), $(QuoteNode(code))))
end


```
-/
/- `@lower code` returns `:(lower($__module__, $(QuoteNode(code))))`. -/
def lower_macro (o : ParseOps m L Mod P S Ty) (__module__ : Mod) (code : Value L) : Value L :=
  .expr "call" [.symbol "lower", .leaf (o.modLeaf __module__), .quoteNode code]

/-- `@lower mod code` returns `:(lower($(esc(mod)), $(QuoteNode(code))))`. -/
def lower_macro_mod (md code : Value L) : Value L :=
  .expr "call" [.symbol "lower", .expr "escape" [md], .quoteNode code]

/--
Julia source: base/meta.jl:292-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## interface to parser ##

"""
    ParseError(msg)

The expression passed to the [`parse`](@ref) function could not be interpreted as a valid Julia
expression.
"""
struct ParseError <: Exception
    msg::String
    detail::Any
end

ParseError(msg::AbstractString) = ParseError(msg, nothing)

```
-/
/- `ParseError(msg) = ParseError(msg, nothing)`. -/
def ParseError_msg (msg : String) : ParseError L := ⟨msg, none⟩

/--
Julia source: base/meta.jl:307-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parser_for_module(mod::Union{Module, Nothing})
    if mod isa Module && invokelatest(isdefined, mod, Symbol("#_internal_julia_parse"))
        invokelatest(getglobal, mod, Symbol("#_internal_julia_parse"))
    else
        Base.VersionedParse(Base.VERSION_EDITION)
    end
end

```
-/
def parser_for_module (o : ParseOps m L Mod P S Ty) (mod : Option Mod) : m P := do
  match mod with
  | some md => if ← o.hasInternalParse md then o.getInternalParse md else pure o.versionedParse
  | none => pure o.versionedParse

/--
Julia source: base/meta.jl:315-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _parse_string(text::AbstractString, filename::AbstractString,
                       lineno::Integer, index::Integer, options, type,
                       _parse=parser_for_module(nothing))
    if index < 1 || index > ncodeunits(text) + 1
        throw(BoundsError(text, index))
    end
    ex, offset::Int = _parse(text, filename, lineno, index-1, options)
    if isdefined(Base, :Syntax) && type == Expr && ex isa Base.Syntax
        ex = Base.syntax_to_expr(ex)
    end
    ex, offset+1
end

```
-/
def _parse_string (o : ParseOps m L Mod P S Ty) (text : S) (filename : String) (lineno index : JInt64)
    (options : Sym) (type : Ty) (_parse : P) : m (Value L × JInt64) := do
  if index.val < 1 || index.val > (o.ncodeunits text).val + 1 then
    throwThe (MetaError L) (.jl .boundsError)
  let (ex, offset) ← o.callParse _parse text filename lineno (JInt.wrap .i64 (index.val - 1)) options
  let ex ← match ex with
    | .leaf x => if (← o.syntaxDefined) && o.isExprType type && o.isSyntax x then o.syntax_to_expr x else pure ex
    | _ => pure ex
  return (ex, addI offset (i64 1))

/--
Julia source: base/meta.jl:328-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_is_parse_error(@nospecialize(ex)) = isexpr(ex, :error) ||
    (isdefined(Base, :Syntax) && ex isa Base.Syntax && Base.head(ex) === :error)

```
-/
def _is_parse_error (o : ParseOps m L Mod P S Ty) (ex : Value L) : m Bool := do
  if isexpr ex "error" then return true
  if ← o.syntaxDefined then
    match ex with
    | .leaf x => return o.isSyntax x && o.syntaxHead x == "error"
    | _ => return false
  return false

/--
Julia source: base/meta.jl:331-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    parse(str, start; greedy=true, raise=true, depwarn=true, filename="none")

Parse the expression string and return an expression (which could later be
passed to eval for execution). `start` is the code unit index into `str` of the
first character to start parsing at (as with all string indexing, these are not
character indices). If `greedy` is `true` (default), `parse` will try to consume
as much input as it can; otherwise, it will stop as soon as it has parsed a
valid expression. Incomplete but otherwise syntactically valid expressions will
return `Expr(:incomplete, "(error message)")`. If `raise` is `true` (default),
syntax errors other than incomplete expressions will raise an error. If `raise`
is `false`, `parse` will return an expression that will raise an error upon
evaluation. If `depwarn` is `false`, deprecation warnings will be suppressed.
The `filename` argument is used to display diagnostics when an error is raised.

```jldoctest
julia> Meta.parse("(α, β) = 3, 5", 1) # start of string
(:((α, β) = (3, 5)), 16)

julia> Meta.parse("(α, β) = 3, 5", 1, greedy=false)
(:((α, β)), 9)

julia> Meta.parse("(α, β) = 3, 5", 16) # end of string
(nothing, 16)

julia> Meta.parse("(α, β) = 3, 5", 11) # index of 3
(:((3, 5)), 16)

julia> Meta.parse("(α, β) = 3, 5", 11, greedy=false)
(3, 13)
```
"""
function parse(str::AbstractString, pos::Integer;
               filename="none", greedy::Bool=true, raise::Bool=true,
               depwarn::Bool=true, mod::Union{Nothing, Module}=nothing,
               type=Expr, _parse = parser_for_module(mod))
    ex, pos = _parse_string(str, String(filename), 1, pos,
                            greedy ? :statement : :atom, type, _parse)
    if raise && _is_parse_error(ex)
        err = (ex isa Expr ? ex : Base.syntax_to_expr(ex)).args[1]
        if err isa String
            err = ParseError(err) # For flisp parser
        end
        throw(err)
    end
    return ex, pos
end

````
-/
/- `parse(str, pos; filename, greedy, raise, depwarn, mod, type, _parse)`; `_parse = none` takes
the default `parser_for_module(mod)`. -/
def parse_pos (o : ParseOps m L Mod P S Ty) (str : S) (pos : JInt64) (filename : String := "none")
    (greedy raise _depwarn : Bool := true) (mod : Option Mod := none) (type : Ty) (_parse : Option P := none) :
    m (Value L × JInt64) := do
  let _parse ← match _parse with
    | some p => pure p
    | none => parser_for_module o mod
  let (ex, pos) ← _parse_string o str filename (i64 1) pos (if greedy then "statement" else "atom") type _parse
  if raise && (← _is_parse_error o ex) then
    let ex' ← match ex with
      | .expr h a => pure (Value.expr h a)
      | .leaf x => o.syntax_to_expr x
      | _ => throwThe (MetaError L) (.jl (.methodError "syntax_to_expr"))
    let err ← match ex' with
      | .expr _ (a :: _) => pure a
      | .expr _ [] => throwThe (MetaError L) (.jl .boundsError)
      | _ => throwThe (MetaError L) .typeError
    match err with
    | .leaf x => match o.asString x with
      | some s => throwThe (MetaError L) (.parseError (ParseError_msg s)) -- For flisp parser
      | none => throwThe (MetaError L) (.thrown err)
    | _ => throwThe (MetaError L) (.thrown err)
  return (ex, pos)

/--
Julia source: base/meta.jl:379-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    parse(str; raise=true, depwarn=true, filename="none")

Parse the expression string greedily, returning a single expression. An error is thrown if
there are additional characters after the first expression. If `raise` is `true` (default),
syntax errors will raise an error; otherwise, `parse` will return an expression that will
raise an error upon evaluation.  If `depwarn` is `false`, deprecation warnings will be
suppressed. The `filename` argument is used to display diagnostics when an error is raised.

```jldoctest; filter=r"(?<=Expr\\(:error).*|(?<=Expr\\(:incomplete).*"
julia> Meta.parse("x = 3")
:(x = 3)

julia> Meta.parse("1.0.2")
ERROR: ParseError:
# Error @ none:1:1
1.0.2
└──┘ ── invalid numeric constant
[...]

julia> Meta.parse("1.0.2"; raise = false)
:(\$(Expr(:error, "invalid numeric constant \"1.0.\"")))

julia> Meta.parse("x = ")
:(\$(Expr(:incomplete, "incomplete: premature end of input")))
```
"""
function parse(str::AbstractString;
               filename="none", raise::Bool=true, depwarn::Bool=true,
               mod::Union{Nothing, Module}=nothing, type=Expr,
               _parse = parser_for_module(mod))
    ex, pos = parse(str, 1; filename, greedy=true, raise, depwarn, type, _parse)
    if _is_parse_error(ex)
        return ex
    end
    if pos <= ncodeunits(str)
        raise && throw(ParseError("extra token after end of expression"))
        err = Expr(:error, "extra token after end of expression")
        return type == Expr ? err :
            Base.expr_to_syntax(err, LineNumberNode(1, Symbol(filename)))
    end
    return ex
end

````
-/
/- `parse(str; filename, raise, depwarn, mod, type, _parse)`. -/
def parse (o : ParseOps m L Mod P S Ty) (str : S) (filename : String := "none") (raise depwarn : Bool := true)
    (mod : Option Mod := none) (type : Ty) (_parse : Option P := none) : m (Value L) := do
  let _parse ← match _parse with
    | some p => pure p
    | none => parser_for_module o mod
  let (ex, pos) ← parse_pos o str (i64 1) filename true raise depwarn none type (some _parse)
  if ← _is_parse_error o ex then return ex
  if pos.val ≤ (o.ncodeunits str).val then
    if raise then throwThe (MetaError L) (.parseError (ParseError_msg "extra token after end of expression"))
    let err : Value L := .expr "error" [.leaf (o.ofString "extra token after end of expression")]
    return ← if o.isExprType type then pure err
      else o.expr_to_syntax err (.lineNumberNode (i64 1) (.symbol filename))
  return ex

/--
Julia source: base/meta.jl:423-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parseatom(text::AbstractString, pos::Integer; filename="none",
                   lineno=1, mod::Union{Nothing, Module}=nothing, type=Expr,
                   _parse = parser_for_module(mod))
    return _parse_string(text, String(filename), lineno, pos, :atom, type, _parse)
end

```
-/
def parseatom (o : ParseOps m L Mod P S Ty) (text : S) (pos : JInt64) (filename : String := "none")
    (lineno : JInt64 := i64 1) (mod : Option Mod := none) (type : Ty) (_parse : Option P := none) :
    m (Value L × JInt64) := do
  let _parse ← match _parse with
    | some p => pure p
    | none => parser_for_module o mod
  _parse_string o text filename lineno pos "atom" type _parse

/--
Julia source: base/meta.jl:429-435 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parseall(text::AbstractString; filename="none", lineno=1,
                  mod::Union{Nothing, Module}=nothing, type=Expr,
                  _parse = parser_for_module(mod))
    ex,_ = _parse_string(text, String(filename), lineno, 1, :all, type, _parse)
    return ex
end

```
-/
def parseall (o : ParseOps m L Mod P S Ty) (text : S) (filename : String := "none")
    (lineno : JInt64 := i64 1) (mod : Option Mod := none) (type : Ty) (_parse : Option P := none) :
    m (Value L) := do
  let _parse ← match _parse with
    | some p => pure p
    | none => parser_for_module o mod
  return (← _parse_string o text filename lineno (i64 1) "all" type _parse).1

end parse

/-- The callees of `partially_inline!`: `type_signature isa UnionAll`, `_instantiate_type_in_env`
(`ccall(:jl_instantiate_type_in_env, ...)`), iterating `x.args[4]`, `Core.svec(xs...)`, and leaf
classifications. -/
structure InlineOps (L T : Type) where
  lo : LeafOps L
  asInt : L → Option JInt64
  isUnionAll : T → Bool
  instantiate : Value L → T → List (Option (Value L)) → Except (MetaError L) (Value L)
  iterate : Value L → Except (MetaError L) (List (Value L))
  svec : List (Value L) → Value L
  /-- `x isa Union{Tuple{Symbol, UInt16, Bool}, Tuple{Symbol, UInt16, Bool, Bool},
  Tuple{Symbol, UInt16, Bool, Bool, Bool}}` of a leaf. -/
  isCallConvTuple : L → Bool

/-- The arguments of `partially_inline!` after `code`. -/
structure InlineCtx (L T : Type) where
  slot_replacements : List (Option (Value L))
  type_signature : T
  static_param_values : List (Option (Value L))
  slot_offset : JInt64
  statement_offset : JInt64
  boundscheck : Sym

section inline
variable {L T : Type}

/-- `v[i]` of a `Vector{Any}` (`none` is `#undef`). -/
def vecAt (v : List (Option (Value L))) (i : JInt64) : Except (MetaError L) (Value L) :=
  if h : 1 ≤ i.val ∧ i.val ≤ v.length then
    match v[(i.val - 1).toNat]'(by omega) with
    | some x => .ok x
    | none => .error .undefRefError
  else .error (.jl .boundsError)

/-- `isassigned(v, i)` with `i` read from an AST leaf: an `Int` index. -/
def isassignedAt (io : InlineOps L T) (v : List (Option (Value L))) (i : Value L) : Except (MetaError L) Bool :=
  match i with
  | .leaf x => match io.asInt x with
    | some k => .ok (1 ≤ k.val ∧ k.val ≤ v.length && (v[(k.val - 1).toNat]?.join).isSome)
    | none => .error (.jl (.methodError "isassigned"))
  | _ => .error (.jl (.methodError "isassigned"))

/-- `args[i]` (1-based). -/
def argAt (args : List (Value L)) (i : Nat) : Except (MetaError L) (Value L) :=
  if i = 0 then .error (.jl .boundsError)
  else match args[i - 1]? with
    | some x => .ok x
    | none => .error (.jl .boundsError)

/-- `args[i] = v`. -/
def argSet (args : List (Value L)) (i : Nat) (v : Value L) : Except (MetaError L) (List (Value L)) :=
  if 1 ≤ i ∧ i ≤ args.length then .ok (args.set (i - 1) v) else .error (.jl .boundsError)

/-- `x.edges .+= slot_offset`: `Int32 + Int` is an `Int`, converted back to `Int32`. -/
def shiftEdge (off : JInt64) (e : JInt .i32) : Except (MetaError L) (JInt .i32) :=
  let s := (addI (JInt.wrap .i64 e.val) off).val
  if IntTy.min .i32 ≤ s ∧ s ≤ IntTy.max .i32 then .ok (JInt.wrap .i32 s)
  else .error (.jl (.inexactError "convert"))

/--
Julia source: base/meta.jl:477-624 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _partially_inline!(@nospecialize(x), slot_replacements::Vector{Any},
                            @nospecialize(type_signature), static_param_values::Vector{Any},
                            slot_offset::Int, statement_offset::Int,
                            boundscheck::Symbol)
    if isa(x, Core.SSAValue)
        return Core.SSAValue(x.id + statement_offset)
    end
    if isa(x, Core.GotoNode)
        return Core.GotoNode(x.label + statement_offset)
    end
    if isa(x, Core.SlotNumber)
        id = x.id
        if 1 <= id <= length(slot_replacements)
            return slot_replacements[id]
        end
        return Core.SlotNumber(id + slot_offset)
    end
    if isa(x, Core.NewvarNode)
        return Core.NewvarNode(_partially_inline!(x.slot, slot_replacements, type_signature,
                                                  static_param_values, slot_offset,
                                                  statement_offset, boundscheck))
    end
    if isa(x, Core.PhiNode)
        partially_inline!(x.values, slot_replacements, type_signature, static_param_values,
                          slot_offset, statement_offset, boundscheck)
        x.edges .+= slot_offset
        return x
    end
    if isa(x, Core.UpsilonNode)
        if !isdefined(x, :val)
            return x
        end
        return Core.UpsilonNode(
            _partially_inline!(x.val, slot_replacements, type_signature, static_param_values,
                               slot_offset, statement_offset, boundscheck),
        )
    end
    if isa(x, Core.PhiCNode)
        _partially_inline!(x.values, slot_replacements, type_signature, static_param_values,
                           slot_offset, statement_offset, boundscheck)
    end
    if isa(x, Core.ReturnNode)
       # Unreachable doesn't have val defined
       if !isdefined(x, :val)
          return x
       else
        return Core.ReturnNode(
            _partially_inline!(x.val, slot_replacements, type_signature, static_param_values,
                               slot_offset, statement_offset, boundscheck),
        )
       end
    end
    if isa(x, Core.GotoIfNot)
        return Core.GotoIfNot(
            _partially_inline!(x.cond, slot_replacements, type_signature, static_param_values,
                               slot_offset, statement_offset, boundscheck),
            x.dest + statement_offset,
        )
    end
    if isa(x, Core.EnterNode)
        if x.catch_dest == 0
            return x
        end
        return Core.EnterNode(x, x.catch_dest + statement_offset)
    end
    if isa(x, Expr)
        head = x.head
        if head === :static_parameter
            if isassigned(static_param_values, x.args[1])
                return QuoteNode(static_param_values[x.args[1]])
            end
            return x
        elseif head === :cfunction
            @assert !isa(type_signature, UnionAll) || !isempty(static_param_values)
            if !isa(x.args[2], QuoteNode) # very common no-op
                x.args[2] = _partially_inline!(x.args[2], slot_replacements, type_signature,
                                               static_param_values, slot_offset,
                                               statement_offset, boundscheck)
            end
            x.args[3] = _instantiate_type_in_env(x.args[3], type_signature, static_param_values)
            x.args[4] = Core.svec(Any[_instantiate_type_in_env(argt, type_signature, static_param_values) for argt in x.args[4]]...)
        elseif head === :foreigncall
            @assert !isa(type_signature, UnionAll) || !isempty(static_param_values)
            for i = 1:length(x.args)
                if i == 2
                    x.args[2] = _instantiate_type_in_env(x.args[2], type_signature, static_param_values)
                elseif i == 3
                    x.args[3] = Core.svec(Any[_instantiate_type_in_env(argt, type_signature, static_param_values) for argt in x.args[3]]...)
                elseif i == 4
                    @assert isa(x.args[4], Int)
                elseif i == 5
                    @assert isa((x.args[5]::QuoteNode).value,
                                Union{Symbol, Tuple{Symbol, UInt16, Bool}, Tuple{Symbol, UInt16, Bool, Bool},
                                      Tuple{Symbol, UInt16, Bool, Bool, Bool}})
                else
                    x.args[i] = _partially_inline!(x.args[i], slot_replacements,
                                                   type_signature, static_param_values,
                                                   slot_offset, statement_offset,
                                                   boundscheck)
                end
            end
        elseif head === :boundscheck
            if boundscheck === :propagate
                return x
            elseif boundscheck === :off
                return false
            else
                return true
            end
        elseif head === :gotoifnot
            x.args[1] = _partially_inline!(x.args[1], slot_replacements, type_signature,
                                           static_param_values, slot_offset,
                                           statement_offset, boundscheck)
            x.args[2] += statement_offset
        elseif head === :isdefined
            arg = x.args[1]
            # inlining a QuoteNode or literal into `Expr(:isdefined, x)` is invalid, replace with true
            if isa(arg, Core.SlotNumber)
                id = arg.id
                if 1 <= id <= length(slot_replacements)
                    replacement = slot_replacements[id]
                    if isa(replacement, Union{Core.SlotNumber, GlobalRef, Symbol})
                        return Expr(:isdefined, replacement)
                    else
                        @assert !isa(replacement, Expr)
                        return true
                    end
                end
                return Expr(:isdefined, Core.SlotNumber(id + slot_offset))
            elseif isexpr(arg, :static_parameter)
                if isassigned(static_param_values, arg.args[1])
                    return true
                end
                return x
            else
                @assert isa(arg, Union{GlobalRef, Symbol})
                return x
            end
        elseif !Base.is_meta_expr_head(head)
            partially_inline!(x.args, slot_replacements, type_signature, static_param_values,
                              slot_offset, statement_offset, boundscheck)
        end
    end
    return x
end

_instantiate_type_in_env(x, spsig, spvals) = ccall(:jl_instantiate_type_in_env, Any, (Any, Any, Ptr{Any}), x, spsig, spvals)

```
-/
/- `_instantiate_type_in_env` over every element of an iterable, collected with `Core.svec`. -/
def instantiateSvec (io : InlineOps L T) (c : InlineCtx L T) (x : Value L) : Except (MetaError L) (Value L) := do
  let elems ← io.iterate x
  return io.svec (← elems.mapM fun argt => io.instantiate argt c.type_signature c.static_param_values)

mutual
/-- `_partially_inline!(x, slot_replacements, type_signature, static_param_values, slot_offset,
statement_offset, boundscheck)`. -/
def _partially_inline (io : InlineOps L T) (c : InlineCtx L T) : Value L → Except (MetaError L) (Value L)
  | .ssaValue id => .ok (.ssaValue (addI id c.statement_offset))
  | .gotoNode label => .ok (.gotoNode (addI label c.statement_offset))
  | .slotNumber id =>
    if 1 ≤ id.val ∧ id.val ≤ c.slot_replacements.length then vecAt c.slot_replacements id
    else .ok (.slotNumber (addI id c.slot_offset))
  | .newvarNode slot => do return .newvarNode (← _partially_inline io c slot)
  | .phiNode edges values => do
    let values ← partially_inline_opts io c values
    let edges ← edges.mapM (shiftEdge c.slot_offset)
    return .phiNode edges values
  | .upsilonNode none => .ok (.upsilonNode none)
  | .upsilonNode (some v) => do return .upsilonNode (some (← _partially_inline io c v))
  -- `_partially_inline!(x.values, ...)` of the `Vector` returns it unchanged; the node is returned
  | .phiCNode values => .ok (.phiCNode values)
  -- Unreachable doesn't have val defined
  | .returnNode none => .ok (.returnNode none)
  | .returnNode (some v) => do return .returnNode (some (← _partially_inline io c v))
  | .gotoIfNot cond dest => do
    return .gotoIfNot (← _partially_inline io c cond) (addI dest c.statement_offset)
  | .enterNode catch_dest scope =>
    if catch_dest.val == 0 then .ok (.enterNode catch_dest scope)
    else .ok (.enterNode (addI catch_dest c.statement_offset) scope)
  | .expr head args => _partially_inline_expr io c head args
  | x => .ok x

/-- The `x isa Expr` branch. -/
def _partially_inline_expr (io : InlineOps L T) (c : InlineCtx L T) (head : Sym) (args : List (Value L)) :
    Except (MetaError L) (Value L) := do
  let x : Value L := .expr head args
  if head == "static_parameter" then
    let a1 ← argAt args 1
    if ← isassignedAt io c.static_param_values a1 then
      match a1 with
      | .leaf k => match io.asInt k with
        | some i => return .quoteNode (← vecAt c.static_param_values i)
        | none => throw (.jl (.methodError "getindex"))
      | _ => throw (.jl (.methodError "getindex"))
    return x
  else if head == "cfunction" then
    if !(!io.isUnionAll c.type_signature || !c.static_param_values.isEmpty) then throw .assertionError
    let mut args := args
    match ← argAt args 2 with
    | .quoteNode _ => pure () -- very common no-op
    | _ => args ← partially_inline_nth io c 2 args
    args ← argSet args 3 (← io.instantiate (← argAt args 3) c.type_signature c.static_param_values)
    args ← argSet args 4 (← instantiateSvec io c (← argAt args 4))
    return .expr head args
  else if head == "foreigncall" then
    if !(!io.isUnionAll c.type_signature || !c.static_param_values.isEmpty) then throw .assertionError
    return .expr head (← partially_inline_foreign io c 1 args)
  else if head == "boundscheck" then
    if c.boundscheck == "propagate" then return x
    else if c.boundscheck == "off" then return .leaf (io.lo.ofBool false)
    else return .leaf (io.lo.ofBool true)
  else if head == "gotoifnot" then
    let args ← partially_inline_nth io c 1 args
    match ← argAt args 2 with
    | .leaf d => match io.asInt d with
      | some dest => return .expr head (← argSet args 2 (.leaf (io.lo.ofInt (addI dest c.statement_offset))))
      | none => throw (.jl (.methodError "+"))
    | _ => throw (.jl (.methodError "+"))
  else if head == "isdefined" then
    let arg ← argAt args 1
    -- inlining a QuoteNode or literal into `Expr(:isdefined, x)` is invalid, replace with true
    match arg with
    | .slotNumber id =>
      if 1 ≤ id.val ∧ id.val ≤ c.slot_replacements.length then
        let replacement ← vecAt c.slot_replacements id
        match replacement with
        | .slotNumber _ | .globalRef _ _ | .symbol _ => return .expr "isdefined" [replacement]
        | .expr _ _ => throw .assertionError
        | _ => return .leaf (io.lo.ofBool true)
      return .expr "isdefined" [.slotNumber (addI id c.slot_offset)]
    | .expr "static_parameter" sargs =>
      if ← isassignedAt io c.static_param_values (← argAt sargs 1) then return .leaf (io.lo.ofBool true)
      return x
    | .globalRef _ _ | .symbol _ => return x
    | _ => throw .assertionError
  else if !is_meta_expr_head head then
    return .expr head (← partially_inline_list io c args)
  else return x

/-- `partially_inline!(x.args, ...)` on the arguments of an `Expr`, which are all assigned. -/
def partially_inline_list (io : InlineOps L T) (c : InlineCtx L T) :
    List (Value L) → Except (MetaError L) (List (Value L))
  | [] => .ok []
  | a :: rest => do
    let a ← _partially_inline io c a
    return a :: (← partially_inline_list io c rest)

/-- `partially_inline!(code, ...)` on a `Vector{Any}` whose unassigned elements are skipped. -/
def partially_inline_opts (io : InlineOps L T) (c : InlineCtx L T) :
    List (Option (Value L)) → Except (MetaError L) (List (Option (Value L)))
  | [] => .ok []
  | none :: rest => do return none :: (← partially_inline_opts io c rest)
  | some a :: rest => do
    let a ← _partially_inline io c a
    return some a :: (← partially_inline_opts io c rest)

/-- `x.args[n] = _partially_inline!(x.args[n], ...)`. -/
def partially_inline_nth (io : InlineOps L T) (c : InlineCtx L T) :
    Nat → List (Value L) → Except (MetaError L) (List (Value L))
  | _, [] => .error (.jl .boundsError)
  | 1, a :: rest => do return (← _partially_inline io c a) :: rest
  | n, a :: rest => do return a :: (← partially_inline_nth io c (n - 1) rest)

/-- The `for i = 1:length(x.args)` loop of the `:foreigncall` branch, from index `i`. -/
def partially_inline_foreign (io : InlineOps L T) (c : InlineCtx L T) :
    Nat → List (Value L) → Except (MetaError L) (List (Value L))
  | _, [] => .ok []
  | i, a :: rest => do
    let a ← if i == 2 then io.instantiate a c.type_signature c.static_param_values
      else if i == 3 then instantiateSvec io c a
      else if i == 4 then
        match a with
        | .leaf k => if (io.asInt k).isSome then pure a else throw .assertionError
        | _ => throw .assertionError
      else if i == 5 then
        match a with
        | .quoteNode (.symbol _) => pure a
        | .quoteNode (.leaf v) => if io.isCallConvTuple v then pure a else throw .assertionError
        | .quoteNode _ => throw .assertionError
        | _ => throw .typeError
      else _partially_inline io c a
    return a :: (← partially_inline_foreign io c (i + 1) rest)
end

/--
Julia source: base/meta.jl:436-476 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    partially_inline!(code::Vector{Any}, slot_replacements::Vector{Any},
                      type_signature::Type{<:Tuple}, static_param_values::Vector{Any},
                      slot_offset::Int, statement_offset::Int,
                      boundscheck::Symbol)

Return `code` after performing an in-place partial inlining pass on the Julia IR stored
within it.

The kind of inlining transformations performed by this function are those that are generally
possible given only a runtime type signature for a method invocation and the corresponding
method's lowered IR. Thus, this function is mainly useful when preparing Julia IR to be
emitted from a `@generated` function.

The performed transformations are:

- replace slot numbers in the range `1:length(slot_replacements)` with the corresponding items in `slot_replacements`
- increment other slot numbers by `slot_offset`
- substitute static parameter placeholders (e.g. `Expr(:static_parameter, 1)`) with the corresponding
values in `static_param_values`
- increment any statement indices present in the IR (`GotoNode`s, `SSAValue`s, etc.) by `statement_offset`
(useful when the caller plans to prepend new statements to the IR)
- turn off boundschecking (if `boundscheck === :off`) or propagate boundschecking (if `boundscheck === :propagate`)

This function is similar to `Core.Compiler.ssa_substitute!`, but works on pre-type-inference
IR instead of the optimizer's IR.
"""
function partially_inline!(code::Vector{Any}, slot_replacements::Vector{Any},
                           @nospecialize(type_signature)#=::Type{<:Tuple}=#,
                           static_param_values::Vector{Any},
                           slot_offset::Int, statement_offset::Int,
                           boundscheck::Symbol)
    for i = 1:length(code)
        isassigned(code, i) || continue
        code[i] = _partially_inline!(code[i], slot_replacements, type_signature,
                                     static_param_values, slot_offset,
                                     statement_offset, boundscheck)
    end
    return code
end

```
-/
/- `partially_inline!(code, slot_replacements, type_signature, static_param_values, slot_offset,
statement_offset, boundscheck)`. -/
def partially_inline (io : InlineOps L T) (code : List (Option (Value L))) (c : InlineCtx L T) :
    Except (MetaError L) (List (Option (Value L))) :=
  partially_inline_opts io c code

end inline

/--
Julia source: base/meta.jl:625-644 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Meta.unblock(expr)

Peel away redundant block expressions.

Specifically, the following expressions are stripped by this function:
- `:block` expressions with a single non-line-number argument.
- Pairs of `:var"hygienic-scope"` / `:escape` expressions.
"""
function unblock(@nospecialize ex)
    while isexpr(ex, :var"hygienic-scope")
        isexpr(ex.args[1], :escape) || break
        ex = ex.args[1].args[1]
    end
    isexpr(ex, :block) || return ex
    exs = filter(ex -> !(isa(ex, LineNumberNode) || isexpr(ex, :line)), ex.args)
    length(exs) == 1 || return ex
    return unblock(exs[1])
end

```
-/
/- `isa(ex, LineNumberNode) || isexpr(ex, :line)`. -/
def isLineExpr {L : Type} (e : Value L) : Bool := (e matches .lineNumberNode _ _) || isexpr e "line"

mutual
/-- `unblock(ex)`. -/
def unblock {L : Type} : Value L → ExceptT (MetaError L) Option (Value L)
  | .expr "hygienic-scope" args => do
    match ← liftE (argAt args 1) with
    | .expr "escape" eargs => unblock (← liftE (argAt eargs 1))
    | _ => unblock_block (.expr "hygienic-scope" args)
  | ex => unblock_block ex
partial_fixpoint
/-- The part of `unblock` after the `while` loop. -/
def unblock_block {L : Type} (ex : Value L) : ExceptT (MetaError L) Option (Value L) :=
  match ex with
  | .expr "block" args =>
    let exs := args.filter fun e => !isLineExpr e
    match (if exs.length == 1 then exs.head? else none) with
    | some e => unblock e
    | none => pure ex
  | _ => pure ex
partial_fixpoint
end

/--
Julia source: base/meta.jl:645-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Meta.unescape(expr)

Peel away `:escape` expressions and redundant block expressions (see
[`unblock`](@ref)).
"""
function unescape(@nospecialize ex)
    ex = unblock(ex)
    while isexpr(ex, :escape) || isexpr(ex, :var"hygienic-scope")
       ex = unblock(ex.args[1])
    end
    return ex
end

```
-/
/- The `while isexpr(ex, :escape) || isexpr(ex, :var"hygienic-scope")` loop of `unescape`. -/
def unescape_loop {L : Type} (ex : Value L) : ExceptT (MetaError L) Option (Value L) :=
  match ex with
  | .expr h args =>
    if h == "escape" || h == "hygienic-scope" then do
      unescape_loop (← unblock (← liftE (argAt args 1)))
    else pure ex
  | _ => pure ex
partial_fixpoint

def unescape {L : Type} (ex : Value L) : ExceptT (MetaError L) Option (Value L) := do
  unescape_loop (← unblock ex)

/--
Julia source: base/meta.jl:659-676 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Meta.reescape(unescaped_expr, original_expr)

Re-wrap `unescaped_expr` with the same level of escaping as `original_expr` had.
This is the inverse operation of [`unescape`](@ref) - if the original expression
was escaped, the unescaped expression is wrapped in `:escape` again.
"""
function reescape(@nospecialize(unescaped_expr), @nospecialize(original_expr))
    if isexpr(original_expr, :escape)
        return reescape(Expr(:escape, unescaped_expr), original_expr.args[1])
    elseif isexpr(original_expr, :var"hygienic-scope")
        next, ctx... = original_expr.args
        return reescape(Expr(:var"hygienic-scope", unescaped_expr, ctx...), next)
    else
        return unescaped_expr
    end
end

```
-/
/- `reescape(unescaped_expr, original_expr)`. -/
def reescape {L : Type} (unescaped_expr : Value L) : Value L → Except (MetaError L) (Value L)
  | .expr "escape" (a1 :: _) => reescape (.expr "escape" [unescaped_expr]) a1
  | .expr "escape" [] => .error (.jl .boundsError)
  | .expr "hygienic-scope" (next :: ctx) => reescape (.expr "hygienic-scope" (unescaped_expr :: ctx)) next
  | .expr "hygienic-scope" [] => .error (.jl .boundsError)
  | _ => .ok unescaped_expr

/--
Julia source: base/meta.jl:677-683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Meta.uncurly(expr)

Turn `T{P...}` into just `T`.
"""
uncurly(@nospecialize ex) = isexpr(ex, :curly) ? ex.args[1] : ex

```
-/
/- `uncurly(ex)`. -/
def uncurly {L : Type} : Value L → Except (MetaError L) (Value L)
  | .expr "curly" args => argAt args 1
  | ex => .ok ex

-- UNTRANSLATED
-- end of `module Meta`; no method
-- Source: base/meta.jl:684-684 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end # module
-- /Source

end JuliaLean.base.meta

namespace JuliaLean.ExprReflect

open JuliaLean

/-- `Meta.quot(ex)`; `base/meta.jl:158`. -/
def quot (ex : Ast) : Ast := .expr "quote" [ex]

/-- Structural content printed by `Meta.show_sexpr`; `base/meta.jl:231-256`.
Indentation and punctuation are presentation details, while this tree records the
head and recursive argument order exactly. -/
inductive SExpr where
  | atom (text : String)
  | form (head : String) (args : List SExpr)
  | quoteNode (value : SExpr)
  deriving Repr, Inhabited

def toSExpr : Ast → SExpr
  | .atom name => .atom name
  | .int value => .atom (toString value)
  | .line => .atom "#line"
  | .expr head args => .form head (args.map toSExpr)
  | .quoteNode value => .quoteNode (toSExpr value)
termination_by ex => sizeOf ex

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

structure IdentifierOracle where
  start : Char → Bool
  rest : Char → Bool
  operator : String → Bool
  unary : String → Bool
  unaryAndBinary : String → Bool
  syntactic : String → Bool
  suffix : Char → Bool

def isIdentifierModel (oracle : IdentifierOracle) (chars : List Char) : Bool :=
  match chars with
  | [] => false
  | first :: rest =>
    let text := String.ofList chars
    text != "true" && text != "false" && oracle.start first && rest.all oracle.rest

def isBinaryOperatorModel (oracle : IdentifierOracle) (symbol : String) : Bool :=
  oracle.operator symbol && (!oracle.unary symbol || oracle.unaryAndBinary symbol) && symbol != "'"

def isPostfixOperatorModel (oracle : IdentifierOracle) (chars : List Char) : Bool :=
  match chars with
  | '\'' :: suffix => suffix.all oracle.suffix
  | _ => false

inductive SourceTree where
  | atom (name : String)
  | macrocall (location : Nat) (children : List SourceTree)
  | node (head : String) (children : List SourceTree)
  deriving Repr, Inhabited

def replaceSourceRoot (location : Nat) : SourceTree → SourceTree
  | .macrocall _ children => .macrocall location children
  | tree => tree

def replaceSourceLoc (location : Nat) : SourceTree → SourceTree
  | .atom name => .atom name
  | .macrocall _ children => .macrocall location (children.map (replaceSourceLoc location))
  | .node head children => .node head (children.map (replaceSourceLoc location))
termination_by tree => sizeOf tree

structure LowerRequest where
  moduleName : String
  expression : String
  deriving Repr, DecidableEq, Inhabited

def lowerModel (request : LowerRequest) : String :=
  "Core._lower(" ++ request.expression ++ "," ++ request.moduleName ++ ")"

def dumpMacroShape (expression : String) : String := "dump(QuoteNode(" ++ expression ++ "))"

inductive ParseNode where | value (text : String) | parseError | incomplete | nothing
  deriving Repr, DecidableEq, Inhabited

structure ParseReply where
  node : ParseNode
  offset : Nat
  deriving Repr, DecidableEq, Inhabited

inductive ParseMode where | statement | atom | all
  deriving Repr, DecidableEq, Inhabited

def parseMode (greedy : Bool) : ParseMode := if greedy then .statement else .atom

def parserSource (moduleHasOverride : Bool) : String :=
  if moduleHasOverride then "module:#_internal_julia_parse" else "Base.VersionedParse"

def parseAtModel (length position : Nat) (greedy raiseError : Bool)
    (oracle : Nat → Bool → ParseReply) : Jl ParseReply :=
  if position < 1 || length + 1 < position then .error .boundsError
  else
    let reply := oracle (position - 1) greedy
    if raiseError && reply.node == .parseError then .error (.argumentError "ParseError")
    else .ok { reply with offset := reply.offset + 1 }

def parseWholeModel (length : Nat) (raiseError : Bool) (reply : ParseReply) : Jl ParseNode :=
  if reply.node == .parseError || reply.node == .incomplete then .ok reply.node
  else if reply.offset ≤ length then
    if raiseError then .error (.argumentError "extra token") else .ok .parseError
  else .ok reply.node

inductive InlineNode where
  | ssa (id : Int) | goto (label : Int) | slot (id : Int) | boundscheck
  | gotoIf (condition : Int) (dest : Int) | enter (dest : Int)
  | newvar (slot : Int) | phi (edges : List Int) | upsilon (value : Option Int)
  | phiC (values : List Int) | ret (value : Option Int)
  | staticParameter (index : Nat) | cfunction | foreigncall | isdefined (slot : Int)
  | expression (head : String) | other (payload : Int)
  deriving Repr, DecidableEq, Inhabited

def partiallyInlineNode (node : InlineNode) (slotCount slotOffset statementOffset : Int)
    (boundscheckOff : Bool) : InlineNode :=
  match node with
  | .ssa id => .ssa (id + statementOffset)
  | .goto label => .goto (label + statementOffset)
  | .slot id => if 1 ≤ id && id ≤ slotCount then .other id else .slot (id + slotOffset)
  | .boundscheck => if boundscheckOff then .other 0 else .boundscheck
  | .gotoIf condition dest => .gotoIf condition (dest + statementOffset)
  | .enter 0 => .enter 0
  | .enter dest => .enter (dest + statementOffset)
  | .newvar slot => .newvar (slot + slotOffset)
  | .phi edges => .phi (edges.map (· + slotOffset))
  | .upsilon value => .upsilon value
  | .phiC values => .phiC values
  | .ret value => .ret value
  | .staticParameter index => .staticParameter index
  | .cfunction => .cfunction
  | .foreigncall => .foreigncall
  | .isdefined slot =>
    if 1 ≤ slot && slot ≤ slotCount then .other 1 else .isdefined (slot + slotOffset)
  | .expression head => .expression head
  | node => node

inductive HygieneFrame where | escape | hygienic (context : List String)
  deriving Repr, DecidableEq, Inhabited

def reescapeFrames (frames : List HygieneFrame) (payload : String) : List HygieneFrame × String :=
  (frames, payload)

def unescapeFrames (wrapped : List HygieneFrame × String) : String := wrapped.2

def unblockCount (nonLineExpressions : Nat) : Bool := nonLineExpressions == 1

def uncurlyHead (isCurly : Bool) (head original : String) : String :=
  if isCurly then head else original

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

def metaRow25 (table : Char → Bool) (character : Char) : Bool := table character

def metaRow26 (table : Char → Bool) (character : Char) : Bool := table character

def metaRow48 (start rest : Char → Bool) (characters : List Char) : Bool :=
  match characters with
  | [] => false
  | first :: tail =>
    let text := String.ofList characters
    text != "true" && text != "false" && start first && tail.all rest

def metaRow56 (stringOfSymbol : String) (start rest : Char → Bool) : Bool :=
  metaRow48 start rest stringOfSymbol.toList

def metaRow58 (table : Char → Bool) (character : Char) : Bool := table character

def metaRow60 (table : String → Bool) (symbol : String) : Bool := table symbol

def metaPostfix (suffixTable : Char → Bool) (symbol : String) : Bool :=
  match symbol.toList with
  | '\'' :: suffix => suffix.all suffixTable
  | _ => false

/-- `isoperator`; `base/meta.jl:73`. -/

def metaRow73 (operatorTable : String → Bool) (suffixTable : Char → Bool) (symbol : String) : Bool :=
  operatorTable symbol || metaPostfix suffixTable symbol

def metaRow86 (table : String → Bool) (symbol : String) : Bool := table symbol

def metaRow87 (table : String → Bool) (symbol : String) : Bool := table symbol

def metaRow88 (table : String → Bool) (symbol : String) : Bool := table symbol

def metaRow101 (isOperator isUnary unaryAndBinary : String → Bool) (symbol : String) : Bool :=
  isOperator symbol && (!isUnary symbol || unaryAndBinary symbol) && symbol != "'"

def metaRow117 (suffixTable : Char → Bool) (symbol : String) : Bool := metaPostfix suffixTable symbol

def metaRow128 (start rest : Char → Bool) (operator syntactic : String → Bool)
    (keywords excludedOperators : List String) (symbol : String) : Bool :=
  (metaRow48 start rest symbol.toList && !keywords.contains symbol) ||
    (operator symbol && !excludedOperators.contains symbol && !syntactic symbol)

def metaRow158 (expression : Ast) : Ast := .expr "quote" [expression]

def metaRow209 (location : Nat) (expression : SourceTree) : SourceTree := replaceSourceLoc location expression

def indentString (indent : Int) : Jl String :=
  if indent < 0 then .error (.argumentError "negative repeat count")
  else .ok (String.ofList (List.replicate indent.toNat ' '))

def metaShowSexpr (showAtom : Ast → String) : Ast → Int → Jl String
  | .quoteNode value, indent => do
    let inner := indent + 2
    let innerSpaces ← indentString inner
    let outerSpaces ← indentString indent
    let rendered ← metaShowSexpr showAtom value inner
    return "(:quote, #QuoteNode\n" ++ innerSpaces ++ rendered ++ "\n" ++ outerSpaces ++ ")"
  | .expr head arguments, indent => do
    let inner := indent + 2
    let innerSpaces ← indentString inner
    let outerSpaces ← indentString indent
    let separator := if head == "block" then ",\n" ++ innerSpaces else ", "
    let rendered ← arguments.mapM fun argument => metaShowSexpr showAtom argument inner
    return "(" ++ showAtom (.atom head) ++
      (if rendered.isEmpty then ",)" else separator ++ String.intercalate separator rendered ++
        (if head == "block" then "\n" ++ outerSpaces else "") ++ ")")
  | value, _indent => .ok (showAtom value)
termination_by value _indent => sizeOf value

/-- `show_sexpr(ex)`; `base/meta.jl:231`. -/

def metaRow231 (showAtom : Ast → String) (expression : Ast) : Jl String := metaShowSexpr showAtom expression 0

def metaRow232 (showAtom : Ast → String) (expression : Ast) : Jl String := metaShowSexpr showAtom expression 0

def metaRow233 (showAtom : Ast → String) (expression : Ast) (_indent : Int) : String := showAtom expression

def metaRow237 (showAtom : Ast → String) (value : Ast) (indent : Int) : Jl String :=
  metaShowSexpr showAtom (.quoteNode value) indent

def metaRow243 (showAtom : Ast → String) (head : String) (arguments : List Ast) (indent : Int) : Jl String :=
  metaShowSexpr showAtom (.expr head arguments) indent

def metaRow264 (expression : Ast) : Ast := .expr "dump" [.quoteNode expression]

def lowerCall (moduleName expression : String) : String :=
  "Core._lower(" ++ expression ++ "," ++ moduleName ++ ",none,0,typemax,false)[1]"

/-- `lower(m, x)`; `base/meta.jl:275`. -/

def metaRow275 (moduleName expression : String) : String := lowerCall moduleName expression

def metaRow284 (callerModule expression : String) : String := lowerCall callerModule expression

def metaRow287 (moduleName expression : String) : String := lowerCall moduleName expression

def metaRow305 (message : String) : String × Option String := (message, none)

def metaRow307 (isModule hasOverride : Bool) : String :=
  if isModule && hasOverride then "invokelatest(module.#_internal_julia_parse)" else "Base.VersionedParse"

inductive ParseResult where
  | expression (value : String)
  | syntax (value : String)
  | error (message : String)
  | incomplete (message : String)
  | nothing
  deriving Repr, DecidableEq, Inhabited

structure ParserReply where
  result : ParseResult
  zeroOffset : Int
  deriving Repr, DecidableEq, Inhabited

abbrev ParserCallback := String → Int → Int → String → ParserReply

/-- `_parse_string`; `base/meta.jl:315-326`. -/

def metaRow315 (length : Int) (filename : String) (line index : Int) (options : String)
    (wantSyntax : Bool) (parser : ParserCallback) : Jl (ParseResult × Int) :=
  if index < 1 || length + 1 < index then .error .boundsError
  else
    let reply := parser filename line (index - 1) options
    let result := match reply.result with
      | .syntax value => if wantSyntax then .syntax value else .expression value
      | other => other
    .ok (result, reply.zeroOffset + 1)

def metaRow328 : ParseResult → Bool | .error _ => true | _ => false

def metaRow363 (length position : Int) (_greedy raiseError wantSyntax : Bool)
    (filename : String) (parser : ParserCallback) : Jl (ParseResult × Int) :=
  let options := if _greedy then "statement" else "atom"
  match metaRow315 length filename 1 position options wantSyntax parser with
  | .error error => .error error
  | .ok reply => match reply.1 with
    | .error message => if raiseError then .error (.argumentError message) else .ok reply
    | _ => .ok reply

def metaRow406 (length finalPosition : Int) (raiseError : Bool) (result : ParseResult) : Jl ParseResult :=
  match result with
  | .error _ | .incomplete _ => .ok result
  | _ => if finalPosition ≤ length then
      if raiseError then .error (.argumentError "extra token after end of expression") else .ok (.error "extra token after end of expression")
    else .ok result

def metaRow423 (length position : Int) (wantSyntax : Bool) (parser : Int → ParserReply) :=
  metaRow315 length "none" 1 position "atom" wantSyntax (fun _ _ index _ => parser index)

def metaRow429 (length : Int) (wantSyntax : Bool) (parser : Int → ParserReply) :=
  metaRow315 length "none" 1 1 "all" wantSyntax (fun _ _ index _ => parser index)

def metaRow463 (code : List (Option InlineNode)) (slotCount slotOffset statementOffset : Int)
    (boundscheckOff : Bool) : List (Option InlineNode) :=
  code.map fun statement => statement.map fun node =>
    partiallyInlineNode node slotCount slotOffset statementOffset boundscheckOff

def metaRow477 (node : InlineNode) (slotCount slotOffset statementOffset : Int) (boundscheckOff : Bool) : InlineNode :=
  partiallyInlineNode node slotCount slotOffset statementOffset boundscheckOff

def metaRow623 (instantiate : String → String → List String → String)
    (value signature : String) (parameters : List String) : String :=
  instantiate value signature parameters

inductive HygieneTree where
  | atom (value : String)
  | line
  | block (values : List HygieneTree)
  | escape (value : HygieneTree)
  | hygienic (value : HygieneTree) (context : List String)
  | curly (head : HygieneTree) (parameters : List HygieneTree)
  deriving Repr, Inhabited

def hygieneNonLine : HygieneTree → Bool | .line => false | _ => true

def metaUnblockFuel : Nat → HygieneTree → HygieneTree
  | 0, value => value
  | fuel + 1, .hygienic (.escape value) _ => metaUnblockFuel fuel value
  | fuel + 1, original@(.block values) =>
    match values.filter hygieneNonLine with | [only] => metaUnblockFuel fuel only | _ => original
  | _, value => value

noncomputable def metaUnblock (value : HygieneTree) : HygieneTree := metaUnblockFuel (sizeOf value) value

/-- `unblock`; `base/meta.jl:634-643`. -/

noncomputable def metaRow634 (value : HygieneTree) : HygieneTree := metaUnblock value

noncomputable def metaUnescapeFuel : Nat → HygieneTree → HygieneTree
  | 0, value => value
  | fuel + 1, .escape value => metaUnescapeFuel fuel (metaUnblock value)
  | fuel + 1, .hygienic value _ => metaUnescapeFuel fuel (metaUnblock value)
  | _, value => metaUnblock value

noncomputable def metaUnescape (value : HygieneTree) : HygieneTree := metaUnescapeFuel (sizeOf value) value

/-- `unescape`; `base/meta.jl:651-657`. -/

noncomputable def metaRow651 (value : HygieneTree) : HygieneTree := metaUnescape value

def metaReescapeFuel : Nat → HygieneTree → HygieneTree → HygieneTree
  | 0, unescaped, _ => unescaped
  | fuel + 1, unescaped, .escape next => metaReescapeFuel fuel (.escape unescaped) next
  | fuel + 1, unescaped, .hygienic next context =>
    metaReescapeFuel fuel (.hygienic unescaped context) next
  | _, unescaped, _ => unescaped

noncomputable def metaReescape (unescaped original : HygieneTree) : HygieneTree :=
  metaReescapeFuel (sizeOf original) unescaped original

/-- `reescape`; `base/meta.jl:666-675`. -/

noncomputable def metaRow666 (unescaped original : HygieneTree) : HygieneTree := metaReescape unescaped original

def metaRow682 : HygieneTree → HygieneTree
  | .curly head _ => head
  | value => value

end JuliaLean.ExprReflect


namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- The parser's operator tables, keyed by symbol name. -/
structure OpData where
  /-- `Base.Meta._isoperator(s)` = `jl_is_operator`, `base/meta.jl:60`. -/
  isOp : String → Bool
  /-- `Base.Meta.isunaryoperator(s)` = `jl_is_unary_operator`, `base/meta.jl:86`. -/
  isUnaryOp : String → Bool
  /-- `Base.Meta.is_unary_and_binary_operator(s)`, `base/meta.jl:87`. -/
  isUnaryAndBinaryOp : String → Bool
  /-- `Base.Meta.is_syntactic_operator(s)`, `base/meta.jl:88`. -/
  isSyntacticOp : String → Bool
  /-- `Base.operator_precedence(s)` = `jl_operator_precedence`, `base/show.jl:1713`. -/
  prec : String → Nat
  /-- `Base.Meta.is_op_suffix_char(c)` on code points, `base/meta.jl:58`. -/
  opSuffix : UInt32 → Bool

/-- `is_id_start_char(c)`, `base/meta.jl:25`: a `ccall` whose `UInt32` argument
conversion `UInt32(c)` throws `InvalidCharError` for a malformed `c`. -/
def isIdStartCharJ (d : UData) (c : UInt32) : SJl Bool := do
  let u ← codepoint c
  pure (idStartChar d u)

/-- `is_id_char(c)`, `base/meta.jl:26`, with the same conversion. -/
def isIdCharJ (d : UData) (c : UInt32) : SJl Bool := do
  let u ← codepoint c
  pure (idChar d u)

/-- `all(is_id_char, rest)` (`base/reduce.jl`, `_all`): stops at the first `false`. -/
def allIdChar (d : UData) : List UInt32 → SJl Bool
  | [] => .ok true
  | c :: cs => do
    if ← isIdCharJ d c then allIdChar d cs else pure false

/-- The body of `isidentifier(s::AbstractString)`, `base/meta.jl:48-55`, on the
chars `cs` of `s`: `Iterators.peel(s)` splits off the first char. -/
def isidentifierOf (d : UData) (s : JStr) (cs : List UInt32) : SJl Bool :=
  match cs with
  | [] => .ok false
  | c :: rest =>
    if s.bytes = asc ['t', 'r', 'u', 'e'] ∨ s.bytes = asc ['f', 'a', 'l', 's', 'e'] then .ok false
    else do
      if ← isIdStartCharJ d c then allIdChar d rest else pure false

/-- `isidentifier(s::AbstractString)`, `base/meta.jl:48-55`, and
`isidentifier(s::Symbol) = isidentifier(string(s))` (`:56`). -/
def isidentifier (d : UData) (s : JStr) : SJl Bool := isidentifierOf d s (chars s)

/-- `keyword_syms`, `base/meta.jl:122-126` (char lists, so the kernel never
decodes a `String`). -/
def keywordSyms : List (List UInt8) :=
  [['b', 'a', 'r', 'e', 'm', 'o', 'd', 'u', 'l', 'e'], ['b', 'e', 'g', 'i', 'n'], ['b', 'r', 'e', 'a', 'k'],
    ['c', 'a', 't', 'c', 'h'], ['c', 'o', 'n', 's', 't'], ['c', 'o', 'n', 't', 'i', 'n', 'u', 'e'],
    ['d', 'o'], ['e', 'l', 's', 'e'], ['e', 'l', 's', 'e', 'i', 'f'], ['e', 'n', 'd'],
    ['e', 'x', 'p', 'o', 'r', 't'], ['f', 'a', 'l', 's', 'e'], ['f', 'i', 'n', 'a', 'l', 'l', 'y'],
    ['f', 'o', 'r'], ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n'], ['g', 'l', 'o', 'b', 'a', 'l'], ['i', 'f'],
    ['i', 'm', 'p', 'o', 'r', 't'], ['l', 'e', 't'], ['l', 'o', 'c', 'a', 'l'], ['m', 'a', 'c', 'r', 'o'],
    ['m', 'o', 'd', 'u', 'l', 'e'], ['p', 'u', 'b', 'l', 'i', 'c'], ['q', 'u', 'o', 't', 'e'],
    ['r', 'e', 't', 'u', 'r', 'n'], ['s', 't', 'r', 'u', 'c', 't'], ['t', 'r', 'u', 'e'], ['t', 'r', 'y'],
    ['u', 's', 'i', 'n', 'g'], ['w', 'h', 'i', 'l', 'e']].map asc

/-- The operator-table key of a symbol name: the Lean `String` with the same
UTF-8 bytes, or `none` when the name is not valid UTF-8. The tables
(`src/julia-parser.scm`) only hold valid UTF-8 names, so such a name is not an
operator. -/
def opName (s : JStr) : Option String :=
  if (chars s).all isvalidChar then some (String.ofList ((chars s).map (fun c => Char.ofNat (cpOf c).toNat)))
  else none

/-- `Meta._isoperator(s)`, `base/meta.jl:60` (`jl_is_operator` on the name's bytes). -/
def isOperatorSym (o : OpData) (s : JStr) : Bool :=
  match opName s with
  | some n => o.isOp n
  | none => false

/-- `Meta.is_syntactic_operator(s)`, `base/meta.jl:88`. -/
def isSyntacticSym (o : OpData) (s : JStr) : Bool :=
  match opName s with
  | some n => o.isSyntacticOp n
  | none => false

/-- `is_valid_identifier(sym)`, `base/meta.jl:128-134`. -/
def isValidIdentifier (d : UData) (o : OpData) (s : JStr) : SJl Bool := do
  let isid ← isidentifier d s
  if isid && !decide (s.bytes ∈ keywordSyms) then pure true
  else pure (isOperatorSym o s && !decide (s.bytes ∈ [asc ['\''], asc [':', ':'], asc ['?']]) &&
    !isSyntacticSym o s)

end JuliaLean.Show
