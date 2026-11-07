import JuliaLean.Core
import JuliaLean.base.int


section

/-!
Macros of `base/boot.jl` and `base/essentials.jl` (master `bbfa0ce4150`) as
functions from their arguments (and `__module__`, `__source__`) to the `Expr`
they return, plus the small doc-system helpers of `Core`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov
-- Source: base/boot.jl:333-361
-- placed here to break an import cycle with boot

/-- The eleven flags of `Expr(:purity, ...)`, in source order. -/
structure EffectFlags where
  consistent : Bool
  effectFree : Bool
  nothrow : Bool
  terminatesGlobally : Bool
  terminatesLocally : Bool
  notaskstate : Bool
  inaccessiblememonly : Bool
  noub : Bool
  noubIfNoinbounds : Bool
  consistentOverlay : Bool
  nortcall : Bool
  deriving Repr, DecidableEq

/-- The `EffectsOverride` that `@assume_effects` builds for a list of settings
(`compute_assumed_setting`, `base/expr.jl:995-1031`), starting from no assumptions. -/
def none_ : EffectFlags := ⟨false, false, false, false, false, false, false, false, false, false, false⟩
def assumeSetting (o : EffectFlags) : String → EffectFlags
  | "consistent" => { o with consistent := true }
  | "effect_free" => { o with effectFree := true }
  | "nothrow" => { o with nothrow := true }
  | "terminates_globally" => { o with terminatesGlobally := true }
  | "terminates_locally" => { o with terminatesLocally := true }
  | "notaskstate" => { o with notaskstate := true }
  | "inaccessiblememonly" => { o with inaccessiblememonly := true }
  | "noub" => { o with noub := true }
  | "noub_if_noinbounds" => { o with noubIfNoinbounds := true }
  | "foldable" =>
    { o with consistent := true, effectFree := true, terminatesGlobally := true, noub := true, nortcall := true }
  | "total" =>
    { o with consistent := true, effectFree := true, nothrow := true, terminatesGlobally := true, notaskstate := true, inaccessiblememonly := true, noub := true, nortcall := true }
  | _ => o
def assumeEffects (settings : List String) : EffectFlags := settings.foldl assumeSetting none_

end JuliaLean.BootCov.Macros

end

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

/-- Julia exceptions thrown by the modelled functions (`JuliaLean.JlError` lacks
`ErrorException`, `KeyError` and `UndefVarError`). -/
inductive DErr where
  | errorException (msg : String)
  | argumentError (msg : String)
  | boundsError
  | methodError (fn : String)
  | keyError (key : String)
  | undefVarError (name : String)
  | typeError
  | assertionError
  | inexactError
  | stringIndexError
  | overflowError (msg : String)
  | eofError
  deriving Repr, DecidableEq, Inhabited

/-- A computation that returns a value or throws one of the exceptions above. -/
abbrev DJ (α : Type) := Except DErr α

/-- A Julia value as seen by the docsystem and `Base.Syntax`. -/
inductive JV where
  /-- A `Symbol`. -/
  | sym (name : String)
  /-- A `String`. -/
  | str (s : String)
  /-- An `Int`. -/
  | int (n : Int)
  /-- A `Bool`. -/
  | bool (b : Bool)
  /-- `nothing`. -/
  | nothing
  /-- `LineNumberNode(line, file)`; the empty name stands for `var""`. -/
  | lnn (line : Int) (file : String)
  /-- `QuoteNode(value)`. -/
  | qn (value : JV)
  /-- `GlobalRef(mod, name)`. -/
  | gref (mod name : String)
  /-- `Expr(head, args...)`. -/
  | expr (head : String) (args : List JV)
  /-- `Base.BaseDocs.Keyword(name)`. -/
  | keyword (name : String)
  /-- `Core.SSAValue(n)`. -/
  | ssa (n : Nat)
  /-- Any other value, by name: a module, a function, a type. -/
  | val (name : String)
  deriving Repr, Inhabited

namespace JV

/-- Structural equality of values (Julia `==` on `Expr`, `Symbol`, ...). -/
def beq : JV → JV → Bool
  | .sym a, .sym b => a == b
  | .str a, .str b => a == b
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .nothing, .nothing => true
  | .lnn l f, .lnn l' f' => l == l' && f == f'
  | .qn a, .qn b => beq a b
  | .gref m n, .gref m' n' => m == m' && n == n'
  | .expr h as, .expr h' bs => h == h' && beqList as bs
  | .keyword a, .keyword b => a == b
  | .ssa a, .ssa b => a == b
  | .val a, .val b => a == b
  | _, _ => false
where
  beqList : List JV → List JV → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false

instance : BEq JV := ⟨beq⟩

/-- `x.args` of an `Expr` (empty for other values). -/
def args : JV → List JV
  | .expr _ as => as
  | _ => []

/-- `x.head` of an `Expr`. -/
def head : JV → String
  | .expr h _ => h
  | _ => ""

/-- `x.args[i]` (1-based) or `none` when out of bounds (a `BoundsError`). -/
def arg? (x : JV) (i : Nat) : Option JV := x.args[i - 1]?

/-- `x.args[i]`, with `nothing` out of bounds; used only after a length check. -/
def arg (x : JV) (i : Nat) : JV := (x.arg? i).getD .nothing

/-- `x.args[end]`. -/
def lastArg (x : JV) : JV := x.args.getLastD .nothing

def isSym : JV → Bool
  | .sym _ => true
  | _ => false

def isQn : JV → Bool
  | .qn _ => true
  | _ => false

def isStr : JV → Bool
  | .str _ => true
  | _ => false

def isBool : JV → Bool
  | .bool _ => true
  | _ => false

def isLnn : JV → Bool
  | .lnn _ _ => true
  | _ => false

end JV

/-- `esc(ex)`: `Expr(:escape, ex)`. -/
def esc (x : JV) : JV := .expr "escape" [x]

/-- A call expression `Expr(:call, f, args...)`. -/
def call (f : JV) (as : List JV) : JV := .expr "call" (f :: as)

/-- Number of constructors in a value; bounds the iterations of the loops below. -/
def JV.size : JV → Nat
  | .qn v => v.size + 1
  | .expr _ as => sizeList as + 1
  | _ => 1
where
  sizeList : List JV → Nat
  | [] => 0
  | a :: as => a.size + sizeList as

/-! `Except` evaluation lemmas for the models of this area. -/

deriving instance DecidableEq for Except

end JuliaLean.DocsSyntaxCov

end


/-!
# Model of `base/expr.jl`

Typed model of the methods of `base/expr.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`
on a 64-bit platform. Each modelled method is a Lean definition whose docstring carries the
method's verbatim source; methods without a model are kept as `UNTRANSLATED` source blocks with
the reason.

* `Value L` is a value that can occur in an `Expr` tree (`Expr.args::Vector{Any}`): the AST and IR
  node types of `Core` are constructors, every other value is a `leaf` of the abstract type `L`
  (numbers, strings, `nothing`, modules, types, …), queried through `LeafOps`.
* `Expr`, `PhiNode` and `PhiCNode` are mutable in Julia. The model represents them by their
  contents: a method that mutates its argument in place returns the updated value, and `===`
  on these objects is content equality (two distinct Julia objects with equal contents are not
  distinguished; sharing of a subtree between two places is not represented).
* A macro is a function of its arguments (and of `__source__`/`__module__` where the body uses
  them) returning the expansion; `esc(e) = Expr(:escape, e)` is `base/essentials.jl`'s method.
* Runtime gensym, macro expansion, and opaque `CodeInfo` field operations are typed interfaces.
* Julia exceptions are `ExprError`.
-/

namespace JuliaLean.base.expr

open JuliaLean

/-- A Julia `Symbol`, by its name. -/
abbrev Sym := String
/-- The bytes of a Julia `String`. -/
abbrev Bytes := List UInt8
/-- An `Int` literal. -/
def i64 (z : Int) : JInt64 := JInt.wrap .i64 z

/-- A value stored in an AST: `Core`'s AST and IR node types, or any other value (`leaf`). -/
inductive Value (L : Type) where
  | expr (head : Sym) (args : List (Value L))
  | symbol (name : Sym)
  | quoteNode (value : Value L)
  | lineNumberNode (line : JInt64) (file : Value L)
  /-- `GlobalRef(mod, name)`; the module is a leaf value. -/
  | globalRef (mod : L) (name : Sym)
  | ssaValue (id : JInt64)
  | slotNumber (id : JInt64)
  | argument (n : JInt64)
  | newvarNode (slot : Value L)
  | gotoNode (label : JInt64)
  | gotoIfNot (cond : Value L) (dest : JInt64)
  /-- `EnterNode(catch_dest[, scope])`; `none` is an undefined `scope`. -/
  | enterNode (catch_dest : JInt64) (scope : Option (Value L))
  /-- `ReturnNode([val])`; `none` is an undefined `val` (unreachable). -/
  | returnNode (val : Option (Value L))
  | piNode (val : Value L) (typ : L)
  /-- `PhiNode(edges, values)`; `none` is an unassigned element of `values`. -/
  | phiNode (edges : List (JInt .i32)) (values : List (Option (Value L)))
  | phiCNode (values : List (Option (Value L)))
  | upsilonNode (val : Option (Value L))
  /-- A `CodeInfo` object. -/
  | codeInfo (ci : L)
  /-- A `Core.BindingPartition` object. -/
  | bindingPartition (b : L)
  /-- Any other value. -/
  | leaf (x : L)

/-- Operations on non-AST values. -/
structure LeafOps (L : Type) where
  nothing : L
  isNothing : L → Bool
  ofBool : Bool → L
  /-- `x::Bool`; `none` when `x` is not a `Bool`. -/
  asBool : L → Option Bool
  ofUInt16 : JInt .u16 → L
  ofInt : JInt64 → L
  /-- `===`. -/
  egal : L → L → Bool
  /-- `x isa typeof(y)`. -/
  sameType : L → L → Bool
  /-- The module `Base`. -/
  base : L

/-- Exceptions thrown by the modelled methods. -/
inductive ExprError where
  | jl (e : JlError)
  /-- `error(msg)`: an `ErrorException`. -/
  | errorException (msg : String)
  /-- A failed type assertion `x::T`. -/
  | typeError
  /-- `UndefRefError` of reading an unassigned array element. -/
  | undefRefError

abbrev ExprResult (α : Type) := Except ExprError α

section
variable {L : Type}

/-- `Expr(head, args...)`. -/
def mkExpr (head : Sym) (args : List (Value L)) : Value L := .expr head args

/-- `esc(e) = Expr(:escape, e)` (`base/essentials.jl`). -/
def esc (e : Value L) : Value L := .expr "escape" [e]

/-- `QuoteNode(:s)`. -/
def quoteSym (s : Sym) : Value L := .quoteNode (.symbol s)

/-- `x::Expr`. -/
def asExpr : Value L → ExprResult (Sym × List (Value L))
  | .expr h a => .ok (h, a)
  | _ => .error .typeError

/-- `args[i]` (1-based) of a `Vector{Any}`. -/
def argAt (args : List (Value L)) (i : Nat) : ExprResult (Value L) :=
  match args[i - 1]? with
  | some x => if i = 0 then .error (.jl .boundsError) else .ok x
  | none => .error (.jl .boundsError)

/-- `args[2:end]`. -/
def argsFrom2 (args : List (Value L)) : List (Value L) := args.drop 1

mutual
/-- `===` of two AST values. Immutable node types compare field by field; `Expr`, `PhiNode` and
`PhiCNode` compare by contents (see the module documentation). -/
def egal (lo : LeafOps L) : Value L → Value L → Bool
  | .expr h a, .expr h' a' => h == h' && egalList lo a a'
  | .symbol s, .symbol s' => s == s'
  | .quoteNode v, .quoteNode v' => egal lo v v'
  | .lineNumberNode l f, .lineNumberNode l' f' => l.val == l'.val && egal lo f f'
  | .globalRef m n, .globalRef m' n' => lo.egal m m' && n == n'
  | .ssaValue i, .ssaValue i' => i.val == i'.val
  | .slotNumber i, .slotNumber i' => i.val == i'.val
  | .argument i, .argument i' => i.val == i'.val
  | .newvarNode s, .newvarNode s' => egal lo s s'
  | .gotoNode l, .gotoNode l' => l.val == l'.val
  | .gotoIfNot c d, .gotoIfNot c' d' => egal lo c c' && d.val == d'.val
  | .enterNode c s, .enterNode c' s' => c.val == c'.val && egalOpt lo s s'
  | .returnNode v, .returnNode v' => egalOpt lo v v'
  | .piNode v t, .piNode v' t' => egal lo v v' && lo.egal t t'
  | .phiNode e v, .phiNode e' v' => e.map (·.val) == e'.map (·.val) && egalOptList lo v v'
  | .phiCNode v, .phiCNode v' => egalOptList lo v v'
  | .upsilonNode v, .upsilonNode v' => egalOpt lo v v'
  | .codeInfo c, .codeInfo c' => lo.egal c c'
  | .bindingPartition b, .bindingPartition b' => lo.egal b b'
  | .leaf x, .leaf x' => lo.egal x x'
  | _, _ => false
def egalList (lo : LeafOps L) : List (Value L) → List (Value L) → Bool
  | [], [] => true
  | x :: xs, y :: ys => egal lo x y && egalList lo xs ys
  | _, _ => false
def egalOpt (lo : LeafOps L) : Option (Value L) → Option (Value L) → Bool
  | none, none => true
  | some x, some y => egal lo x y
  | _, _ => false
def egalOptList (lo : LeafOps L) : List (Option (Value L)) → List (Option (Value L)) → Bool
  | [], [] => true
  | x :: xs, y :: ys => egalOpt lo x y && egalOptList lo xs ys
  | _, _ => false
end

/-- `x isa typeof(y)`: same node type, or leaves of the same type. -/
def sameType (lo : LeafOps L) : Value L → Value L → Bool
  | .expr .., .expr .. | .symbol _, .symbol _ | .quoteNode _, .quoteNode _
  | .lineNumberNode .., .lineNumberNode .. | .globalRef .., .globalRef .. | .ssaValue _, .ssaValue _
  | .slotNumber _, .slotNumber _ | .argument _, .argument _ | .newvarNode _, .newvarNode _
  | .gotoNode _, .gotoNode _ | .gotoIfNot .., .gotoIfNot .. | .enterNode .., .enterNode ..
  | .returnNode _, .returnNode _ | .piNode .., .piNode .. | .phiNode .., .phiNode ..
  | .phiCNode _, .phiCNode _ | .upsilonNode _, .upsilonNode _ | .codeInfo _, .codeInfo _
  | .bindingPartition _, .bindingPartition _ => true
  | .leaf x, .leaf y => lo.sameType x y
  | _, _ => false

/-- `x === nothing`. -/
def isNothing (lo : LeafOps L) : Value L → Bool
  | .leaf x => lo.isNothing x
  | _ => false

/-- `x === false`. -/
def isFalse (lo : LeafOps L) : Value L → Bool
  | .leaf x => lo.asBool x == some false
  | _ => false

/--
Julia source: base/expr.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# This file is a part of Julia. License is MIT: https://julialang.org/license

isexpr(@nospecialize(ex), heads) = isa(ex, Expr) && in(ex.head, heads)
isexpr(@nospecialize(ex), heads, n::Int) = isa(ex, Expr) && in(ex.head, heads) && length(ex.args) == n
```
-/
def isexpr_heads (ex : Value L) (heads : List Sym) : Bool :=
  match ex with
  | .expr head _ => heads.contains head
  | _ => false
def isexpr_heads_n (ex : Value L) (heads : List Sym) (n : JInt64) : Bool :=
  match ex with
  | .expr head args => heads.contains head && (i64 args.length).val == n.val
  | _ => false

structure GensymOps (S : Type) where
  untagged : S → Sym × S
  tagged : S → Bytes → JInt .u64 → Sym × S
  symbolBytes : Sym → Bytes

/--
Julia source: base/expr.jl:7-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## symbols ##

"""
    gensym([tag])

Generate a symbol unique among all calls to this function within the same process.
If a string or symbol tag argument is specified, it is included in the generated name.

Note that packages may be precompiled in separate processes, so names will not be unique
between definition time and run time.
"""
gensym() = ccall(:jl_gensym, Ref{Symbol}, ())

gensym(s::String) = ccall(:jl_tagged_gensym, Ref{Symbol}, (Ptr{UInt8}, Csize_t), s, sizeof(s))

gensym(ss::String...) = map(gensym, ss)
gensym(s::Symbol) = ccall(:jl_tagged_gensym, Ref{Symbol}, (Ptr{UInt8}, Csize_t), s, -1 % Csize_t)

```
-/
def gensym0 {S : Type} (ops : GensymOps S) (state : S) : Sym × S :=
  ops.untagged state

def gensymString {S : Type} (ops : GensymOps S) (state : S) (tag : Bytes) : Sym × S :=
  ops.tagged state tag (JInt.wrap .u64 (Int.ofNat tag.length))

def gensymStrings {S : Type} (ops : GensymOps S) : List Bytes → S → List Sym × S
  | [], state => ([], state)
  | tag :: tags, state =>
      let (symbol, nextState) := gensymString ops state tag
      let (symbols, finalState) := gensymStrings ops tags nextState
      (symbol :: symbols, finalState)

def gensymSymbol {S : Type} (ops : GensymOps S) (state : S) (tag : Sym) : Sym × S :=
  ops.tagged state (ops.symbolBytes tag) (JInt.wrap .u64 (-1))

/--
Julia source: base/expr.jl:25-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @gensym var1 var2 ...

Generate symbols with [`gensym`](@ref) and assign them to the given variables.
For example, `@gensym x y` is transformed into `x = gensym("x"); y = gensym("y")`.
"""
macro gensym(names...)
    blk = Expr(:block)
    for name in names
        push!(blk.args, :($(esc(name)) = gensym($(string(name)))))
    end
    push!(blk.args, :nothing)
    return blk
end

```
-/
def macro_gensym (string : Value L → Bytes) (ofString : Bytes → L) (names : List (Value L)) : Value L := Id.run do
  let mut blk : List (Value L) := []
  for name in names do
    blk := blk ++ [.expr "=" [esc name, .expr "call" [.symbol "gensym", .leaf (ofString (string name))]]]
  blk := blk ++ [.symbol "nothing"]
  return .expr "block" blk

/--
Julia source: base/expr.jl:40-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## expressions ##

isexpr(@nospecialize(ex), head::Symbol) = isa(ex, Expr) && ex.head === head
isexpr(@nospecialize(ex), head::Symbol, n::Int) = isa(ex, Expr) && ex.head === head && length(ex.args) == n

```
-/
def isexpr (ex : Value L) (head : Sym) : Bool :=
  match ex with
  | .expr h _ => h == head
  | _ => false
def isexpr_n (ex : Value L) (head : Sym) (n : JInt64) : Bool :=
  match ex with
  | .expr h args => h == head && (i64 args.length).val == n.val
  | _ => false

/--
Julia source: base/expr.jl:5-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const is_expr = isexpr

```
-/
-- `is_expr` names the generic function `isexpr`; its methods with a `Symbol` head.
abbrev is_expr (ex : Value L) (head : Sym) : Bool := isexpr ex head
abbrev is_expr_n (ex : Value L) (head : Sym) (n : JInt64) : Bool := isexpr_n ex head n

/--
Julia source: base/expr.jl:81-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@eval exprarray(head::Symbol, arg::Array{Any,1}) = $(Expr(:new, :Expr, :head, :arg))

```
-/
def exprarray (head : Sym) (arg : List (Value L)) : Value L := .expr head arg

mutual

/--
Julia source: base/expr.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(e::Expr) = exprarray(e.head, copy_exprargs(e.args))
```
-/
def copy_Expr (head : Sym) (args : List (Value L)) : Value L :=
  exprarray head (copy_exprargs args)

/--
Julia source: base/expr.jl:46-55 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy(x::PhiNode)
    values = x.values
    nvalues = length(values)
    new_values = Vector{Any}(undef, nvalues)
    @inbounds for i = 1:nvalues
        isassigned(values, i) || continue
        new_values[i] = copy_exprs(values[i])
    end
    return PhiNode(copy(x.edges), new_values)
end
```
-/
def copy_PhiNode (edges : List (JInt .i32)) (values : List (Option (Value L))) : Value L :=
  -- `isassigned(values, i) || continue` leaves `new_values[i]` unassigned.
  .phiNode edges (copy_phivalues values)

/--
Julia source: base/expr.jl:56-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy(x::PhiCNode)
    values = x.values
    nvalues = length(values)
    new_values = Vector{Any}(undef, nvalues)
    @inbounds for i = 1:nvalues
        isassigned(values, i) || continue
        new_values[i] = copy_exprs(values[i])
    end
    return PhiCNode(new_values)
end

```
-/
def copy_PhiCNode (values : List (Option (Value L))) : Value L :=
  .phiCNode (copy_phivalues values)

/--
Julia source: base/expr.jl:67-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# copy parts of an IR that the compiler mutates
# (this is not a general-purpose copy for an Expr AST)
function copy_exprs(@nospecialize(x))
    if isa(x, Expr)
        return copy(x)
    elseif isa(x, PhiNode)
        return copy(x)
    elseif isa(x, PhiCNode)
        return copy(x)
    end
    return x
end
copy_exprargs(x::Array{Any,1}) = Any[copy_exprs(@inbounds x[i]) for i in eachindex(x)]

```
-/
def copy_exprs : Value L → Value L
  | .expr h a => copy_Expr h a
  | .phiNode e v => copy_PhiNode e v
  | .phiCNode v => copy_PhiCNode v
  | x => x
def copy_exprargs : List (Value L) → List (Value L)
  | [] => []
  | x :: xs => copy_exprs x :: copy_exprargs xs

/-- The `for i = 1:nvalues` loop of `copy(::PhiNode)`/`copy(::PhiCNode)`. -/
def copy_phivalues : List (Option (Value L)) → List (Option (Value L))
  | [] => []
  | none :: xs => none :: copy_phivalues xs
  | some x :: xs => some (copy_exprs x) :: copy_phivalues xs
end

/-- `copy(x)` of an AST value: `Expr`, `PhiNode` and `PhiCNode` have `copy` methods. -/
def copy (x : Value L) : Value L := copy_exprs x

structure CodeInfoCopyOps (L C : Type) where
  jlCopyCodeInfo : C → ExprResult C
  code : C → List (Value L)
  setCode : C → List (Value L) → C
  slotnames : C → L
  setSlotnames : C → L → C
  slotflags : C → L
  setSlotflags : C → L → C
  slottypes : C → L
  setSlottypes : C → L → C
  ssaflags : C → L
  setSsaflags : C → L → C
  edges : C → L
  setEdges : C → L → C
  ssavaluetypes : C → L
  setSsavaluetypes : C → L → C
  copyArray : L → ExprResult L
  isVectorAny : L → Bool
  isSimpleVector : L → Bool
  isVector : L → Bool

/--
Julia source: base/expr.jl:83-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# create copies of the CodeInfo definition, and any mutable fields
function copy(c::CodeInfo)
    cnew = ccall(:jl_copy_code_info, Ref{CodeInfo}, (Any,), c)
    cnew.code = copy_exprargs(cnew.code)
    cnew.slotnames = copy(cnew.slotnames)
    cnew.slotflags = copy(cnew.slotflags)
    if cnew.slottypes !== nothing
        cnew.slottypes = copy(cnew.slottypes::Vector{Any})
    end
    cnew.ssaflags  = copy(cnew.ssaflags)
    cnew.edges     = cnew.edges === nothing || cnew.edges isa Core.SimpleVector ? cnew.edges : copy(cnew.edges::Vector)
    ssavaluetypes  = cnew.ssavaluetypes
    ssavaluetypes isa Vector{Any} && (cnew.ssavaluetypes = copy(ssavaluetypes))
    return cnew
end

```
-/
def copy_CodeInfo {L C : Type} (lo : LeafOps L) (ops : CodeInfoCopyOps L C) (c : C) :
    ExprResult C := do
  let cnew ← ops.jlCopyCodeInfo c
  let cnew := ops.setCode cnew (copy_exprargs (ops.code cnew))
  let slotnames ← ops.copyArray (ops.slotnames cnew)
  let cnew := ops.setSlotnames cnew slotnames
  let slotflags ← ops.copyArray (ops.slotflags cnew)
  let cnew := ops.setSlotflags cnew slotflags
  let slottypes := ops.slottypes cnew
  let cnew ←
    if lo.isNothing slottypes then
      pure cnew
    else if !ops.isVectorAny slottypes then
      throw .typeError
    else do
      let slottypes ← ops.copyArray slottypes
      pure (ops.setSlottypes cnew slottypes)
  let ssaflags ← ops.copyArray (ops.ssaflags cnew)
  let cnew := ops.setSsaflags cnew ssaflags
  let edges := ops.edges cnew
  let cnew ←
    if lo.isNothing edges || ops.isSimpleVector edges then
      pure cnew
    else if !ops.isVector edges then
      throw .typeError
    else do
      let edges ← ops.copyArray edges
      pure (ops.setEdges cnew edges)
  let ssavaluetypes := ops.ssavaluetypes cnew
  let cnew ←
    if ops.isVectorAny ssavaluetypes then do
      let ssavaluetypes ← ops.copyArray ssavaluetypes
      pure (ops.setSsavaluetypes cnew ssavaluetypes)
    else
      pure cnew
  return cnew

mutual

/--
Julia source: base/expr.jl:99-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isequal_exprarg(@nospecialize(x), @nospecialize(y))
    x isa typeof(y) || return false
    x === y && return true
    # c.f. list of types in copy_expr also
    if x isa Expr
        x == (y::Expr) && return true
    elseif x isa QuoteNode
        x == (y::QuoteNode) && return true
    elseif x isa PhiNode
        x == (y::PhiNode) && return true
    elseif x isa PhiCNode
        x == (y::PhiCNode) && return true
    elseif x isa CodeInfo
        x == (y::CodeInfo) && return true
    end
    return false
end


```
-/
def isequal_exprarg (lo : LeafOps L) (codeInfoEq : L → L → Bool) (x y : Value L) : Bool :=
  if !sameType lo x y then false
  -- `x === y && return true`; for `Expr`, `QuoteNode`, `PhiNode` and `PhiCNode` the `==` below
  -- holds whenever `===` does.
  else if (match x with
      | .expr .. | .quoteNode _ | .phiNode .. | .phiCNode _ => false
      | _ => egal lo x y) then true
  else match x, y with
    | .expr h a, .expr h' a' => eq_Expr lo codeInfoEq h a h' a'
    | .quoteNode v, .quoteNode v' => eq_QuoteNode lo codeInfoEq v v'
    | .phiNode e v, .phiNode e' v' => eq_PhiNode lo codeInfoEq e v e' v'
    | .phiCNode v, .phiCNode v' => eq_PhiCNode lo codeInfoEq v v'
    | .codeInfo c, .codeInfo c' => codeInfoEq c c'
    | _, _ => false

/--
Julia source: base/expr.jl:118-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function isequal_exprargs(x::Array{Any,1}, y::Array{Any,1})
    l = length(x)
    l == length(y) || return false
    for i = 1:l
        if !isassigned(x, i)
            # phi and phic values are permitted to be undef
            isassigned(y, i) && return false
        else
            isassigned(y, i) || return false
            isequal_exprarg(x[i], y[i]) || return false
        end
    end
    return true
end

```
-/
-- `isequal_exprargs` on `Vector{Any}`s whose unassigned elements are `none`.
def isequal_exprargs (lo : LeafOps L) (codeInfoEq : L → L → Bool) :
    List (Option (Value L)) → List (Option (Value L)) → Bool
  | [], [] => true
  | none :: xs, none :: ys => isequal_exprargs lo codeInfoEq xs ys
  | none :: _, some _ :: _ => false
  | some _ :: _, none :: _ => false
  | some x :: xs, some y :: ys => isequal_exprarg lo codeInfoEq x y && isequal_exprargs lo codeInfoEq xs ys
  -- `l == length(y) || return false`
  | _, _ => false

/--
Julia source: base/expr.jl:133-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# define == such that == inputs to parsing (including line numbers) yield == outputs from lowering (including all metadata)
# (aside from cases where parsing just returns a number, which are ambiguous here)
==(x::Expr, y::Expr) = x.head === y.head && isequal_exprargs(x.args, y.args)

==(x::QuoteNode, y::QuoteNode) = isequal_exprarg(x.value, y.value)

==(stmt1::Core.PhiNode, stmt2::Core.PhiNode) = isequal(stmt1.edges, stmt2.edges) && isequal_exprargs(stmt1.values, stmt2.values)

==(stmt1::Core.PhiCNode, stmt2::Core.PhiCNode) = isequal_exprargs(stmt1.values, stmt2.values)

```
-/
def eq_Expr (lo : LeafOps L) (codeInfoEq : L → L → Bool) (h : Sym) (a : List (Value L)) (h' : Sym)
    (a' : List (Value L)) : Bool :=
  h == h' && isequal_exprargs_all lo codeInfoEq a a'
def eq_QuoteNode (lo : LeafOps L) (codeInfoEq : L → L → Bool) (x y : Value L) : Bool :=
  isequal_exprarg lo codeInfoEq x y
def eq_PhiNode (lo : LeafOps L) (codeInfoEq : L → L → Bool) (e : List (JInt .i32)) (v : List (Option (Value L)))
    (e' : List (JInt .i32)) (v' : List (Option (Value L))) : Bool :=
  e.map (·.val) == e'.map (·.val) && isequal_exprargs lo codeInfoEq v v'
def eq_PhiCNode (lo : LeafOps L) (codeInfoEq : L → L → Bool) (v v' : List (Option (Value L))) : Bool :=
  isequal_exprargs lo codeInfoEq v v'

/-- `isequal_exprargs` on the `args` of two `Expr`s, whose elements are all assigned. -/
def isequal_exprargs_all (lo : LeafOps L) (codeInfoEq : L → L → Bool) :
    List (Value L) → List (Value L) → Bool
  | [], [] => true
  | x :: xs, y :: ys => isequal_exprarg lo codeInfoEq x y && isequal_exprargs_all lo codeInfoEq xs ys
  | _, _ => false
end

inductive CodeInfoFieldKind where
  | anyVector
  | debugInfo
  | vector
  | other
  deriving DecidableEq

structure CodeInfoEqOps (L : Type) where
  fieldCount : L → Nat
  isDefined : L → Nat → Bool
  sameFieldType : L → L → Nat → Bool
  fieldKind : L → Nat → CodeInfoFieldKind
  anyVector : L → Nat → List (Option (Value L))
  debugInfo : L → Nat → L
  debugInfoEqual : L → L → Bool
  vector : L → Nat → List L
  identical : L → L → Bool
  identicalField : L → L → Nat → Bool
  leaves : LeafOps L

def identicalList {L : Type} (identical : L → L → Bool) : List L → List L → Bool
  | [], [] => true
  | x :: xs, y :: ys => identical x y && identicalList identical xs ys
  | _, _ => false

def codeInfoFieldEqual {L : Type} (ops : CodeInfoEqOps L)
    (codeInfoEq : L → L → Bool) (x y : L) (i : Nat) : Bool :=
  if !ops.sameFieldType x y i then false else
  match ops.fieldKind x i, ops.fieldKind y i with
  | .anyVector, .anyVector =>
    isequal_exprargs ops.leaves codeInfoEq (ops.anyVector x i) (ops.anyVector y i)
  | .debugInfo, .debugInfo => ops.debugInfoEqual (ops.debugInfo x i) (ops.debugInfo y i)
  | .vector, .vector => identicalList ops.identical (ops.vector x i) (ops.vector y i)
  | .other, .other => ops.identicalField x y i
  | _, _ => false

def codeInfoFieldsEqual {L : Type} (ops : CodeInfoEqOps L)
    (codeInfoEq : L → L → Bool) (x y : L) : List Nat → Bool
  | [] => true
  | i :: rest =>
    if !ops.isDefined x i then
      !ops.isDefined y i && codeInfoFieldsEqual ops codeInfoEq x y rest
    else if !ops.isDefined y i then false
    else codeInfoFieldEqual ops codeInfoEq x y i && codeInfoFieldsEqual ops codeInfoEq x y rest


/-!
Julia source: base/expr.jl:143-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(stmt1::CodeInfo, stmt2::CodeInfo)
    for i in 1:nfields(stmt1)
        if !isdefined(stmt1, i)
            isdefined(stmt2, i) && return false
        else
            isdefined(stmt2, i) || return false
            f1 = getfield(stmt1, i)
            f2 = getfield(stmt2, i)
            f1 isa typeof(f2) || return false
            if f1 isa Vector{Any}
                # code or types vectors
                isequal_exprargs(f1, f2::Vector{Any}) || return false
            elseif f1 isa DebugInfo
                f1 == f2::DebugInfo || return false
            elseif f1 isa Vector
                # misc data
                l = length(f1)
                l == length(f2::Vector) || return false
                for i = 1:l
                    f1[i] === f2[i] || return false
                end
            else
                # misc fields
                f1 === f2 || return false
            end
        end
    end
    return true
end

```
-/
partial def eqCodeInfo {L : Type} (ops : CodeInfoEqOps L) (x y : L) : Bool :=
  codeInfoFieldsEqual ops (fun a b => eqCodeInfo ops a b) x y
    ((List.range (ops.fieldCount x)).map (· + 1))

structure DebugInfoEqOps (D L : Type) where
  fieldCount : D → Nat
  getField : D → Nat → ExprResult L
  eqField : L → L → ExprResult Bool

def debugInfoEqFields {D L : Type} (ops : DebugInfoEqOps D L) (x y : D) :
    Nat → Nat → ExprResult Bool
  | 0, _ => .ok true
  | remaining + 1, index => do
      let left ← ops.getField x index
      let right ← ops.getField y index
      let equal ← ops.eqField left right
      if equal then debugInfoEqFields ops x y remaining (index + 1) else pure false

/--
Julia source: base/expr.jl:173-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(x::DebugInfo, y::DebugInfo)
    for i in 1:nfields(x)
        getfield(x, i) == getfield(y, i) || return false
    end
    return true
end
```
-/
def eq_DebugInfo {D L : Type} (ops : DebugInfoEqOps D L) (x y : D) : ExprResult Bool :=
  debugInfoEqFields ops x y (ops.fieldCount x) 1

structure MacroexpandOps (L : Type) where
  call : Value L → L → JInt .i32 → JInt .i32 → JInt .i32 → ExprResult (Value L)

def boolCint (value : Bool) : JInt .i32 :=
  JInt.wrap .i32 (if value then 1 else 0)

/--
Julia source: base/expr.jl:180-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    macroexpand(m::Module, x; recursive=true, legacyscope=true)

Take the expression `x` and return an equivalent expression with all macros removed (expanded)
for executing in module `m`.
The `recursive` keyword controls whether deeper levels of nested macros are also expanded.
The `legacyscope` keyword controls whether legacy macroscope expansion is performed.
This is demonstrated in the example below:
```jldoctest; filter = r"#= .*:6 =#"
julia> module M
           macro m1()
               42
           end
           macro m2()
               :(@m1())
           end
       end
M

julia> macroexpand(M, :(@m2()), recursive=true)
42

julia> macroexpand(M, :(@m2()), recursive=false)
:(#= REPL[1]:6 =# @m1)
```

!!! compat "Julia 1.13"
    The `legacyscope` keyword argument requires at least Julia 1.13.
"""
function macroexpand(m::Module, @nospecialize(x); recursive=true, legacyscope=true)
    ccall(:jl_macroexpand, Any, (Any, Any, Cint, Cint, Cint), x, m, recursive, false, legacyscope)
end

"""
    macroexpand!(m::Module, x; recursive=true, legacyscope=false)

Take the expression `x` and return an equivalent expression with all macros removed (expanded)
for executing in module `m`, modifying `x` in place without copying.
The `recursive` keyword controls whether deeper levels of nested macros are also expanded.
The `legacyscope` keyword controls whether legacy macroscope expansion is performed.

This function performs macro expansion without the initial copy step, making it more efficient
when the original expression is no longer needed. By default, macroscope expansion is disabled
for in-place expansion as it can be called separately if needed.

!!! warning
    This function modifies the input expression `x` in place. Use `macroexpand` if you need
    to preserve the original expression.

!!! compat "Julia 1.13"
    This function requires at least Julia 1.13.
"""
function macroexpand!(m::Module, @nospecialize(x); recursive=true, legacyscope=false)
    ccall(:jl_macroexpand, Any, (Any, Any, Cint, Cint, Cint), x, m, recursive, true, legacyscope)
end

````
-/
def macroexpand {L : Type} (ops : MacroexpandOps L) (mod : L) (x : Value L)
    (recursive : Bool := true) (legacyscope : Bool := true) : ExprResult (Value L) :=
  ops.call x mod (boolCint recursive) (boolCint false) (boolCint legacyscope)

def macroexpandBang {L : Type} (ops : MacroexpandOps L) (mod : L) (x : Value L)
    (recursive : Bool := true) (legacyscope : Bool := false) : ExprResult (Value L) :=
  ops.call x mod (boolCint recursive) (boolCint true) (boolCint legacyscope)

/-- `macroexpand(mod, QuoteNode(code); recursive, legacyscope)` as parsed: keyword arguments
are a leading `:parameters` argument. -/
def macroexpandCall (lo : LeafOps L) (mod code : Value L) (recursive : Bool) : Value L :=
  .expr "call" [.symbol "macroexpand",
    .expr "parameters" [.expr "kw" [.symbol "recursive", .leaf (lo.ofBool recursive)],
      .expr "kw" [.symbol "legacyscope", .leaf (lo.ofBool true)]],
    mod, .quoteNode code]

/--
Julia source: base/expr.jl:236-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @macroexpand [mod,] ex

Return equivalent expression with all macros removed (expanded).
If two arguments are provided, the first is the module to evaluate in.

There are differences between `@macroexpand` and [`macroexpand`](@ref).

* While [`macroexpand`](@ref) takes a keyword argument `recursive`, `@macroexpand`
  is always recursive. For a non recursive macro version, see [`@macroexpand1`](@ref).

* While [`macroexpand`](@ref) has an explicit `module` argument, `@macroexpand` always
  expands with respect to the module in which it is called.

This is best seen in the following example:
```jldoctest
julia> module M
           macro m()
               1
           end
           function f()
               (@macroexpand(@m),
                macroexpand(M, :(@m)),
                macroexpand(parentmodule(M), :(@m))
               )
           end
       end
M

julia> macro m()
           2
       end
@m (macro with 1 method)

julia> M.f()
(1, 1, 2)
```
With `@macroexpand` the expression expands where `@macroexpand` appears in the code (module `M` in the example).
With `macroexpand` the expression expands in the module given as the first argument.

!!! compat "Julia 1.11"
    The two-argument form requires at least Julia 1.11.
"""
macro macroexpand(code)
    return :(macroexpand($__module__, $(QuoteNode(code)); recursive=true, legacyscope=true))
end
macro macroexpand(mod, code)
    return :(macroexpand($(esc(mod)), $(QuoteNode(code)); recursive=true, legacyscope=true))
end

````
-/
def macro_macroexpand (lo : LeafOps L) (__module__ : L) (code : Value L) : Value L :=
  macroexpandCall lo (.leaf __module__) code true
def macro_macroexpand_mod (lo : LeafOps L) (mod code : Value L) : Value L :=
  macroexpandCall lo (esc mod) code true

/--
Julia source: base/expr.jl:286-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @macroexpand1 [mod,] ex

Non recursive version of [`@macroexpand`](@ref).
"""
macro macroexpand1(code)
    return :(macroexpand($__module__, $(QuoteNode(code)); recursive=false, legacyscope=true))
end
macro macroexpand1(mod, code)
    return :(macroexpand($(esc(mod)), $(QuoteNode(code)); recursive=false, legacyscope=true))
end

```
-/
def macro_macroexpand1 (lo : LeafOps L) (__module__ : L) (code : Value L) : Value L :=
  macroexpandCall lo (.leaf __module__) code false
def macro_macroexpand1_mod (lo : LeafOps L) (mod code : Value L) : Value L :=
  macroexpandCall lo (esc mod) code false

-- UNTRANSLATED
-- docstring attached to the builtin `Core.eval`; no method
-- Source: base/expr.jl:298-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ## misc syntax ##
-- 
-- """
--     Core.eval(m::Module, expr)
-- 
-- Evaluate an expression in the given module and return the result.
-- """
-- Core.eval
-- 
-- /Source

/--
Julia source: base/expr.jl:1165-1175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## some macro utilities ##

unwrap_macrocalls(@nospecialize(x)) = x
function unwrap_macrocalls(ex::Expr)
    inner = ex
    while isexpr(inner, :macrocall)
        inner = inner.args[end]
    end
    return inner
end

```
-/
def unwrap_macrocalls_Any (x : Value L) : Value L := x
mutual
/-- `unwrap_macrocalls(ex::Expr)`, with the path of `args[end]` indices to the result. -/
def unwrap_macrocalls_path : Value L → ExprResult (Value L × List Nat)
  | .expr "macrocall" args => unwrap_macrocalls_last args 0
  | ex => .ok (ex, [])
/-- `inner = inner.args[end]` (`BoundsError` when `args` is empty). -/
def unwrap_macrocalls_last : List (Value L) → Nat → ExprResult (Value L × List Nat)
  | [], _ => .error (.jl .boundsError)
  | [inner], i => do
    let (r, path) ← unwrap_macrocalls_path inner
    return (r, i :: path)
  | _ :: rest, i => unwrap_macrocalls_last rest (i + 1)
end
def unwrap_macrocalls (ex : Value L) : ExprResult (Value L) := do
  return (← unwrap_macrocalls_path ex).1

/-- Replace the subtree of `x` at `path` (each step an index into an `Expr`'s `args`) by `f` of
it: in-place mutation of a nested object. -/
def modifyAt (f : Value L → ExprResult (Value L)) : List Nat → Value L → ExprResult (Value L)
  | [], x => f x
  | i :: path, .expr h args =>
    match args[i]? with
    | some a => do return .expr h (args.set i (← modifyAt f path a))
    | none => .error (.jl .boundsError)
  | _ :: _, _ => .error .typeError

/-- Replace the `args` array at `path` inside `args`: each step descends into `args[i].args`. -/
def modifyArgsAt (f : List (Value L) → ExprResult (List (Value L))) :
    List Nat → List (Value L) → ExprResult (List (Value L))
  | [], args => f args
  | i :: path, args =>
    match args[i]? with
    | some (.expr h a) => do return args.set i (.expr h (← modifyArgsAt f path a))
    | some _ => .error .typeError
    | none => .error (.jl .boundsError)

mutual

/--
Julia source: base/expr.jl:1265-1281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findmeta_block(exargs, argsmatch=args->true)
    for i = 1:length(exargs)
        a = exargs[i]
        if isa(a, Expr)
            if a.head === :meta && argsmatch(a.args)
                return i, exargs
            elseif a.head === :block
                idx, exa = findmeta_block(a.args, argsmatch)
                if idx != 0
                    return idx, exa
                end
            end
        end
    end
    return 0, []
end

```
-/
def findmeta_block (exargs : List (Value L)) (argsmatch : List (Value L) → Bool := fun _ => true) :
    Nat × List (Value L) × List Nat :=
  findmeta_block_loop exargs argsmatch exargs 0

/-- The `for i = 1:length(exargs)` loop of `findmeta_block`, from the 0-based index `i`; it also
returns the path (indices of nested `:block` arguments) of the returned array inside `exargs`. -/
def findmeta_block_loop (exargs : List (Value L)) (argsmatch : List (Value L) → Bool) :
    List (Value L) → Nat → Nat × List (Value L) × List Nat
  | [], _ => (0, [], [])
  | a :: rest, i =>
    match a with
    | .expr "meta" margs =>
      if argsmatch margs then (i + 1, exargs, [])
      else findmeta_block_loop exargs argsmatch rest (i + 1)
    | .expr "block" bargs =>
      let (idx, exa, path) := findmeta_block bargs argsmatch
      if idx != 0 then (idx, exa, i :: path)
      else findmeta_block_loop exargs argsmatch rest (i + 1)
    | _ => findmeta_block_loop exargs argsmatch rest (i + 1)
end

/--
Julia source: base/expr.jl:1215-1226 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Find index of `sym` in a meta expression argument list, or 0.
function findmetaarg(metaargs, sym)
    for i = 1:length(metaargs)
        arg = metaargs[i]
        if (isa(arg, Symbol) && (arg::Symbol)    == sym) ||
           (isa(arg, Expr)   && (arg::Expr).head == sym)
            return i
        end
    end
    return 0
end

```
-/
def findmetaarg (metaargs : List (Value L)) (sym : Sym) : Nat :=
  go metaargs 1
where
  go : List (Value L) → Nat → Nat
    | [], _ => 0
    | arg :: rest, i =>
      match arg with
      | .symbol s => if s == sym then i else go rest (i + 1)
      | .expr head _ => if head == sym then i else go rest (i + 1)
      | _ => go rest (i + 1)

/--
Julia source: base/expr.jl:1242-1253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function is_short_function_def(@nospecialize(ex))
    isexpr(ex, :(=)) || return false
    while length(ex.args) >= 1 && isa(ex.args[1], Expr)
        (ex.args[1].head === :call) && return true
        (ex.args[1].head === :where || ex.args[1].head === :(::)) || return false
        ex = ex.args[1]::Expr
    end
    return false
end
is_function_def(@nospecialize(ex)) =
    return isexpr(ex, :function) || is_short_function_def(ex) || isexpr(ex, :->)

```
-/
def is_short_function_def : Value L → Bool
  | .expr "=" args =>
    match args with
    | (.expr "call" _) :: _ => true
    | (.expr "where" a) :: _ | (.expr "::" a) :: _ => is_short_function_def_loop a
    | _ => false
  | _ => false
where
  /-- The `while` loop after `ex = ex.args[1]::Expr`. -/
  is_short_function_def_loop : List (Value L) → Bool
    | (.expr "call" _) :: _ => true
    | (.expr "where" a) :: _ | (.expr "::" a) :: _ => is_short_function_def_loop a
    | _ => false
def is_function_def (ex : Value L) : Bool :=
  isexpr ex "function" || is_short_function_def ex || isexpr ex "->"

/--
Julia source: base/expr.jl:1254-1262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findmeta(ex::Expr)
    if is_function_def(ex)
        body = ex.args[2]::Expr
        body.head === :block || error(body, " is not a block expression")
        return findmeta_block(ex.args)
    end
    error(ex, " is not a function expression")
end

```
-/
def findmeta (ex : Value L) : ExprResult (Nat × List (Value L) × List Nat) :=
  if is_function_def ex then
    match ex with
    | .expr _ args => do
      match ← argAt args 2 with
      | .expr "block" _ => return findmeta_block args
      | .expr _ _ => .error (.errorException "is not a block expression")
      | _ => .error .typeError
    | _ => .error .typeError
  else .error (.errorException "is not a function expression")

/--
Julia source: base/expr.jl:1263-1264 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findmeta(ex::Array{Any,1}) = findmeta_block(ex)

```
-/
def findmeta_Array (ex : List (Value L)) : Nat × List (Value L) × List Nat := findmeta_block ex

/--
Julia source: base/expr.jl:1176-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushmeta!(ex::Expr, tag::Union{Symbol,Expr})
    inner = unwrap_macrocalls(ex)
    idx, exargs = findmeta(inner)
    if idx != 0
        metastmt = exargs[idx]::Expr
        push!(metastmt.args, tag)
    else
        body = inner.args[2]::Expr
        pushfirst!(body.args, Expr(:meta, tag))
    end
    return ex
end

```
-/
def pushmeta! (ex : Value L) (tag : Value L) : ExprResult (Value L) := do
  let (inner, innerPath) ← unwrap_macrocalls_path ex
  let (idx, _exargs, path) ← findmeta inner
  modifyAt (fun inner => do
    match inner with
    | .expr h args =>
      if idx != 0 then
        -- `metastmt = exargs[idx]::Expr; push!(metastmt.args, tag)`
        return .expr h (← modifyArgsAt (fun exargs => do
          match exargs[idx - 1]? with
          | some (.expr mh margs) => return exargs.set (idx - 1) (.expr mh (margs ++ [tag]))
          | some _ => .error .typeError
          | none => .error (.jl .boundsError)) path args)
      else
        -- `body = inner.args[2]::Expr; pushfirst!(body.args, Expr(:meta, tag))`
        match ← argAt args 2 with
        | .expr bh bargs => return .expr h (args.set 1 (.expr bh (.expr "meta" [tag] :: bargs)))
        | _ => .error .typeError
    | _ => .error .typeError) innerPath ex

/--
Julia source: base/expr.jl:1192-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _getmeta(body::Expr, sym::Symbol, delete::Bool)
    body.head === :block || return false, []
    _getmeta(body.args, sym, delete)
end
_getmeta(arg, sym, delete::Bool) = (false, [])
function _getmeta(body::Array{Any,1}, sym::Symbol, delete::Bool)
    idx, blockargs = findmeta_block(body, args -> findmetaarg(args,sym)!=0)
    if idx == 0
        return false, []
    end
    metaargs = blockargs[idx].args
    i = findmetaarg(blockargs[idx].args, sym)
    if i == 0
        return false, []
    end
    ret = isa(metaargs[i], Expr) ? (metaargs[i]::Expr).args : []
    if delete
        deleteat!(metaargs, i)
        isempty(metaargs) && deleteat!(blockargs, idx)
    end
    true, ret
end

```
-/
-- `_getmeta(body::Array{Any,1}, sym, delete)`: the result and the (mutated) `body`.
def _getmeta_Array (body : List (Value L)) (sym : Sym) (delete : Bool) :
    ExprResult ((Bool × List (Value L)) × List (Value L)) := do
  let (idx, blockargs, path) := findmeta_block body (fun args => findmetaarg args sym != 0)
  if idx == 0 then return ((false, []), body)
  let metaargs ← match blockargs[idx - 1]? with
    | some (.expr _ a) => pure a
    | some _ => .error .typeError
    | none => .error (.jl .boundsError)
  let i := findmetaarg metaargs sym
  if i == 0 then return ((false, []), body)
  let ret := match metaargs[i - 1]? with
    | some (.expr _ a) => a
    | _ => []
  if delete then
    let body ← modifyArgsAt (fun blockargs => do
      match blockargs[idx - 1]? with
      | some (.expr mh margs) =>
        let margs := margs.eraseIdx (i - 1)
        if margs.isEmpty then return blockargs.eraseIdx (idx - 1)
        else return blockargs.set (idx - 1) (.expr mh margs)
      | _ => .error .typeError) path body
    return ((true, ret), body)
  return ((true, ret), body)
/-- `_getmeta(body::Expr, sym, delete)`. -/
def _getmeta_Expr (head : Sym) (args : List (Value L)) (sym : Sym) (delete : Bool) :
    ExprResult ((Bool × List (Value L)) × Value L) := do
  if head != "block" then return ((false, []), .expr head args)
  let (r, args) ← _getmeta_Array args sym delete
  return (r, .expr head args)
def _getmeta_Any {X : Type} (arg : X) (_sym : Sym) (_delete : Bool) : (Bool × List (Value L)) × X :=
  ((false, []), arg)

/-- A `body` argument of `popmeta!`/`peekmeta`: an `Expr`, an `Array{Any,1}`, or another value. -/
inductive MetaBody (L : Type) where
  | expr (x : Value L)
  | array (args : List (Value L))

/-- *dispatch*: `_getmeta(body, sym, delete)`. -/
def _getmeta (body : MetaBody L) (sym : Sym) (delete : Bool) :
    ExprResult ((Bool × List (Value L)) × MetaBody L) :=
  match body with
  | .array args => do
    let (r, args) ← _getmeta_Array args sym delete
    return (r, .array args)
  | .expr (.expr h a) => do
    let (r, x) ← _getmeta_Expr h a sym delete
    return (r, .expr x)
  | .expr x => return (_getmeta_Any x sym delete).map id (fun x => .expr x)

/--
Julia source: base/expr.jl:1189-1191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
popmeta!(body, sym) = _getmeta(body, sym, true)
peekmeta(body, sym) = _getmeta(body, sym, false)

```
-/
def popmeta! (body : MetaBody L) (sym : Sym) : ExprResult ((Bool × List (Value L)) × MetaBody L) :=
  _getmeta body sym true
def peekmeta (body : MetaBody L) (sym : Sym) : ExprResult (Bool × List (Value L)) := do
  return (← _getmeta body sym false).1

/--
Julia source: base/expr.jl:1227-1241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function annotate_meta_def_or_block(@nospecialize(ex), meta::Symbol)
    inner = unwrap_macrocalls(ex)
    if is_function_def(inner)
        # annotation on a definition
        return esc(pushmeta!(ex, meta))
    else
        # annotation on a block
        return Expr(:block,
                    Expr(meta, true),
                    Expr(:local, Expr(:(=), :val, esc(ex))),
                    Expr(meta, false),
                    :val)
    end
end

```
-/
def annotate_meta_def_or_block (lo : LeafOps L) (ex : Value L) (meta_ : Sym) : ExprResult (Value L) := do
  let inner ← unwrap_macrocalls ex
  if is_function_def inner then
    -- annotation on a definition
    return esc (← pushmeta! ex (.symbol meta_))
  else
    -- annotation on a block
    return .expr "block" [.expr meta_ [.leaf (lo.ofBool true)],
      .expr "local" [.expr "=" [.symbol "val", esc ex]],
      .expr meta_ [.leaf (lo.ofBool false)],
      .symbol "val"]

/--
Julia source: base/expr.jl:307-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @inline

Give a hint to the compiler that this function is worth inlining.

Small functions typically do not need the `@inline` annotation,
as the compiler does it automatically. By using `@inline` on bigger functions,
an extra nudge can be given to the compiler to inline it.

`@inline` can be applied immediately before a function definition or within a function body.

```julia
# annotate long-form definition
@inline function longdef(x)
    ...
end

# annotate short-form definition
@inline shortdef(x) = ...

# annotate anonymous function that a `do` block creates
f() do
    @inline
    ...
end
```

!!! compat "Julia 1.8"
    The usage within a function body requires at least Julia 1.8.

---
    @inline block

Give a hint to the compiler that calls within `block` are worth inlining.

```julia
# The compiler will try to inline `f`
@inline f(...)

# The compiler will try to inline `f`, `g` and `+`
@inline f(...) + g(...)
```

!!! note
    A callsite annotation always has the precedence over the annotation applied to the
    definition of the called function:
    ```julia
    @noinline function explicit_noinline(args...)
        # body
    end

    let
        @inline explicit_noinline(args...) # will be inlined
    end
    ```

!!! note
    The callsite annotation applies to all calls in the block, including function arguments
    that are themselves calls:
    ```julia
    # The compiler will not inline `getproperty`, `g` or `f`
    @noinline f(x.inner, g(y))
    ```

!!! note
    When there are nested callsite annotations, the innermost annotation has the precedence:
    ```julia
    @noinline let a0, b0 = ...
        a = @inline f(a0)  # the compiler will try to inline this call
        b = f(b0)          # the compiler will NOT try to inline this call
        return a, b
    end
    ```

!!! warning
    Although a callsite annotation will try to force inlining regardless of the cost model,
    there are still chances it can't succeed in it. Especially, recursive calls can not be
    inlined even if they are annotated as `@inline`d.

!!! compat "Julia 1.8"
    The callsite annotation requires at least Julia 1.8.
"""
macro inline(x)
    return annotate_meta_def_or_block(x, :inline)
end

````
-/
def macro_inline (lo : LeafOps L) (x : Value L) : ExprResult (Value L) :=
  annotate_meta_def_or_block lo x "inline"

/--
Julia source: base/expr.jl:393-469 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @noinline

Give a hint to the compiler that it should not inline a function.

Small functions are typically inlined automatically.
By using `@noinline` on small functions, auto-inlining can be
prevented.

`@noinline` can be applied immediately before a function definition or within a function body.

```julia
# annotate long-form definition
@noinline function longdef(x)
    ...
end

# annotate short-form definition
@noinline shortdef(x) = ...

# annotate anonymous function that a `do` block creates
f() do
    @noinline
    ...
end
```

!!! compat "Julia 1.8"
    The usage within a function body requires at least Julia 1.8.

---
    @noinline block

Give a hint to the compiler that it should not inline the calls within `block`.

```julia
# The compiler will try to not inline `f`
@noinline f(...)

# The compiler will try to not inline `f`, `g` and `+`
@noinline f(...) + g(...)
```

!!! note
    A callsite annotation always has the precedence over the annotation applied to the
    definition of the called function:
    ```julia
    @inline function explicit_inline(args...)
        # body
    end

    let
        @noinline explicit_inline(args...) # will not be inlined
    end
    ```

!!! note
    When there are nested callsite annotations, the innermost annotation has the precedence:
    ```julia
    @inline let a0, b0 = ...
        a = @noinline f(a0)  # the compiler will NOT try to inline this call
        b = f(b0)            # the compiler will try to inline this call
        return a, b
    end
    ```

!!! compat "Julia 1.8"
    The callsite annotation requires at least Julia 1.8.

---
!!! note
    If the function is trivial (for example returning a constant) it might get inlined anyway.
"""
macro noinline(x)
    return annotate_meta_def_or_block(x, :noinline)
end

````
-/
def macro_noinline (lo : LeafOps L) (x : Value L) : ExprResult (Value L) :=
  annotate_meta_def_or_block lo x "noinline"

/--
Julia source: base/expr.jl:515-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function constprop_setting(@nospecialize setting)
    s = setting
    isa(setting, QuoteNode) && (setting = setting.value)
    if setting === :aggressive
        return :aggressive_constprop
    elseif setting === :none
        return :no_constprop
    end
    throw(ArgumentError(LazyString("`Base.@constprop ", s, "` not supported")))
end

```
-/
def constprop_setting (setting : Value L) : ExprResult Sym :=
  let s := match setting with
    | .quoteNode v => v
    | v => v
  match s with
  | .symbol "aggressive" => .ok "aggressive_constprop"
  | .symbol "none" => .ok "no_constprop"
  | _ => .error (.jl (.argumentError "`Base.@constprop` setting not supported"))

/--
Julia source: base/expr.jl:470-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Base.@constprop setting [ex]

Control the mode of interprocedural constant propagation for the annotated function.

Two `setting`s are supported:

- `Base.@constprop :aggressive [ex]`: apply constant propagation aggressively.
  For a method where the return type depends on the value of the arguments,
  this can yield improved inference results at the cost of additional compile time.
- `Base.@constprop :none [ex]`: disable constant propagation. This can reduce compile
  times for functions that Julia might otherwise deem worthy of constant-propagation.
  Common cases are for functions with `Bool`- or `Symbol`-valued arguments or keyword arguments.

`Base.@constprop` can be applied immediately before a function definition or within a function body.

```julia
# annotate long-form definition
Base.@constprop :aggressive function longdef(x)
    ...
end

# annotate short-form definition
Base.@constprop :aggressive shortdef(x) = ...

# annotate anonymous function that a `do` block creates
f() do
    Base.@constprop :aggressive
    ...
end
```

!!! compat "Julia 1.10"
    The usage within a function body requires at least Julia 1.10.
"""
macro constprop(setting, ex)
    sym = constprop_setting(setting)
    isa(ex, Expr) && return esc(pushmeta!(ex, sym))
    throw(ArgumentError(LazyString("Bad expression `", ex, "` in `@constprop settings ex`")))
end
macro constprop(setting)
    sym = constprop_setting(setting)
    return Expr(:meta, sym)
end

````
-/
def macro_constprop (setting ex : Value L) : ExprResult (Value L) := do
  let sym ← constprop_setting setting
  match ex with
  | .expr .. => return esc (← pushmeta! ex (.symbol sym))
  | _ => .error (.jl (.argumentError "Bad expression in `@constprop settings ex`"))
def macro_constprop_1 (setting : Value L) : ExprResult (Value L) := do
  let sym ← constprop_setting setting
  return .expr "meta" [.symbol sym]

/--
Julia source: base/expr.jl:948-961 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct EffectsOverride
    consistent::Bool
    effect_free::Bool
    nothrow::Bool
    terminates_globally::Bool
    terminates_locally::Bool
    notaskstate::Bool
    inaccessiblememonly::Bool
    noub::Bool
    noub_if_noinbounds::Bool
    consistent_overlay::Bool
    nortcall::Bool
end

```
-/
structure EffectsOverride where
  consistent : Bool
  effect_free : Bool
  nothrow : Bool
  terminates_globally : Bool
  terminates_locally : Bool
  notaskstate : Bool
  inaccessiblememonly : Bool
  noub : Bool
  noub_if_noinbounds : Bool
  consistent_overlay : Bool
  nortcall : Bool
  deriving DecidableEq, Repr

/--
Julia source: base/expr.jl:962-989 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function EffectsOverride(
    override::EffectsOverride =
        EffectsOverride(false, false, false, false, false, false, false, false, false, false, false);
    consistent::Bool = override.consistent,
    effect_free::Bool = override.effect_free,
    nothrow::Bool = override.nothrow,
    terminates_globally::Bool = override.terminates_globally,
    terminates_locally::Bool = override.terminates_locally,
    notaskstate::Bool = override.notaskstate,
    inaccessiblememonly::Bool = override.inaccessiblememonly,
    noub::Bool = override.noub,
    noub_if_noinbounds::Bool = override.noub_if_noinbounds,
    consistent_overlay::Bool = override.consistent_overlay,
    nortcall::Bool = override.nortcall)
    return EffectsOverride(
        consistent,
        effect_free,
        nothrow,
        terminates_globally,
        terminates_locally,
        notaskstate,
        inaccessiblememonly,
        noub,
        noub_if_noinbounds,
        consistent_overlay,
        nortcall)
end

```
-/
def EffectsOverride.kw (override : EffectsOverride := ⟨false, false, false, false, false, false, false, false, false,
      false, false⟩)
    (consistent : Bool := override.consistent) (effect_free : Bool := override.effect_free)
    (nothrow : Bool := override.nothrow) (terminates_globally : Bool := override.terminates_globally)
    (terminates_locally : Bool := override.terminates_locally) (notaskstate : Bool := override.notaskstate)
    (inaccessiblememonly : Bool := override.inaccessiblememonly) (noub : Bool := override.noub)
    (noub_if_noinbounds : Bool := override.noub_if_noinbounds)
    (consistent_overlay : Bool := override.consistent_overlay) (nortcall : Bool := override.nortcall) :
    EffectsOverride :=
  ⟨consistent, effect_free, nothrow, terminates_globally, terminates_locally, notaskstate, inaccessiblememonly,
    noub, noub_if_noinbounds, consistent_overlay, nortcall⟩

/--
Julia source: base/expr.jl:990-994 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const NUM_EFFECTS_OVERRIDES = 11 # sync with julia.h

# `:reset_safe` is ccall_only at the moment.
const CCALL_EFFECT_RESET_SAFE = 0x0800

```
-/
def NUM_EFFECTS_OVERRIDES : Nat := 11 -- sync with julia.h
def CCALL_EFFECT_RESET_SAFE : JInt .u16 := JInt.wrap .u16 0x0800

/--
Julia source: base/expr.jl:995-1034 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_assumed_setting(override::EffectsOverride, @nospecialize(setting), val::Bool=true)
    if isexpr(setting, :call) && setting.args[1] === :(!)
        return compute_assumed_setting(override, setting.args[2], !val)
    elseif isa(setting, QuoteNode)
        return compute_assumed_setting(override, setting.value, val)
    end
    if setting === :consistent
        return EffectsOverride(override; consistent = val)
    elseif setting === :effect_free
        return EffectsOverride(override; effect_free = val)
    elseif setting === :nothrow
        return EffectsOverride(override; nothrow = val)
    elseif setting === :terminates_globally
        return EffectsOverride(override; terminates_globally = val)
    elseif setting === :terminates_locally
        return EffectsOverride(override; terminates_locally = val)
    elseif setting === :notaskstate
        return EffectsOverride(override; notaskstate = val)
    elseif setting === :inaccessiblememonly
        return EffectsOverride(override; inaccessiblememonly = val)
    elseif setting === :noub
        return EffectsOverride(override; noub = val)
    elseif setting === :noub_if_noinbounds
        return EffectsOverride(override; noub_if_noinbounds = val)
    elseif setting === :foldable
        consistent = effect_free = terminates_globally = noub = nortcall = val
        return EffectsOverride(override; consistent, effect_free, terminates_globally, noub, nortcall)
    elseif setting === :removable
        effect_free = nothrow = terminates_globally = val
        return EffectsOverride(override; effect_free, nothrow, terminates_globally)
    elseif setting === :total
        consistent = effect_free = nothrow = terminates_globally = notaskstate =
            inaccessiblememonly = noub = nortcall = val
        return EffectsOverride(override;
            consistent, effect_free, nothrow, terminates_globally, notaskstate,
            inaccessiblememonly, noub, nortcall)
    end
    return nothing
end

```
-/
def compute_assumed_setting (override : EffectsOverride) (setting : Value L) (val : Bool := true) :
    ExprResult (Option EffectsOverride) :=
  match setting with
  | .expr "call" [] => .error (.jl .boundsError) -- `setting.args[1]`
  | .expr "call" (.symbol "!" :: rest) =>
    match rest with
    | arg2 :: _ => compute_assumed_setting override arg2 !val
    | [] => .error (.jl .boundsError) -- `setting.args[2]`
  | .quoteNode v => compute_assumed_setting override v val
  | .symbol "consistent" => .ok (some (EffectsOverride.kw override (consistent := val)))
  | .symbol "effect_free" => .ok (some (EffectsOverride.kw override (effect_free := val)))
  | .symbol "nothrow" => .ok (some (EffectsOverride.kw override (nothrow := val)))
  | .symbol "terminates_globally" => .ok (some (EffectsOverride.kw override (terminates_globally := val)))
  | .symbol "terminates_locally" => .ok (some (EffectsOverride.kw override (terminates_locally := val)))
  | .symbol "notaskstate" => .ok (some (EffectsOverride.kw override (notaskstate := val)))
  | .symbol "inaccessiblememonly" => .ok (some (EffectsOverride.kw override (inaccessiblememonly := val)))
  | .symbol "noub" => .ok (some (EffectsOverride.kw override (noub := val)))
  | .symbol "noub_if_noinbounds" => .ok (some (EffectsOverride.kw override (noub_if_noinbounds := val)))
  | .symbol "foldable" =>
    .ok (some (EffectsOverride.kw override (consistent := val) (effect_free := val) (terminates_globally := val)
      (noub := val) (nortcall := val)))
  | .symbol "removable" =>
    .ok (some (EffectsOverride.kw override (effect_free := val) (nothrow := val) (terminates_globally := val)))
  | .symbol "total" =>
    .ok (some (EffectsOverride.kw override (consistent := val) (effect_free := val) (nothrow := val)
      (terminates_globally := val) (notaskstate := val) (inaccessiblememonly := val) (noub := val)
      (nortcall := val)))
  | _ => .ok none

/--
Julia source: base/expr.jl:938-947 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function compute_assumed_settings(settings)
    override = EffectsOverride()
    for setting in settings
        override = compute_assumed_setting(override, setting)
        override === nothing &&
            throw(ArgumentError("`@assume_effects $setting` not supported"))
    end
    return override
end

```
-/
def compute_assumed_settings (settings : List (Value L)) : ExprResult EffectsOverride := do
  let mut override := EffectsOverride.kw
  for setting in settings do
    match ← compute_assumed_setting override setting with
    | some o => override := o
    | none => throw (.jl (.argumentError "`@assume_effects setting` not supported"))
  return override

/--
Julia source: base/expr.jl:1035-1050 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function encode_effects_override(eo::EffectsOverride)
    e = 0x0000
    eo.consistent          && (e |= (0x0001 << 0))
    eo.effect_free         && (e |= (0x0001 << 1))
    eo.nothrow             && (e |= (0x0001 << 2))
    eo.terminates_globally && (e |= (0x0001 << 3))
    eo.terminates_locally  && (e |= (0x0001 << 4))
    eo.notaskstate         && (e |= (0x0001 << 5))
    eo.inaccessiblememonly && (e |= (0x0001 << 6))
    eo.noub                && (e |= (0x0001 << 7))
    eo.noub_if_noinbounds  && (e |= (0x0001 << 8))
    eo.consistent_overlay  && (e |= (0x0001 << 9))
    eo.nortcall            && (e |= (0x0001 << 10))
    return e
end

```
-/
def encode_effects_override (eo : EffectsOverride) : JInt .u16 := Id.run do
  let bit (k : Nat) : JInt .u16 := JuliaLean.base.int.shl_Int (JInt.wrap .u16 1) (i64 k)
  let mut e : JInt .u16 := JInt.wrap .u16 0
  if eo.consistent then e := JuliaLean.base.int.bor e (bit 0)
  if eo.effect_free then e := JuliaLean.base.int.bor e (bit 1)
  if eo.nothrow then e := JuliaLean.base.int.bor e (bit 2)
  if eo.terminates_globally then e := JuliaLean.base.int.bor e (bit 3)
  if eo.terminates_locally then e := JuliaLean.base.int.bor e (bit 4)
  if eo.notaskstate then e := JuliaLean.base.int.bor e (bit 5)
  if eo.inaccessiblememonly then e := JuliaLean.base.int.bor e (bit 6)
  if eo.noub then e := JuliaLean.base.int.bor e (bit 7)
  if eo.noub_if_noinbounds then e := JuliaLean.base.int.bor e (bit 8)
  if eo.consistent_overlay then e := JuliaLean.base.int.bor e (bit 9)
  if eo.nortcall then e := JuliaLean.base.int.bor e (bit 10)
  return e

/--
Julia source: base/expr.jl:1051-1065 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function decode_effects_override(e::UInt16)
    return EffectsOverride(
        !iszero(e & (0x0001 << 0)),
        !iszero(e & (0x0001 << 1)),
        !iszero(e & (0x0001 << 2)),
        !iszero(e & (0x0001 << 3)),
        !iszero(e & (0x0001 << 4)),
        !iszero(e & (0x0001 << 5)),
        !iszero(e & (0x0001 << 6)),
        !iszero(e & (0x0001 << 7)),
        !iszero(e & (0x0001 << 8)),
        !iszero(e & (0x0001 << 9)),
        !iszero(e & (0x0001 << 10)))
end

```
-/
def decode_effects_override (e : JInt .u16) : EffectsOverride :=
  let bit (k : Nat) : Bool :=
    (JuliaLean.base.int.band e (JuliaLean.base.int.shl_Int (JInt.wrap .u16 1) (i64 k))).val != 0
  ⟨bit 0, bit 1, bit 2, bit 3, bit 4, bit 5, bit 6, bit 7, bit 8, bit 9, bit 10⟩

/--
Julia source: base/expr.jl:1066-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function form_purity_expr(override::EffectsOverride)
    ex = Expr(:purity)
    for i = 1:NUM_EFFECTS_OVERRIDES
        push!(ex.args, getfield(override, i))
    end
    return ex
end

```
-/
def form_purity_expr (lo : LeafOps L) (override : EffectsOverride) : Value L :=
  -- `getfield(override, i)` for `i = 1:NUM_EFFECTS_OVERRIDES`
  .expr "purity" ([override.consistent, override.effect_free, override.nothrow, override.terminates_globally,
    override.terminates_locally, override.notaskstate, override.inaccessiblememonly, override.noub,
    override.noub_if_noinbounds, override.consistent_overlay, override.nortcall].map fun b => .leaf (lo.ofBool b))

/--
Julia source: base/expr.jl:526-937 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Base.@assume_effects setting... [ex]

Override the compiler's effect modeling.
This macro can be used in several contexts:
1. Immediately before a method definition, to override the entire effect modeling of the applied method.
2. Within a function body without any arguments, to override the entire effect modeling of the enclosing method.
3. Applied to a code block, to override the local effect modeling of the applied code block.

# Examples
```jldoctest
julia> Base.@assume_effects :terminates_locally function fact(x)
           # usage 1:
           # this :terminates_locally allows `fact` to be constant-folded
           res = 1
           0 ≤ x < 20 || error("bad fact")
           while x > 1
               res *= x
               x -= 1
           end
           return res
       end
fact (generic function with 1 method)

julia> code_typed() do
           fact(12)
       end |> only
CodeInfo(
1 ─     return 479001600
) => Int64

julia> code_typed() do
           map((2,3,4)) do x
               # usage 2:
               # this :terminates_locally allows this anonymous function to be constant-folded
               Base.@assume_effects :terminates_locally
               res = 1
               0 ≤ x < 20 || error("bad fact")
               while x > 1
                   res *= x
                   x -= 1
               end
               return res
           end
       end |> only
CodeInfo(
1 ─     return (2, 6, 24)
) => Tuple{Int64, Int64, Int64}

julia> code_typed() do
           map((2,3,4)) do x
               res = 1
               0 ≤ x < 20 || error("bad fact")
               # usage 3:
               # with this :terminates_locally annotation the compiler skips tainting
               # `:terminates` effect within this `while` block, allowing the parent
               # anonymous function to be constant-folded
               Base.@assume_effects :terminates_locally while x > 1
                   res *= x
                   x -= 1
               end
               return res
           end
       end |> only
CodeInfo(
1 ─     return (2, 6, 24)
) => Tuple{Int64, Int64, Int64}
```

!!! compat "Julia 1.8"
    Using `Base.@assume_effects` requires Julia version 1.8.

!!! compat "Julia 1.10"
    The usage within a function body requires at least Julia 1.10.

!!! compat "Julia 1.11"
    The code block annotation requires at least Julia 1.11.

!!! warning
    Improper use of this macro causes undefined behavior (including crashes,
    incorrect answers, or other hard to track bugs). Use with care and only as a
    last resort if absolutely required. Even in such a case, you SHOULD take all
    possible steps to minimize the strength of the effect assertion (e.g.,
    do not use `:total` if `:nothrow` would have been sufficient).

In general, each `setting` value makes an assertion about the behavior of the
function, without requiring the compiler to prove that this behavior is indeed
true. These assertions are made for all world ages. It is thus advisable to limit
the use of generic functions that may later be extended to invalidate the
assumption (which would cause undefined behavior).

The following `setting`s are supported.
- `:consistent`
- `:effect_free`
- `:nothrow`
- `:terminates_globally`
- `:terminates_locally`
- `:notaskstate`
- `:inaccessiblememonly`
- `:noub`
- `:noub_if_noinbounds`
- `:nortcall`
- `:reset_safe`
- `:foldable`
- `:removable`
- `:total`

# Extended help

---
## `:consistent`

The `:consistent` setting asserts that for egal (`===`) inputs:
- The manner of termination (return value, exception, non-termination) will always be the same.
- If the method returns, the results will always be egal.

!!! note
    This in particular implies that the method must not return a freshly allocated
    mutable object. Multiple allocations of mutable objects (even with identical
    contents) are not egal.

!!! note
    The `:consistent`-cy assertion is made with respect to a particular world range `R`.
    More formally, write ``fᵢ`` for the evaluation of ``f`` in world-age ``i``, then this setting requires:
    ```math
    ∀ i ∈ R, j ∈ R, x, y: x ≡ y → fᵢ(x) ≡ fⱼ(y)
    ```

    For `@assume_effects`, the range `R` is `m.primary_world:m.deleted_world` of
    the annotated or containing method.

    For ordinary code instances, `R` is `ci.min_world:ci.max_world`.

    A further implication is that `:consistent` functions may not make their
    return value dependent on the state of the heap or any other global state
    that is not constant over the given world age range.

!!! note
    The `:consistent`-cy includes all legal rewrites performed by the optimizer.
    For example, floating-point fastmath operations are not considered `:consistent`,
    because the optimizer may rewrite them causing the output to not be `:consistent`,
    even for the same world age (e.g. because one ran in the interpreter, while
    the other was optimized).

!!! note
    If `:consistent` functions terminate by throwing an exception, that exception
    itself is not required to meet the egality requirement specified above.

---
## `:effect_free`

The `:effect_free` setting asserts that the method is free of externally semantically
visible side effects. The following is an incomplete list of externally semantically
visible side effects:
- Changing the value of a global variable.
- Mutating the heap (e.g. an array or mutable value), except as noted below
- Changing the method table (e.g. through calls to eval)
- File/Network/etc. I/O
- Task switching

However, the following are explicitly not semantically visible, even if they
may be observable:
- Memory allocations (both mutable and immutable)
- Elapsed time
- Garbage collection
- Heap mutations of objects whose lifetime does not exceed the method (i.e.
  were allocated in the method and do not escape).
- The returned value (which is externally visible, but not a side effect)

The rule of thumb here is that an externally visible side effect is anything
that would affect the execution of the remainder of the program if the function
were not executed.

!!! note
    The `:effect_free` assertion is made both for the method itself and any code
    that is executed by the method. Keep in mind that the assertion must be
    valid for all world ages and limit use of this assertion accordingly.

---
## `:nothrow`

The `:nothrow` setting asserts that this method does not throw an exception
(i.e. will either always return a value or never return).

!!! note
    It is permissible for `:nothrow` annotated methods to make use of exception
    handling internally as long as the exception is not rethrown out of the
    method itself.

!!! note
    If the execution of a method may raise `MethodError`s and similar exceptions, then
    the method is not considered as `:nothrow`.
    However, note that environment-dependent errors like `StackOverflowError` or `InterruptException`
    are not modeled by this effect and thus a method that may result in `StackOverflowError`
    does not necessarily need to be `!:nothrow` (although it should usually be `!:terminates` too).

---
## `:terminates_globally`

The `:terminates_globally` setting asserts that this method will eventually terminate
(either normally or abnormally), i.e. does not loop indefinitely.

!!! note
    This `:terminates_globally` assertion covers any other methods called by the annotated method.

!!! note
    The compiler will consider this a strong indication that the method will
    terminate relatively *quickly* and may (if otherwise legal) call this
    method at compile time. I.e. it is a bad idea to annotate this setting
    on a method that *technically*, but not *practically*, terminates.

---
## `:terminates_locally`

The `:terminates_locally` setting is like `:terminates_globally`, except that it only
applies to syntactic control flow *within* the annotated method. It is thus
a much weaker (and thus safer) assertion that allows for the possibility of
non-termination if the method calls some other method that does not terminate.

!!! note
    `:terminates_globally` implies `:terminates_locally`.

---
## `:notaskstate`

The `:notaskstate` setting asserts that the method does not use or modify the
local task state (task local storage, RNG state, etc.) and may thus be safely
moved between tasks without observable results.

!!! note
    The implementation of exception handling makes use of state stored in the
    task object. However, this state is currently not considered to be within
    the scope of `:notaskstate` and is tracked separately using the `:nothrow`
    effect.

!!! note
    The `:notaskstate` assertion concerns the state of the *currently running task*.
    If a reference to a `Task` object is obtained by some other means that
    does not consider which task is *currently* running, the `:notaskstate`
    effect need not be tainted. This is true, even if said task object happens
    to be `===` to the currently running task.

!!! note
    Access to task state usually also results in the tainting of other effects,
    such as `:effect_free` (if task state is modified) or `:consistent` (if
    task state is used in the computation of the result). In particular,
    code that is not `:notaskstate`, but is `:effect_free` and `:consistent`
    may still be dead-code-eliminated and thus promoted to `:total`.

---
## `:inaccessiblememonly`

The `:inaccessiblememonly` setting asserts that the method does not access or modify
externally accessible mutable memory. This means the method can access or modify mutable
memory for newly allocated objects that is not accessible by other methods or top-level
execution before return from the method, but it can not access or modify any mutable
global state or mutable memory pointed to by its arguments.

!!! note
    Below is an incomplete list of examples that invalidate this assumption:
    - a global reference or `getglobal` call to access a mutable global variable
    - a global assignment or `setglobal!` call to perform assignment to a non-constant global variable
    - `setfield!` call that changes a field of a global mutable variable

!!! note
    This `:inaccessiblememonly` assertion covers any other methods called by the annotated method.

---
## `:noub`

The `:noub` setting asserts that the method will not execute any undefined behavior
(for any input). Note that undefined behavior may technically cause the method to violate
any other effect assertions (such as `:consistent` or `:effect_free`) as well, but we do
not model this, and they assume the absence of undefined behavior.

---
## `:nortcall`

The `:nortcall` setting asserts that the method does not call `Core.Compiler.return_type`,
and that any other methods this method might call also do not call `Core.Compiler.return_type`.

!!! note
    To be precise, this assertion can be used when a call to `Core.Compiler.return_type` is
    not made at runtime; that is, when the result of `Core.Compiler.return_type` is known
    exactly at compile time and the call is eliminated by the optimizer. However, since
    whether the result of `Core.Compiler.return_type` is folded at compile time depends
    heavily on the compiler's implementation, it is generally risky to assert this if
    the method in question uses `Core.Compiler.return_type` in any form.

---
## `:foldable`

This setting is a convenient shortcut for the set of effects that the compiler
requires to be guaranteed to constant fold a call at compile time. It is
currently equivalent to the following `setting`s:
- `:consistent`
- `:effect_free`
- `:terminates_globally`
- `:noub`
- `:nortcall`

!!! note
    This list in particular does not include `:nothrow`. The compiler will still
    attempt constant propagation and note any thrown error at compile time. Note
    however, that by the `:consistent`-cy requirements, any such annotated call
    must consistently throw given the same argument values.

!!! note
    An explicit `@inbounds` annotation inside the function will also disable
    constant folding and not be overridden by `:foldable`.

---
## `:removable`

This setting is a convenient shortcut for the set of effects that the compiler
requires to be guaranteed to delete a call whose result is unused at compile time.
It is currently equivalent to the following `setting`s:
- `:effect_free`
- `:nothrow`
- `:terminates_globally`

---
## `:total`

This `setting` is the maximum possible set of effects. It currently implies
the following other `setting`s:
- `:consistent`
- `:effect_free`
- `:nothrow`
- `:terminates_globally`
- `:notaskstate`
- `:inaccessiblememonly`
- `:noub`
- `:nortcall`

!!! warning
    `:total` is a very strong assertion and will likely gain additional semantics
    in future versions of Julia (e.g. if additional effects are added and included
    in the definition of `:total`). As a result, it should be used with care.
    Whenever possible, prefer to use the minimum possible set of specific effect
    assertions required for a particular application. In cases where a large
    number of effect overrides apply to a set of functions, a custom macro is
    recommended over the use of `:total`.

---
## `:reset_safe`

The `:reset_safe` asserts that it is safe to abandon execution of the annotated
function at any point. For functions so inferred, the compiler may extend the
reset region of a cancellation point through the `:reset_safe` regions. It thus
in particular implies `:effect_free`, but is a stronger assertion. For example,
an `:effect_free` function could in principle take a read-only lock (under appropriate
assumptions on how this is implemented and annotated), but a `:reset_safe` function
may not, because it could be abandoned inside the critical section.

The same also applies to many implicitly inserted intrinsics and thus codegen for
a `:reset_safe` function requires cooperation by the code generator to uphold the
invariant throughout the entire body of the generated code.

As such, annotating a function as `:reset_safe` is currently ignored as an effect
override and will only apply to [`@ccall`](@ref) sites. See the ccall documentation
for further details on this interaction.

---
## Negated effects

Effect names may be prefixed by `!` to indicate that the effect should be removed
from an earlier meta effect. For example, `:total !:nothrow` indicates that while
the call is generally total, it may however throw.
"""
macro assume_effects(args...)
    lastex = args[end]
    settings = args[begin:end-1]
    if isexpr(lastex, :macrocall) && lastex.args[1] === Symbol("@ccall")
        # `:reset_safe` is a foreigncall-only setting (it marks the call for
        # the cancellation lowering, not the enclosing method): peel it off
        # and carry it in a dedicated bit above the standard effects
        # overrides in the `@ccall_effects` word.
        reset_safe = false
        rest = ()
        for st in settings
            if st === QuoteNode(:reset_safe)
                reset_safe = true
            else
                rest = (rest..., st)
            end
        end
        override = compute_assumed_settings(rest)
        word = encode_effects_override(override)
        reset_safe && (word |= CCALL_EFFECT_RESET_SAFE)
        lastex.args[1] = GlobalRef(Base, Symbol("@ccall_effects"))
        insert!(lastex.args, 3, word)
        return esc(lastex)
    end
    override = compute_assumed_settings(settings)
    if is_function_def(unwrap_macrocalls(lastex))
        return esc(pushmeta!(lastex::Expr, form_purity_expr(override)))
    end
    override′ = compute_assumed_setting(override, lastex)
    if override′ !== nothing
        # anonymous function case
        return Expr(:meta, form_purity_expr(override′))
    else
        # call site annotation case
        return Expr(:block,
                    form_purity_expr(override),
                    Expr(:local, Expr(:(=), :val, esc(lastex))),
                    Expr(:purity), # region end token
                    :val)
    end
end

````
-/
def macro_assume_effects (lo : LeafOps L) (args : List (Value L)) : ExprResult (Value L) := do
  let lastex ← match args.getLast? with
    | some x => pure x
    | none => throw (.jl .boundsError)
  let settings := args.dropLast
  match lastex with
  | .expr "macrocall" (.symbol "@ccall" :: largs) =>
    -- `:reset_safe` is a foreigncall-only setting: peel it off and carry it in a dedicated bit.
    let mut reset_safe := false
    let mut rest : List (Value L) := []
    for st in settings do
      if egal lo st (quoteSym "reset_safe") then
        reset_safe := true
      else
        rest := rest ++ [st]
    let override ← compute_assumed_settings rest
    let mut word := encode_effects_override override
    if reset_safe then word := JuliaLean.base.int.bor word CCALL_EFFECT_RESET_SAFE
    -- `lastex.args[1] = GlobalRef(Base, Symbol("@ccall_effects"))`; `insert!(lastex.args, 3, word)`
    let largs := Value.globalRef lo.base "@ccall_effects" :: largs
    if largs.length < 2 then throw (.jl .boundsError)
    let largs := largs.take 2 ++ [.leaf (lo.ofUInt16 word)] ++ largs.drop 2
    return esc (.expr "macrocall" largs)
  | _ =>
    let override ← compute_assumed_settings settings
    if is_function_def (← unwrap_macrocalls lastex) then
      match lastex with
      | .expr .. => return esc (← pushmeta! lastex (form_purity_expr lo override))
      | _ => throw .typeError
    match ← compute_assumed_setting override lastex with
    | some override' =>
      -- anonymous function case
      return .expr "meta" [form_purity_expr lo override']
    | none =>
      -- call site annotation case
      return .expr "block" [form_purity_expr lo override,
        .expr "local" [.expr "=" [.symbol "val", esc lastex]],
        .expr "purity" [], -- region end token
        .symbol "val"]

/--
Julia source: base/expr.jl:1074-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Base.@nospecializeinfer function f(args...)
        @nospecialize ...
        ...
    end
    Base.@nospecializeinfer f(@nospecialize args...) = ...

Tells the compiler to infer `f` using the declared types of `@nospecialize`d arguments.
This can be used to limit the number of compiler-generated specializations during inference.

# Examples

```jldoctest; setup = :(using InteractiveUtils)
julia> f(A::AbstractArray) = g(A)
f (generic function with 1 method)

julia> @noinline Base.@nospecializeinfer g(@nospecialize(A::AbstractArray)) = A[1]
g (generic function with 1 method)

julia> @code_typed f([1.0])
CodeInfo(
1 ─ %1 =    invoke g(A::AbstractArray)::Any
└──      return %1
) => Any
```

In this example, `f` will be inferred for each specific type of `A`,
but `g` will only be inferred once with the declared argument type `A::AbstractArray`,
meaning that the compiler will not likely see the excessive inference time on it
while it can not infer the concrete return type of it.
Without the `@nospecializeinfer`, `f([1.0])` would infer the return type of `g` as `Float64`,
indicating that inference ran for `g(::Vector{Float64})` despite the prohibition on
specialized code generation.

!!! compat "Julia 1.10"
    Using `Base.@nospecializeinfer` requires Julia version 1.10.
"""
macro nospecializeinfer(ex)
    esc(isa(ex, Expr) ? pushmeta!(ex, :nospecializeinfer) : ex)
end

````
-/
def macro_nospecializeinfer (ex : Value L) : ExprResult (Value L) := do
  match ex with
  | .expr .. => return esc (← pushmeta! ex (.symbol "nospecializeinfer"))
  | _ => return esc ex

/--
Julia source: base/expr.jl:1115-1155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @propagate_inbounds

Tells the compiler to inline a function while retaining the caller's inbounds context.

An [`@inbounds`](@ref) block only elides the [`@boundscheck`](@ref) blocks of functions that
are inlined directly into it, i.e. one level of inlining deep. Marking a function with
`@propagate_inbounds` makes it pass on its caller's inbounds context, so that `@boundscheck`
blocks in the functions it calls are elided too when it is called from an `@inbounds` block.
This is useful e.g. for an indexing method that forwards to the indexing of another array.

See also [Propagating inbounds](@ref) in the developer documentation.

# Examples
```julia-repl
julia> @inline g(x) = (@boundscheck println("checking bounds"); x);

julia> f1(x) = g(x);

julia> Base.@propagate_inbounds f2(x) = g(x);

julia> h1(x) = @inbounds f1(x);

julia> h2(x) = @inbounds f2(x);

julia> h1(1)
checking bounds
1

julia> h2(1)
1
```
"""
macro propagate_inbounds(ex)
    if isa(ex, Expr)
        pushmeta!(ex, :inline)
        pushmeta!(ex, :propagate_inbounds)
    end
    esc(ex)
end

````
-/
def macro_propagate_inbounds (ex : Value L) : ExprResult (Value L) := do
  let mut ex := ex
  match ex with
  | .expr .. =>
    ex ← pushmeta! ex (.symbol "inline")
    ex ← pushmeta! ex (.symbol "propagate_inbounds")
  | _ => pure ()
  return esc ex

/--
Julia source: base/expr.jl:1156-1164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    @polly

Tells the compiler to apply the polyhedral optimizer Polly to a function.
"""
macro polly(ex)
    esc(isa(ex, Expr) ? pushmeta!(ex, :polly) : ex)
end

```
-/
def macro_polly (ex : Value L) : ExprResult (Value L) := do
  match ex with
  | .expr .. => return esc (← pushmeta! ex (.symbol "polly"))
  | _ => return esc ex

/-- The `filter!` predicate of `remove_linenums!`. -/
def keepNonLine : Value L → Bool
  | .expr "line" _ => false
  | .lineNumberNode .. => false
  | _ => true

/--
Julia source: base/expr.jl:1282-1305 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.remove_linenums!(ex)

Remove all line-number metadata from expression-like object `ex`.
"""
function remove_linenums!(@nospecialize ex)
    if ex isa Expr
        if ex.head === :block || ex.head === :quote
            # remove line number expressions from metadata (not argument literal or inert) position
            filter!(ex.args) do x
                isa(x, Expr) && x.head === :line && return false
                isa(x, LineNumberNode) && return false
                return true
            end
        end
        for subex in ex.args
            subex isa Expr && remove_linenums!(subex)
        end
    elseif ex isa CodeInfo
        ex.debuginfo = Core.DebugInfo(ex.debuginfo.def) # TODO: filter partially, but keep edges
    end
    return ex
end

```
-/
def remove_linenums! (codeInfoNoLines : L → L) : Value L → Value L
  | .expr head args =>
    -- remove line number expressions from metadata (not argument literal or inert) position,
    -- then `remove_linenums!` each remaining `Expr` argument
    .expr head (remove_linenums_args codeInfoNoLines (head == "block" || head == "quote") args)
  | .codeInfo ci => .codeInfo (codeInfoNoLines ci)
  | ex => ex
where
  remove_linenums_args (codeInfoNoLines : L → L) (filt : Bool) : List (Value L) → List (Value L)
    | [] => []
    | x :: xs =>
      if filt && !keepNonLine x then remove_linenums_args codeInfoNoLines filt xs
      else (match x with
        | .expr .. => remove_linenums! codeInfoNoLines x
        | _ => x) :: remove_linenums_args codeInfoNoLines filt xs

/-- The `map!` function of `replace_linenums!`. -/
def replaceLine (lo : LeafOps L) (ln : JInt64 × Value L) : Value L → Value L
  | .expr "line" [_] => .expr "line" [.leaf (lo.ofInt ln.1)]
  | .expr "line" [_, _] => .expr "line" [.leaf (lo.ofInt ln.1), ln.2]
  | .lineNumberNode .. => .lineNumberNode ln.1 ln.2
  | x => x

mutual

/--
Julia source: base/expr.jl:1306-1325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
replace_linenums!(ex, ln::LineNumberNode) = ex
function replace_linenums!(ex::Expr, ln::LineNumberNode)
    if ex.head === :block || ex.head === :quote
        # replace line number expressions from metadata (not argument literal or inert) position
        map!(ex.args, ex.args) do @nospecialize(x)
            isa(x, Expr) && x.head === :line && length(x.args) == 1 && return Expr(:line, ln.line)
            isa(x, Expr) && x.head === :line && length(x.args) == 2 && return Expr(:line, ln.line, ln.file)
            isa(x, LineNumberNode) && return ln
            return x
        end
    end
    # preserve any linenums inside `esc(...)` guards
    if ex.head !== :escape
        for subex in ex.args
            subex isa Expr && replace_linenums!(subex, ln)
        end
    end
    return ex
end

```
-/
def replace_linenums_Any (ex : Value L) (_ln : JInt64 × Value L) : Value L := ex
-- `replace_linenums!(ex::Expr, ln::LineNumberNode)`; `ln` is given as `(ln.line, ln.file)`. `none` is a
-- non-terminating call (possible only when `ln.file` itself contains line-number expressions).
def replace_linenums! (lo : LeafOps L) (ln : JInt64 × Value L) : Value L → Option (Value L)
  | .expr head args => do
    -- replace line number expressions from metadata (not argument literal or inert) position
    let args := if head == "block" || head == "quote" then args.map (replaceLine lo ln) else args
    -- preserve any linenums inside `esc(...)` guards
    if head != "escape" then return .expr head (← replace_linenums_args lo ln args) else return .expr head args
  | ex => some (replace_linenums_Any ex ln)
partial_fixpoint

/-- `for subex in ex.args; subex isa Expr && replace_linenums!(subex, ln); end`. -/
def replace_linenums_args (lo : LeafOps L) (ln : JInt64 × Value L) : List (Value L) → Option (List (Value L))
  | [] => some []
  | x :: xs => do
    let y ← match x with
      | .expr .. => replace_linenums! lo ln x
      | _ => some x
    return y :: (← replace_linenums_args lo ln xs)
partial_fixpoint
end

/-- `error("could not parse @atomic expression $ex")`. -/
def atomicParseError {α : Type} : ExprResult α := .error (.errorException "could not parse @atomic expression")

/--
Julia source: base/expr.jl:1555-1566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_atomic(order, a1, op, a2)
    @nospecialize
    if is_expr(a1, :., 2)
        a1l, a1r, op, a2 = esc(a1.args[1]), esc(a1.args[2]), esc(op), esc(a2)
        return :(modifyproperty!($a1l, $a1r, $op, $a2, $order))
    elseif is_expr(a1, :ref)
        x, idcs, op, a2 = esc(a1.args[1]), map(esc, a1.args[2:end]), esc(op), esc(a2)
        return :(modifyindex_atomic!($x, $order, $op, $a2, $(idcs...)))
    end
    error("@atomic modify expression missing field access or indexing")
end

```
-/
def make_atomic4 (order a1 op a2 : Value L) : ExprResult (Value L) := do
  if is_expr_n a1 "." (i64 2) then
    let (_, a1args) ← asExpr a1
    let a1l := esc (← argAt a1args 1)
    let a1r := esc (← argAt a1args 2)
    return .expr "call" [.symbol "modifyproperty!", a1l, a1r, esc op, esc a2, order]
  else if is_expr a1 "ref" then
    let (_, a1args) ← asExpr a1
    let x := esc (← argAt a1args 1)
    let idcs := (argsFrom2 a1args).map esc
    return .expr "call" ([.symbol "modifyindex_atomic!", x, order, esc op, esc a2] ++ idcs)
  throw (.errorException "@atomic modify expression missing field access or indexing")

/-- The modifying-operator symbol of an update-assignment head, or `none` (`op` undefined). -/
def atomicUpdateOp (head : Sym) : Option Sym :=
  if head == "+=" then some "+"
  else if head == "+%=" then some "+%"
  else if head == "-=" then some "-"
  else if head == "-%=" then some "-%"
  else if head == "*%=" then some "*%"
  else if head == "|=" then some "|"
  else if head == "&=" then some "&"
  -- `@isdefined string` holds: `string` is defined when the macro runs.
  else if head.endsWith "=" then some (String.ofList head.toList.dropLast)
  else none

/--
Julia source: base/expr.jl:1506-1554 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_atomic(order, ex)
    @nospecialize
    if ex isa Expr
        if isexpr(ex, :., 2)
            l, r = esc(ex.args[1]), esc(ex.args[2])
            return :(getproperty($l, $r, $order))
        elseif isexpr(ex, :call, 3)
            return make_atomic(order, ex.args[2], ex.args[1], ex.args[3])
        elseif isexpr(ex, :ref)
            x, idcs = esc(ex.args[1]), map(esc, ex.args[2:end])
            return :(getindex_atomic($x, $order, $(idcs...)))
        elseif ex.head === :(=)
            l, r = ex.args[1], esc(ex.args[2])
            if is_expr(l, :., 2)
                ll, lr = esc(l.args[1]), esc(l.args[2])
                return :(setproperty!($ll, $lr, $r, $order))
            elseif is_expr(l, :ref)
                x, idcs = esc(l.args[1]), map(esc, l.args[2:end])
                return :(setindex_atomic!($x, $order, $r, $(idcs...)))
            end
        end
        if length(ex.args) == 2
            if ex.head === :(+=)
                op = :+
            elseif ex.head === Symbol("+%=")
                op = Symbol("+%")
            elseif ex.head === :(-=)
                op = :-
            elseif ex.head === Symbol("-%=")
                op = Symbol("-%")
            elseif ex.head === Symbol("*%=")
                op = Symbol("*%")
            elseif ex.head === :(|=)
                op = :|
            elseif ex.head === :(&=)
                op = :&
            elseif @isdefined string
                shead = string(ex.head)
                if endswith(shead, '=')
                    op = Symbol(shead[1:prevind(shead, end)])
                end
            end
            if @isdefined(op)
                return Expr(:ref, make_atomic(order, ex.args[1], op, ex.args[2]), 2)
            end
        end
    end
    error("could not parse @atomic expression $ex")
end
```
-/
def make_atomic (lo : LeafOps L) (order ex : Value L) : ExprResult (Value L) := do
  match ex with
  | .expr head args =>
    if is_expr_n ex "." (i64 2) then
      let l := esc (← argAt args 1)
      let r := esc (← argAt args 2)
      return .expr "call" [.symbol "getproperty", l, r, order]
    else if is_expr_n ex "call" (i64 3) then
      return ← make_atomic4 order (← argAt args 2) (← argAt args 1) (← argAt args 3)
    else if is_expr ex "ref" then
      let x := esc (← argAt args 1)
      let idcs := (argsFrom2 args).map esc
      return .expr "call" ([.symbol "getindex_atomic", x, order] ++ idcs)
    else if head == "=" then
      let l ← argAt args 1
      let r := esc (← argAt args 2)
      if is_expr_n l "." (i64 2) then
        let (_, largs) ← asExpr l
        return .expr "call" [.symbol "setproperty!", esc (← argAt largs 1), esc (← argAt largs 2), r, order]
      else if is_expr l "ref" then
        let (_, largs) ← asExpr l
        return .expr "call" ([.symbol "setindex_atomic!", esc (← argAt largs 1), order, r] ++
          (argsFrom2 largs).map esc)
    if args.length == 2 then
      match atomicUpdateOp head with
      | some op =>
        return .expr "ref" [← make_atomic4 order (← argAt args 1) (.symbol op) (← argAt args 2), .leaf (lo.ofInt (i64 2))]
      | none => pure ()
    atomicParseError
  | _ => atomicParseError

/--
Julia source: base/expr.jl:1622-1635 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_atomicswap(order, ex)
    @nospecialize
    is_expr(ex, :(=), 2) || error("@atomicswap expression missing assignment")
    l, val = ex.args[1], esc(ex.args[2])
    if is_expr(l, :., 2)
        ll, lr = esc(l.args[1]), esc(l.args[2])
        return :(swapproperty!($ll, $lr, $val, $order))
    elseif is_expr(l, :ref)
        x, idcs = esc(l.args[1]), map(esc, l.args[2:end])
        return :(swapindex_atomic!($x, $order, $val, $(idcs...)))
    end
    error("@atomicswap expression missing field access or indexing")
end

```
-/
def make_atomicswap (order ex : Value L) : ExprResult (Value L) := do
  if !is_expr_n ex "=" (i64 2) then throw (.errorException "@atomicswap expression missing assignment")
  let (_, args) ← asExpr ex
  let l ← argAt args 1
  let val := esc (← argAt args 2)
  if is_expr_n l "." (i64 2) then
    let (_, largs) ← asExpr l
    return .expr "call" [.symbol "swapproperty!", esc (← argAt largs 1), esc (← argAt largs 2), val, order]
  else if is_expr l "ref" then
    let (_, largs) ← asExpr l
    return .expr "call" ([.symbol "swapindex_atomic!", esc (← argAt largs 1), order, val] ++
      (argsFrom2 largs).map esc)
  throw (.errorException "@atomicswap expression missing field access or indexing")

/-- `$old_new::Pair...`. -/
def splatPair (old_new : Value L) : Value L := .expr "..." [.expr "::" [old_new, .symbol "Pair"]]

/-- `is_expr(old_new, :call, 3) && old_new.args[1] === :(=>)`. -/
def isPairCall (old_new : Value L) : Bool :=
  is_expr_n old_new "call" (i64 3) && (match old_new with
    | .expr _ (.symbol "=>" :: _) => true
    | _ => false)

/--
Julia source: base/expr.jl:1722-1745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_atomicreplace(success_order, fail_order, ex, old_new)
    @nospecialize
    if is_expr(ex, :., 2)
        ll, lr = esc(ex.args[1]), esc(ex.args[2])
        if is_expr(old_new, :call, 3) && old_new.args[1] === :(=>)
            exp, rep = esc(old_new.args[2]), esc(old_new.args[3])
            return :(replaceproperty!($ll, $lr, $exp, $rep, $success_order, $fail_order))
        else
            old_new = esc(old_new)
            return :(replaceproperty!($ll, $lr, $old_new::Pair..., $success_order, $fail_order))
        end
    elseif is_expr(ex, :ref)
        x, idcs = esc(ex.args[1]), map(esc, ex.args[2:end])
        if is_expr(old_new, :call, 3) && old_new.args[1] === :(=>)
            exp, rep = esc(old_new.args[2]), esc(old_new.args[3])
            return :(replaceindex_atomic!($x, $success_order, $fail_order, $exp, $rep, $(idcs...)))
        else
            old_new = esc(old_new)
            return :(replaceindex_atomic!($x, $success_order, $fail_order, $old_new::Pair..., $(idcs...)))
        end
    end
    error("@atomicreplace expression missing field access or indexing")
end

```
-/
def make_atomicreplace (success_order fail_order ex old_new : Value L) : ExprResult (Value L) := do
  if is_expr_n ex "." (i64 2) then
    let (_, args) ← asExpr ex
    let ll := esc (← argAt args 1)
    let lr := esc (← argAt args 2)
    if isPairCall old_new then
      let (_, oargs) ← asExpr old_new
      let exp := esc (← argAt oargs 2)
      let rep := esc (← argAt oargs 3)
      return .expr "call" [.symbol "replaceproperty!", ll, lr, exp, rep, success_order, fail_order]
    else
      let old_new := esc old_new
      return .expr "call" [.symbol "replaceproperty!", ll, lr, splatPair old_new, success_order, fail_order]
  else if is_expr ex "ref" then
    let (_, args) ← asExpr ex
    let x := esc (← argAt args 1)
    let idcs := (argsFrom2 args).map esc
    if isPairCall old_new then
      let (_, oargs) ← asExpr old_new
      let exp := esc (← argAt oargs 2)
      let rep := esc (← argAt oargs 3)
      return .expr "call" ([.symbol "replaceindex_atomic!", x, success_order, fail_order, exp, rep] ++ idcs)
    else
      let old_new := esc old_new
      return .expr "call" ([.symbol "replaceindex_atomic!", x, success_order, fail_order, splatPair old_new] ++ idcs)
  throw (.errorException "@atomicreplace expression missing field access or indexing")

/--
Julia source: base/expr.jl:1825-1838 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function make_atomiconce(success_order, fail_order, ex)
    @nospecialize
    is_expr(ex, :(=), 2) || error("@atomiconce expression missing assignment")
    l, val = ex.args[1], esc(ex.args[2])
    if is_expr(l, :., 2)
        ll, lr = esc(l.args[1]), esc(l.args[2])
        return :(setpropertyonce!($ll, $lr, $val, $success_order, $fail_order))
    elseif is_expr(l, :ref)
        x, idcs = esc(l.args[1]), map(esc, l.args[2:end])
        return :(setindexonce_atomic!($x, $success_order, $fail_order, $val, $(idcs...)))
    end
    error("@atomiconce expression missing field access or indexing")
end

```
-/
def make_atomiconce (success_order fail_order ex : Value L) : ExprResult (Value L) := do
  if !is_expr_n ex "=" (i64 2) then throw (.errorException "@atomiconce expression missing assignment")
  let (_, args) ← asExpr ex
  let l ← argAt args 1
  let val := esc (← argAt args 2)
  if is_expr_n l "." (i64 2) then
    let (_, largs) ← asExpr l
    return .expr "call" [.symbol "setpropertyonce!", esc (← argAt largs 1), esc (← argAt largs 2), val,
      success_order, fail_order]
  else if is_expr l "ref" then
    let (_, largs) ← asExpr l
    return .expr "call" ([.symbol "setindexonce_atomic!", esc (← argAt largs 1), success_order, fail_order, val] ++
      (argsFrom2 largs).map esc)
  throw (.errorException "@atomiconce expression missing field access or indexing")

/--
Julia source: base/expr.jl:1326-1329 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro generated()
    return Expr(:generated)
end

```
-/
def macro_generated_0 : Value L := .expr "generated" []

/--
Julia source: base/expr.jl:1330-1376 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @generated f

`@generated` is used to annotate a function which will be generated.
In the body of the generated function, only types of arguments can be read
(not the values). The function returns a quoted expression evaluated when the
function is called. The `@generated` macro should not be used on functions mutating
the global scope or depending on mutable elements.

See [Metaprogramming](@ref) for further details.

# Examples
```jldoctest
julia> @generated function bar(x)
           if x <: Integer
               return :(x ^ 2)
           else
               return :(x)
           end
       end
bar (generic function with 1 method)

julia> bar(4)
16

julia> bar("baz")
"baz"
```
"""
macro generated(f)
    if isa(f, Expr) && (f.head === :function || is_short_function_def(f))
        body = f.args[2]
        lno = body.args[1]
        return Expr(:escape,
                    Expr(f.head, f.args[1],
                         Expr(:block,
                              lno,
                              Expr(:if, Expr(:generated),
                                   body,
                                   Expr(:block,
                                        Expr(:meta, :generated_only),
                                        Expr(:return, nothing))))))
    else
        error("invalid syntax; @generated must be used with a function definition")
    end
end

````
-/
def macro_generated (lo : LeafOps L) (f : Value L) : ExprResult (Value L) := do
  match f with
  | .expr fhead fargs =>
    if fhead == "function" || is_short_function_def f then
      let body ← argAt fargs 2
      let lno ← match body with
        | .expr _ bargs => argAt bargs 1
        | _ => throw (.jl (.methodError "getproperty"))
      return .expr "escape" [.expr fhead [← argAt fargs 1,
        .expr "block" [lno,
          .expr "if" [.expr "generated" [], body,
            .expr "block" [.expr "meta" [.symbol "generated_only"], .expr "return" [.leaf lo.nothing]]]]]]
    else throw (.errorException "invalid syntax; @generated must be used with a function definition")
  | _ => throw (.errorException "invalid syntax; @generated must be used with a function definition")

/--
Julia source: base/expr.jl:1377-1505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @atomic var
    @atomic order ex

Mark `var` or `ex` as being performed atomically, if `ex` is a supported expression.
If no `order` is specified it defaults to :sequentially_consistent.

    @atomic a.b.x = new
    @atomic a.b.x += addend
    @atomic :release a.b.x = new
    @atomic :acquire_release a.b.x += addend
    @atomic m[idx] = new
    @atomic m[idx] += addend
    @atomic :release m[idx] = new
    @atomic :acquire_release m[idx] += addend

Perform the store operation expressed on the right atomically and return the
new value.

With assignment (`=`), this operation translates to a `setproperty!(a.b, :x, new)`
or, in case of reference, to a `setindex_atomic!(m, order, new, idx)` call,
with `order` defaulting to `:sequentially_consistent`.

With any modifying operator this operation translates to a
`modifyproperty!(a.b, :x, op, addend)[2]` or, in case of reference, to a
`modifyindex_atomic!(m, order, op, addend, idx...)[2]` call,
with `order` defaulting to `:sequentially_consistent`.

    @atomic a.b.x max arg2
    @atomic a.b.x + arg2
    @atomic max(a.b.x, arg2)
    @atomic :acquire_release max(a.b.x, arg2)
    @atomic :acquire_release a.b.x + arg2
    @atomic :acquire_release a.b.x max arg2
    @atomic m[idx] max arg2
    @atomic m[idx] + arg2
    @atomic max(m[idx], arg2)
    @atomic :acquire_release max(m[idx], arg2)
    @atomic :acquire_release m[idx] + arg2
    @atomic :acquire_release m[idx] max arg2

Perform the binary operation expressed on the right atomically. Store the
result into the field or the reference in the first argument, and return the values
`(old, new)`.

This operation translates to a `modifyproperty!(a.b, :x, func, arg2)` or,
in case of reference to a `modifyindex_atomic!(m, order, func, arg2, idx)` call,
with `order` defaulting to `:sequentially_consistent`.

See [Per-field atomics](@ref man-atomics) section in the manual for more details.

# Examples
```jldoctest
julia> mutable struct Atomic{T}; @atomic x::T; end

julia> a = Atomic(1)
Atomic{Int64}(1)

julia> @atomic a.x # fetch field x of a, with sequential consistency
1

julia> @atomic :sequentially_consistent a.x = 2 # set field x of a, with sequential consistency
2

julia> @atomic a.x += 1 # increment field x of a, with sequential consistency
3

julia> @atomic a.x + 1 # increment field x of a, with sequential consistency
3 => 4

julia> @atomic a.x # fetch field x of a, with sequential consistency
4

julia> @atomic max(a.x, 10) # change field x of a to the max value, with sequential consistency
4 => 10

julia> @atomic a.x max 5 # again change field x of a to the max value, with sequential consistency
10 => 10
```

```jldoctest
julia> mem = AtomicMemory{Int}(undef, 2);

julia> @atomic mem[1] = 2 # set mem[1] to value 2 with sequential consistency
2

julia> @atomic :monotonic mem[1] # fetch the first value of mem, with monotonic consistency
2

julia> @atomic mem[1] += 1 # increment the first value of mem, with sequential consistency
3

julia> @atomic mem[1] + 1 # increment the first value of mem, with sequential consistency
3 => 4

julia> @atomic mem[1] # fetch the first value of mem, with sequential consistency
4

julia> @atomic max(mem[1], 10) # change the first value of mem to the max value, with sequential consistency
4 => 10

julia> @atomic mem[1] max 5 # again change the first value of mem to the max value, with sequential consistency
10 => 10
```

!!! compat "Julia 1.7"
    Atomic fields functionality requires at least Julia 1.7.

!!! compat "Julia 1.12"
    Atomic reference functionality requires at least Julia 1.12.
"""
macro atomic(ex)
    if !isa(ex, Symbol) && !is_expr(ex, :(::))
        return make_atomic(QuoteNode(:sequentially_consistent), ex)
    end
    return esc(Expr(:atomic, ex))
end
macro atomic(order, ex)
    order isa QuoteNode || (order = esc(order))
    return make_atomic(order, ex)
end
macro atomic(a1, op, a2)
    return make_atomic(QuoteNode(:sequentially_consistent), a1, op, a2)
end
macro atomic(order, a1, op, a2)
    order isa QuoteNode || (order = esc(order))
    return make_atomic(order, a1, op, a2)
end
````
-/
def macro_atomic_1 (lo : LeafOps L) (ex : Value L) : ExprResult (Value L) := do
  if !(match ex with | .symbol _ => true | _ => false) && !is_expr ex "::" then
    return ← make_atomic lo (quoteSym "sequentially_consistent") ex
  return esc (.expr "atomic" [ex])
def macro_atomic_2 (lo : LeafOps L) (order ex : Value L) : ExprResult (Value L) :=
  let order := match order with
    | .quoteNode _ => order
    | _ => esc order
  make_atomic lo order ex
def macro_atomic_3 (a1 op a2 : Value L) : ExprResult (Value L) :=
  make_atomic4 (quoteSym "sequentially_consistent") a1 op a2
def macro_atomic_4 (order a1 op a2 : Value L) : ExprResult (Value L) :=
  let order := match order with
    | .quoteNode _ => order
    | _ => esc order
  make_atomic4 order a1 op a2

/--
Julia source: base/expr.jl:1567-1621 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @atomicswap a.b.x = new
    @atomicswap :sequentially_consistent a.b.x = new
    @atomicswap m[idx] = new
    @atomicswap :sequentially_consistent m[idx] = new

Stores `new` into `a.b.x` (`m[idx]` in case of reference) and returns the old
value of `a.b.x` (the old value stored at `m[idx]`, respectively).

This operation translates to a `swapproperty!(a.b, :x, new)` or,
in case of reference, `swapindex_atomic!(mem, order, new, idx)` call,
with `order` defaulting to `:sequentially_consistent`.

See [Per-field atomics](@ref man-atomics) section in the manual for more details.

# Examples
```jldoctest
julia> mutable struct Atomic{T}; @atomic x::T; end

julia> a = Atomic(1)
Atomic{Int64}(1)

julia> @atomicswap a.x = 2+2 # replace field x of a with 4, with sequential consistency
1

julia> @atomic a.x # fetch field x of a, with sequential consistency
4
```

```jldoctest
julia> mem = AtomicMemory{Int}(undef, 2);

julia> @atomic mem[1] = 1;

julia> @atomicswap mem[1] = 4 # replace the first value of `mem` with 4, with sequential consistency
1

julia> @atomic mem[1] # fetch the first value of mem, with sequential consistency
4
```

!!! compat "Julia 1.7"
    Atomic fields functionality requires at least Julia 1.7.

!!! compat "Julia 1.12"
    Atomic reference functionality requires at least Julia 1.12.
"""
macro atomicswap(order, ex)
    order isa QuoteNode || (order = esc(order))
    return make_atomicswap(order, ex)
end
macro atomicswap(ex)
    return make_atomicswap(QuoteNode(:sequentially_consistent), ex)
end
````
-/
def macro_atomicswap_2 (order ex : Value L) : ExprResult (Value L) :=
  let order := match order with
    | .quoteNode _ => order
    | _ => esc order
  make_atomicswap order ex
def macro_atomicswap_1 (ex : Value L) : ExprResult (Value L) :=
  make_atomicswap (quoteSym "sequentially_consistent") ex

/--
Julia source: base/expr.jl:1636-1721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia

"""
    @atomicreplace a.b.x expected => desired
    @atomicreplace :sequentially_consistent a.b.x expected => desired
    @atomicreplace :sequentially_consistent :monotonic a.b.x expected => desired
    @atomicreplace m[idx] expected => desired
    @atomicreplace :sequentially_consistent m[idx] expected => desired
    @atomicreplace :sequentially_consistent :monotonic m[idx] expected => desired

Perform the conditional replacement expressed by the pair atomically, returning
the values `(old, success::Bool)`. Where `success` indicates whether the
replacement was completed.

This operation translates to a `replaceproperty!(a.b, :x, expected, desired)` or,
in case of reference, to a
`replaceindex_atomic!(mem, success_order, fail_order, expected, desired, idx)` call,
with both orders defaulting to `:sequentially_consistent`.

See [Per-field atomics](@ref man-atomics) section in the manual for more details.

# Examples
```jldoctest
julia> mutable struct Atomic{T}; @atomic x::T; end

julia> a = Atomic(1)
Atomic{Int64}(1)

julia> @atomicreplace a.x 1 => 2 # replace field x of a with 2 if it was 1, with sequential consistency
(old = 1, success = true)

julia> @atomic a.x # fetch field x of a, with sequential consistency
2

julia> @atomicreplace a.x 1 => 3 # replace field x of a with 2 if it was 1, with sequential consistency
(old = 2, success = false)

julia> xchg = 2 => 0; # replace field x of a with 0 if it was 2, with sequential consistency

julia> @atomicreplace a.x xchg
(old = 2, success = true)

julia> @atomic a.x # fetch field x of a, with sequential consistency
0
```

```jldoctest
julia> mem = AtomicMemory{Int}(undef, 2);

julia> @atomic mem[1] = 1;

julia> @atomicreplace mem[1] 1 => 2 # replace the first value of mem with 2 if it was 1, with sequential consistency
(old = 1, success = true)

julia> @atomic mem[1] # fetch the first value of mem, with sequential consistency
2

julia> @atomicreplace mem[1] 1 => 3 # replace field x of a with 2 if it was 1, with sequential consistency
(old = 2, success = false)

julia> xchg = 2 => 0; # replace field x of a with 0 if it was 2, with sequential consistency

julia> @atomicreplace mem[1] xchg
(old = 2, success = true)

julia> @atomic mem[1] # fetch the first value of mem, with sequential consistency
0
```

!!! compat "Julia 1.7"
    Atomic fields functionality requires at least Julia 1.7.

!!! compat "Julia 1.12"
    Atomic reference functionality requires at least Julia 1.12.
"""
macro atomicreplace(success_order, fail_order, ex, old_new)
    fail_order isa QuoteNode || (fail_order = esc(fail_order))
    success_order isa QuoteNode || (success_order = esc(success_order))
    return make_atomicreplace(success_order, fail_order, ex, old_new)
end
macro atomicreplace(order, ex, old_new)
    order isa QuoteNode || (order = esc(order))
    return make_atomicreplace(order, order, ex, old_new)
end
macro atomicreplace(ex, old_new)
    return make_atomicreplace(QuoteNode(:sequentially_consistent), QuoteNode(:sequentially_consistent), ex, old_new)
end
````
-/
def macro_atomicreplace_4 (success_order fail_order ex old_new : Value L) : ExprResult (Value L) :=
  let fail_order := match fail_order with
    | .quoteNode _ => fail_order
    | _ => esc fail_order
  let success_order := match success_order with
    | .quoteNode _ => success_order
    | _ => esc success_order
  make_atomicreplace success_order fail_order ex old_new
def macro_atomicreplace_3 (order ex old_new : Value L) : ExprResult (Value L) :=
  let order := match order with
    | .quoteNode _ => order
    | _ => esc order
  make_atomicreplace order order ex old_new
def macro_atomicreplace_2 (ex old_new : Value L) : ExprResult (Value L) :=
  make_atomicreplace (quoteSym "sequentially_consistent") (quoteSym "sequentially_consistent") ex old_new

/--
Julia source: base/expr.jl:1746-1824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @atomiconce a.b.x = value
    @atomiconce :sequentially_consistent a.b.x = value
    @atomiconce :sequentially_consistent :monotonic a.b.x = value
    @atomiconce m[idx] = value
    @atomiconce :sequentially_consistent m[idx] = value
    @atomiconce :sequentially_consistent :monotonic m[idx] = value

Perform the conditional assignment of value atomically if it was previously
unset. Returned value `success::Bool` indicates whether the assignment was completed.

This operation translates to a `setpropertyonce!(a.b, :x, value)` or,
in case of reference, to a `setindexonce_atomic!(m, success_order, fail_order, value, idx)` call,
with both orders defaulting to `:sequentially_consistent`.

See [Per-field atomics](@ref man-atomics) section in the manual for more details.

# Examples
```jldoctest
julia> mutable struct AtomicOnce
           @atomic x
           AtomicOnce() = new()
       end

julia> a = AtomicOnce()
AtomicOnce(#undef)

julia> @atomiconce a.x = 1 # set field x of a to 1, if unset, with sequential consistency
true

julia> @atomic a.x # fetch field x of a, with sequential consistency
1

julia> @atomiconce :monotonic a.x = 2 # set field x of a to 1, if unset, with monotonic consistence
false
```

```jldoctest
julia> mem = AtomicMemory{Vector{Int}}(undef, 1);

julia> isassigned(mem, 1)
false

julia> @atomiconce mem[1] = [1] # set the first value of mem to [1], if unset, with sequential consistency
true

julia> isassigned(mem, 1)
true

julia> @atomic mem[1] # fetch the first value of mem, with sequential consistency
1-element Vector{Int64}:
 1

julia> @atomiconce :monotonic mem[1] = [2] # set the first value of mem to [2], if unset, with monotonic
false

julia> @atomic mem[1]
1-element Vector{Int64}:
 1
```

!!! compat "Julia 1.11"
    Atomic fields functionality requires at least Julia 1.11.

!!! compat "Julia 1.12"
    Atomic reference functionality requires at least Julia 1.12.
"""
macro atomiconce(success_order, fail_order, ex)
    fail_order isa QuoteNode || (fail_order = esc(fail_order))
    success_order isa QuoteNode || (success_order = esc(success_order))
    return make_atomiconce(success_order, fail_order, ex)
end
macro atomiconce(order, ex)
    order isa QuoteNode || (order = esc(order))
    return make_atomiconce(order, order, ex)
end
macro atomiconce(ex)
    return make_atomiconce(QuoteNode(:sequentially_consistent), QuoteNode(:sequentially_consistent), ex)
end
````
-/
def macro_atomiconce_3 (success_order fail_order ex : Value L) : ExprResult (Value L) :=
  let fail_order := match fail_order with
    | .quoteNode _ => fail_order
    | _ => esc fail_order
  let success_order := match success_order with
    | .quoteNode _ => success_order
    | _ => esc success_order
  make_atomiconce success_order fail_order ex
def macro_atomiconce_2 (order ex : Value L) : ExprResult (Value L) :=
  let order := match order with
    | .quoteNode _ => order
    | _ => esc order
  make_atomiconce order order ex
def macro_atomiconce_1 (ex : Value L) : ExprResult (Value L) :=
  make_atomiconce (quoteSym "sequentially_consistent") (quoteSym "sequentially_consistent") ex

/--
Julia source: base/expr.jl:1839-1843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Meta expression head, these generally can't be deleted even when they are
# in a dead branch but can be ignored when analyzing uses/liveness.
is_meta_expr_head(head::Symbol) = head === :boundscheck || head === :meta || head === :loopinfo
is_meta_expr(@nospecialize x) = isa(x, Expr) && is_meta_expr_head(x.head)

```
-/
def is_meta_expr_head (head : Sym) : Bool := head == "boundscheck" || head == "meta" || head == "loopinfo"
def is_meta_expr : Value L → Bool
  | .expr head _ => is_meta_expr_head head
  | _ => false

/--
Julia source: base/expr.jl:1844-1872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    isa_ast_node(x)

Return false if `x` is not interpreted specially by any of inference, lowering,
or codegen as either an AST or IR special form.
"""
function isa_ast_node(@nospecialize x)
    # c.f. Core.IR module, augmented with AST types
    return x isa NewvarNode ||
           x isa CodeInfo ||
           x isa LineNumberNode ||
           x isa GotoNode ||
           x isa GotoIfNot ||
           x isa EnterNode ||
           x isa ReturnNode ||
           x isa SSAValue ||
           x isa SlotNumber ||
           x isa Argument ||
           x isa QuoteNode ||
           x isa GlobalRef ||
           x isa Core.BindingPartition ||
           x isa Symbol ||
           x isa PiNode ||
           x isa PhiNode ||
           x isa PhiCNode ||
           x isa UpsilonNode ||
           x isa Expr
end

```
-/
def isa_ast_node : Value L → Bool
  | .leaf _ => false
  | _ => true

/--
Julia source: base/expr.jl:1873-1874 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_self_quoting(@nospecialize(x)) = !isa_ast_node(x)

```
-/
def is_self_quoting (x : Value L) : Bool := !isa_ast_node x

/--
Julia source: base/expr.jl:1875-1884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    quoted(x)

Return `x` made safe for inserting as a constant into IR. Note that this does
not make it safe for inserting into an AST, since eval will sometimes copy some
types of AST object inside, and even may sometimes evaluate and interpolate any
`\$` inside, depending on the context.
"""
quoted(@nospecialize(x)) = isa_ast_node(x) ? QuoteNode(x) : x

```
-/
def quoted (x : Value L) : Value L := if isa_ast_node x then .quoteNode x else x

-- UNTRANSLATED
-- lowering a generated function body is a `ccall` into the front end (`jl_fl_lower`) producing a `CodeInfo`
-- Source: base/expr.jl:1885-1912 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Implementation of generated functions
-- function generated_body_to_codeinfo(ex::Expr, defmod::Module, isva::Bool, loc::LineNumberNode)
--     ci = ccall(:jl_fl_lower, Any, (Any, Any, Ptr{UInt8}, Csize_t, Csize_t, Cint),
--                ex, defmod, loc.file, loc.line, typemax(Csize_t), 0)[1]
--     if !isa(ci, CodeInfo)
--         if isa(ci, Expr) && ci.head === :error
--             msg = ci.args[1]
--             error(msg isa String ? strcat("syntax: ", msg) : msg)
--         end
--         error("The function body AST defined by this @generated function is not pure. This likely means it contains a closure, a comprehension or a generator.")
--     end
--     # `getfield`/`setfield!`: the `CodeInfo` property methods in deprecated.jl would
--     # invalidate this code, which early-defined generators run in their old world
--     setfield!(ci, :isva, isva)
--     code = getfield(ci, :code)
--     bindings = IdSet{Core.Binding}()
--     for i = 1:length(code)
--         stmt = code[i]
--         if isa(stmt, GlobalRef)
--             push!(bindings, convert(Core.Binding, stmt))
--         end
--     end
--     if !isempty(bindings)
--         setfield!(ci, :edges, Core.svec(bindings...))
--     end
--     return ci
-- end
-- 
-- /Source

-- UNTRANSLATED
-- invoking a `Core.GeneratedFunctionStub` reflects over a `Method` and lowers through `generated_body_to_codeinfo`
-- Source: base/expr.jl:1913-1933 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # invoke and wrap the results of @generated expression
-- function (g::Core.GeneratedFunctionStub)(world::UInt, source::Method, @nospecialize args...)
--     # args is (spvals..., argtypes...)
--     body = g.gen(args...)
--     file = source.file
--     file isa Symbol || (file = :none)
--     loc = LineNumberNode(Int(source.line), source.file)
--     lam = Expr(:lambda, Expr(:argnames, g.argnames...).args,
--                Expr(:var"scope-block",
--                     Expr(:block,
--                          loc,
--                          Expr(:meta, :push_loc, file, :var"@generated body"),
--                          Expr(:return, Expr(:toplevel_pure, body)),
--                          Expr(:meta, :pop_loc))))
--     spnames = g.spnames
--     return generated_body_to_codeinfo(
--         spnames === Core.svec() ? lam : Expr(Symbol("with-static-parameters"), lam, spnames...),
--         source.module,
--         source.isva,
--         loc)
-- end
-- /Source

end

end JuliaLean.base.expr

/-!
Small executable models for expression utilities, enum construction, reflection,
and `Base.Cartesian` on Julia master `bbfa0ce4150`.
-/

/-!
Executable source-body models used by the whole-Base method coverage manifests.
Opaque runtime operations such as `ccall`, compiler queries, lowering, and world-age
lookups enter as explicit oracle values. The Julia wrappers, validation branches,
argument order, AST constructors, list traversal, and error paths remain executable.
-/

namespace JuliaLean.ExprReflect

open JuliaLean

/-- Julia AST values needed by the modelled metaprogramming functions. -/
inductive Ast where
  | atom (name : String)
  | int (value : Int)
  | line
  | expr (head : String) (args : List Ast)
  | quoteNode (value : Ast)
  deriving Repr, Inhabited

/-- `isexpr(ex, heads[, n])`; `base/expr.jl:3-4,42-43`. -/
def isExpr (ex : Ast) (heads : List String) (arity : Option Nat := none) : Bool :=
  match ex with
  | .expr head args => heads.contains head && arity.all (args.length == ·)
  | _ => false

/-!
`copy(::Expr)` recursively copies direct `Expr` arguments but does not descend
through `QuoteNode`. Natural numbers stand for mutable Expr identities.
`base/expr.jl:45,67-81`.
-/
inductive CopyVal where
  | nil
  | atom (name : String)
  | args (first rest : CopyVal)
  | expr (id : Nat) (head : String) (args : CopyVal)
  | quoteNode (value : CopyVal)
  deriving Repr, DecidableEq, Inhabited

def copyExprs (fresh : Nat) : CopyVal → CopyVal
  | .nil => .nil
  | .atom name => .atom name
  | .args first rest => .args (copyExprs fresh first) (copyExprs fresh rest)
  | .expr id head args => .expr (fresh + id) head (copyExprs fresh args)
  | .quoteNode value => .quoteNode value

def eraseCopyIds : CopyVal → CopyVal
  | .nil => .nil
  | .atom name => .atom name
  | .args first rest => .args (eraseCopyIds first) (eraseCopyIds rest)
  | .expr _ head args => .expr 0 head (eraseCopyIds args)
  | .quoteNode value => .quoteNode (eraseCopyIds value)

def copyIds : CopyVal → List Nat
  | .nil => []
  | .atom _ => []
  | .args first rest => copyIds first ++ copyIds rest
  | .expr id _ args => id :: copyIds args
  | .quoteNode value => copyIds value

def allIdsBelow (value : CopyVal) (fresh : Nat) : Bool :=
  (copyIds value).all (· < fresh)

def idsDisjoint (left right : List Nat) : Bool :=
  left.all fun id => !right.contains id

/-! ### Annotation macros -/

/-- Normalized effect of `annotate_meta_def_or_block`; `base/expr.jl:1227-1239`.
The Bool records the preceding `is_function_def` result. -/
def annotateInline (isFunction : Bool) (ex : Ast) : Ast :=
  if isFunction then
    .expr "escape" [.expr "pushmeta" [.atom "inline", ex]]
  else
    .expr "block" [
      .expr "inline" [.atom "true"],
      .expr "local" [.expr "=" [.atom "val", .expr "escape" [ex]]],
      .expr "inline" [.atom "false"],
      .atom "val"]

/-- Normalized `@generated` transformation; `base/expr.jl:1359-1374`. -/
def annotateGenerated (isFunction : Bool) (signature body : Ast) : Jl Ast :=
  if isFunction then
    .ok (.expr "escape" [.expr "function" [signature,
      .expr "if" [.expr "generated" [], body,
        .expr "block" [.expr "meta" [.atom "generated_only"],
          .expr "return" [.atom "nothing"]]]]])
  else
    .error (.argumentError "invalid syntax; @generated must be used with a function definition")

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

def gensymTag (tag : Option String) (counter : Nat) : String :=
  match tag with
  | none => "##" ++ toString counter
  | some tag => "##" ++ tag ++ "#" ++ toString counter

def gensymMany (tags : List String) (counter : Nat) : List String :=
  tags.mapIdx fun index tag => gensymTag (some tag) (counter + index)

def gensymMacro : List String → List (String × String)
  | [] => []
  | name :: names => (name, name) :: gensymMacro names

inductive IRKind where
  | expr | phi | phiC | codeInfo | quoteNode | debugInfo | other
  deriving Repr, DecidableEq, Inhabited

structure IRObject where
  kind : IRKind
  immutable : List Int
  mutableIds : List Nat
  deriving Repr, DecidableEq, Inhabited

def copyIRObject (fresh : Nat) (object : IRObject) : IRObject :=
  match object.kind with
  | .expr | .phi | .phiC | .codeInfo =>
    { object with mutableIds := object.mutableIds.map (fresh + ·) }
  | _ => object

def isequalIRArg (left right : IRObject) : Bool :=
  left.kind == right.kind && left.immutable == right.immutable &&
    left.mutableIds == right.mutableIds

/-- Mutable `CodeInfo` fields copied at `base/expr.jl:84-97`. -/

structure CodeInfoFields where
  code : List IRObject
  slotnames : List String
  slotflags : List Nat
  slottypes : Option (List String)
  ssaflags : List Nat
  edges : Option (List Nat)
  ssavaluetypes : Option (List String)
  deriving Repr, DecidableEq, Inhabited

def copyCodeInfoFields (fresh : Nat) (codeInfo : CodeInfoFields) : CodeInfoFields := {
  code := codeInfo.code.map (copyIRObject fresh)
  slotnames := codeInfo.slotnames
  slotflags := codeInfo.slotflags
  slottypes := codeInfo.slottypes.map id
  ssaflags := codeInfo.ssaflags
  edges := codeInfo.edges.map id
  ssavaluetypes := codeInfo.ssavaluetypes.map id }

def codeInfoEqual (left right : CodeInfoFields) : Bool :=
  left == right

structure MacroexpandFlags where
  recursive : Bool
  inplace : Bool
  legacyscope : Bool
  deriving Repr, DecidableEq, Inhabited

def macroexpandFlags (recursive legacyscope : Bool) : MacroexpandFlags :=
  ⟨recursive, false, legacyscope⟩

def macroexpandBangFlags (recursive legacyscope : Bool) : MacroexpandFlags :=
  ⟨recursive, true, legacyscope⟩

def macroexpandMacroFlags : MacroexpandFlags := ⟨true, false, true⟩

def macroexpand1MacroFlags : MacroexpandFlags := ⟨false, false, true⟩

inductive ConstpropSetting where
  | aggressive | none | unsupported
  deriving Repr, DecidableEq, Inhabited

def constpropTag : ConstpropSetting → Jl String
  | .aggressive => .ok "aggressive_constprop"
  | .none => .ok "no_constprop"
  | .unsupported => .error (.argumentError "unsupported @constprop setting")

structure EffectOverride where
  consistent : Bool := false
  effectFree : Bool := false
  nothrow : Bool := false
  terminatesGlobally : Bool := false
  terminatesLocally : Bool := false
  notaskstate : Bool := false
  inaccessibleMemOnly : Bool := false
  noub : Bool := false
  noubIfNoInbounds : Bool := false
  consistentOverlay : Bool := false
  nortcall : Bool := false
  deriving Repr, DecidableEq, Inhabited

def effectBits (override : EffectOverride) : List Bool := [
  override.consistent, override.effectFree, override.nothrow,
  override.terminatesGlobally, override.terminatesLocally, override.notaskstate,
  override.inaccessibleMemOnly, override.noub, override.noubIfNoInbounds,
  override.consistentOverlay, override.nortcall]

def decodeEffectBits (bits : List Bool) : EffectOverride := {
  consistent := bits[0]?.getD false
  effectFree := bits[1]?.getD false
  nothrow := bits[2]?.getD false
  terminatesGlobally := bits[3]?.getD false
  terminatesLocally := bits[4]?.getD false
  notaskstate := bits[5]?.getD false
  inaccessibleMemOnly := bits[6]?.getD false
  noub := bits[7]?.getD false
  noubIfNoInbounds := bits[8]?.getD false
  consistentOverlay := bits[9]?.getD false
  nortcall := bits[10]?.getD false }

inductive EffectSetting where
  | consistent | effectFree | nothrow | terminatesGlobally | terminatesLocally
  | notaskstate | inaccessibleMemOnly | noub | noubIfNoInbounds | nortcall
  | foldable | removable | total
  deriving Repr, DecidableEq, Inhabited

def applyEffectSetting (override : EffectOverride) (setting : EffectSetting)
    (value : Bool := true) : EffectOverride :=
  match setting with
  | .consistent => { override with consistent := value }
  | .effectFree => { override with effectFree := value }
  | .nothrow => { override with nothrow := value }
  | .terminatesGlobally => { override with terminatesGlobally := value }
  | .terminatesLocally => { override with terminatesLocally := value }
  | .notaskstate => { override with notaskstate := value }
  | .inaccessibleMemOnly => { override with inaccessibleMemOnly := value }
  | .noub => { override with noub := value }
  | .noubIfNoInbounds => { override with noubIfNoInbounds := value }
  | .nortcall => { override with nortcall := value }
  | .foldable => {
      consistent := value, effectFree := value, nothrow := override.nothrow,
      terminatesGlobally := value, terminatesLocally := override.terminatesLocally,
      notaskstate := override.notaskstate, inaccessibleMemOnly := override.inaccessibleMemOnly,
      noub := value, noubIfNoInbounds := override.noubIfNoInbounds,
      consistentOverlay := override.consistentOverlay, nortcall := value }
  | .removable => {
      consistent := override.consistent, effectFree := value, nothrow := value,
      terminatesGlobally := value, terminatesLocally := override.terminatesLocally,
      notaskstate := override.notaskstate, inaccessibleMemOnly := override.inaccessibleMemOnly,
      noub := override.noub, noubIfNoInbounds := override.noubIfNoInbounds,
      consistentOverlay := override.consistentOverlay, nortcall := override.nortcall }
  | .total => {
      consistent := value, effectFree := value, nothrow := value,
      terminatesGlobally := value, terminatesLocally := override.terminatesLocally,
      notaskstate := value, inaccessibleMemOnly := value, noub := value,
      noubIfNoInbounds := override.noubIfNoInbounds,
      consistentOverlay := override.consistentOverlay, nortcall := value }

inductive EffectTarget where | ccall | functionDef | anonymous | callsite
  deriving Repr, DecidableEq, Inhabited

def assumeEffectsShape : EffectTarget → String
  | .ccall => "ccall_effects-word"
  | .functionDef => "pushmeta-purity"
  | .anonymous => "meta-purity"
  | .callsite => "purity-region"

def annotationTag (tag : String) (isFunction : Bool) : String :=
  if isFunction then "pushmeta:" ++ tag else "region:" ++ tag

def constpropShape (setting : ConstpropSetting) (hasExpression : Bool) : Jl String := do
  let tag ← constpropTag setting
  return if hasExpression then "pushmeta:" ++ tag else "meta:" ++ tag

/-! ## base/expr.jl: metadata, line numbers, and generated annotations -/

def unwrapMacroDepth : Nat → Ast → Ast
  | 0, expression => expression
  | depth + 1, expression => unwrapMacroDepth depth expression

def metaGet (args : List String) (tag : String) (delete : Bool) : Option String × List String :=
  (args.find? (· == tag), if delete then args.filter (· != tag) else args)

def isFunctionHead (head : String) : Bool :=
  head == "function" || head == "=" || head == "->"

def generatedMarker : Ast := .expr "generated" []

/-! A direct tree for the metadata and line-number methods at
`base/expr.jl:1167-1324`. -/

inductive CoverageAst where
  | nil
  | atom (value : String)
  | line (line : Int) (file : Option String)
  | args (first rest : CoverageAst)
  | expr (head : String) (args : CoverageAst)
  deriving Repr, DecidableEq, Inhabited

namespace CoverageAst

def filterLines : CoverageAst → CoverageAst
  | .nil => .nil
  | .args (.line _ _) rest => filterLines rest
  | .args first rest => .args first (filterLines rest)
  | other => other

def removeLineNums : CoverageAst → CoverageAst
  | .nil => .nil
  | .atom value => .atom value
  | .line lineNumber file => .line lineNumber file
  | .args first rest => .args (removeLineNums first) (removeLineNums rest)
  | .expr head arguments =>
    let arguments := removeLineNums arguments
    let arguments := if head == "block" || head == "quote" then filterLines arguments else arguments
    .expr head arguments

def replaceLineNums (replacement : Int) : CoverageAst → CoverageAst
  | .nil => .nil
  | .atom value => .atom value
  | .line _ file => .line replacement file
  | .args first rest => .args (replaceLineNums replacement first) (replaceLineNums replacement rest)
  | .expr "escape" arguments => .expr "escape" arguments
  | .expr head arguments => .expr head (replaceLineNums replacement arguments)

def unwrapMacrocall : CoverageAst → CoverageAst
  | .expr "macrocall" (.args _ (.args inner .nil)) => unwrapMacrocall inner
  | expression => expression
termination_by expression => sizeOf expression

def isFunctionDef : CoverageAst → Bool
  | .expr "function" _ | .expr "->" _ => true
  | .expr "=" (.args (.expr "call" _) _) => true
  | _ => false

end CoverageAst

inductive AtomicTarget where | field | index
  deriving Repr, DecidableEq, Inhabited

inductive AtomicOperation where | fetch | store | modify | swap | replace | once
  deriving Repr, DecidableEq, Inhabited

def atomicPrimitive : AtomicOperation → AtomicTarget → String
  | .fetch, .field => "getproperty"
  | .fetch, .index => "getindex_atomic"
  | .store, .field => "setproperty!"
  | .store, .index => "setindex_atomic!"
  | .modify, .field => "modifyproperty!"
  | .modify, .index => "modifyindex_atomic!"
  | .swap, .field => "swapproperty!"
  | .swap, .index => "swapindex_atomic!"
  | .replace, .field => "replaceproperty!"
  | .replace, .index => "replaceindex_atomic!"
  | .once, .field => "setpropertyonce!"
  | .once, .index => "setindexonce_atomic!"

def atomicOrderCount : AtomicOperation → Nat
  | .fetch | .store | .modify | .swap => 1
  | .replace | .once => 2

inductive AstNodeKind where
  | newvar | codeInfo | line | goto | gotoIf | enter | ret | ssa | slot | argument
  | quote | globalRef | binding | symbol | pi | phi | phiC | upsilon | expr | other
  deriving Repr, DecidableEq, Inhabited

def isaAstNode : AstNodeKind → Bool
  | .other => false
  | _ => true

def quotedShape (kind : AstNodeKind) : String :=
  if isaAstNode kind then "QuoteNode" else "self"

inductive LoweredGenerated where | codeInfo | syntaxError | impure
  deriving Repr, DecidableEq, Inhabited

def generatedBodyResult (lowered : LoweredGenerated) : Jl String :=
  match lowered with
  | .codeInfo => .ok "CodeInfo:isva+binding-edges"
  | .syntaxError => .error (.argumentError "syntax")
  | .impure => .error (.argumentError "generated body is not pure")

end JuliaLean.ExprReflect

namespace JuliaLean.ExprReflect

open JuliaLean

def exprRow3 (expression : Ast) (heads : List String) : Bool := isExpr expression heads none

def exprRow4 (expression : Ast) (heads : List String) (arity : Nat) : Bool := isExpr expression heads (some arity)

structure GensymState where
  next : Nat
  names : List String
  deriving Repr, DecidableEq, Inhabited

def jlGensym (tag : Option String) (state : GensymState) : String × GensymState :=
  let name := gensymTag tag state.next
  (name, ⟨state.next + 1, state.names ++ [name]⟩)

def exprRow18 (state : GensymState) := jlGensym none state

def exprRow20 (tag : String) (state : GensymState) := jlGensym (some tag) state

def exprRow22 : List String → GensymState → List String × GensymState
  | [], state => ([],state)
  | tag::tags, state =>
    let (name,state) := jlGensym (some tag) state
    let (names,state) := exprRow22 tags state
    (name::names,state)

def exprRow23 (tag : String) (state : GensymState) := jlGensym (some tag) state

def exprRow31 (names : List String) (state : GensymState) : List (String × String) × GensymState :=
  let (generated,state) := exprRow22 names state
  (List.zip names generated, state)

def exprRow42 (expression : Ast) (head : String) : Bool := isExpr expression [head] none

def exprRow43 (expression : Ast) (head : String) (arity : Nat) : Bool := isExpr expression [head] (some arity)

structure PhiModel where
  edges : List Int
  values : List (Option IRObject)
  deriving Repr, DecidableEq, Inhabited

structure PhiCModel where
  values : List (Option IRObject)
  deriving Repr, DecidableEq, Inhabited

def copyOptionalIR (fresh : Nat) : Option IRObject → Option IRObject
  | none => none
  | some value => some (copyIRObject fresh value)

def exprRow45 (fresh : Nat) (object : IRObject) : IRObject := copyIRObject fresh { object with kind := .expr }

def exprRow46 (fresh : Nat) (node : PhiModel) : PhiModel :=
  ⟨node.edges, node.values.map (copyOptionalIR fresh)⟩

def exprRow56 (fresh : Nat) (node : PhiCModel) : PhiCModel :=
  ⟨node.values.map (copyOptionalIR fresh)⟩

def exprRow69 (fresh : Nat) (object : IRObject) : IRObject :=
  match object.kind with
  | .expr | .phi | .phiC => copyIRObject fresh object
  | _ => object

def exprRow79 (fresh : Nat) (arguments : List (Option IRObject)) : List (Option IRObject) :=
  arguments.map (copyOptionalIR fresh)

def exprRow81 (head : String) (arguments : List Ast) : Ast := .expr head arguments

def exprRow84 (fresh : Nat) (code : CodeInfoFields) : CodeInfoFields := copyCodeInfoFields fresh code

def exprRow99 (left right : IRObject) : Bool := isequalIRArg left right

def exprRow118 (left right : List IRObject) : Bool :=
  left.length == right.length && (List.zip left right).all fun pair => isequalIRArg pair.1 pair.2

def exprStructuralEqual (left right : IRObject) : Bool := isequalIRArg left right

def exprRow135 := exprStructuralEqual

def exprRow137 := exprStructuralEqual

def exprRow139 := exprStructuralEqual

def exprRow141 := exprStructuralEqual

def exprRow143 := exprStructuralEqual

def exprRow173 := exprStructuralEqual

def exprRow209 (recursive legacy : Bool) : MacroexpandFlags := ⟨recursive,false,legacy⟩

def exprRow232 (recursive legacy : Bool) : MacroexpandFlags := ⟨recursive,true,legacy⟩

def exprRow279 (moduleName expression : String) : String := "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),true,true)"

def exprRow282 := exprRow279

def exprRow291 (moduleName expression : String) : String := "macroexpand(" ++ moduleName ++ ",QuoteNode(" ++ expression ++ "),false,true)"

def exprRow294 := exprRow291

def exprRow389 (isFunction : Bool) : String := annotationTag "inline" isFunction

def exprRow466 (isFunction : Bool) : String := annotationTag "noinline" isFunction

def exprRow505 (setting : ConstpropSetting) (isExpression : Bool) := constpropShape setting isExpression

def exprRow510 (setting : ConstpropSetting) := constpropShape setting false

def exprRow515 := constpropTag

def exprRow896 (target : EffectTarget) : String := assumeEffectsShape target

def exprRow938 (settings : List (EffectSetting × Bool)) : EffectOverride :=
  settings.foldl (fun override setting => applyEffectSetting override setting.1 setting.2) default

def exprRow962 (override : EffectOverride) := override

def exprRow995 (override : EffectOverride) (setting : EffectSetting) (value : Bool) :=
  applyEffectSetting override setting value

def exprRow1035 := effectBits

def exprRow1051 := decodeEffectBits

def exprRow1066 := effectBits

def exprRow1111 (isExpression : Bool) := if isExpression then "pushmeta:nospecializeinfer" else "identity"

def exprRow1148 (isExpression : Bool) := if isExpression then ["inline","propagate_inbounds"] else []

def exprRow1161 (isExpression : Bool) := if isExpression then ["polly"] else []

def exprRow1167 (value : CoverageAst) : CoverageAst := value

def exprRow1168 (value : CoverageAst) : CoverageAst := CoverageAst.unwrapMacrocall value

structure MetaBody where
  tags : List String
  statements : List CoverageAst
  deriving Repr, DecidableEq, Inhabited

/-- `pushmeta!`; `base/expr.jl:1176-1187`. -/

def exprRow1176 (body : MetaBody) (tag : String) : MetaBody :=
  { body with tags := body.tags ++ [tag] }

def getMetaTag (body : MetaBody) (tag : String) (delete : Bool) : Option String × MetaBody :=
  match body.tags.findIdx? (· == tag) with
  | none => (none,body)
  | some index =>
    let found := body.tags[index]!
    (some found, if delete then { body with tags := body.tags.eraseIdx index } else body)

/-- `popmeta!`; `base/expr.jl:1189`. -/

def exprRow1189 (body : MetaBody) (tag : String) := getMetaTag body tag true

def exprRow1190 (body : MetaBody) (tag : String) := getMetaTag body tag false

def exprRow1192 (body : MetaBody) (tag : String) (delete : Bool) := getMetaTag body tag delete

def exprRow1196 (body : CoverageAst) : Option String × CoverageAst := (none,body)

def exprRow1197 (body : MetaBody) (tag : String) (delete : Bool) := getMetaTag body tag delete

def exprRow1216 (arguments : List String) (tag : String) : Nat :=
  match arguments.findIdx? (· == tag) with | none => 0 | some index => index + 1

def exprRow1227 (isFunction : Bool) (tag : String) : String := annotationTag tag isFunction

def exprRow1242 (value : CoverageAst) : Bool :=
  match value with | .expr "=" (.args (.expr "call" _) _) => true | _ => false

def exprRow1251 (value : CoverageAst) : Bool := CoverageAst.isFunctionDef value

def exprRow1254 (isFunction : Bool) (body : MetaBody) : Jl (Nat × MetaBody) :=
  if isFunction then .ok (if body.tags.isEmpty then 0 else 1,body)
  else .error (.argumentError "not a function expression")

def exprRow1263 (body : MetaBody) : Nat × MetaBody := (if body.tags.isEmpty then 0 else 1,body)

def exprRow1265 (body : MetaBody) (predicate : List String → Bool) : Nat :=
  match body.tags.findIdx? (fun tag => predicate [tag]) with | none => 0 | some index => index + 1

def exprRow1287 (value : CoverageAst) := CoverageAst.removeLineNums value

def exprRow1306 (value : CoverageAst) (_line : Int) := value

def exprRow1307 (value : CoverageAst) (line : Int) := CoverageAst.replaceLineNums line value

def exprRow1326 : Ast := .expr "generated" []

def exprRow1359 (isFunction : Bool) (signature body : Ast) : Jl Ast := annotateGenerated isFunction signature body

inductive AtomicSyntax where
  | field (object field : String)
  | index (object : String) (indices : List String)
  | call (operator : String) (target : AtomicSyntax) (argument : String)
  | assign (target : AtomicSyntax) (value : String)
  | modify (target : AtomicSyntax) (operator value : String)
  | replace (target : AtomicSyntax) (expected replacement : String)
  | once (target : AtomicSyntax) (value : String)
  | invalid
  deriving Repr, Inhabited

structure AtomicCall where
  primitive : String
  arguments : List String
  selectSecond : Bool := false
  deriving Repr, DecidableEq, Inhabited

def lowerAtomic (operation : AtomicOperation) (successOrder failOrder : String)
    (target : AtomicSyntax) (operator value extra : String) (selectSecond : Bool := false) : Jl AtomicCall :=
  match target with
  | .field object field =>
    let arguments := match operation with
      | .fetch => [object,field,successOrder]
      | .store | .swap => [object,field,value,successOrder]
      | .modify => [object,field,operator,value,successOrder]
      | .replace => [object,field,value,extra,successOrder,failOrder]
      | .once => [object,field,value,successOrder,failOrder]
    .ok ⟨atomicPrimitive operation .field,arguments,selectSecond⟩
  | .index object indices =>
    let callPrefix := match operation with
      | .fetch => [object,successOrder]
      | .store | .swap => [object,successOrder,value]
      | .modify => [object,successOrder,operator,value]
      | .replace => [object,successOrder,failOrder,value,extra]
      | .once => [object,successOrder,failOrder,value]
    .ok ⟨atomicPrimitive operation .index,callPrefix ++ indices,selectSecond⟩
  | _ => .error (.argumentError "atomic target must be field access or indexing")

def sequentialOrder : String := "sequentially_consistent"

def exprRow1489 (isDeclaration : Bool) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  if isDeclaration then .ok ⟨"Expr(:atomic)",[],false⟩
  else lowerAtomic .fetch sequentialOrder sequentialOrder atomicExpression "" "" ""

def exprRow1495 (order : String) (atomicExpression : AtomicSyntax) :=
  lowerAtomic .fetch order order atomicExpression "" "" ""

def exprRow1499 (target : AtomicSyntax) (operator value : String) :=
  lowerAtomic .modify sequentialOrder sequentialOrder target operator value ""

def exprRow1502 := exprRow1499

def exprRow1506 (order : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .field _ _ | .index _ _ => lowerAtomic .fetch order order atomicExpression "" "" ""
  | .call operator target value => lowerAtomic .modify order order target operator value ""
  | .assign target value => lowerAtomic .store order order target "" value ""
  | .modify target operator value => lowerAtomic .modify order order target operator value "" true
  | .invalid => .error (.argumentError "could not parse @atomic expression")
  | _ => .error (.argumentError "could not parse @atomic expression")

def exprRow1555 (order : String) (target : AtomicSyntax) (operator value : String) :=
  lowerAtomic .modify order order target operator value ""

def makeAtomicSwap (order : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .assign target value => lowerAtomic .swap order order target "" value ""
  | _ => .error (.argumentError "@atomicswap expression missing assignment")

def exprRow1615 (order : String) (atomicExpression : AtomicSyntax) := makeAtomicSwap order atomicExpression

def exprRow1619 (atomicExpression : AtomicSyntax) := makeAtomicSwap sequentialOrder atomicExpression

def exprRow1622 (order : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  makeAtomicSwap order atomicExpression

def makeAtomicReplace (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .replace target expected replacement =>
    lowerAtomic .replace success fail target "" expected replacement
  | _ => .error (.argumentError "@atomicreplace expression missing field access or indexing")

def exprRow1710 (success fail : String) (atomicExpression : AtomicSyntax) :=
  makeAtomicReplace success fail atomicExpression

def exprRow1715 (order : String) (atomicExpression : AtomicSyntax) := makeAtomicReplace order order atomicExpression

def exprRow1719 (atomicExpression : AtomicSyntax) := makeAtomicReplace sequentialOrder sequentialOrder atomicExpression

def exprRow1722 (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  makeAtomicReplace success fail atomicExpression

def makeAtomicOnce (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  match atomicExpression with
  | .once target value | .assign target value => lowerAtomic .once success fail target "" value ""
  | _ => .error (.argumentError "@atomiconce expression missing assignment")

def exprRow1813 (success fail : String) (atomicExpression : AtomicSyntax) :=
  makeAtomicOnce success fail atomicExpression

def exprRow1818 (order : String) (atomicExpression : AtomicSyntax) := makeAtomicOnce order order atomicExpression

def exprRow1822 (atomicExpression : AtomicSyntax) := makeAtomicOnce sequentialOrder sequentialOrder atomicExpression

def exprRow1825 (success fail : String) (atomicExpression : AtomicSyntax) : Jl AtomicCall :=
  makeAtomicOnce success fail atomicExpression

def exprRow1841 (head : String) : Bool := head == "boundscheck" || head == "meta" || head == "loopinfo"

def exprRow1842 (isExpression : Bool) (head : String) : Bool := isExpression && exprRow1841 head

def exprRow1850 := isaAstNode

def exprRow1873 (kind : AstNodeKind) : Bool := !isaAstNode kind

def exprRow1883 := quotedShape

def exprRow1886 := generatedBodyResult

structure GeneratedStubInput where
  body : String
  file : Option String
  line : Int
  argnames : List String
  staticParameters : List String
  moduleName : String
  isVararg : Bool
  deriving Repr, DecidableEq, Inhabited

def exprRow1914 (input : GeneratedStubInput) : String :=
  let file := input.file.getD "none"
  let lambda := "lambda(" ++ String.intercalate "," input.argnames ++ "):push_loc(" ++ file ++ "):return(toplevel_pure(" ++ input.body ++ ")):pop_loc"
  if input.staticParameters.isEmpty then lambda else "with-static-parameters(" ++ lambda ++ "," ++ String.intercalate "," input.staticParameters ++ ")"

end JuliaLean.ExprReflect

/-!
# Julia surface ASTs

`JE` is the subset of Julia's `Expr` trees that the printer and parser models
share. Symbols and strings are Lean `String`s holding the UTF-8 name. Numeric
literals carry their Julia value:

* `int v` is an `Int64` literal (`-2^63 ≤ v < 2^63`);
* `flt neg ip fp` is the `Float64` literal `±ip.fp` whose shortest
  representation (`string(x)`, `base/ryu/Ryu.jl`) is `ip.fp` written with the
  decimal digits `fp`, which has no trailing zero unless it is `[0]`. `neg`
  is the sign bit, so `flt true 0 [0]` is `-0.0`.

`qn v` is a `QuoteNode` and `node h args` is `Expr(Symbol(h), args...)`.
-/

namespace JuliaLean.Show

inductive JE where
  | sym (name : String)
  | int (v : Int)
  | flt (neg : Bool) (ip : Nat) (fp : List Nat)
  | str (s : String)
  | qn (v : JE)
  | node (head : String) (args : List JE)
  deriving Repr, Inhabited

mutual
/-- Structural equality of `JE` trees, as `==` on `Expr`/`QuoteNode` and `===`
on symbols and literals. -/
def JE.beq : JE → JE → Bool
  | .sym a, .sym b => a == b
  | .int a, .int b => a == b
  | .flt n i f, .flt n' i' f' => n == n' && i == i' && f == f'
  | .str a, .str b => a == b
  | .qn a, .qn b => JE.beq a b
  | .node h as, .node h' bs => h == h' && JE.beqList as bs
  | _, _ => false
def JE.beqList : List JE → List JE → Bool
  | [], [] => true
  | a :: as, b :: bs => JE.beq a b && JE.beqList as bs
  | _, _ => false
end

mutual
/-- Decidable equality of `JE` trees. -/
def JE.decEq : (x y : JE) → Decidable (x = y)
  | .sym a, .sym b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => JE.noConfusion e (fun h' => h h'))
  | .int a, .int b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => JE.noConfusion e (fun h' => h h'))
  | .str a, .str b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => JE.noConfusion e (fun h' => h h'))
  | .flt a b c, .flt a' b' c' =>
    if h : a = a' ∧ b = b' ∧ c = c' then isTrue (by obtain ⟨h1, h2, h3⟩ := h; subst h1; subst h2; subst h3; rfl)
    else isFalse (fun e => JE.noConfusion e (fun h1 h2 h3 => h ⟨h1, h2, h3⟩))
  | .qn a, .qn b =>
    match JE.decEq a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => JE.noConfusion e (fun h' => h h'))
  | .node a as, .node b bs =>
    if h : a = b then
      match JE.decEqList as bs with
      | isTrue h' => isTrue (by subst h; subst h'; rfl)
      | isFalse h' => isFalse (fun e => JE.noConfusion e (fun _ h2 => h' h2))
    else isFalse (fun e => JE.noConfusion e (fun h1 _ => h h1))
  | .sym _, .int _ => isFalse (fun e => JE.noConfusion e)
  | .sym _, .flt _ _ _ => isFalse (fun e => JE.noConfusion e)
  | .sym _, .str _ => isFalse (fun e => JE.noConfusion e)
  | .sym _, .qn _ => isFalse (fun e => JE.noConfusion e)
  | .sym _, .node _ _ => isFalse (fun e => JE.noConfusion e)
  | .int _, .sym _ => isFalse (fun e => JE.noConfusion e)
  | .int _, .flt _ _ _ => isFalse (fun e => JE.noConfusion e)
  | .int _, .str _ => isFalse (fun e => JE.noConfusion e)
  | .int _, .qn _ => isFalse (fun e => JE.noConfusion e)
  | .int _, .node _ _ => isFalse (fun e => JE.noConfusion e)
  | .flt _ _ _, .sym _ => isFalse (fun e => JE.noConfusion e)
  | .flt _ _ _, .int _ => isFalse (fun e => JE.noConfusion e)
  | .flt _ _ _, .str _ => isFalse (fun e => JE.noConfusion e)
  | .flt _ _ _, .qn _ => isFalse (fun e => JE.noConfusion e)
  | .flt _ _ _, .node _ _ => isFalse (fun e => JE.noConfusion e)
  | .str _, .sym _ => isFalse (fun e => JE.noConfusion e)
  | .str _, .int _ => isFalse (fun e => JE.noConfusion e)
  | .str _, .flt _ _ _ => isFalse (fun e => JE.noConfusion e)
  | .str _, .qn _ => isFalse (fun e => JE.noConfusion e)
  | .str _, .node _ _ => isFalse (fun e => JE.noConfusion e)
  | .qn _, .sym _ => isFalse (fun e => JE.noConfusion e)
  | .qn _, .int _ => isFalse (fun e => JE.noConfusion e)
  | .qn _, .flt _ _ _ => isFalse (fun e => JE.noConfusion e)
  | .qn _, .str _ => isFalse (fun e => JE.noConfusion e)
  | .qn _, .node _ _ => isFalse (fun e => JE.noConfusion e)
  | .node _ _, .sym _ => isFalse (fun e => JE.noConfusion e)
  | .node _ _, .int _ => isFalse (fun e => JE.noConfusion e)
  | .node _ _, .flt _ _ _ => isFalse (fun e => JE.noConfusion e)
  | .node _ _, .str _ => isFalse (fun e => JE.noConfusion e)
  | .node _ _, .qn _ => isFalse (fun e => JE.noConfusion e)
def JE.decEqList : (xs ys : List JE) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | x :: xs, y :: ys =>
    match JE.decEq x y, JE.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (by subst h1; subst h2; rfl)
    | isFalse h1, _ => isFalse (by intro e; injection e with h _; exact h1 h)
    | _, isFalse h2 => isFalse (by intro e; injection e with _ h; exact h2 h)
end

instance : DecidableEq JE := JE.decEq

end JuliaLean.Show

namespace JuliaLean.MiscCov.Experimental

/-- `Base.unwrap_macrocalls(ex)`: the last argument of nested macro calls. -/
def unwrapMacrocalls : Nat → Ex → Ex
  | 0, ex => ex
  | n + 1, .expr "macrocall" args =>
    match args.getLast? with
    | some a => unwrapMacrocalls n a
    | none => .expr "macrocall" args
  | _, ex => ex

/-- `Meta.is_function_def(ex)` (`base/expr.jl`): `function`, `->`, or a short definition
`f(...) = ...` (possibly through `::` and `where`). -/
def isShortSig : Nat → Ex → Bool
  | 0, _ => false
  | n + 1, .expr "call" _ => true
  | n + 1, .expr "::" (a :: _) => isShortSig n a
  | n + 1, .expr "where" (a :: _) => isShortSig n a
  | _, _ => false

def isFunctionDef (ex : Ex) : Bool :=
  match ex with
  | .expr "function" _ => true
  | .expr "->" _ => true
  | .expr "=" (lhs :: _) => isShortSig 100 lhs
  | _ => false

end JuliaLean.MiscCov.Experimental

namespace JuliaLean.MiscCov.CInterface

/-- `CCALL_EFFECT_RESET_SAFE`, `base/expr.jl:993`. -/
def resetSafeBit : Nat := 0x0800

end JuliaLean.MiscCov.CInterface

namespace JuliaLean.MiscCov.Deprecated

/-! ## Line numbers, `base/expr.jl` -/

/-- `remove_linenums!(ex)`: drop `LineNumberNode`s from every `Expr`'s arguments. -/
def removeLinenums : Ex → Ex
  | .expr h as => .expr h ((as.filter (fun a => !a.isLnn)).attach.map (fun ⟨a, _⟩ => removeLinenums a))
  | e => e
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem (List.mem_filter.mp ‹_›).1
  simp_wf; omega

/-- `replace_linenums!(ex, lnn)`: every `LineNumberNode` becomes the macro's source. -/
def replaceLinenums : Ex → Ex
  | .expr h as => .expr h (as.attach.map (fun ⟨a, _⟩ => replaceLinenums a))
  | .lnn => .lnn
  | e => e
termination_by e => sizeOf e
decreasing_by
  have := List.sizeOf_lt_of_mem ‹_›
  simp_wf; omega

end JuliaLean.MiscCov.Deprecated
