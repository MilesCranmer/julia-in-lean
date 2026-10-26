import JuliaLean.Core

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

/-- `Base.Meta.quot(ex)`: `Expr(:quote, ex)`. -/
def quot (x : JV) : JV := .expr "quote" [x]

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

/-! `Except` evaluation lemmas for the models of this area. -/

deriving instance DecidableEq for Except

@[simp] theorem exc_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
@[simp] theorem exc_map_ok {ε α β : Type} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl
@[simp] theorem exc_bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl
@[simp] theorem exc_bind_error {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

end JuliaLean.DocsSyntaxCov
