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


/-- Result of the parser model on a source text: the parsed tree, a Julia
`ParseError`, or `unknown` when the text leaves the modelled fragment. -/
inductive PResult where
  | ok (e : JE)
  | error
  | unknown
  deriving Repr, Inhabited, DecidableEq

end JuliaLean.Show
