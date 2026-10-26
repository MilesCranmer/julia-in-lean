import JuliaLean.IteratorsCov.Base

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

/-- The parser accepts exactly assignment/in iteration forms with a symbol;
body validation rejects nested break/continue/goto; a valid one-dimensional
loop compiles to the recorded variable, range, body and dependency flag; the
range helpers and both macros follow their source bodies. -/
def SimdLoopSemantics : Prop :=
  (∀ head var range, (head = "=" ∨ head = "in") →
    parseIterationSpace (.expr head [.symbol var, range]) = .ok (var, range)) ∧
  (∀ x, checkSimdBody x = if forbidden x then
    .error (.simdError "invalid control flow inside a @simd loop body") else .ok true) ∧
  (∀ (α : Type) (r : List α) j, simdOuterRange r = [0] ∧
    simdInnerLength r j = r.length) ∧
  (∀ (α : Type) (r : List α) j i value, r[i]? = some value →
    simdIndex r j i = .ok value) ∧
  (∀ var range body ivdep,
    forbidden (.expr "for" [.expr "=" [.symbol var, range], body]) = false →
    compileSimd (.expr "for" [.expr "=" [.symbol var, range], body]) ivdep =
      .ok { varName := var, range := range, body := body, ivdep := ivdep }) ∧
  (∀ loop, simdMacro loop = compileSimd loop none) ∧
  (∀ loop, simdIvdepMacro "ivdep" loop = compileSimd loop (some "julia.ivdep")) ∧
  (∀ tag loop, tag ≠ "ivdep" →
    simdIvdepMacro tag loop =
      .error (.simdError "Only ivdep is valid as the first argument to @simd"))

theorem simdLoopSemantics : SimdLoopSemantics := by
  refine ⟨?_, fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, ?_, ?_,
    fun _ => rfl, ?_, ?_⟩
  · intro head var range h
    rcases h with rfl | rfl <;> rfl
  · intro α r j i value h
    simp [simdIndex, h]
  · intro var range body ivdep h
    simp [compileSimd, checkSimdBody, h, parseIterationSpace]
    rfl
  · intro loop
    simp [simdIvdepMacro]
  · intro tag loop h
    simp [simdIvdepMacro, h]

end JuliaLean.IteratorsCov
