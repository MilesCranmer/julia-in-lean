import JuliaLean.Core

/-!
Shared source-faithful models for the allocation and `ccall` wrapper patterns in
`base/gmp.jl` and `base/mpfr.jl`.  A function argument represents the documented
GMP or MPFR primitive.  The Julia method still controls allocation, argument
order, mutation, error checks, and the returned value.
-/

namespace JuliaLean.BigNumsCov

/-- A small mutable-number model.  `serial` distinguishes fresh allocations. -/
structure Cell where
  value : Int
  serial : Nat
  deriving Repr, DecidableEq

/-- `op!(x, a); x`: the common one-input GMP wrapper body. -/
def inplaceUnary (op : Cell → Int → Cell) (x : Cell) (a : Int) : Cell :=
  op x a

/-- `op(a) = op!(BigInt(), a)`. -/
def allocatingUnary (op : Cell → Int → Cell) (fresh : Cell) (a : Int) : Cell :=
  inplaceUnary op fresh a

/-- `op!(x, a, b); x`: the common two-input GMP/MPFR wrapper body. -/
def inplaceBinary (op : Cell → Int → Int → Cell) (x : Cell) (a b : Int) : Cell :=
  op x a b

/-- `op(a, b) = op!(BigInt(), a, b)`. -/
def allocatingBinary (op : Cell → Int → Int → Cell) (fresh : Cell) (a b : Int) : Cell :=
  inplaceBinary op fresh a b

/-- `op!(x, x, b)`: the aliasing convenience overload. -/
def aliasingBinary (op : Cell → Int → Int → Cell) (x : Cell) (b : Int) : Cell :=
  inplaceBinary op x x.value b

/-- The allocation/call/return body shared by MPFR unary methods. -/
def mpfrUnary (op : Cell → Int → Cell) (fresh : Cell) (x : Int) : Cell :=
  op fresh x

/-- The allocation/call/return body shared by MPFR binary methods. -/
def mpfrBinary (op : Cell → Int → Int → Cell) (fresh : Cell) (x y : Int) : Cell :=
  op fresh x y

/-- The allocation/call/return body shared by MPFR ternary methods. -/
def mpfrTernary (op : Cell → Int → Int → Int → Cell) (fresh : Cell)
    (x y z : Int) : Cell :=
  op fresh x y z

/-- Julia's generated left-folding three-argument wrapper. -/
def fold3 (op : Int → Int → Int) (a b c : Int) : Int :=
  op (op a b) c

/-- Julia's generated left-folding four-argument wrapper. -/
def fold4 (op : Int → Int → Int) (a b c d : Int) : Int :=
  op (op (op a b) c) d

/-- Julia's generated left-folding five-argument wrapper. -/
def fold5 (op : Int → Int → Int) (a b c d e : Int) : Int :=
  op (op (op (op a b) c) d) e

def WrapperAllocationCorrect : Prop :=
  (∀ op fresh a, allocatingUnary op fresh a = op fresh a) ∧
  (∀ op fresh a b, allocatingBinary op fresh a b = op fresh a b) ∧
  (∀ op x b, aliasingBinary op x b = op x x.value b)

theorem wrapperAllocationCorrect : WrapperAllocationCorrect := by
  simp [WrapperAllocationCorrect, allocatingUnary, allocatingBinary,
    aliasingBinary, inplaceUnary, inplaceBinary]

def MpfrWrapperCorrect : Prop :=
  (∀ op fresh x, mpfrUnary op fresh x = op fresh x) ∧
  (∀ op fresh x y, mpfrBinary op fresh x y = op fresh x y) ∧
  (∀ op fresh x y z, mpfrTernary op fresh x y z = op fresh x y z)

theorem mpfrWrapperCorrect : MpfrWrapperCorrect := by
  simp [MpfrWrapperCorrect, mpfrUnary, mpfrBinary, mpfrTernary]

def GeneratedFoldCorrect : Prop :=
  (∀ op a b c, fold3 op a b c = op (op a b) c) ∧
  (∀ op a b c d, fold4 op a b c d = op (op (op a b) c) d) ∧
  (∀ op a b c d e, fold5 op a b c d e = op (op (op (op a b) c) d) e)

theorem generatedFoldCorrect : GeneratedFoldCorrect := by
  simp [GeneratedFoldCorrect, fold3, fold4, fold5]

end JuliaLean.BigNumsCov
