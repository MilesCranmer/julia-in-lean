import JuliaLean.base.fastmath
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.fastmath
open JuliaLean.base.fastmath JuliaLean.Registry

def fallbackUnaryGroupError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (xs : List Value) (error : Error),
    ops.baseCall op xs = .error error →
      fallbackUnaryGroup ops op xs = .error error

theorem fallbackUnaryGroupError_proven : fallbackUnaryGroupError := by
  unfold fallbackUnaryGroupError
  intros
  simp_all [fallbackUnaryGroup]

def fallbackVariadicGroupError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (xs : List Value) (error : Error),
    ops.baseCall op xs = .error error →
      fallbackVariadicGroup ops op xs = .error error

theorem fallbackVariadicGroupError_proven : fallbackVariadicGroupError := by
  unfold fallbackVariadicGroupError
  intros
  simp_all [fallbackVariadicGroup]

def fallbackPromoteVariadicNumbersError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (xs : List Value) (error : Error),
    ops.promote xs = .error error →
      fallbackPromoteVariadicNumbers ops op xs = .error error

theorem fallbackPromoteVariadicNumbersError_proven : fallbackPromoteVariadicNumbersError := by
  unfold fallbackPromoteVariadicNumbersError
  intros
  simp_all [fallbackPromoteVariadicNumbers, bind, Except.bind]

def fallbackSameTypeNumbersError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (xs : List Value) (error : Error),
    ops.baseCall op xs = .error error →
      fallbackSameTypeNumbers ops op xs = .error error

theorem fallbackSameTypeNumbersError_proven : fallbackSameTypeNumbersError := by
  unfold fallbackSameTypeNumbersError
  intros
  simp_all [fallbackSameTypeNumbers]

def fallbackUnaryBasicError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x : Value) (error : Error),
    ops.baseCall op [x] = .error error →
      fallbackUnaryBasic ops op x = .error error

theorem fallbackUnaryBasicError_proven : fallbackUnaryBasicError := by
  unfold fallbackUnaryBasicError
  intros
  simp_all [fallbackUnaryBasic]

def fallbackBinaryBasicError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.baseCall op [x, y] = .error error →
      fallbackBinaryBasic ops op x y = .error error

theorem fallbackBinaryBasicError_proven : fallbackBinaryBasicError := by
  unfold fallbackBinaryBasicError
  intros
  simp_all [fallbackBinaryBasic]

def fallbackPromoteBinaryNumbersError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.promote [x, y] = .error error →
      fallbackPromoteBinaryNumbers ops op x y = .error error

theorem fallbackPromoteBinaryNumbersError_proven : fallbackPromoteBinaryNumbersError := by
  unfold fallbackPromoteBinaryNumbersError
  intros
  simp_all [fallbackPromoteBinaryNumbers, bind, Except.bind]

def fallbackSameTypeBinaryNumbersError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.baseCall op [x, y] = .error error →
      fallbackSameTypeBinaryNumbers ops op x y = .error error

theorem fallbackSameTypeBinaryNumbersError_proven : fallbackSameTypeBinaryNumbersError := by
  unfold fallbackSameTypeBinaryNumbersError
  intros
  simp_all [fallbackSameTypeBinaryNumbers]

def fallbackFoldBasicError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (a b c : Value) (xs : List Value) (error : Error),
    ops.fastCall op [a, b] = .error error →
      fallbackFoldBasic ops op a b c xs = .error error

theorem fallbackFoldBasicError_proven : fallbackFoldBasicError := by
  unfold fallbackFoldBasicError
  intros
  simp_all [fallbackFoldBasic, bind, Except.bind]

def fallbackPromoteFoldNumbersError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (a b c : Value) (xs : List Value) (error : Error),
    ops.promote (a :: b :: c :: xs) = .error error →
      fallbackPromoteFoldNumbers ops op a b c xs = .error error

theorem fallbackPromoteFoldNumbersError_proven : fallbackPromoteFoldNumbersError := by
  unfold fallbackPromoteFoldNumbersError
  intros
  simp_all [fallbackPromoteFoldNumbers, bind, Except.bind]

def fallbackSameTypeFoldNumbersError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (a b c : Value) (xs : List Value) (error : Error),
    ops.fastCall op [a, b] = .error error →
      fallbackSameTypeFoldNumbers ops op a b c xs = .error error

theorem fallbackSameTypeFoldNumbersError_proven : fallbackSameTypeFoldNumbersError := by
  unfold fallbackSameTypeFoldNumbersError
  intros
  simp_all [fallbackSameTypeFoldNumbers, bind, Except.bind]

def fallbackMathUnaryError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x : Value) (error : Error),
    ops.baseCall op [x] = .error error →
      fallbackMathUnary ops op x = .error error

theorem fallbackMathUnaryError_proven : fallbackMathUnaryError := by
  unfold fallbackMathUnaryError
  intros
  simp_all [fallbackMathUnary]

def fallbackMathBinaryError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.baseCall op [x, y] = .error error →
      fallbackMathBinary ops op x y = .error error

theorem fallbackMathBinaryError_proven : fallbackMathBinaryError := by
  unfold fallbackMathBinaryError
  intros
  simp_all [fallbackMathBinary]

def fallbackPromoteMathBinaryError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.promote [x, y] = .error error →
      fallbackPromoteMathBinary ops op x y = .error error

theorem fallbackPromoteMathBinaryError_proven : fallbackPromoteMathBinaryError := by
  unfold fallbackPromoteMathBinaryError
  intros
  simp_all [fallbackPromoteMathBinary, bind, Except.bind]

def fallbackSameTypeMathBinaryError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.baseCall op [x, y] = .error error →
      fallbackSameTypeMathBinary ops op x y = .error error

theorem fallbackSameTypeMathBinaryError_proven : fallbackSameTypeMathBinaryError := by
  unfold fallbackSameTypeMathBinaryError
  intros
  simp_all [fallbackSameTypeMathBinary]

def fallbackIntegerExponentError : Prop :=
  ∀ {Value Error : Type} (ops : FastFallbackOps Value Error) (op : String)
    (x y : Value) (error : Error),
    ops.baseCall op [x, y] = .error error →
      fallbackIntegerExponent ops op x y = .error error

theorem fallbackIntegerExponentError_proven : fallbackIntegerExponentError := by
  unfold fallbackIntegerExponentError
  intros
  simp_all [fallbackIntegerExponent]

def entries : List Entry := [
  { id := "fastmath-ordinary-variadic-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 250"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:250", status := .proven
    prop := ``fallbackUnaryGroupError, thm := some ``fallbackUnaryGroupError_proven },
  { id := "fastmath-ordinary-binary-variadic-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 258"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:258", status := .proven
    prop := ``fallbackVariadicGroupError, thm := some ``fallbackVariadicGroupError_proven },
  { id := "fastmath-promotion-variadic-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 260"]
    statement := "Promotion failures propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:260", status := .proven
    prop := ``fallbackPromoteVariadicNumbersError, thm := some ``fallbackPromoteVariadicNumbersError_proven },
  { id := "fastmath-same-type-variadic-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 263"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:263", status := .proven
    prop := ``fallbackSameTypeNumbersError, thm := some ``fallbackSameTypeNumbersError_proven },
  { id := "fastmath-ordinary-unary-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 270"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:270", status := .proven
    prop := ``fallbackUnaryBasicError, thm := some ``fallbackUnaryBasicError_proven },
  { id := "fastmath-ordinary-binary-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 272"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:272", status := .proven
    prop := ``fallbackBinaryBasicError, thm := some ``fallbackBinaryBasicError_proven },
  { id := "fastmath-promotion-binary-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 274"]
    statement := "Promotion failures propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:274", status := .proven
    prop := ``fallbackPromoteBinaryNumbersError, thm := some ``fallbackPromoteBinaryNumbersError_proven },
  { id := "fastmath-same-type-binary-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 277"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:277", status := .proven
    prop := ``fallbackSameTypeBinaryNumbersError, thm := some ``fallbackSameTypeBinaryNumbersError_proven },
  { id := "fastmath-fold-first-error-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 281"]
    statement := "Failures in the first binary operation propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:281", status := .proven
    prop := ``fallbackFoldBasicError, thm := some ``fallbackFoldBasicError_proven },
  { id := "fastmath-promotion-fold-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 286"]
    statement := "Promotion failures propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:286", status := .proven
    prop := ``fallbackPromoteFoldNumbersError, thm := some ``fallbackPromoteFoldNumbersError_proven },
  { id := "fastmath-same-type-fold-first-error-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 289"]
    statement := "Failures in the first binary operation propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:289", status := .proven
    prop := ``fallbackSameTypeFoldNumbersError, thm := some ``fallbackSameTypeFoldNumbersError_proven },
  { id := "fastmath-math-unary-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 377"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:377", status := .proven
    prop := ``fallbackMathUnaryError, thm := some ``fallbackMathUnaryError_proven },
  { id := "fastmath-math-binary-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 385"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:385", status := .proven
    prop := ``fallbackMathBinaryError, thm := some ``fallbackMathBinaryError_proven },
  { id := "fastmath-math-promotion-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 387"]
    statement := "Promotion failures propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:387", status := .proven
    prop := ``fallbackPromoteMathBinaryError, thm := some ``fallbackPromoteMathBinaryError_proven },
  { id := "fastmath-math-same-type-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 389"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:389", status := .proven
    prop := ``fallbackSameTypeMathBinaryError, thm := some ``fallbackSameTypeMathBinaryError_proven },
  { id := "fastmath-integer-exponent-errors", juliaFile := "base/fastmath.jl"
    juliaFns := ["generated fallback at line 393"]
    statement := "Ordinary-method exceptions propagate unchanged, without evaluating later calls."
    source := "base/fastmath.jl:393", status := .proven
    prop := ``fallbackIntegerExponentError, thm := some ``fallbackIntegerExponentError_proven }
]

end JuliaLean.Proofs.base.fastmath
