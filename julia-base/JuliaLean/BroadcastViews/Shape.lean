import JuliaLean.Core

/-!
Broadcast shape combination, `base/broadcast.jl` at master `bbfa0ce4150`.

* A size tuple of `Int`s is a `List I64`; an axis tuple is modelled only through the
  `_bcs1(::Integer, ::AbstractUnitRange)` method (`Ax`).
* Exceptions are `Err`; message texts are not modelled.
-/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- Julia exception types thrown by the modelled functions. -/
inductive Err where
  | dimensionMismatch
  | boundsError
  | inexactError
  | methodError
  | argumentError
  deriving Repr, DecidableEq, Inhabited

/-- A Julia call that may throw. -/
abbrev R (α : Type) := Except Err α

deriving instance DecidableEq for Except

/-- Julia `Int`. -/
abbrev I64 := JInt .i64

/-- An `Int` literal. -/
def i64 (x : Int) : I64 := JInt.lit .i64 x

/-- `_bcs1(a::Integer, b::Integer)`, `base/broadcast.jl:531`:
`a == 1 ? b : (b == 1 ? a : (a == b ? a : throw(DimensionMismatch(...))))`. -/
def bcs1 (a b : I64) : R I64 :=
  if a.val = 1 then .ok b
  else if b.val = 1 then .ok a
  else if a.val = b.val then .ok a
  else .error .dimensionMismatch

/-- `_bcs(shape, newshape)`, `base/broadcast.jl:524-529`: combine two size tuples dimension by
dimension, copying the trailing dimensions of the longer one. -/
def bcs : List I64 → List I64 → R (List I64)
  | [], [] => .ok []
  | [], b :: bs => do let r ← bcs [] bs; pure (b :: r)
  | a :: as, [] => do let r ← bcs as []; pure (a :: r)
  | a :: as, b :: bs => do let x ← bcs1 a b; let r ← bcs as bs; pure (x :: r)

/-- `broadcast_shape(shape, shapes...)`, `base/broadcast.jl:521-522`:
`broadcast_shape(shape, shape1, shapes...) = broadcast_shape(_bcs(shape, shape1), shapes...)`. -/
def broadcastShape : List I64 → List (List I64) → R (List I64)
  | s, [] => .ok s
  | s, t :: ts => do let u ← bcs s t; broadcastShape u ts

/-- The extent of dimension `d` (0-based) of a size tuple; dimensions past its end have extent 1. -/
def ext (s : List I64) (d : Nat) : Int :=
  match s[d]? with
  | some x => x.val
  | none => 1

/-- Largest number of dimensions among the size tuples. -/
def maxLen (shapes : List (List I64)) : Nat := shapes.foldr (fun s m => max s.length m) 0

/-! ## Axes mixed with integer sizes

`_bcs1(a::Integer, b)` for an axis `b` (line 532) and `_bcs1(a, b::Integer) = _bcs1(b, a)`
(line 533). A one-based axis `OneTo(n)`/`1:n` is `Ax.oneTo n`; `first(b) == 1`, `last(b) == n`. -/

/-- A one-based `AbstractUnitRange{Int}` axis `1:n`. -/
structure Ax where
  n : I64
  deriving DecidableEq, Repr

/-- An entry of a shape tuple: an integer size or an axis. -/
inductive Dim where
  | size (n : I64)
  | axis (a : Ax)
  deriving DecidableEq, Repr

/-- The length of a shape entry. -/
def Dim.len : Dim → Int
  | .size n => n.val
  | .axis a => a.n.val

/-- `_bcs1` on one integer size and one axis, `base/broadcast.jl:532-533`:
`a == 1 ? b : (first(b) == 1 && last(b) == a ? b : throw(DimensionMismatch(...)))`. -/
def bcs1Mixed : Dim → Dim → R Dim
  | .size a, .axis b => if a.val = 1 then .ok (.axis b) else if b.n.val = a.val then .ok (.axis b) else .error .dimensionMismatch
  | .axis b, .size a => if a.val = 1 then .ok (.axis b) else if b.n.val = a.val then .ok (.axis b) else .error .dimensionMismatch
  | .size a, .size b => (bcs1 a b).map Dim.size
  | .axis a, .axis b =>
    -- `_bcs1(a, b) = _bcsm(b, a) ? axistype(b, a) : _bcsm(a, b) ? axistype(a, b) : throw(...)`,
    -- `_bcsm(a, b) = a == b || length(b) == 1` (lines 534-536); one-based axes are equal iff their lengths are.
    if b.n.val = a.n.val ∨ a.n.val = 1 then .ok (.axis b)
    else if a.n.val = b.n.val ∨ b.n.val = 1 then .ok (.axis a)
    else .error .dimensionMismatch

end JuliaLean.BroadcastViews
