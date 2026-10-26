import JuliaLean.IteratorsCov.Base

/-!
# `Iterators.countfrom` (base/iterators.jl:743-774)

Numbers are `Bool`, `Int64` and `Char` (a non-`Number` with `+(::Char, ::Integer)`).
`Bool + Bool` is an `Int` (base/bool.jl: `+(x::Bool, y::Bool) = Int(x) + Int(y)`),
`Bool + Int` promotes to `Int`, `Int + Int` wraps, and `Char + Int` is the
`Char` with the shifted code point (base/char.jl), which throws for a negative
or too large code point.
-/

namespace JuliaLean.IteratorsCov

open JuliaLean

/-- Numbers and characters of the model. -/
inductive Num where
  | bool (b : Bool)
  | int (x : JInt64)
  | chr (c : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Their types (`Bool`, `Int64`, `Char`). -/
inductive NTy where
  | bool
  | int
  | chr
  deriving Repr, DecidableEq, Inhabited

def Num.ty : Num → NTy
  | .bool _ => .bool
  | .int _ => .int
  | .chr _ => .chr

/-- `x isa Number`. -/
def Num.isNumber : Num → Bool
  | .chr _ => false
  | _ => true

/-- `Int(x)` of a `Bool`. -/
def boolInt (b : Bool) : JInt64 := if b then i64 1 else i64 0

/-- `x + y`. -/
def numAdd : Num → Num → R Num
  | .bool a, .bool b => .ok (.int (boolInt a + boolInt b))
  | .bool a, .int y => .ok (.int (boolInt a + y))
  | .int x, .bool b => .ok (.int (x + boolInt b))
  | .int x, .int y => .ok (.int (x + y))
  | .chr c, .int y =>
    if 0 ≤ (c : Int) + y.val ∧ (c : Int) + y.val < 0x110000 then .ok (.chr ((c : Int) + y.val).toNat)
    else jthrow (.argumentError "invalid code point")
  | _, _ => jthrow (.methodError "+")

/-- `oneunit(x)`. -/
def oneunit : Num → R Num
  | .bool _ => .ok (.bool true)
  | .int _ => .ok (.int (i64 1))
  | .chr _ => jthrow (.methodError "oneunit")

/-- `convert(T, x)` into the field type `T` of a `Count{T,S}`. -/
def numConvert : NTy → Num → R Num
  | .bool, .bool b => .ok (.bool b)
  | .bool, .int x =>
    if x.val = 0 then .ok (.bool false) else if x.val = 1 then .ok (.bool true)
    else jthrow (.inexactError "Bool")
  | .int, .bool b => .ok (.int (boolInt b))
  | .int, .int x => .ok (.int x)
  | .chr, .chr c => .ok (.chr c)
  | _, _ => jthrow (.methodError "convert")

/-- `promote(x, y)` of two numbers (`Bool` promotes to `Int`). -/
def numPromote : Num → Num → R (Num × Num)
  | .bool a, .int y => .ok (.int (boolInt a), .int y)
  | .int x, .bool b => .ok (.int x, .int (boolInt b))
  | x, y => .ok (x, y)

/-- An `Iterators.Count{T,S}` object: its type parameter `T` and its fields. -/
structure Count where
  T : NTy
  start : Num
  step : Num
  deriving Repr

/-- The default constructor `Count(start, step)`: `T = typeof(start)`. -/
def mkCount (start step : Num) : Count := ⟨start.ty, start, step⟩

/-- The `countfrom` methods, base/iterators.jl:764-767:
`countfrom(start::T, step::S) = Count{typeof(start+step),S}(start, step)` for
non-numbers (764), `countfrom(start::Number, step::Number) =
Count(promote(start, step)...)` (765). -/
def countfrom2 (start step : Num) : R Count :=
  if start.isNumber && step.isNumber then do
    let (a, b) ← numPromote start step
    pure (mkCount a b)
  else do
    let t ← numAdd start step
    let s ← numConvert t.ty start
    pure ⟨t.ty, s, step⟩

/-- `countfrom(start) = Count(start, oneunit(start))`, base/iterators.jl:766. -/
def countfrom1 (start : Num) : R Count := do pure (mkCount start (← oneunit start))

/-- `countfrom() = Count(1, 1)`, base/iterators.jl:767. -/
def countfrom0 : Count := mkCount (.int (i64 1)) (.int (i64 1))

/-- `eltype(::Type{<:Count{T}}) = T`, base/iterators.jl:770. -/
def Count.eltype (c : Count) : NTy := c.T

/-- `iterate(it::Count, state=it.start) = (state, state + it.step)`,
base/iterators.jl:772: the first `k` elements and the state after them. -/
def countRun (c : Count) : Nat → Num → R (List Num)
  | 0, _ => .ok []
  | k + 1, st => do
    let nx ← numAdd st c.step
    pure (st :: (← countRun c k nx))

/-- The first `k` elements of `countfrom(...)`. -/
def countPrefix (c : Count) (k : Nat) : R (List Num) := countRun c k c.start

/-- Every element `countfrom(start, step)`, `countfrom(start)` and
`countfrom()` yield is an `eltype` of the iterator (`eltype(::Count{T}) = T`). -/
def CountfromEltype : Prop :=
  ∀ (start step : Num) (k : Nat),
    (∀ c xs, countfrom2 start step = .ok c → countPrefix c k = .ok xs → ∀ x ∈ xs, x.ty = c.eltype) ∧
    (∀ c xs, countfrom1 start = .ok c → countPrefix c k = .ok xs → ∀ x ∈ xs, x.ty = c.eltype) ∧
    (∀ xs, countPrefix countfrom0 k = .ok xs → ∀ x ∈ xs, x.ty = countfrom0.eltype)

/-- `countfrom(true)` is a `Count{Bool,Bool}`, but its second element is
`true + true == 2`. -/
theorem countfromEltype_refuted : ¬ CountfromEltype := by
  intro h
  have := (h (.bool true) (.bool true) 2).2.1 ⟨.bool, .bool true, .bool true⟩
    [.bool true, .int (i64 2)] rfl rfl (.int (i64 2)) (by simp)
  exact absurd this (by decide)

/-- `s, s + d, s + d + d, ...` with `Int` wraparound: the first `k` terms. -/
def addChain (d : JInt64) : Nat → JInt64 → List Num
  | 0, _ => []
  | k + 1, s => .int s :: addChain d k (s + d)

/-- `countfrom(start, step)` and `countfrom(start)` of `Int`s, and `countfrom()`,
count forever (`IteratorSize` `IsInfinite`, base/iterators.jl:774): every
prefix exists and consists of `start`, `start + step`, `start + 2step`, ...
with `Int` wraparound, `Int`s as `eltype` says (base/iterators.jl:751). -/
def CountfromInts : Prop :=
  ∀ (s d : JInt64) (k : Nat),
    (∃ c, countfrom2 (.int s) (.int d) = .ok c ∧ countPrefix c k = .ok (addChain d k s) ∧
      c.eltype = .int) ∧
    (∃ c, countfrom1 (.int s) = .ok c ∧ countPrefix c k = .ok (addChain (i64 1) k s) ∧
      c.eltype = .int) ∧
    countPrefix countfrom0 k = .ok (addChain (i64 1) k (i64 1))

theorem countRun_int (T : NTy) (s0 d : JInt64) : ∀ (k : Nat) (s : JInt64),
    countRun ⟨T, .int s0, .int d⟩ k (.int s) = .ok (addChain d k s) := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    simp only [countRun, numAdd, bind, Except.bind, pure, Except.pure, ih] <;> rfl

theorem countfromInts : CountfromInts := by
  intro s d k
  refine ⟨⟨⟨.int, .int s, .int d⟩, rfl, countRun_int _ _ _ _ _, rfl⟩,
    ⟨⟨.int, .int s, .int (i64 1)⟩, rfl, countRun_int _ _ _ _ _, rfl⟩, countRun_int _ _ _ _ _⟩

end JuliaLean.IteratorsCov
