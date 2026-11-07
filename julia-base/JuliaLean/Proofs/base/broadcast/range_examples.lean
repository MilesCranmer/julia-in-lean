import JuliaLean.base.broadcast
import JuliaLean.base.range
import JuliaLean.Proofs.base.range.floating_support

namespace JuliaLean.base.broadcast.RangeExamples
open Sizes
structure URange where
  lo : I64
  hi : I64
  deriving DecidableEq, Repr

def URange.len (r : URange) : Nat := (r.hi.val - r.lo.val + 1).toNat

def URange.elems (r : URange) : List I64 := (List.range r.len).map (fun k : Nat => r.lo + i64 k)


def bcAddVectors (a b : List I64) : R (List I64) :=
  if a.length = b.length then .ok (List.zipWith (· + ·) a b)
  else if a.length = 1 then .ok (b.map (fun y => a.headD (i64 0) + y))
  else if b.length = 1 then .ok (a.map (fun x => x + b.headD (i64 0)))
  else .error .dimensionMismatch

inductive RefT where
  | float
  | twicePrecision
  deriving DecidableEq, Repr

inductive FloatT where
  | f32
  | f64
  deriving DecidableEq, Repr

def colonRefT : FloatT → RefT
  | .f64 => .twicePrecision
  | .f32 => .float

def ldivField : RefT → R RefT
  | .float => .ok .float
  | .twicePrecision => .error .methodError

/--
Julia source: base/broadcast.jl:1236-1236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(\), x::Number, r::StepRangeLen) = StepRangeLen(x\r.ref, x\r.step, length(r), r.offset)
```
-/
def bcLdivRange (fieldT : RefT) : R RefT := do
  let ref ← ldivField fieldT
  let _step ← ldivField fieldT
  pure ref

abbrev U64 := JInt .u64

def roundHalfEven (n d : Int) : Int :=
  let n' := if d < 0 then -n else n
  let d' := if d < 0 then -d else d
  let q := n'.fdiv d'
  let r := n' - q * d'
  if 2 * r < d' then q else if 2 * r > d' then q + 1 else if q % 2 = 0 then q else q + 1

def floatrangeU (startN stepN : Int) (len : U64) : R (Int × U64) :=
  if len.val < 2 ∨ stepN = 0 then .ok (startN, JInt.lit .u64 1)
  else
    let k := roundHalfEven (stepN - startN) stepN
    if k < 0 then .error .inexactError
    else
      let imin : U64 := JInt.wrap .u64 (max 1 (min k len.val))
      let refN : U64 := JInt.wrap .u64 (startN + (imin.val - 1) * stepN)
      if refN.val ≥ 2 ^ 64 - 2 ^ 10 then .error .inexactError
      else .ok (refN.val, imin)

def srlElemU (ref : Int) (offset : U64) (stepN : Int) (i : Nat) : Int :=
  ref + (JInt.wrap .u64 ((i : Int) - offset.val)).val * stepN

/--
Julia source: base/broadcast.jl:1200-1200 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
broadcasted(::DefaultArrayStyle{1}, ::typeof(-), r::AbstractRange, x::Number) = range(first(r) - x, step=step(r), length=length(r))
```
-/
def bcSubFloatElem (a s n : U64) (x : Int) (i : Nat) : R Int := do
  let (ref, off) ← floatrangeU (a.val - x) s.val n
  pure (srlElemU ref off s.val i)

abbrev U8 := JInt .u8

def observeIntegerRange {t : IntTy} (r : JuliaLean.Ranges.Rng) : Jl (List (JInt t)) := do
  let n ← JuliaLean.Ranges.length r
  (List.range n.val.toNat).mapM fun (k : Nat) => do
    let value ← JuliaLean.Ranges.getindex r
      (JuliaLean.Ranges.Num.lit (.bit .i64) ((k : Int) + 1))
    JInt.convert (t.name) t value.val

def observeResultRange {t : IntTy} (r : JuliaLean.Ranges.ResultRng) : Jl (List (JInt t)) := do
  let n ← JuliaLean.Ranges.resultLength r
  (List.range n.val.toNat).mapM fun (k : Nat) => do
    let value ← JuliaLean.Ranges.resultGetindex r
      (JuliaLean.Ranges.Num.lit (.bit .i64) ((k : Int) + 1))
    JInt.convert (t.name) t value.val

def urange8Elems (lo hi : U8) : List U8 :=
  (List.range (hi.val - lo.val + 1).toNat).map (fun k : Nat => JInt.wrap .u8 (lo.val + (k : Int)))


end JuliaLean.base.broadcast.RangeExamples
