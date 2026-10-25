import JuliaLean.Core

/-!
Byte-level model of `ReinterpretArray` element access (`base/reinterpretarray.jl`, master).

An isbits value is its list of bytes (`aligned_sizeof` of them). A parent column
`a.parent[:, tailinds...]` is a list of elements; `a.parent[j, tailinds...]` is its
`j`-th entry (1-based) and throws `BoundsError` outside it. Element types are described by
their `aligned_sizeof` and by `_is_scalar_reinterpret_applicable(T, S)`
(`base/reinterpretarray.jl:466-468`); `issingletontype(T)` is `aligned_sizeof(T) == 0`.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

abbrev Bytes := List UInt8

/-- `a.parent[j, tailinds...]` for a 1-based parent column. -/
def colGet (col : List Bytes) (j : Int) : Jl Bytes :=
  if 1 ≤ j ∧ j ≤ col.length then .ok (col.getD (j - 1).toNat []) else .error .boundsError

/-- `a.parent[j, tailinds...] = s`. -/
def colSet (col : List Bytes) (j : Int) (s : Bytes) : Jl (List Bytes) :=
  if 1 ≤ j ∧ j ≤ col.length then .ok (col.set (j - 1).toNat s) else .error .boundsError

/-- `size(a, 1)` of `reinterpret(T, A)` for `size(A, 1) = len`, `base/reinterpretarray.jl:371-375`:
`div(psize[1]*aligned_sizeof(S), aligned_sizeof(T))` in `Int`. -/
def raSize1 (sS sT : Nat) (len : JInt64) : Jl JInt64 :=
  if sT = 0 then .ok len
  else JInt.div (len * JInt.lit .i64 sS) (JInt.lit .i64 sT)

/-- The first-dimension check of `reinterpret(T, a)`, `base/reinterpretarray.jl:90-99`, for
`dim = length(axes(a, 1))`, `first(axes(a, 1)) == 1` and `aligned_sizeof(S) != aligned_sizeof(T)`. -/
def raNewCheck (sS sT : Nat) (dim : JInt64) : Jl Unit := do
  if sT = 0 then
    if sS = 0 then pure () else throw (.argumentError "singleton")
  else
    let r ← JInt.remInt (dim * JInt.lit .i64 sS) (JInt.lit .i64 sT)
    if r.val = 0 then pure () else throw (.argumentError "non-integral first dimension")

/-- `checkbounds(a, i1, tailinds...)` on the first dimension. -/
def checkFirst (sz1 : JInt64) (i1 : JInt64) : Jl Unit :=
  if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then .ok () else .error .boundsError

/-- Partial-element copy loop of `_getindex_ra`, `base/reinterpretarray.jl:500-519`: reads
`a.parent[ind_start + i]` for `i = 1, 2, ...` (here the remaining column `elems`) until
`aligned_sizeof(T)` bytes are copied. -/
def raGetLoop (sS sT : Nat) : Nat → Nat → List Bytes → Bytes → Jl Bytes
  | sidx, copied, elems, acc =>
    if copied < sT then
      match elems with
      | [] => .error .boundsError
      | s :: rest =>
        let nb := min (sS - sidx) (sT - copied)
        raGetLoop sS sT 0 (copied + nb) rest (acc ++ (s.drop sidx).take nb)
    else .ok acc

/-- `_getindex_ra(a::NonReshapedReinterpretArray, i1, tailinds)`, `base/reinterpretarray.jl:470-522`,
on the parent column `col` with `size(a, 1) = sz1`. -/
def raGet (sS sT : Nat) (scalar : Bool) (col : List Bytes) (sz1 i1 : JInt64) : Jl Bytes := do
  if sT = 0 then
    checkFirst sz1 i1
    pure []
  else if scalar then
    colGet col i1.val
  else
    checkFirst sz1 i1
    let x := (i1 - JInt.lit .i64 1) * JInt.lit .i64 sT
    let indStart ← JInt.div x (JInt.lit .i64 sS)
    let sidx ← JInt.remInt x (JInt.lit .i64 sS)
    if sT % sS = 0 then
      let n := sT / sS
      let parts ← (List.range n).mapM (fun (i : Nat) => colGet col (indStart.val + ((i : Int) + 1)))
      pure parts.flatten
    else if sS % sT = 0 then
      let s ← colGet col (indStart.val + 1)
      pure ((s.drop sidx.val.toNat).take sT)
    else
      raGetLoop sS sT sidx.val.toNat 0 (col.drop indStart.val.toNat) []

/-- `memcpy(dst + off, src, nb)` on byte lists. -/
def overwrite (dst : Bytes) (off : Nat) (src : Bytes) : Bytes :=
  dst.take off ++ src ++ dst.drop (off + src.length)

/-- `_setindex_ra!(a::NonReshapedReinterpretArray, v, i1, tailinds)`,
`base/reinterpretarray.jl:616-683`, on the parent column `col`; returns the new column.
`s = Ref{S}()` starts as the zero element: it is only read after being fully overwritten. -/
def raSet (sS sT : Nat) (scalar : Bool) (col : List Bytes) (sz1 i1 : JInt64) (v : Bytes) :
    Jl (List Bytes) := do
  if sT = 0 then
    checkFirst sz1 i1
    pure col
  else if scalar then
    colSet col i1.val v
  else
    checkFirst sz1 i1
    let x := (i1 - JInt.lit .i64 1) * JInt.lit .i64 sT
    let indStart ← JInt.div x (JInt.lit .i64 sS)
    let sidx ← JInt.remInt x (JInt.lit .i64 sS)
    if sT % sS = 0 then
      let n := sT / sS
      (List.range n).foldlM (fun c (i : Nat) =>
        colSet c (indStart.val + ((i : Int) + 1)) ((v.drop (i * sS)).take sS)) col
    else if sS % sT = 0 then
      let s ← colGet col (indStart.val + 1)
      colSet col (indStart.val + 1) (overwrite s sidx.val.toNat v)
    else
      let sidx := sidx.val.toNat
      let st0 : List Bytes × Bytes × Nat × Int := (col, List.replicate sS 0, 0, 1)
      let st1 ← if sidx ≠ 0 then do
          let (c, _, copied, i) := st0
          let s ← colGet c (indStart.val + i)
          let nb := min (sS - sidx) sT
          let s := overwrite s sidx (v.take nb)
          let c ← colSet c (indStart.val + i) s
          pure (c, s, copied + nb, i + 1)
        else pure st0
      let st2 ← raSetMain sS sT indStart.val v st1.1 st1.2.1 st1.2.2.1 st1.2.2.2 sT
      let (c, _, copied, i) := st2
      if copied < sT then
        let s ← colGet c (indStart.val + i)
        let nb := min sS (sT - copied)
        colSet c (indStart.val + i) (overwrite s 0 ((v.drop copied).take nb))
      else pure c
where
  /-- The main-body loop, `base/reinterpretarray.jl:665-671`; `fuel` bounds the iterations
  (each copies `aligned_sizeof(S) ≥ 1` bytes, so `aligned_sizeof(T)` passes suffice). -/
  raSetMain (sS sT : Nat) (indStart : Int) (v : Bytes) :
      List Bytes → Bytes → Nat → Int → Nat → Jl (List Bytes × Bytes × Nat × Int)
    | c, s, copied, i, 0 => .ok (c, s, copied, i)
    | c, s, copied, i, fuel + 1 =>
      if copied < sT ∧ sT - copied > sS then do
        let nb := min sS (sT - copied)
        let s := overwrite s 0 ((v.drop copied).take nb)
        let c ← colSet c (indStart + i) s
        raSetMain sS sT indStart v c s (copied + nb) (i + 1) fuel
      else .ok (c, s, copied, i)

/-- `size(reinterpret(reshape, T, a))` for `size(a) = dims`, `base/reinterpretarray.jl:128-140`
(constructor checks) and `base/reinterpretarray.jl:376-381` (`size`). -/
def rrSize (sS sT : Nat) (dims : List Nat) : Jl (List Nat) :=
  if sS = sT then .ok dims
  else if sS > sT then
    if sT = 0 then .error (.argumentError "singleton")
    else if sS % sT ≠ 0 then .error (.argumentError "integer multiple")
    else .ok (sS / sT :: dims)
  else
    if sS = 0 then .error (.argumentError "from singleton")
    else if sT % sS ≠ 0 then .error (.argumentError "integer multiple")
    else match dims with
      | [] => .error (.argumentError "zero-dimensional")
      | d1 :: rest => if d1 = sT / sS then .ok rest else .error (.argumentError "axes(a, 1)")

/-- `reinterpret(reshape, T, b)` where `b = reinterpret(reshape, S, a)` and `a` has element type `U`,
with `T`, `S`, `U` distinct: `base/reinterpretarray.jl:191` forwards to
`reinterpret(reshape, T, a)`. Returns the resulting size. -/
def rrNestedSize (sU sS sT : Nat) (dims : List Nat) : Jl (List Nat) := do
  let _ ← rrSize sU sS dims
  rrSize sU sT dims

end JuliaLean.ReinterpretArrays
