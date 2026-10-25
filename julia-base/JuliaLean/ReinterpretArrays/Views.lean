import JuliaLean.Core

/-!
Index arithmetic of fast linear `SubArray`s (`base/subarray.jl`) and of `PermutedDimsArray`
(`base/permuteddimsarray.jl`, `base/combinatorics.jl`), master.
-/

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- `compute_linindex(f, s, IP, I)`, `base/subarray.jl:491-501`, for 1-based parent axes of lengths
`ips` (padded with `OneTo(1)` by `fill_to_length`, line 488) and indices whose `first` are `is`:
`Δi = first(I[1]) - first(IP[1])`. -/
def computeLinindex (f s : JInt64) : List JInt64 → List JInt64 → JInt64
  | _, [] => f
  | _, [i] => f + (i - JInt.lit .i64 1) * s
  | ips, i :: is => computeLinindex (f + (i - JInt.lit .i64 1) * s) (s * ips.headD (JInt.lit .i64 1)) ips.tail is

/-- `(offset1, stride1)` of `view(A, r, c2, ..., ck)` for a range `r = start:step:stop` and integer
scalars `cs`, `base/subarray.jl:34-44`: `compute_stride1` (lines 448-454) is `1 * step(r)`;
`compute_offset1` is `first(r) - stride1 * first(axes1(r))` for a vector parent (line 471) and
`compute_linindex(parent, I) - stride1 * first(axes1(r))` otherwise (lines 478-483, 486-490), with
`first(axes1(r)) == 1` and `first(LinearIndices(parent)) == 1`. -/
def viewLayout (sizes : List JInt64) (start step : JInt64) (cs : List JInt64) : JInt64 × JInt64 :=
  let stride1 := JInt.lit .i64 1 * step
  match cs with
  | [] => (start - stride1 * JInt.lit .i64 1, stride1)
  | _ => (computeLinindex (JInt.lit .i64 1) (JInt.lit .i64 1) sizes (start :: cs) - stride1 * JInt.lit .i64 1, stride1)

/-- `_reindexlinear(V, i) = V.offset1 + V.stride1*i`, `base/subarray.jl:327`: the parent linear index
read by `V[i]` (`base/subarray.jl:330-344`). -/
def viewParentIndex (layout : JInt64 × JInt64) (i : JInt64) : JInt64 := layout.1 + layout.2 * i

/-- `invperm(a::AbstractVector)`, `base/combinatorics.jl:286-296`. -/
def invperm (a : List Int) : Jl (List Int) :=
  let n := a.length
  (a.zipIdx 1).foldlM (fun (b : List Int) (p : Int × Nat) =>
    let (j, i) := p
    if 1 ≤ j ∧ j ≤ n ∧ b.getD (j - 1).toNat 0 = 0 then .ok (b.set (j - 1).toNat i)
    else .error (.argumentError "argument is not a permutation")) (List.replicate n 0)

/-- `isperm(p)`, `base/combinatorics.jl:59-101`: every value `1:n` occurs exactly once. -/
def isperm (p : List Int) : Bool :=
  (List.range p.length).all (fun k => p.count ((k : Int) + 1) = 1)

/-- `genperm(I, perm)`, `base/permuteddimsarray.jl:87`: `ntuple(d -> I[perm[d]], N)`. -/
def genperm {α : Type} [Inhabited α] (I : List α) (perm : List Int) : List α :=
  perm.map (fun p => I.getD (p - 1).toNat default)

/-- `PermutedDimsArray(data, perm)` for `ndims(data) == N`, `base/permuteddimsarray.jl:42-46` and the
inner constructor's checks, lines 12-17; returns `iperm`. -/
def pdaNew (perm : List Int) (N : Nat) : Jl (List Int) := do
  if perm.length ≠ N then throw (.argumentError "not a valid permutation")
  let iperm ← invperm perm
  if !isperm perm then throw (.argumentError "not a valid permutation")
  if !((List.range N).all (fun d => iperm.getD ((perm.getD d 0) - 1).toNat 0 = (d : Int) + 1)) then
    throw (.argumentError "must be inverses")
  pure iperm

end JuliaLean.ReinterpretArrays
