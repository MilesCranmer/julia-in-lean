import JuliaLean.AbstractArraySpecs.CopyRows
import JuliaLean.AbstractArraySpecs.Props

/-!
Spec-first properties of the `copyto!`/`copy!`/`copyto_axcheck!` methods modelled in
`CopyRows.lean`. The reference side uses only element lists (column-major order) and
the manual's linear-index positions `refLinPos`.

Sources: copyto! docstring (base/abstractarray.jl:1042-1071: "Copy all elements from
collection src to array dest, whose length must be greater than or equal to the length n
of src. The first n elements of dest are overwritten, the other elements are left
untouched."), the five-argument docstring (base/array.jl:282-287: "Copy n elements from
collection src starting at the linear index soffs, to array dest starting at the index
doffs. Return dest."), and the copy! docstring (base/abstractarray.jl:898-918).
-/

namespace JuliaLean.AbstractArraySpecs

/-- `xs` written over `d` from position `p` on. -/
def spliceAt {α : Type} (d xs : List α) (p : Nat) : List α :=
  d.take p ++ xs ++ d.drop (p + xs.length)

/-- The position of linear index `k` of `A` when `n` elements starting there fit in `A`. -/
def fitsAt {α : Type} (A : Arr α) (k : I64) (n : Nat) : Option Nat :=
  match refLinPos A k.val with
  | some p => if p + n ≤ A.data.length then some p else none
  | none => none

/-- `copyto!(dest, src)` with an iterable `src` (any collection): the first
`length(src)` elements of `dest` become `src`'s elements and the rest are untouched; a
`dest` with fewer elements is an error. -/
def CopytoIterPrefix : Prop :=
  ∀ {α : Type} (dest : Arr α) (src : List α), dest.WF →
    (src.length ≤ dest.data.length → copytoIter dest src = .ok { dest with data := spliceAt dest.data src 0 }) ∧
    (dest.data.length < src.length → ∃ e, copytoIter dest src = .error e)

/-- `copyto!(dest, dstart, src)`: `src`'s elements are written to `dest` at the
consecutive linear indices starting at `dstart`; nothing happens for an empty `src`;
`BoundsError` when they do not all lie in `dest`. Holds whether or not `src` has a
length. -/
def CopytoIterAtSpec : Prop :=
  ∀ {α : Type} (hasLen : Bool) (dest : Arr α) (dstart : I64) (src : List α), dest.WF →
    (src.length : Int) ≤ tmax →
    copytoIterAt hasLen dest dstart src =
      if src = [] then .ok dest
      else match fitsAt dest dstart src.length with
        | some p => .ok { dest with data := spliceAt dest.data src p }
        | none => .error .boundsError

/-- `copyto!(dest, dstart, src, sstart)`: the elements of `src` from position `sstart`
(1-based) on are written to `dest` from linear index `dstart` on; a start outside
`1:length(src)` is an error, and elements that do not fit raise `BoundsError`. -/
def CopytoIterFromSpec : Prop :=
  ∀ {α : Type} (dest : Arr α) (dstart : I64) (src : List α) (sstart : I64), dest.WF →
    ((sstart.val < 1 ∨ (src.length : Int) < sstart.val) → ∃ e, copytoIterFrom dest dstart src sstart = .error e) ∧
    (1 ≤ sstart.val → sstart.val ≤ src.length →
      copytoIterFrom dest dstart src sstart =
        match fitsAt dest dstart (src.drop (sstart.val - 1).toNat).length with
        | some p => .ok { dest with data := spliceAt dest.data (src.drop (sstart.val - 1).toNat) p }
        | none => .error .boundsError)

/-- `copyto!(dest, dstart, src, sstart, n)` with an iterable `src`: `n` elements of `src`
from position `sstart` on are written to `dest` from linear index `dstart` on; `n == 0`
does nothing; any other request that does not fit `src` or `dest` (or a negative `n`) is
an error. -/
def CopytoIterNSpec : Prop :=
  ∀ {α : Type} (dest : Arr α) (dstart : I64) (src : List α) (sstart n : I64), dest.WF →
    (n.val = 0 → copytoIterN dest dstart src sstart n = .ok dest) ∧
    (0 < n.val → 1 ≤ sstart.val → sstart.val - 1 + n.val ≤ src.length →
      ∀ p, fitsAt dest dstart n.val.toNat = some p →
        copytoIterN dest dstart src sstart n =
          .ok { dest with data := spliceAt dest.data ((src.drop (sstart.val - 1).toNat).take n.val.toNat) p }) ∧
    (n.val ≠ 0 → ¬ (0 < n.val ∧ 1 ≤ sstart.val ∧ sstart.val - 1 + n.val ≤ src.length ∧
        (fitsAt dest dstart n.val.toNat).isSome) →
      ∃ e, copytoIterN dest dstart src sstart n = .error e)

/-- `copyto!(dest, dstart, src, sstart, n)` for arrays: `n` elements of `src` from linear
index `sstart` on go to `dest` from linear index `dstart` on; `n == 0` does nothing, a
negative `n` is an error, and a range outside either array raises `BoundsError`; for any
`mightalias` outcome. -/
def CopytoNSpec : Prop :=
  ∀ {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α) (sstart n : I64),
    dest.WF → src.WF →
    (n.val = 0 → copytoN aliased dest dstart src sstart n = .ok dest) ∧
    (n.val < 0 → ∃ e, copytoN aliased dest dstart src sstart n = .error e) ∧
    (0 < n.val → copytoN aliased dest dstart src sstart n =
      match fitsAt dest dstart n.val.toNat, fitsAt src sstart n.val.toNat with
      | some p, some q => .ok { dest with data := spliceAt dest.data ((src.data.drop q).take n.val.toNat) p }
      | _, _ => .error .boundsError)

/-- `copyto!(dest, dstart, src)` for arrays: all of `src` goes to `dest` from linear index
`dstart` on; an empty `src` does nothing; `BoundsError` when it does not fit. -/
def CopytoAtSpec : Prop :=
  ∀ {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α), dest.WF → src.WF →
    copytoAt aliased dest dstart src =
      if src.data = [] then .ok dest
      else match fitsAt dest dstart src.data.length with
        | some p => .ok { dest with data := spliceAt dest.data src.data p }
        | none => .error .boundsError

/-- `copyto!(dest, dstart, src, sstart)` for arrays: the elements of `src` from linear
index `sstart` to the end go to `dest` from linear index `dstart` on; `BoundsError` when
`sstart` is not a linear index of `src` or the elements do not fit. -/
def CopytoFromSpec : Prop :=
  ∀ {α : Type} (aliased : Bool) (dest : Arr α) (dstart : I64) (src : Arr α) (sstart : I64),
    dest.WF → src.WF →
    copytoFrom aliased dest dstart src sstart =
      match refLinPos src sstart.val with
      | none => .error .boundsError
      | some q => match fitsAt dest dstart (src.data.length - q) with
        | some p => .ok { dest with data := spliceAt dest.data (src.data.drop q) p }
        | none => .error .boundsError

/-- Index `i` lies in axis `r`. -/
def inAxis (r : Ax) (i : I64) : Prop := r.lo.val ≤ i.val ∧ i.val ≤ r.hi.val

instance (r : Ax) (i : I64) : Decidable (inAxis r i) := by unfold inAxis; infer_instance

/-- Axis `d` (0-based) of a vector or matrix; a vector's second axis is `1:1`. -/
def axisVM {α : Type} (A : Arr α) (d : Nat) : Ax := (A.axes[d]?).getD (oneTo (i64 1))

/-- Every element of both ranges is an index of the matching axis. -/
def blockInBounds {α : Type} (A : Arr α) (ir jr : Rg) : Prop :=
  (∀ x ∈ ir.elems, inAxis (axisVM A 0) x) ∧ (∀ y ∈ jr.elems, inAxis (axisVM A 1) y)

instance {α : Type} (A : Arr α) (ir jr : Rg) : Decidable (blockInBounds A ir jr) := by
  unfold blockInBounds; infer_instance

/-- The assignments `B[ir_dest[p], jr_dest[q]] = A[ir_src[p], jr_src[q]]` for the
paired elements of the ranges, in column-major order of `(p, q)`, on the reference
element positions. -/
def blockRef {α : Type} (B A : Arr α) (ird jrd irs jrs : Rg) : R (Arr α) :=
  (jrd.elems.zip jrs.elems).foldlM (fun D jq =>
    (ird.elems.zip irs.elems).foldlM (fun D ip => do
      let v ← refGet A [ip.2, jq.2]
      refSet D v [ip.1, jq.1]) D) B

/-- `copyto!(B, ir_dest, jr_dest, A, ir_src, jr_src)` copies the block `A[ir_src, jr_src]`
to `B[ir_dest, jr_dest]`: `ArgumentError` when the range lengths differ, `BoundsError`
when a range leaves its axis, otherwise the elementwise assignments in column order, for
vectors and matrices of either style with any axes and any `mightalias` outcome. -/
def CopytoBlockSpec : Prop :=
  ∀ {α : Type} (aliased : Bool) (B A : Arr α) (ird jrd irs jrs : Rg),
    B.WF → A.WF → B.axes.length ≤ 2 → A.axes.length ≤ 2 → 1 ≤ B.axes.length → 1 ≤ A.axes.length →
    ird.WF → jrd.WF → irs.WF → jrs.WF →
    copytoBlock aliased B ird jrd A irs jrs =
      if ird.len ≠ irs.len ∨ jrd.len ≠ jrs.len then .error .argumentError
      else if blockInBounds B ird jrd ∧ blockInBounds A irs jrs then blockRef B A ird jrd irs jrs
      else .error .boundsError

/-- Two axis tuples have the same indices in every dimension. -/
def sameAxes : List Ax → List Ax → Prop
  | [], [] => True
  | r :: rs, s :: ss => ((r.len = 0 ∧ s.len = 0) ∨ (r.lo = s.lo ∧ r.hi = s.hi)) ∧ sameAxes rs ss
  | _, _ => False

instance sameAxesDec : (a b : List Ax) → Decidable (sameAxes a b)
  | [], [] => isTrue trivial
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id
  | r :: rs, s :: ss =>
    have := sameAxesDec rs ss
    if h : ((r.len = 0 ∧ s.len = 0) ∨ (r.lo = s.lo ∧ r.hi = s.hi)) ∧ sameAxes rs ss then isTrue h else isFalse h

/-- `_checkaxs(axd, axs)` returns `true` when the axes agree (same indices in every
dimension) and throws `DimensionMismatch` ("axes must agree") otherwise. -/
def CheckaxsSpec : Prop :=
  ∀ (axd axs : List Ax), (∀ r ∈ axd, r.WF) → (∀ r ∈ axs, r.WF) →
    checkaxs axd axs = if sameAxes axd axs then .ok true else .error .dimensionMismatch

/-- `copyto_axcheck!(dest, src)` copies `src` into `dest` when their axes agree (so `dest`
then holds exactly `src`'s elements) and throws `DimensionMismatch` otherwise. -/
def CopytoAxcheckSpec : Prop :=
  ∀ {α : Type} (destBit aliased : Bool) (dest src : Arr α), dest.WF → src.WF →
    (destBit = true → dest.style = .linear ∧ ∀ r ∈ dest.axes, r.kind = .oneTo) →
    copytoAxcheck destBit aliased dest src =
      if sameAxes dest.axes src.axes then .ok { dest with data := src.data } else .error .dimensionMismatch

/-- `copy!(dst, src)` for arrays: "multidimensional arrays must have equal axes"
(`ArgumentError` otherwise), and then `dst` holds exactly `src`'s elements
(copy! docstring: "dst == src should hold after the call"). -/
def CopyBangArraySpec : Prop :=
  ∀ {α : Type} (destBit aliased : Bool) (dst src : Arr α), dst.WF → src.WF →
    (destBit = true → dst.style = .linear ∧ ∀ r ∈ dst.axes, r.kind = .oneTo) →
    copyBangA destBit aliased dst src =
      if sameAxes dst.axes src.axes then .ok { dst with data := src.data } else .error .argumentError

/-- The `resize!(a, n)` contract (base/array.jl, resize! docstring: "Resize a to contain
n elements. If n is smaller than the current collection length, the first n elements will
be retained."), for a vector type keeping its first index, style and axis kind. -/
def ResizeContract {α : Type} (resize : Arr α → I64 → R (Arr α)) : Prop :=
  ∀ (a : Arr α) (n : I64), a.WF → a.axes.length = 1 → 0 ≤ n.val →
    ∃ a', resize a n = .ok a' ∧ a'.WF ∧ a'.axes.length = 1 ∧ a'.data.length = n.val.toNat ∧
      (linearAxis a').lo = (linearAxis a).lo ∧ a'.style = a.style ∧
      a'.axes.map (·.kind) = a.axes.map (·.kind)

/-- `copy!(dst, src)` for vectors: "they must have equal offset" (`ArgumentError`
otherwise); then `dst` is resized to `length(src)` if needed and holds exactly `src`'s
elements, with the same first index ("dst == src should hold after the call"). -/
def CopyBangVectorSpec : Prop :=
  ∀ {α : Type} (resize : Arr α → I64 → R (Arr α)) (destBit aliased : Bool) (dst src : Arr α),
    ResizeContract resize → dst.WF → src.WF → dst.axes.length = 1 → src.axes.length = 1 →
    (destBit = true → dst.style = .linear ∧ ∀ r ∈ dst.axes, r.kind = .oneTo) →
    ((linearAxis dst).lo ≠ (linearAxis src).lo → ∃ e, copyBangV resize destBit aliased dst src = .error e) ∧
    ((linearAxis dst).lo = (linearAxis src).lo → ∃ r, copyBangV resize destBit aliased dst src = .ok r ∧
      r.data = src.data ∧ (linearAxis r).lo = (linearAxis src).lo)

end JuliaLean.AbstractArraySpecs
