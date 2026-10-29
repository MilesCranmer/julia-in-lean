import JuliaLean.AbstractArraySpecs.Cat

/-!
The generic concatenation kernel at Julia commit
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`, abstracting the dynamically
selected `similar`, range assignment, view and fill methods as operations. The
operations return the actual destination state and may throw. Array arguments
carry their own element type, including when the array is empty.
-/

namespace JuliaLean.AbstractArraySpecs.CatTyped

structure Universe where
  Ty : Type
  Val : Ty → Type

inductive Item (U : Universe) where
  | scalar (t : U.Ty) (value : U.Val t)
  | array (t : U.Ty) (value : Arr (U.Val t))

def eltype {U : Universe} : Item U → U.Ty
  | .scalar t _ => t
  | .array t _ => t

def sizeAll {U : Universe} : Item U → List I64
  | .scalar _ _ => [i64 1]
  | .array _ a => sizeA a

def sizeDim {U : Universe} : Item U → Nat → I64
  | .scalar _ _, _ => i64 1
  | .array _ a, d => ((sizeA a)[d]?).getD (i64 1)

def indices {U : Universe} : Item U → Nat → Ax
  | .scalar _ _, _ => oneTo (i64 1)
  | .array _ a, d => (a.axes[d]?).getD (oneTo (i64 1))

def shapeFrom {U : Universe} (dims : List Bool) : List I64 → List (Item U) → R (List I64)
  | s, [] => .ok s
  | s, x :: xs => do
      let s ← cshp' dims s (sizeAll x)
      shapeFrom dims s xs

def shape {U : Universe} (dims : List Bool) : List (Item U) → R (List I64)
  | [] => .ok (List.replicate dims.length (i64 0))
  | x :: xs => do
      let s ← cshp' dims [] (sizeAll x)
      shapeFrom dims s xs

/-- Operations dispatched on the source and destination array types. `Dest t`
contains the state of an array whose declared element type is `t`. `viewFill`
models `fill!(view(A, inds...), x)` as one operation, so its bounds and
conversion errors occur in the implementation's own order. `assign` models
`A[inds...] = x`. -/
structure Ops (U : Universe) where
  Dest : U.Ty → Type
  promote : List U.Ty → R U.Ty
  convert : (s t : U.Ty) → U.Val s → R (U.Val t)
  zero : (t : U.Ty) → R (U.Val t)
  similar : (t : U.Ty) → Item U → List I64 → R (Dest t)
  axes : {t : U.Ty} → Dest t → List Ax
  read : {t : U.Ty} → Dest t → List I64 → R (U.Val t)
  write : {s t : U.Ty} → Dest t → List I64 → U.Val s → R (Dest t)
  fillAll : {t : U.Ty} → Dest t → U.Val t → R (Dest t)
  viewFill : {s t : U.Ty} → Dest t → List (I64 × I64) → U.Val s → R (Dest t)
  assign : {s t : U.Ty} → Dest t → List (I64 × I64) → Arr (U.Val s) → R (Dest t)

def copyOrFill {U : Universe} (ops : Ops U) {t : U.Ty} (a : ops.Dest t)
    (inds : List (I64 × I64)) : Item U → R (ops.Dest t)
  | .scalar _ x => ops.viewFill a inds x
  | .array _ x => ops.assign a inds x

def offset1 {U : Universe} (ops : Ops U) {t : U.Ty} (a : ops.Dest t)
    (shape : List I64) (catdims : List Bool) (offsets : List I64) (x : Item U) :
    R (ops.Dest t × List I64) := do
  let inds := (List.range offsets.length).map (fun i =>
    if catdims.getD i false then
      let r := indices x i
      (offsets.getD i (i64 0) + r.lo, offsets.getD i (i64 0) + r.hi)
    else (i64 1, shape.getD i (i64 0)))
  let a ← copyOrFill ops a inds x
  let next := (List.range offsets.length).map (fun i =>
    if catdims.getD i false then offsets.getD i (i64 0) + sizeDim x i
    else offsets.getD i (i64 0))
  .ok (a, next)

def offset {U : Universe} (ops : Ops U) {t : U.Ty} (shape : List I64)
    (catdims : List Bool) : ops.Dest t → List I64 → List (Item U) → R (ops.Dest t)
  | a, _, [] => .ok a
  | a, offsets, x :: xs => do
      let (a, offsets) ← offset1 ops a shape catdims offsets x
      offset ops shape catdims a offsets xs

def catT {U : Universe} (ops : Ops U) (t : U.Ty) (dims : List Int)
    (xs : List (Item U)) : R (ops.Dest t) := do
  let catdims ← dims2cat dims
  let shape ← shape catdims xs
  let a ← match xs with
    | [] => .error .boundsError
    | x :: _ => ops.similar t x shape
  let a ← if (catdims.filter id).length > 1 then do
    let z ← ops.zero t
    ops.fillAll a z
  else .ok a
  offset ops shape catdims a (List.replicate shape.length (i64 0)) xs

/-- The result retains the selected type together with its dependent destination. -/
def catPromote {U : Universe} (ops : Ops U) (dims : List Int) (xs : List (Item U)) :
    R (Sigma ops.Dest) := do
  let t ← ops.promote (xs.map eltype)
  let a ← catT ops t dims xs
  .ok ⟨t, a⟩

/-- Empty arrays still contribute their declared element type to promotion. -/
theorem empty_array_eltype {U : Universe} (t : U.Ty) (a : Arr (U.Val t))
    (_ : a.data = []) : eltype (Item.array t a) = t := rfl

/-- An invalid dimension is rejected before allocation or any store. -/
theorem catT_invalid_dims {U : Universe} (ops : Ops U) (t : U.Ty)
    (dims : List Int) (xs : List (Item U))
    (h : dims2cat dims = .error .argumentError) :
    catT ops t dims xs = .error .argumentError := by
  simp [catT, h, bind, Except.bind]

/-- An allocation error is returned before zero initialization or copying. -/
theorem catT_allocation_error {U : Universe} (ops : Ops U) (t : U.Ty)
    (dims : List Int) (x : Item U) (xs : List (Item U)) (ds : List Bool)
    (s : List I64) (e : Err) (hd : dims2cat dims = .ok ds)
    (hs : shape ds (x :: xs) = .ok s)
    (ha : ops.similar t x s = .error e) :
    catT ops t dims (x :: xs) = .error e := by
  simp [catT, hd, hs, ha, bind, Except.bind]

/-- Dense `Array` allocation for a requested element type. The input is ignored
by the `cat_similar` fallback and `Array` methods. -/
def denseSimilar {U : Universe} (t : U.Ty) (_x : Item U) (shape : List I64) :
    R (CatOut (U.Val t)) := arrayUndef shape

/-- The dense destination's range assignment and scalar-view fill, including
conversion from each argument's own element type. -/
def denseCopy {U : Universe} (convert : (s t : U.Ty) → U.Val s → R (U.Val t))
    {t : U.Ty} (a : CatOut (U.Val t)) (inds : List (I64 × I64)) :
    Item U → R (CatOut (U.Val t))
  | .scalar s x => fillRanges (convert s t) a inds x
  | .array s x => setRanges (convert s t) a inds x

/-- On an in-bounds scalar view, a conversion failure is observable even when
the view contains no cells. -/
theorem dense_scalar_conversion_error {U : Universe}
    (convert : (s t : U.Ty) → U.Val s → R (U.Val t))
    (s t : U.Ty) (a : CatOut (U.Val t)) (inds : List (I64 × I64))
    (x : U.Val s) (e : Err) (hb : rangesInBounds a inds = true)
    (hc : convert s t x = .error e) :
    denseCopy convert a inds (.scalar s x) = .error e := by
  simp [denseCopy, fillRanges, hb, hc, bind, Except.bind]

end JuliaLean.AbstractArraySpecs.CatTyped
