import JuliaLean.Core
import JuliaLean.ArrayCov.ReshapedShape

namespace JuliaLean.ArrayCov

inductive ReshapeCoreError where
  | argumentError
  | dimensionMismatch
  | methodError
  deriving Repr, DecidableEq

abbrev ReshapeCoreJl (α : Type) := Except ReshapeCoreError α

structure ArrayReshapeState where
  parent : List Int
  dims : List JInt64
  mi : List JInt64 := []
  deriving Repr, DecidableEq

def reshaped43Array (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (parent : List Int) (dims : List JInt64) : ReshapeCoreJl ArrayReshapeState := do
  let length ← checkedDims dims
  if length.val != parent.length then throw .dimensionMismatch
  pure ⟨parent, dims, []⟩

def reshaped55ArrayBang (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (array : ArrayReshapeState) (dims : List JInt64) : ReshapeCoreJl ArrayReshapeState := do
  let length ← checkedDims dims
  if length.val != array.parent.length then throw .dimensionMismatch
  pure { array with dims := dims }

def reshaped138ThrowManyColon (_dims : List ReshapeDim) : ReshapeCoreJl Unit :=
  .error .dimensionMismatch

def reshaped140ThrowIndivisible (_length : JInt64) (_dims : List ReshapeDim) :
    ReshapeCoreJl Unit := .error .dimensionMismatch

def reshaped143Uncolon (promote : Int → ReshapeCoreJl Int)
    (before : List ReshapeDim → ReshapeCoreJl (List JInt64))
    (after : List ReshapeDim → ReshapeCoreJl (List ReshapeDim))
    (anyColon : List ReshapeDim → Bool)
    (compute : JInt64 → List ReshapeDim → List JInt64 → List JInt64 →
      ReshapeCoreJl (List JInt64))
    (parent : List Int) (rawDims : List ReshapeDim) : ReshapeCoreJl (List JInt64) := do
  let dims ← rawDims.mapM fun dim =>
    match dim with
    | .colon => pure .colon
    | .integer value => .integer <$> promote value
  let pre ← before dims
  let post ← after dims
  if anyColon post then throw .dimensionMismatch
  let post := post.filterMap fun dim => match dim with
    | .colon => none
    | .integer value => some (JInt.lit .i64 value)
  compute (JInt.lit .i64 parent.length) dims pre post

def reshaped152ComputeInt (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (length : JInt64) (_dims : List ReshapeDim) (pre post : List JInt64) :
    ReshapeCoreJl (List JInt64) := do
  let size ← if length.val = 0 then pure (JInt.lit .i64 0) else do
    let product ← checkedDims (pre ++ post)
    if product.val = 0 then throw .dimensionMismatch
    let quotient ← JInt.div length product |>.mapError fun _ => .argumentError
    let remainder ← JInt.remInt length product |>.mapError fun _ => .argumentError
    if remainder.val != 0 then throw .dimensionMismatch
    pure quotient
  pure (pre ++ [size] ++ post)

def reshaped172ComputeNonempty (isZero : Int → Bool)
    (divrem : Int → Int → ReshapeCoreJl (Int × Int))
    (length : Int) (_dims : List ReshapeDim) (product : Int) : ReshapeCoreJl Int := do
  if isZero product then throw .dimensionMismatch
  let (quotient, remainder) ← divrem length product
  if !isZero remainder then throw .dimensionMismatch
  pure quotient

def reshaped163ComputeGeneric (product : List Int → Int)
    (isZero : Int → Bool) (promotedZero : Int → Int → Int)
    (compute : Int → List ReshapeDim → Int → ReshapeCoreJl Int)
    (length : Int) (dims : List ReshapeDim) (pre post : List Int) :
    ReshapeCoreJl (List Int) := do
  let product := product (pre ++ post)
  let size ← if isZero length then pure (promotedZero length product)
    else compute length dims product
  pure (pre ++ [size] ++ post)

def reshaped187Val (axes : List Int → List Int)
    (rdims : Nat → List Int → List JInt64)
    (reshape : List Int → List JInt64 → ReshapeCoreJl ArrayReshapeState)
    (parent : List Int) (rank : Nat) : ReshapeCoreJl ArrayReshapeState :=
  reshape parent (rdims rank (axes parent))

def reshaped214VectorOne (oneBased : List Int → ReshapeCoreJl Unit)
    (parent : List Int) (length : JInt64) : ReshapeCoreJl (List Int) := do
  oneBased parent
  if length.val != parent.length then throw .dimensionMismatch
  pure parent

def reshaped221General (checkedDims : List JInt64 → ReshapeCoreJl JInt64)
    (construct : List Int → List JInt64 → ReshapeCoreJl ArrayReshapeState)
    (parent : List Int) (dims : List JInt64) : ReshapeCoreJl ArrayReshapeState := do
  let product ← checkedDims dims
  if product.val != parent.length then throw .dimensionMismatch
  construct parent dims

def reshaped227ThrowDmrs (_length : JInt64) (_kind : String) (_dims : List JInt64) :
    ReshapeCoreJl Unit := .error .dimensionMismatch

def reshaped235ConstructCartesian (size : List Int → List JInt64)
    (makeMi : List JInt64 → List JInt64) (parent : List Int)
    (dims : List JInt64) : ArrayReshapeState :=
  let sizes := (size parent).dropLast.map fun value =>
    if value.val < 1 then JInt.lit .i64 1 else value
  ⟨parent, dims, makeMi sizes⟩

def reshaped243ConstructZero (parent : List Int) (dims : List JInt64) : ArrayReshapeState :=
  ⟨parent, dims, []⟩

def reshaped248ConstructLinear (parent : List Int) (dims : List JInt64) : ArrayReshapeState :=
  ⟨parent, dims, []⟩

def ReshapeCoreCorrect : Prop :=
  (∀ checked parent dims, reshaped43Array checked parent dims = do
      let length ← checked dims
      if length.val != parent.length then throw .dimensionMismatch
      pure ⟨parent, dims, []⟩) ∧
  (∀ checked array dims, reshaped55ArrayBang checked array dims = do
      let length ← checked dims
      if length.val != array.parent.length then throw .dimensionMismatch
      pure { array with dims := dims }) ∧
  (∀ dims, reshaped138ThrowManyColon dims = .error .dimensionMismatch) ∧
  (∀ length dims, reshaped140ThrowIndivisible length dims = .error .dimensionMismatch) ∧
  (∀ promote before after any compute parent dims,
      reshaped143Uncolon promote before after any compute parent dims = do
      let dims ← dims.mapM fun dim => match dim with
        | .colon => pure .colon
        | .integer value => .integer <$> promote value
      let pre ← before dims
      let post ← after dims
      if any post then throw .dimensionMismatch
      let post := post.filterMap fun dim => match dim with
        | .colon => none
        | .integer value => some (JInt.lit .i64 value)
      compute (JInt.lit .i64 parent.length) dims pre post) ∧
  (∀ checked length dims pre post, reshaped152ComputeInt checked length dims pre post = do
      let size ← if length.val = 0 then pure (JInt.lit .i64 0) else do
        let product ← checked (pre ++ post)
        if product.val = 0 then throw .dimensionMismatch
        let quotient ← JInt.div length product |>.mapError fun _ => .argumentError
        let remainder ← JInt.remInt length product |>.mapError fun _ => .argumentError
        if remainder.val != 0 then throw .dimensionMismatch
        pure quotient
      pure (pre ++ [size] ++ post)) ∧
  (∀ product isZero zero compute length dims pre post,
      reshaped163ComputeGeneric product isZero zero compute length dims pre post = do
      let product := product (pre ++ post)
      let size ← if isZero length then pure (zero length product)
        else compute length dims product
      pure (pre ++ [size] ++ post)) ∧
  (∀ isZero divrem length dims product,
      reshaped172ComputeNonempty isZero divrem length dims product = do
      if isZero product then throw .dimensionMismatch
      let (quotient, remainder) ← divrem length product
      if !isZero remainder then throw .dimensionMismatch
      pure quotient) ∧
  (∀ axes rdims reshape parent rank, reshaped187Val axes rdims reshape parent rank =
      reshape parent (rdims rank (axes parent))) ∧
  (∀ oneBased parent length, reshaped214VectorOne oneBased parent length = do
      oneBased parent
      if length.val != parent.length then throw .dimensionMismatch
      pure parent) ∧
  (∀ checked construct parent dims, reshaped221General checked construct parent dims = do
      let product ← checked dims
      if product.val != parent.length then throw .dimensionMismatch
      construct parent dims) ∧
  (∀ length kind dims, reshaped227ThrowDmrs length kind dims = .error .dimensionMismatch) ∧
  (∀ size makeMi parent dims, reshaped235ConstructCartesian size makeMi parent dims =
      let sizes := (size parent).dropLast.map fun value =>
        if value.val < 1 then JInt.lit .i64 1 else value
      ⟨parent, dims, makeMi sizes⟩) ∧
  (∀ parent dims, reshaped243ConstructZero parent dims = ⟨parent, dims, []⟩) ∧
  (∀ parent dims, reshaped248ConstructLinear parent dims = ⟨parent, dims, []⟩)

theorem reshapeCoreCorrect : ReshapeCoreCorrect := by
  simp [ReshapeCoreCorrect, reshaped43Array, reshaped55ArrayBang,
    reshaped138ThrowManyColon, reshaped140ThrowIndivisible, reshaped143Uncolon,
    reshaped152ComputeInt, reshaped163ComputeGeneric, reshaped172ComputeNonempty, reshaped187Val,
    reshaped214VectorOne, reshaped221General, reshaped227ThrowDmrs,
    reshaped235ConstructCartesian, reshaped243ConstructZero, reshaped248ConstructLinear]

end JuliaLean.ArrayCov
