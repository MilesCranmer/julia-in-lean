import JuliaLean.Core
import JuliaLean.ArrayCov.ReshapedSimple

namespace JuliaLean.ArrayCov

inductive ReshapeDim where
  | integer (value : Int)
  | colon
  deriving Repr, DecidableEq

def reshaped122Varargs (reshapeTuple : List Int → Jl Int)
    (dims : List Int) : Jl Int := reshapeTuple dims

def reshaped123AbstractAxes (toShape : List Int → List Int)
    (reshapeTuple : List Int → Jl Int) (shape : List Int) : Jl Int :=
  reshapeTuple (toShape shape)

def reshaped126OneToAxes (toShape : List Int → List Int)
    (reshapeTuple : List Int → Jl Int) (shape : List Int) : Jl Int :=
  reshapeTuple (toShape shape)

def reshaped127ConvertDims (convertInt : Int → Jl Int)
    (reshapeTuple : List Int → Jl Int) (dims : List Int) : Jl Int := do
  let dims ← dims.mapM convertInt
  reshapeTuple dims

def reshaped128Dims (_reshape : List Int → Jl Int) (dims : List Int) : Jl Int :=
  _reshape dims

def reshaped131VectorColon (parent : List Int) : List Int := parent
def reshaped132VectorColonTuple (parent : List Int) : List Int := parent

def reshaped133IntVarargs (reshapeTuple : List Int → Jl Int)
    (dims : List Int) : Jl Int := reshapeTuple dims

def reshaped134IntegerVarargs (reshapeTuple : List Int → Jl Int)
    (dims : List Int) : Jl Int := reshapeTuple dims

def reshaped135ColonVarargs (reshapeTuple : List ReshapeDim → Jl Int)
    (dims : List ReshapeDim) : Jl Int := reshapeTuple dims

def reshaped136ColonTuple (uncolon : List ReshapeDim → Jl (List Int))
    (reshapeDims : List Int → Jl Int) (dims : List ReshapeDim) : Jl Int := do
  let dims ← uncolon dims
  reshapeDims dims

def reshapeAnyColon : List ReshapeDim → Bool
  | [] => false
  | .colon :: _ => true
  | .integer _ :: tail => reshapeAnyColon tail

abbrev ReshapeTupleResult := Except JlError (List ReshapeDim)

def reshapeBeforeColon : List ReshapeDim → ReshapeTupleResult
  | [] => .error (.methodError "_before_colon")
  | .colon :: _ => .ok []
  | head@(.integer _) :: tail => do
      let rest ← reshapeBeforeColon tail
      .ok (head :: rest)

def reshapeAfterColon : List ReshapeDim → ReshapeTupleResult
  | [] => .error (.methodError "_after_colon")
  | .colon :: tail => .ok tail
  | .integer _ :: tail => reshapeAfterColon tail

def ReshapedShapeWrappersCorrect : Prop :=
  (∀ call dims, reshaped122Varargs call dims = call dims) ∧
  (∀ shape call dims, reshaped123AbstractAxes shape call dims = call (shape dims)) ∧
  (∀ shape call dims, reshaped126OneToAxes shape call dims = call (shape dims)) ∧
  (∀ convert call dims, reshaped127ConvertDims convert call dims = do
      let dims ← dims.mapM convert; call dims) ∧
  (∀ call dims, reshaped128Dims call dims = call dims) ∧
  (∀ parent, reshaped131VectorColon parent = parent) ∧
  (∀ parent, reshaped132VectorColonTuple parent = parent) ∧
  (∀ call dims, reshaped133IntVarargs call dims = call dims) ∧
  (∀ call dims, reshaped134IntegerVarargs call dims = call dims) ∧
  (∀ call dims, reshaped135ColonVarargs call dims = call dims) ∧
  (∀ uncolon call dims, reshaped136ColonTuple uncolon call dims = do
      let dims ← uncolon dims; call dims) ∧
  reshapeAnyColon [] = false ∧
  (∀ tail, reshapeAnyColon (.colon :: tail) = true) ∧
  (∀ value tail, reshapeAnyColon (.integer value :: tail) = reshapeAnyColon tail) ∧
  (∀ tail, reshapeBeforeColon (.colon :: tail) = .ok []) ∧
  (∀ value tail, reshapeBeforeColon (.integer value :: tail) = do
      let rest ← reshapeBeforeColon tail; .ok (.integer value :: rest)) ∧
  (∀ tail, reshapeAfterColon (.colon :: tail) = .ok tail) ∧
  (∀ value tail, reshapeAfterColon (.integer value :: tail) = reshapeAfterColon tail)

theorem reshapedShapeWrappersCorrect : ReshapedShapeWrappersCorrect := by
  simp [ReshapedShapeWrappersCorrect, reshaped122Varargs, reshaped123AbstractAxes,
    reshaped126OneToAxes, reshaped127ConvertDims, reshaped128Dims,
    reshaped131VectorColon, reshaped132VectorColonTuple, reshaped133IntVarargs,
    reshaped134IntegerVarargs, reshaped135ColonVarargs, reshaped136ColonTuple,
    reshapeAnyColon, reshapeBeforeColon, reshapeAfterColon] <;> simp_all

def reshaped186SameRank (parent : List Int) (_rank : Nat) : List Int := parent

def reshaped194Trailing : List JInt64 → JInt64
  | [] => JInt.lit .i64 1
  | length :: rest => length * reshaped194Trailing rest

def reshaped195TrailingOne (length : JInt64) : JInt64 := length

def reshaped196RdimsVal (rdims : List JInt64 → List JInt64 → List JInt64)
    (rank : Nat) (indices : List JInt64) : List JInt64 :=
  rdims (List.replicate rank (JInt.lit .i64 1)) indices

def reshaped197RdimsEmptyEmpty (_ : Unit) : List JInt64 := []
def reshaped198RdimsEmptyOne (_index : JInt64) : List JInt64 := []
def reshaped199RdimsEmptyMany (_indices : List JInt64) : List JInt64 := []
def reshaped200RdimsOneEmpty (output : JInt64) : List JInt64 := [output]
def reshaped201RdimsManyEmpty (output : List JInt64) : List JInt64 := output
def reshaped202RdimsOneOne (index : JInt64) : List JInt64 := [index]

def reshaped203RdimsOneMany (oneto : JInt64 → JInt64)
    (indices : List JInt64) : List JInt64 :=
  [oneto (reshaped194Trailing indices)]

def reshaped204RdimsEqual (indices : List JInt64) : List JInt64 := indices

def reshaped205RdimsRecursive
    (rdims : List JInt64 → List JInt64 → List JInt64)
    (output indices : List JInt64) : List JInt64 :=
  match indices with
  | [] => output
  | first :: tail => first :: rdims output.tail tail

def reshaped209VectorOne (parent : List Int) (_dims : List Int) : List Int := parent
def reshaped210ArrayOne (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims
def reshaped211ArrayDims (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims
def reshaped232NestedVector (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims
def reshaped233Nested (reshape : List Int → List Int → Jl Int)
    (parent dims : List Int) : Jl Int := reshape parent dims

def ReshapedRankRoutesCorrect : Prop :=
  (∀ parent rank, reshaped186SameRank parent rank = parent) ∧
  (∀ length rest, reshaped194Trailing (length :: rest) =
      length * reshaped194Trailing rest) ∧
  (∀ length, reshaped195TrailingOne length = length) ∧
  (∀ rdims rank indices, reshaped196RdimsVal rdims rank indices =
      rdims (List.replicate rank (JInt.lit .i64 1)) indices) ∧
  (∀ u, reshaped197RdimsEmptyEmpty u = []) ∧
  (∀ index, reshaped198RdimsEmptyOne index = []) ∧
  (∀ indices, reshaped199RdimsEmptyMany indices = []) ∧
  (∀ output, reshaped200RdimsOneEmpty output = [output]) ∧
  (∀ output, reshaped201RdimsManyEmpty output = output) ∧
  (∀ index, reshaped202RdimsOneOne index = [index]) ∧
  (∀ oneto indices, reshaped203RdimsOneMany oneto indices =
      [oneto (reshaped194Trailing indices)]) ∧
  (∀ indices, reshaped204RdimsEqual indices = indices) ∧
  (∀ rdims output first tail, reshaped205RdimsRecursive rdims output (first :: tail) =
      first :: rdims output.tail tail) ∧
  (∀ parent dims, reshaped209VectorOne parent dims = parent) ∧
  (∀ call parent dims, reshaped210ArrayOne call parent dims = call parent dims) ∧
  (∀ call parent dims, reshaped211ArrayDims call parent dims = call parent dims) ∧
  (∀ call parent dims, reshaped232NestedVector call parent dims = call parent dims) ∧
  (∀ call parent dims, reshaped233Nested call parent dims = call parent dims)

theorem reshapedRankRoutesCorrect : ReshapedRankRoutesCorrect := by
  simp [ReshapedRankRoutesCorrect, reshaped186SameRank, reshaped194Trailing,
    reshaped195TrailingOne, reshaped196RdimsVal, reshaped197RdimsEmptyEmpty,
    reshaped198RdimsEmptyOne, reshaped199RdimsEmptyMany, reshaped200RdimsOneEmpty,
    reshaped201RdimsManyEmpty, reshaped202RdimsOneOne, reshaped203RdimsOneMany,
    reshaped204RdimsEqual, reshaped205RdimsRecursive, reshaped209VectorOne,
    reshaped210ArrayOne, reshaped211ArrayDims, reshaped232NestedVector, reshaped233Nested]

end JuliaLean.ArrayCov
