import JuliaLean.base.reshapedarray
import JuliaLean.Core
import JuliaLean.Proofs.base.reshapedarray.coverage_reshaped_simple

namespace JuliaLean.ArrayCov

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
