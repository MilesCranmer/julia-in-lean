import JuliaLean.base.broadcast

namespace JuliaLean.BroadcastCov.BroadcastCore

def StyleMethods : Prop :=
  (∀ extra, bottomStyle extra = if extra then .error .methodError else .ok .unknown) ∧
  (∀ tuple ar fallback, typeStyle tuple ar fallback =
    if tuple then .tuple else if ar > 0 then .defaultArray ar else .defaultArray fallback) ∧
  (∀ family rank, arrayStyle family rank = .array family rank) ∧
  (∀ rank, defaultArrayStyle rank = .defaultArray rank) ∧
  (arrayConflict = .conflict) ∧
  (∀ a b same, pairStyle a b same = pairStyle a b same) ∧
  (∀ a b f r, resultJoin a b f r = resultJoin a b f r) ∧
  (∀ a b sameObject sameFamily,
    resultStyle a b sameObject sameFamily =
      if a = b then if sameObject then .ok a else .error .argumentError
      else resultJoin a b (pairStyle a b sameFamily) (pairStyle b a sameFamily))

theorem styleMethods : StyleMethods := by
  exact ⟨fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, rfl,
    fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def LazyExpressionMethods : Prop :=
  (∀ style tag args ax, construct style tag args ax = ⟨style, tag, args, ax⟩) ∧
  (tupleFunctionConstructor = .error .methodError) ∧
  (∀ style bc, convertStyle style bc = { bc with style := style }) ∧
  (∀ bc, showParts bc = (if bc.axes.isSome then [1] else []) ++ [bc.tag, bc.args.length]) ∧
  (∀ boolean dims, similarStorage boolean dims =
    (if boolean then .bitArray else .array, dims)) ∧
  (∀ bc, expressionStyle bc =
    if bc.style = .unknown then .error .argumentError else .ok bc.style) ∧
  (∀ bc, argtype bc = bc.args.length) ∧
  (∀ a b, andAnd a b = (a && b)) ∧
  (∀ a b, orOr a b = (a || b)) ∧
  (∀ arg, flattenArgs arg = flattenArgs arg) ∧
  (∀ arg, isFlat arg = isFlat arg) ∧
  (∀ args, catNested args = args.flatMap flattenArgs) ∧
  (∀ arg, leafCount arg = leafCount arg) ∧
  (∀ args start, makeArgRanges args start = makeArgRanges args start) ∧
  (∀ n args, pick n args = args.getD n 0) ∧
  (∀ styles, combineStyles styles = combineStyles styles) ∧
  (∀ bc compatible, instantiate bc compatible =
    match bc.axes with
    | none => .ok { bc with axes := some (combineArgAxes bc.args) }
    | some _ => if compatible then .ok bc else .error .dimensionMismatch)

theorem lazyExpressionMethods : LazyExpressionMethods := by
  exact ⟨fun _ _ _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

def AxisAndIndexMethods : Prop :=
  (∀ bc, axes bc = bc.axes.getD (combineArgAxes bc.args)) ∧
  (∀ bc d, axesDim bc d =
    if 1 ≤ d ∧ d ≤ (axes bc).length then .ok ((axes bc).getD (d - 1).toNat 1)
    else if d > (axes bc).length then .ok 1 else .error .boundsError) ∧
  (∀ bc, size bc = axes bc) ∧
  (∀ bc, length bc = (size bc).foldl (· * ·) 1) ∧
  (∀ bc, ndims bc = (axes bc).length) ∧
  (∀ args, maxNdim args = args.foldl (fun n a => max n a.axes.length) 0) ∧
  (∀ args, combineArgAxes args =
    [args.foldl (fun n a => max n (a.axes.getD 0 1)) 1]) ∧
  (∀ shape source, checkBroadcastShape shape source = checkBroadcastShape shape source) ∧
  (∀ bc, indexStyle bc = if (axes bc).length = 1 then .linear else .cartesian) ∧
  (∀ bc, eachindex bc = List.range (length bc)) ∧
  (∀ bc state, iterate bc state =
    if state < length bc then
      match getindex bc state with
      | .ok value => some (value, state + 1)
      | .error _ => none
    else none) ∧
  (∀ bc, iteratorTraits bc = (ndims bc, false)) ∧
  (∀ firsts indices lengths, newIndex firsts indices lengths =
    newIndexGo firsts indices lengths) ∧
  (∀ firsts lengths, newIndexer firsts lengths = (lengths.map (· != 1), firsts)) ∧
  (∀ indices, toIndex indices = indices) ∧
  (∀ shape indices, checkBounds shape indices =
    (indices.length == shape.length &&
      (indices.zip shape).all (fun p => decide (1 ≤ p.1 ∧ p.1 ≤ p.2)))) ∧
  (∀ arg index, getArg arg index = arg.eval index) ∧
  (∀ bc index, getindex bc index =
    if index < length bc then .ok (bc.tag + (bc.args.map (fun a => getArg a index)).sum)
    else .error .boundsError)

theorem axisAndIndexMethods : AxisAndIndexMethods := by
  exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

def MaterializationMethods : Prop :=
  (∀ scalarLike already reserved, broadcastable scalarLike already reserved =
    if reserved then .reservedError else if scalarLike then .ref
    else if already then .identity else .collected) ∧
  (∀ bc i, inferredSamples bc i = bc.args.map (fun a => getArg a i)) ∧
  (∀ tag args, broadcastValues tag args =
    match args with
    | [] => [tag]
    | first :: rest => (List.range first.length).map fun i =>
        tag + first.getD i 0 + (rest.map (fun xs => xs.getD i 0)).sum) ∧
  (∀ result ax, preservingZeroD result ax =
    if ax = [] then [result] else List.replicate (ax.foldl (· * ·) 1) result) ∧
  (∀ bc, materialize bc =
    match instantiate bc true with
    | .error e => .error e
    | .ok ready => .ok ((List.range (length ready)).map fun i =>
        ready.tag + (ready.args.map (fun a => getArg a i)).sum)) ∧
  (∀ n bc, copyto n bc = if n != length bc then .error .dimensionMismatch else materialize bc) ∧
  (∀ writable n bc, materializeBang writable n bc =
    if writable then copyto n bc else .error .unwritable) ∧
  (∀ assigned bc, copy assigned bc = if assigned then materialize bc else .error .argumentError) ∧
  (∀ same arg, preprocess same arg = (false && same, arg)) ∧
  (∀ written rest, copyNonleaf written rest = written ++ rest) ∧
  (throwDimensionMismatch = .error .dimensionMismatch)

theorem materializationMethods : MaterializationMethods := by
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, rfl⟩

end JuliaLean.BroadcastCov.BroadcastCore
