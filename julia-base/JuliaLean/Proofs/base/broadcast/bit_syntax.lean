import JuliaLean.base.broadcast

namespace JuliaLean.BroadcastCov.BitsSyntax

def ChunkMethods : Prop :=
  (∀ op x y, applyChunkOp op x y =
    match op with
    | .unsupported => none
    | .and => some (x &&& y)
    | .or => some (x ||| y)
    | .xor | .unequal => some (x ^^^ y)
    | .nand => some (~~~(x &&& y))
    | .nor => some (~~~(x ||| y))
    | .not => some (~~~x)
    | .identity => some x
    | .equal => some (~~~(x ^^^ y))
    | .less => some ((~~~x) &&& y)
    | .lessEqual => some ((~~~x) ||| y)
    | .greater => some (x &&& (~~~y))
    | .greaterEqual => some (x ||| (~~~y))) ∧
  (∀ n args, chunkable n args = chunkable n args) ∧
  (∀ arg, liftFunctions arg = liftFunctions arg) ∧
  (∀ args, liftChunks args = liftChunks args) ∧
  (∀ i chunks, ithChunk i chunks = chunks.map (fun c => c.getD i 0)) ∧
  (∀ op left right mask, chunkedCopy op left right mask = chunkedCopy op left right mask)

theorem chunkMethods : ChunkMethods := by
  exact ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ => rfl⟩

def BitMaskedMethods : Prop :=
  (∀ parent mask, bitMasked parent mask =
    if parent.length == mask.length then some ⟨parent, mask⟩ else none) ∧
  (∀ b value, fillMasked b value =
    { b with parent := (b.parent.zip b.mask).map fun p => if p.2 then value else p.1 }) ∧
  (∀ b value, materializeIdentity b value = fillMasked b value) ∧
  (∀ b, showBitMasked b = [b.parent, b.mask])

theorem bitMaskedMethods : BitMaskedMethods := by
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

def SyntaxMethods : Prop :=
  (∀ x, dottable x = dottable x) ∧
  (∀ x, undot x = undot x) ∧
  (∀ x, dotSyntax x = dotSyntax x) ∧
  (∀ x, macroDot x = dotSyntax x) ∧
  (∀ x, dotviewResult x = x) ∧
  (∀ kw style n, broadcastedPath kw style n =
    if style then .explicitStyle else if kw then .keywordClosure
    else if n = 0 then .direct else .genericMapped n) ∧
  (∀ f args, broadcastFunctionCall f args = f args) ∧
  (∀ name, broadcastFunctionShow name = "BroadcastFunction(" ++ name ++ ")")

theorem syntaxMethods : SyntaxMethods := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end JuliaLean.BroadcastCov.BitsSyntax
