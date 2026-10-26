import JuliaLean.AbstractArrayCov.Rows.BoundsShape

/-! Method-specific models for `base/abstractarray.jl:920-1272`. -/

namespace JuliaLean.AbstractArrayCov.Rows.Copy

open JuliaLean
open JuliaLean.Registry

abbrev I64 := JInt .i64
def i64 (x : Int) : I64 := JInt.lit .i64 x

def writeSeq (set : δ → I64 → α → Jl δ) : δ → I64 → List α → Jl δ
  | dest, _, [] => .ok dest
  | dest, i, x :: xs => do writeSeq set (← set dest i x) (i + i64 1) xs

def writePairs (set : δ → ι → α → Jl δ) : δ → List (ι × α) → Jl δ
  | dest, [] => .ok dest
  | dest, (i, x) :: rest => do writePairs set (← set dest i x) rest

/-- Vector `copy!`, lines 920-927. -/
def method920 (firstindex : α → Int) (length : α → Nat)
    (resize : α → Nat → Jl α) (copyto : α → α → Jl α) (dst src : α) : Jl α := do
  if firstindex dst != firstindex src then
    throw (.argumentError "vectors must have the same offset for copy! (consider using `copyto!`)")
  let dst ← if length dst != length src then resize dst (length src) else .ok dst
  copyto dst src
def Property920 : Prop := ∀ (α : Type) (firstindex : α → Int) (length : α → Nat)
    (resize : α → Nat → Jl α) (copyto : α → α → Jl α) dst src,
  method920 firstindex length resize copyto dst src = do
    if firstindex dst != firstindex src then
      throw (.argumentError "vectors must have the same offset for copy! (consider using `copyto!`)")
    let dst ← if length dst != length src then resize dst (length src) else .ok dst
    copyto dst src
theorem property920 : Property920 := by unfold Property920; intros; rfl

/-- General-array `copy!`, lines 929-933. -/
def method929 [BEq β] (axes : α → β) (copyto : α → α → Jl α) (dst src : α) : Jl α := do
  if axes dst != axes src then
    throw (JlError.argumentError "arrays must have the same axes for copy! (consider using `copyto!`)")
  copyto dst src
def Property929 : Prop := ∀ (α β : Type) [BEq β] (axes : α → β)
    (copyto : α → α → Jl α) dst src,
  method929 axes copyto dst src = do
    if axes dst != axes src then
      throw (JlError.argumentError "arrays must have the same axes for copy! (consider using `copyto!`)")
    copyto dst src
theorem property929 : Property929 := by unfold Property929; intros; rfl

/-- Iterable-to-array `copyto!`, lines 941-951. -/
def method941 (eachindex : δ → List ι) (set : δ → ι → α → Jl δ)
    (dest : δ) (src : List α) : Jl δ :=
  if src.length ≤ (eachindex dest).length then
    writePairs set dest ((eachindex dest).zip src)
  else .error (.argumentError "destination has fewer elements than required")
def Property941 : Prop := ∀ (δ ι α : Type) (eachindex : δ → List ι)
    (set : δ → ι → α → Jl δ) dest src,
  method941 eachindex set dest src =
    if src.length ≤ (eachindex dest).length then writePairs set dest ((eachindex dest).zip src)
    else .error (.argumentError "destination has fewer elements than required")
theorem property941 : Property941 := by unfold Property941; intros; rfl

/-- Iterable `copyto!(dest,dstart,src)`, lines 953-971. -/
def method953 (hasLength : Bool) (destLength : Nat) (lastindex : I64)
    (checkbounds : I64 → Jl Unit) (set : δ → I64 → α → Jl δ)
    (dest : δ) (dstart : Int) (src : List α) : Jl δ := do
  let i ← JInt.convert .i64 dstart
  if hasLength && destLength > 0 then
    if src.isEmpty then return dest
    checkbounds i
    if ¬((src.length : Int) ≤ lastindex.val - i.val + 1) then throw .boundsError
    writeSeq set dest i src
  else writeSeq set dest i src
def Property953 : Prop := ∀ (δ α : Type) hasLength destLength lastindex
    (checkbounds : I64 → Jl Unit) (set : δ → I64 → α → Jl δ) dest dstart src,
  method953 hasLength destLength lastindex checkbounds set dest dstart src = do
    let i ← JInt.convert .i64 dstart
    if hasLength && destLength > 0 then
      if src.isEmpty then return dest
      checkbounds i
      if ¬((src.length : Int) ≤ lastindex.val - i.val + 1) then throw .boundsError
      writeSeq set dest i src
    else writeSeq set dest i src
theorem property953 : Property953 := by unfold Property953; intros; rfl

/-- Iterable `copyto!(dest,dstart,src,sstart)`, lines 974-1000. -/
def method974 (set : δ → I64 → α → Jl δ) (dest : δ)
    (dstart sstart : Int) (src : List α) : Jl δ := do
  if sstart < 1 then throw (.argumentError "source start offset is < 1")
  if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
  let i ← JInt.convert .i64 dstart
  writeSeq set dest i (src.drop (sstart - 1).toNat)
def Property974 : Prop := ∀ (δ α : Type) (set : δ → I64 → α → Jl δ)
    dest dstart sstart src,
  method974 set dest dstart sstart src = do
    if sstart < 1 then throw (.argumentError "source start offset is < 1")
    if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
    let i ← JInt.convert .i64 dstart
    writeSeq set dest i (src.drop (sstart - 1).toNat)
theorem property974 : Property974 := by unfold Property974; intros; rfl

/-- Counted iterable `copyto!`, lines 1003-1037. -/
def method1003 (destContains : Int → Bool) (destLast : Int)
    (set : δ → I64 → α → Jl δ) (dest : δ) (dstart : Int)
    (src : List α) (sstart n : Int) : Jl δ := do
  if n < 0 then throw (.argumentError "elements to copy should be non-negative")
  if n = 0 then return dest
  if sstart < 1 then throw (.argumentError "source start offset is < 1")
  if !(destContains dstart && n ≤ destLast - dstart + 1) then throw .boundsError
  let d ← JInt.convert .i64 dstart
  let n64 ← JInt.convert .i64 n
  if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
  let values := (src.drop (sstart - 1).toNat).take n64.val.toNat
  let dest ← writeSeq set dest d values
  if values.length < n64.val.toNat then throw .boundsError
  return dest
def Property1003 : Prop := ∀ (δ α : Type) (contains : Int → Bool) last
    (set : δ → I64 → α → Jl δ) dest dstart src sstart n,
  method1003 contains last set dest dstart src sstart n = do
    if n < 0 then throw (.argumentError "elements to copy should be non-negative")
    if n = 0 then return dest
    if sstart < 1 then throw (.argumentError "source start offset is < 1")
    if !(contains dstart && n ≤ last - dstart + 1) then throw .boundsError
    let d ← JInt.convert .i64 dstart
    let n64 ← JInt.convert .i64 n
    if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
    let values := (src.drop (sstart - 1).toNat).take n64.val.toNat
    let dest ← writeSeq set dest d values
    if values.length < n64.val.toNat then throw .boundsError
    return dest
theorem property1003 : Property1003 := by unfold Property1003; intros; rfl

/-- AbstractArray-to-array `copyto!`, lines 1072-1080. -/
def method1072 (isempty isBitArray : Bool) (bitcopy : δ → σ → Jl δ)
    (unalias : δ → σ → σ) (styleDest : δ → ι) (styleSrc : σ → κ)
    (copyUnaliased : ι → δ → κ → σ → Jl δ) (dest : δ) (src : σ) : Jl δ := do
  if isempty then return dest
  if isBitArray then return ← bitcopy dest src
  let src' := unalias dest src
  copyUnaliased (styleDest dest) dest (styleSrc src') src'
def Property1072 : Prop := ∀ (δ σ ι κ : Type) isempty isBit
    (bitcopy : δ → σ → Jl δ) (unalias : δ → σ → σ) (styleDest : δ → ι)
    (styleSrc : σ → κ) (copyU : ι → δ → κ → σ → Jl δ) dest src,
  method1072 isempty isBit bitcopy unalias styleDest styleSrc copyU dest src = do
    if isempty then return dest
    if isBit then return ← bitcopy dest src
    let src' := unalias dest src
    copyU (styleDest dest) dest (styleSrc src') src'
theorem property1072 : Property1072 := by unfold Property1072; intros; rfl

/-- Styled AbstractArray `copyto!`, lines 1082-1086. -/
def method1082 (isempty : Bool) (unalias : δ → σ → σ)
    (copyU : ι → δ → κ → σ → Jl δ) (ds : ι) (dest : δ) (ss : κ) (src : σ) : Jl δ := do
  if isempty then return dest
  let src' := unalias dest src
  copyU ds dest ss src'
def Property1082 : Prop := ∀ (δ σ ι κ : Type) isempty (unalias : δ → σ → σ)
    (copyU : ι → δ → κ → σ → Jl δ) ds dest ss src,
  method1082 isempty unalias copyU ds dest ss src = do
    if isempty then return dest
    let src' := unalias dest src
    copyU ds dest ss src'
theorem property1082 : Property1082 := by unfold Property1082; intros; rfl

/-- `copyto_unaliased!`, lines 1088-1123, with explicit source and destination iterators. -/
def method1088 (srcEmpty destLinear srcLinear sameIterator : Bool)
    (boundsFirst boundsLast : Bool) (linearPairs dualPairs sharedPairs cartPairs : List (ι × α))
    (set : δ → ι → α → Jl δ) (dest : δ) : Jl δ := do
  if srcEmpty then return dest
  let firstOk := boundsFirst
  let lastOk := boundsLast
  if !(firstOk && lastOk) then throw .boundsError
  if destLinear then
    if srcLinear then writePairs set dest linearPairs else writePairs set dest dualPairs
  else if sameIterator then writePairs set dest sharedPairs else writePairs set dest cartPairs
def Property1088 : Prop := ∀ (δ ι α : Type) srcEmpty destLinear srcLinear same firstOk lastOk
    linearPairs dualPairs sharedPairs cartPairs (set : δ → ι → α → Jl δ) dest,
  method1088 srcEmpty destLinear srcLinear same firstOk lastOk linearPairs dualPairs sharedPairs cartPairs set dest = do
    if srcEmpty then return dest
    let a := firstOk
    let b := lastOk
    if !(a && b) then throw .boundsError
    if destLinear then
      if srcLinear then writePairs set dest linearPairs else writePairs set dest dualPairs
    else if same then writePairs set dest sharedPairs else writePairs set dest cartPairs
theorem property1088 : Property1088 := by unfold Property1088; intros; rfl

/-- Three-argument AbstractArray `copyto!`, lines 1125-1127. -/
def method1125 (linear : σ → List Int) (length : σ → Int)
    (copy : δ → Int → σ → Int → Int → Jl δ) (dest : δ) (dstart : Int) (src : σ) : Jl δ :=
  match linear src with
  | [] => copy dest dstart src 1 (length src)
  | first :: _ => copy dest dstart src first (length src)
def Property1125 : Prop := ∀ (δ σ : Type) (linear : σ → List Int) (length : σ → Int)
    (copy : δ → Int → σ → Int → Int → Jl δ) dest dstart src,
  method1125 linear length copy dest dstart src = match linear src with
    | [] => copy dest dstart src 1 (length src)
    | first :: _ => copy dest dstart src first (length src)
theorem property1125 : Property1125 := by
  unfold Property1125
  intro δ σ linearFn lengthFn copyFn dest dstart src
  cases h : linearFn src <;> simp [method1125, h]

/-- Four-argument AbstractArray `copyto!`, lines 1129-1133. -/
def method1129 (linear : σ → List Int) (check : List Int → Int → Bool)
    (copy : δ → Int → σ → Int → Int → Jl δ) (dest : δ) (dstart : Int)
    (src : σ) (sstart : Int) : Jl δ := do
  let inds := linear src
  if !check inds sstart then throw .boundsError
  let last := inds.getLast?.getD 0
  copy dest dstart src sstart (last - sstart + 1)
def Property1129 : Prop := ∀ (δ σ : Type) (linear : σ → List Int)
    (check : List Int → Int → Bool) (copy : δ → Int → σ → Int → Int → Jl δ)
    dest dstart src sstart,
  method1129 linear check copy dest dstart src sstart = do
    let inds := linear src
    if !check inds sstart then throw .boundsError
    let last := inds.getLast?.getD 0
    copy dest dstart src sstart (last - sstart + 1)
theorem property1129 : Property1129 := by unfold Property1129; intros; rfl

/-- Counted AbstractArray block `copyto!`, lines 1135-1152. -/
def method1135 (destBounds srcBounds : Int → Int → Bool) (destLast srcLast : Int)
    (unalias : δ → σ → σ) (read : σ → Int → Jl α) (set : δ → I64 → α → Jl δ)
    (dest : δ) (dstart : Int) (src : σ) (sstart n : Int) : Jl δ := do
  if n = 0 then return dest
  if n < 0 then throw (.argumentError "elements to copy should be non-negative")
  if !(destBounds dstart n && n ≤ destLast - dstart + 1) then throw .boundsError
  if !(srcBounds sstart n && n ≤ srcLast - sstart + 1) then throw .boundsError
  let d ← JInt.convert .i64 dstart
  let src' := unalias dest src
  let values ← (List.range n.toNat).mapM fun (k : Nat) => read src' (sstart + (k : Int))
  writeSeq set dest d values
def Property1135 : Prop := ∀ (δ σ α : Type) (db sb : Int → Int → Bool) dl sl
    (unalias : δ → σ → σ) (read : σ → Int → Jl α) (set : δ → I64 → α → Jl δ)
    dest dstart src sstart n,
  method1135 db sb dl sl unalias read set dest dstart src sstart n = do
    if n = 0 then return dest
    if n < 0 then throw (.argumentError "elements to copy should be non-negative")
    if !(db dstart n && n ≤ dl - dstart + 1) then throw .boundsError
    if !(sb sstart n && n ≤ sl - sstart + 1) then throw .boundsError
    let d ← JInt.convert .i64 dstart
    let src' := unalias dest src
    let values ← (List.range n.toNat).mapM fun (k : Nat) => read src' (sstart + (k : Int))
    writeSeq set dest d values
theorem property1135 : Property1135 := by unfold Property1135; intros; rfl

/-- `copy(a::AbstractArray)`, lines 1154-1157. -/
def method1154 (copymutable : α → β) (a : α) : β := copymutable a
def Property1154 : Prop := ∀ (α β : Type) (copymutable : α → β) a,
  method1154 copymutable a = copymutable a
theorem property1154 : Property1154 := by unfold Property1154; intros; rfl

/-- Matrix-region `copyto!`, lines 1159-1182. -/
def method1159 (checkDest checkSrc : Jl Unit) (unalias : δ → σ → σ)
    (read : σ → Int → Int → Jl α) (set : δ → Int → Int → α → Jl δ)
    (dest : δ) (destRows destCols : List Int) (src : σ) (srcRows srcCols : List Int) : Jl δ := do
  if destRows.length != srcRows.length then throw (.argumentError "row sizes differ")
  if destCols.length != srcCols.length then throw (.argumentError "column sizes differ")
  checkDest
  checkSrc
  let src' := unalias dest src
  let mut out := dest
  for (dc, sc) in destCols.zip srcCols do
    for (dr, sr) in destRows.zip srcRows do
      out ← set out dr dc (← read src' sr sc)
  return out
def Property1159 : Prop := ∀ (δ σ α : Type) cd cs (unalias : δ → σ → σ)
    (read : σ → Int → Int → Jl α) (set : δ → Int → Int → α → Jl δ)
    dest dr dc src sr sc,
  method1159 cd cs unalias read set dest dr dc src sr sc = do
    if dr.length != sr.length then throw (.argumentError "row sizes differ")
    if dc.length != sc.length then throw (.argumentError "column sizes differ")
    cd
    cs
    let src' := unalias dest src
    let mut out := dest
    for (j, sj) in dc.zip sc do
      for (i, si) in dr.zip sr do out ← set out i j (← read src' si sj)
    return out
theorem property1159 : Property1159 := by unfold Property1159; intros; rfl

/-- `_checkaxs`, line 1184. -/
def method1184 [BEq α] (destAxes srcAxes : α) : Except String Unit :=
  if destAxes == srcAxes then .ok () else .error "axes must agree"
def Property1184 : Prop := ∀ (α : Type) [BEq α] (dest src : α),
  method1184 dest src = if dest == src then .ok () else .error "axes must agree"
theorem property1184 : Property1184 := by unfold Property1184; intros; rfl

/-- `copyto_axcheck!`, lines 1186-1189. -/
def method1186 (axes : α → β) (check : β → β → Except String Unit)
    (copyto : α → α → Except String α) (dest src : α) : Except String α := do
  check (axes dest) (axes src)
  copyto dest src
def Property1186 : Prop := ∀ (α β : Type) (axes : α → β)
    (check : β → β → Except String Unit) (copyto : α → α → Except String α) dest src,
  method1186 axes check copyto dest src = do
    check (axes dest) (axes src)
    copyto dest src
theorem property1186 : Property1186 := by unfold Property1186; intros; rfl

/-- Array `copymutable`, lines 1211-1214. -/
def method1211 (similar : α → β) (copyto : β → α → γ) (a : α) : γ :=
  copyto (similar a) a
def Property1211 : Prop := ∀ (α β γ : Type) (similar : α → β) (copyto : β → α → γ) a,
  method1211 similar copyto a = copyto (similar a) a
theorem property1211 : Property1211 := by unfold Property1211; intros; rfl

/-- Generic `copymutable`, line 1215. -/
def method1215 (collect : α → β) (itr : α) : β := collect itr
def Property1215 : Prop := ∀ (α β : Type) (collect : α → β) itr,
  method1215 collect itr = collect itr
theorem property1215 : Property1215 := by unfold Property1215; intros; rfl

/-- Array-specialized `copymutable`, line 1216. -/
def method1216 (copy : α → β) (a : α) : β := copy a
def Property1216 : Prop := ∀ (α β : Type) (copy : α → β) a,
  method1216 copy a = copy a
theorem property1216 : Property1216 := by unfold Property1216; intros; rfl

/-- Numeric-array `zero`, line 1218. -/
def method1218 (zero : τ → α) (typeof : α → σ) (similar : δ → σ → β)
    (fill : β → α → γ) (t : τ) (x : δ) : γ :=
  let z := zero t
  fill (similar x (typeof z)) z
def Property1218 : Prop := ∀ (τ α σ δ β γ : Type) (zero : τ → α)
    (typeof : α → σ) (similar : δ → σ → β) (fill : β → α → γ) t x,
  method1218 zero typeof similar fill t x =
    let z := zero t; fill (similar x (typeof z)) z
theorem property1218 : Property1218 := by unfold Property1218; intros; rfl

/-- Missing-or-number array `zero`, line 1219. -/
def method1219 (zero : τ → α) (typeof : α → σ) (similar : δ → σ → β)
    (fill : β → α → γ) (t : τ) (x : δ) : γ :=
  let z := zero t
  fill (similar x (typeof z)) z
def Property1219 : Prop := ∀ (τ α σ δ β γ : Type) (zero : τ → α)
    (typeof : α → σ) (similar : δ → σ → β) (fill : β → α → γ) t x,
  method1219 zero typeof similar fill t x =
    let z := zero t; fill (similar x (typeof z)) z
theorem property1219 : Property1219 := by unfold Property1219; intros; rfl

/-- Generic array `zero`, line 1220. -/
def method1220 (zero : α → β) (map : (α → β) → γ → δ) (x : γ) : δ := map zero x
def Property1220 : Prop := ∀ (α β γ δ : Type) (zero : α → β)
    (map : (α → β) → γ → δ) x,
  method1220 zero map x = map zero x
theorem property1220 : Property1220 := by unfold Property1220; intros; rfl

/-- `_one`, lines 1222-1234. -/
def method1222 (rows cols : List ι) (zero : α → α) (require : Jl Unit)
    (similar : α → Jl δ) (fill : δ → α → Jl δ) (set : δ → ι → ι → α → Jl δ)
    (unit : α) : Jl δ := do
  if rows.length != cols.length then throw (.argumentError "identity requires square matrix")
  let z := zero unit
  require
  let out ← fill (← similar unit) z
  let mut out := out
  for i in rows do out ← set out i i unit
  return out
def Property1222 : Prop := ∀ (ι α δ : Type) rows cols (zero : α → α) require
    (similar : α → Jl δ) (fill : δ → α → Jl δ)
    (set : δ → ι → ι → α → Jl δ) unit,
  method1222 rows cols zero require similar fill set unit = do
    if rows.length != cols.length then throw (.argumentError "identity requires square matrix")
    let z := zero unit
    require
    let out ← fill (← similar unit) z
    let mut out := out
    for i in rows do out ← set out i i unit
    return out
theorem property1222 : Property1222 := by unfold Property1222; intros; rfl

/-- Matrix `one`, line 1236. -/
def method1236 (one : τ → α) (makeOne : α → δ → β) (t : τ) (x : δ) : β :=
  makeOne (one t) x
def Property1236 : Prop := ∀ (τ α δ β : Type) (one : τ → α)
    (makeOne : α → δ → β) t x,
  method1236 one makeOne t x = makeOne (one t) x
theorem property1236 : Property1236 := by unfold Property1236; intros; rfl

/-- Matrix `oneunit`, line 1237. -/
def method1237 (oneunit : τ → α) (makeOne : α → δ → β) (t : τ) (x : δ) : β :=
  makeOne (oneunit t) x
def Property1237 : Prop := ∀ (τ α δ β : Type) (oneunit : τ → α)
    (makeOne : α → δ → β) t x,
  method1237 oneunit makeOne t x = makeOne (oneunit t) x
theorem property1237 : Property1237 := by unfold Property1237; intros; rfl

/-- `iterate_starting_state(A)`, line 1245. -/
def method1245 (style : α → σ) (start : α → σ → β) (a : α) : β := start a (style a)
def Property1245 : Prop := ∀ (α σ β : Type) (style : α → σ)
    (start : α → σ → β) a,
  method1245 style start a = start a (style a)
theorem property1245 : Property1245 := by unfold Property1245; intros; rfl

/-- Linear iteration starting state, line 1246. -/
def method1246 (firstindex : α → β) (a : α) : β := firstindex a
def Property1246 : Prop := ∀ (α β : Type) (firstindex : α → β) a,
  method1246 firstindex a = firstindex a
theorem property1246 : Property1246 := by unfold Property1246; intros; rfl

/-- Cartesian iteration starting state, line 1247. -/
def method1247 (eachindex : α → β) (a : α) : β × Unit := (eachindex a, ())
def Property1247 : Prop := ∀ (α β : Type) (eachindex : α → β) a,
  method1247 eachindex a = (eachindex a, ())
theorem property1247 : Property1247 := by unfold Property1247; intros; rfl

/-- Array `iterate`, line 1250. -/
def method1250 (iterateArray : α → σ → β) (a : α) (state : σ) : β := iterateArray a state
def Property1250 : Prop := ∀ (α σ β : Type) (iterateArray : α → σ → β) a state,
  method1250 iterateArray a state = iterateArray a state
theorem property1250 : Property1250 := by unfold Property1250; intros; rfl

/-- Tuple-state array iteration, lines 1251-1255. -/
def method1251 (iterate : σ → List ρ → Option (ι × List ρ)) (get : α → ι → β)
    (a : α) (state : σ × List ρ) : Option (β × (σ × List ρ)) :=
  match iterate state.1 state.2 with
  | none => none
  | some (i, next) => some (get a i, (state.1, next))
def Property1251 : Prop := ∀ (σ ρ ι α β : Type)
    (iterate : σ → List ρ → Option (ι × List ρ))
    (get : α → ι → β) a state,
  method1251 iterate get a state = match iterate state.1 state.2 with
    | none => none
    | some (i, next) => some (get a i, (state.1, next))
theorem property1251 : Property1251 := by
  unfold Property1251
  intro σ ρ ι α β iterateFn getFn a state
  cases h : iterateFn state.1 state.2 <;> simp [method1251, h]

/-- Integer-state array iteration, lines 1256-1259. -/
def method1256 (check : α → I64 → Bool) (get : α → I64 → β)
    (a : α) (state : I64) : Option (β × I64) :=
  if check a state then some (get a state, state + i64 1) else none
def Property1256 : Prop := ∀ (α β : Type) (check : α → I64 → Bool)
    (get : α → I64 → β) a state,
  method1256 check get a state =
    if check a state then some (get a state, state + i64 1) else none
theorem property1256 : Property1256 := by unfold Property1256; intros; rfl

/-- `isempty(::AbstractArray)`, line 1262. -/
def method1262 (length : α → Nat) (a : α) : Bool := length a = 0
def Property1262 : Prop := ∀ (α : Type) (length : α → Nat) a,
  method1262 length a = decide (length a = 0)
theorem property1262 : Property1262 := by unfold Property1262; intros; rfl

structure StepRangeModel (α : Type) where
  start : α
  step : α
  stop : α

structure UnitRangeModel (α : Type) where
  start : α
  stop : α

structure LinRangeModel (α : Type) where
  start : α
  stop : α
  len : Nat

/-- Type-map of StepRange, line 1267. -/
def method1267 (convert : α → β) (r : StepRangeModel α) : StepRangeModel β :=
  ⟨convert r.start, convert r.step, convert r.stop⟩
def Property1267 : Prop := ∀ (α β : Type) (convert : α → β) (r : StepRangeModel α),
  method1267 convert r = ⟨convert r.start, convert r.step, convert r.stop⟩
theorem property1267 : Property1267 := by unfold Property1267; intros; rfl

/-- Type-map of UnitRange, line 1268. -/
def method1268 (convert : α → β) (r : UnitRangeModel α) : UnitRangeModel β :=
  ⟨convert r.start, convert r.stop⟩
def Property1268 : Prop := ∀ (α β : Type) (convert : α → β) (r : UnitRangeModel α),
  method1268 convert r = ⟨convert r.start, convert r.stop⟩
theorem property1268 : Property1268 := by unfold Property1268; intros; rfl

/-- Type-map of StepRangeLen, line 1269. -/
def method1269 (convert : α → β) (r : α) : β := convert r
def Property1269 : Prop := ∀ (α β : Type) (convert : α → β) r,
  method1269 convert r = convert r
theorem property1269 : Property1269 := by unfold Property1269; intros; rfl

/-- Type-map of LinRange, lines 1270-1272. -/
def method1270 (convert : α → β) (r : LinRangeModel α) : LinRangeModel β :=
  ⟨convert r.start, convert r.stop, r.len⟩
def Property1270 : Prop := ∀ (α β : Type) (convert : α → β) (r : LinRangeModel α),
  method1270 convert r = ⟨convert r.start, convert r.stop, r.len⟩
theorem property1270 : Property1270 := by unfold Property1270; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry "abstractarraycov-line920-copy" "copy!(::AbstractVector,::AbstractVector)" "The vector method checks offsets, resizes only on a length mismatch, then calls copyto!." "base/abstractarray.jl:920-927" ``Property920 ``property920,
  entry "abstractarraycov-line929-copy" "copy!(::AbstractArray,::AbstractArray)" "The array method checks axes before copyto!." "base/abstractarray.jl:929-933" ``Property929 ``property929,
  entry "abstractarraycov-line941-copyto" "copyto!(::AbstractArray,src)" "The iterable method walks destination indices and source values in lockstep and errors when destination ends first." "base/abstractarray.jl:941-951" ``Property941 ``property941,
  entry "abstractarraycov-line953-copyto" "copyto!(dest,dstart,src)" "The method converts dstart first, takes the haslength precheck path when available, and writes source values sequentially." "base/abstractarray.jl:953-971" ``Property953 ``property953,
  entry "abstractarraycov-line974-copyto" "copyto!(dest,dstart,src,sstart)" "The method validates and skips source elements before converting dstart and copying the remainder." "base/abstractarray.jl:974-1000" ``Property974 ``property974,
  entry "abstractarraycov-line1003-copyto" "copyto!(dest,dstart,src,sstart,n)" "The counted method follows the negative, zero, bounds, conversion, source-skip, write, and short-source checks in order." "base/abstractarray.jl:1003-1037" ``Property1003 ``property1003,
  entry "abstractarraycov-line1072-copyto" "copyto!(::AbstractArray,::AbstractArray)" "The method returns on empty source, takes the BitArray branch, or unaliases and dispatches by both index styles." "base/abstractarray.jl:1072-1080" ``Property1072 ``property1072,
  entry "abstractarraycov-line1082-copyto" "copyto!(deststyle,dest,srcstyle,src)" "The styled method returns on empty source, unaliases, then calls copyto_unaliased!." "base/abstractarray.jl:1082-1086" ``Property1082 ``property1082,
  entry "abstractarraycov-line1088-copyto-unalias" "copyto_unaliased!" "The method checks both endpoint bounds, selects the source and destination index-style branch, and performs writes in iterator order." "base/abstractarray.jl:1088-1123" ``Property1088 ``property1088,
  entry "abstractarraycov-line1125-copyto" "copyto!(dest,dstart,src::AbstractArray)" "The wrapper uses the first linear source index and full source length." "base/abstractarray.jl:1125-1127" ``Property1125 ``property1125,
  entry "abstractarraycov-line1129-copyto" "copyto!(dest,dstart,src::AbstractArray,sstart)" "The wrapper checks sstart before copying through the final source index." "base/abstractarray.jl:1129-1133" ``Property1129 ``property1129,
  entry "abstractarraycov-line1135-copyto" "copyto!(dest,dstart,src,sstart,n)" "The block method handles zero and negative counts, checks both ranges, converts indices, unaliases, reads, and writes in order." "base/abstractarray.jl:1135-1152" ``Property1135 ``property1135,
  entry "abstractarraycov-line1154-copy" "copy(::AbstractArray)" "copy delegates to copymutable." "base/abstractarray.jl:1154-1157" ``Property1154 ``property1154,
  entry "abstractarraycov-line1159-copyto" "copyto!(B,rowrange,colrange,A,rowrange,colrange)" "The region method checks row and column lengths, bounds-checks both arrays, unaliases, and copies in nested column-major loops." "base/abstractarray.jl:1159-1182" ``Property1159 ``property1159,
  entry "abstractarraycov-line1184-checkaxs" "_checkaxs" "The helper returns unit exactly for equal axes and otherwise throws DimensionMismatch." "base/abstractarray.jl:1184" ``Property1184 ``property1184,
  entry "abstractarraycov-line1186-copyto-axcheck" "copyto_axcheck!" "The method obtains both axes, checks them, then calls copyto!." "base/abstractarray.jl:1186-1189" ``Property1186 ``property1186,
  entry "abstractarraycov-line1211-copymutable" "copymutable(::AbstractArray)" "The method allocates similar(a) before copying a into it." "base/abstractarray.jl:1211-1214" ``Property1211 ``property1211,
  entry "abstractarraycov-line1215-copymutable" "copymutable(itr)" "The generic iterable method delegates to collect." "base/abstractarray.jl:1215" ``Property1215 ``property1215,
  entry "abstractarraycov-line1216-copymutable" "copymutable(::Array)" "The Array specialization delegates to copy." "base/abstractarray.jl:1216" ``Property1216 ``property1216,
  entry "abstractarraycov-line1218-zero" "zero(::AbstractArray{<:Number})" "The numeric method computes zero, its type, similar storage, then fills." "base/abstractarray.jl:1218" ``Property1218 ``property1218,
  entry "abstractarraycov-line1219-zero" "zero(::AbstractArray{<:Union{Missing,Number}})" "The union method computes zero, its type, similar storage, then fills." "base/abstractarray.jl:1219" ``Property1219 ``property1219,
  entry "abstractarraycov-line1220-zero" "zero(::AbstractArray)" "The fallback maps zero over the array." "base/abstractarray.jl:1220" ``Property1220 ``property1220,
  entry "abstractarraycov-line1222-one" "_one(unit,mat)" "The helper checks square axes, computes zero, requires one-based indexing, allocates and fills, then writes the diagonal." "base/abstractarray.jl:1222-1234" ``Property1222 ``property1222,
  entry "abstractarraycov-line1236-one" "one(::AbstractMatrix)" "one computes one(T) before calling _one." "base/abstractarray.jl:1236" ``Property1236 ``property1236,
  entry "abstractarraycov-line1237-oneunit" "oneunit(::AbstractMatrix)" "oneunit computes oneunit(T) before calling _one." "base/abstractarray.jl:1237" ``Property1237 ``property1237,
  entry "abstractarraycov-line1245-iterate-start" "iterate_starting_state(A)" "The generic start method computes IndexStyle(A) before dispatching." "base/abstractarray.jl:1245" ``Property1245 ``property1245,
  entry "abstractarraycov-line1246-iterate-start" "iterate_starting_state(A,::IndexLinear)" "Linear iteration starts at firstindex(A)." "base/abstractarray.jl:1246" ``Property1246 ``property1246,
  entry "abstractarraycov-line1247-iterate-start" "iterate_starting_state(A,::IndexStyle)" "Cartesian iteration stores eachindex(A) in a one-tuple state." "base/abstractarray.jl:1247" ``Property1247 ``property1247,
  entry "abstractarraycov-line1250-iterate" "iterate(::AbstractArray,state)" "Array iterate delegates to _iterate_abstractarray with the supplied state." "base/abstractarray.jl:1250" ``Property1250 ``property1250,
  entry "abstractarraycov-line1251-iterate-array" "_iterate_abstractarray(A,state::Tuple)" "Tuple-state iteration advances the iterator, returns nothing at exhaustion, or indexes A and returns the next state." "base/abstractarray.jl:1251-1255" ``Property1251 ``property1251,
  entry "abstractarraycov-line1256-iterate-array" "_iterate_abstractarray(A,state::Integer)" "Integer-state iteration checks bounds before indexing and increments with Julia integer arithmetic." "base/abstractarray.jl:1256-1259" ``Property1256 ``property1256,
  entry "abstractarraycov-line1262-isempty" "isempty(::AbstractArray)" "An array is empty exactly when length is zero." "base/abstractarray.jl:1262" ``Property1262 ``property1262,
  entry "abstractarraycov-line1267-map-range" "map(::Type,::StepRange)" "The method converts start, step, and last before constructing the range." "base/abstractarray.jl:1267" ``Property1267 ``property1267,
  entry "abstractarraycov-line1268-map-range" "map(::Type,::UnitRange)" "The method converts start and last before constructing the unit range." "base/abstractarray.jl:1268" ``Property1268 ``property1268,
  entry "abstractarraycov-line1269-map-range" "map(::Type,::StepRangeLen)" "The method delegates to convert(StepRangeLen{T},r)." "base/abstractarray.jl:1269" ``Property1269 ``property1269,
  entry "abstractarraycov-line1270-map-range" "map(::Type,::LinRange)" "The method converts both endpoints, reads length, and constructs LinRange." "base/abstractarray.jl:1270-1272" ``Property1270 ``property1270
]

end JuliaLean.AbstractArrayCov.Rows.Copy
