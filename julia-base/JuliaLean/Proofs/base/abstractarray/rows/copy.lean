import JuliaLean.base.abstractarray
import JuliaLean.Proofs.base.abstractarray.rows.bounds_shape


namespace JuliaLean.AbstractArrayCov.Rows.Copy

open JuliaLean
open JuliaLean.Registry

def Property920 : Prop := ∀ (α : Type) (firstindex : α → Int) (length : α → Nat)
    (resize : α → Nat → Jl α) (copyto : α → α → Jl α) dst src,
  method920 firstindex length resize copyto dst src = do
    if firstindex dst != firstindex src then
      throw (.argumentError "vectors must have the same offset for copy! (consider using `copyto!`)")
    let dst ← if length dst != length src then resize dst (length src) else .ok dst
    copyto dst src
theorem property920 : Property920 := by unfold Property920; intros; rfl

def Property929 : Prop := ∀ (α β : Type) [BEq β] (axes : α → β)
    (copyto : α → α → Jl α) dst src,
  method929 axes copyto dst src = do
    if axes dst != axes src then
      throw (JlError.argumentError "arrays must have the same axes for copy! (consider using `copyto!`)")
    copyto dst src
theorem property929 : Property929 := by unfold Property929; intros; rfl

def Property941 : Prop := ∀ (δ ι α : Type) (eachindex : δ → List ι)
    (set : δ → ι → α → Jl δ) dest src,
  method941 eachindex set dest src =
    if src.length ≤ (eachindex dest).length then writePairs set dest ((eachindex dest).zip src)
    else .error (.argumentError "destination has fewer elements than required")
theorem property941 : Property941 := by unfold Property941; intros; rfl

def Property953 : Prop := ∀ (δ α : Type) hasLength destLength lastindex
    (checkbounds : I64 → Jl Unit) (set : δ → I64 → α → Jl δ) dest dstart src,
  method953 hasLength destLength lastindex checkbounds set dest dstart src = do
    let i ← JInt.convert (IntTy.i64.name) .i64 dstart
    if hasLength && destLength > 0 then
      if src.isEmpty then return dest
      checkbounds i
      if ¬((src.length : Int) ≤ lastindex.val - i.val + 1) then throw .boundsError
      writeSeq set dest i src
    else writeSeq set dest i src
theorem property953 : Property953 := by unfold Property953; intros; rfl

def Property974 : Prop := ∀ (δ α : Type) (set : δ → I64 → α → Jl δ)
    dest dstart sstart src,
  method974 set dest dstart sstart src = do
    if sstart < 1 then throw (.argumentError "source start offset is < 1")
    if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
    let i ← JInt.convert (IntTy.i64.name) .i64 dstart
    writeSeq set dest i (src.drop (sstart - 1).toNat)
theorem property974 : Property974 := by unfold Property974; intros; rfl

def Property1003 : Prop := ∀ (δ α : Type) (contains : Int → Bool) last
    (set : δ → I64 → α → Jl δ) dest dstart src sstart n,
  method1003 contains last set dest dstart src sstart n = do
    if n < 0 then throw (.argumentError "elements to copy should be non-negative")
    if n = 0 then return dest
    if sstart < 1 then throw (.argumentError "source start offset is < 1")
    if !(contains dstart && n ≤ last - dstart + 1) then throw .boundsError
    let d ← JInt.convert (IntTy.i64.name) .i64 dstart
    let n64 ← JInt.convert (IntTy.i64.name) .i64 n
    if src.length < sstart.toNat then throw (.argumentError "source has fewer elements than required")
    let values := (src.drop (sstart - 1).toNat).take n64.val.toNat
    let dest ← writeSeq set dest d values
    if values.length < n64.val.toNat then throw .boundsError
    return dest
theorem property1003 : Property1003 := by unfold Property1003; intros; rfl

def Property1072 : Prop := ∀ (δ σ ι κ : Type) isempty isBit
    (bitcopy : δ → σ → Jl δ) (unalias : δ → σ → σ) (styleDest : δ → ι)
    (styleSrc : σ → κ) (copyU : ι → δ → κ → σ → Jl δ) dest src,
  method1072 isempty isBit bitcopy unalias styleDest styleSrc copyU dest src = do
    if isempty then return dest
    if isBit then return ← bitcopy dest src
    let src' := unalias dest src
    copyU (styleDest dest) dest (styleSrc src') src'
theorem property1072 : Property1072 := by unfold Property1072; intros; rfl

def Property1082 : Prop := ∀ (δ σ ι κ : Type) isempty (unalias : δ → σ → σ)
    (copyU : ι → δ → κ → σ → Jl δ) ds dest ss src,
  method1082 isempty unalias copyU ds dest ss src = do
    if isempty then return dest
    let src' := unalias dest src
    copyU ds dest ss src'
theorem property1082 : Property1082 := by unfold Property1082; intros; rfl

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

def Property1125 : Prop := ∀ (δ σ : Type) (linear : σ → List Int) (length : σ → Int)
    (copy : δ → Int → σ → Int → Int → Jl δ) dest dstart src,
  method1125 linear length copy dest dstart src = match linear src with
    | [] => copy dest dstart src 1 (length src)
    | first :: _ => copy dest dstart src first (length src)
theorem property1125 : Property1125 := by
  unfold Property1125
  intro δ σ linearFn lengthFn copyFn dest dstart src
  cases h : linearFn src <;> simp [method1125, h]

def Property1129 : Prop := ∀ (δ σ : Type) (linear : σ → List Int)
    (check : List Int → Int → Bool) (copy : δ → Int → σ → Int → Int → Jl δ)
    dest dstart src sstart,
  method1129 linear check copy dest dstart src sstart = do
    let inds := linear src
    if !check inds sstart then throw .boundsError
    let last := inds.getLast?.getD 0
    copy dest dstart src sstart (last - sstart + 1)
theorem property1129 : Property1129 := by unfold Property1129; intros; rfl

def Property1135 : Prop := ∀ (δ σ α : Type) (db sb : Int → Int → Bool) dl sl
    (unalias : δ → σ → σ) (read : σ → Int → Jl α) (set : δ → I64 → α → Jl δ)
    dest dstart src sstart n,
  method1135 db sb dl sl unalias read set dest dstart src sstart n = do
    if n = 0 then return dest
    if n < 0 then throw (.argumentError "elements to copy should be non-negative")
    if !(db dstart n && n ≤ dl - dstart + 1) then throw .boundsError
    if !(sb sstart n && n ≤ sl - sstart + 1) then throw .boundsError
    let d ← JInt.convert (IntTy.i64.name) .i64 dstart
    let src' := unalias dest src
    let values ← (List.range n.toNat).mapM fun (k : Nat) => read src' (sstart + (k : Int))
    writeSeq set dest d values
theorem property1135 : Property1135 := by unfold Property1135; intros; rfl

def Property1154 : Prop := ∀ (α β : Type) (copymutable : α → β) a,
  method1154 copymutable a = copymutable a
theorem property1154 : Property1154 := by unfold Property1154; intros; rfl

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

def Property1184 : Prop := ∀ (α : Type) [BEq α] (dest src : α),
  method1184 dest src = if dest == src then .ok () else .error "axes must agree"
theorem property1184 : Property1184 := by unfold Property1184; intros; rfl

def Property1186 : Prop := ∀ (α β : Type) (axes : α → β)
    (check : β → β → Except String Unit) (copyto : α → α → Except String α) dest src,
  method1186 axes check copyto dest src = do
    check (axes dest) (axes src)
    copyto dest src
theorem property1186 : Property1186 := by unfold Property1186; intros; rfl

def Property1211 : Prop := ∀ (α β γ : Type) (similar : α → β) (copyto : β → α → γ) a,
  method1211 similar copyto a = copyto (similar a) a
theorem property1211 : Property1211 := by unfold Property1211; intros; rfl

def Property1215 : Prop := ∀ (α β : Type) (collect : α → β) itr,
  method1215 collect itr = collect itr
theorem property1215 : Property1215 := by unfold Property1215; intros; rfl

def Property1216 : Prop := ∀ (α β : Type) (copy : α → β) a,
  method1216 copy a = copy a
theorem property1216 : Property1216 := by unfold Property1216; intros; rfl

def Property1218 : Prop := ∀ (τ α σ δ β γ : Type) (zero : τ → α)
    (typeof : α → σ) (similar : δ → σ → β) (fill : β → α → γ) t x,
  method1218 zero typeof similar fill t x =
    let z := zero t; fill (similar x (typeof z)) z
theorem property1218 : Property1218 := by unfold Property1218; intros; rfl

def Property1219 : Prop := ∀ (τ α σ δ β γ : Type) (zero : τ → α)
    (typeof : α → σ) (similar : δ → σ → β) (fill : β → α → γ) t x,
  method1219 zero typeof similar fill t x =
    let z := zero t; fill (similar x (typeof z)) z
theorem property1219 : Property1219 := by unfold Property1219; intros; rfl

def Property1220 : Prop := ∀ (α β γ δ : Type) (zero : α → β)
    (map : (α → β) → γ → δ) x,
  method1220 zero map x = map zero x
theorem property1220 : Property1220 := by unfold Property1220; intros; rfl

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

def Property1236 : Prop := ∀ (τ α δ β : Type) (one : τ → α)
    (makeOne : α → δ → β) t x,
  method1236 one makeOne t x = makeOne (one t) x
theorem property1236 : Property1236 := by unfold Property1236; intros; rfl

def Property1237 : Prop := ∀ (τ α δ β : Type) (oneunit : τ → α)
    (makeOne : α → δ → β) t x,
  method1237 oneunit makeOne t x = makeOne (oneunit t) x
theorem property1237 : Property1237 := by unfold Property1237; intros; rfl

def Property1245 : Prop := ∀ (α σ β : Type) (style : α → σ)
    (start : α → σ → β) a,
  method1245 style start a = start a (style a)
theorem property1245 : Property1245 := by unfold Property1245; intros; rfl

def Property1246 : Prop := ∀ (α β : Type) (firstindex : α → β) a,
  method1246 firstindex a = firstindex a
theorem property1246 : Property1246 := by unfold Property1246; intros; rfl

def Property1247 : Prop := ∀ (α β : Type) (eachindex : α → β) a,
  method1247 eachindex a = (eachindex a, ())
theorem property1247 : Property1247 := by unfold Property1247; intros; rfl

def Property1250 : Prop := ∀ (α σ β : Type) (iterateArray : α → σ → β) a state,
  method1250 iterateArray a state = iterateArray a state
theorem property1250 : Property1250 := by unfold Property1250; intros; rfl

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

def Property1256 : Prop := ∀ (α β : Type) (check : α → I64 → Bool)
    (get : α → I64 → β) a state,
  method1256 check get a state =
    if check a state then some (get a state, state + i64 1) else none
theorem property1256 : Property1256 := by unfold Property1256; intros; rfl

def Property1262 : Prop := ∀ (α : Type) (length : α → Nat) a,
  method1262 length a = decide (length a = 0)
theorem property1262 : Property1262 := by unfold Property1262; intros; rfl

def Property1267 : Prop := ∀ (α β : Type) (convert : α → β) (r : StepRangeModel α),
  method1267 convert r = ⟨convert r.start, convert r.step, convert r.stop⟩
theorem property1267 : Property1267 := by unfold Property1267; intros; rfl

def Property1268 : Prop := ∀ (α β : Type) (convert : α → β) (r : UnitRangeModel α),
  method1268 convert r = ⟨convert r.start, convert r.stop⟩
theorem property1268 : Property1268 := by unfold Property1268; intros; rfl

def Property1269 : Prop := ∀ (α β : Type) (convert : α → β) r,
  method1269 convert r = convert r
theorem property1269 : Property1269 := by unfold Property1269; intros; rfl

def Property1270 : Prop := ∀ (α β : Type) (convert : α → β) (r : LinRangeModel α),
  method1270 convert r = ⟨convert r.start, convert r.stop, r.len⟩
theorem property1270 : Property1270 := by unfold Property1270; intros; rfl

private def entry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/abstractarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.AbstractArrayCov.Rows.Copy
