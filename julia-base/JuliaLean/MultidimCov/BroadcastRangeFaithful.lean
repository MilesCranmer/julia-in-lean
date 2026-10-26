import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastRangeFaithful

open JuliaLean.Registry

inductive Error where | arithmetic | construction deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure RangeView (α : Type) where
  first : α
  last : α
  step : α
  ref : α
  start : α
  stop : α
  len : Nat
  offset : Nat
  deriving Repr, DecidableEq

inductive RangeOut (α : Type) where
  | original (range : RangeView α)
  | generic (start step : α) (len : Nat)
  | ordinal (first last step : α)
  | unit (first last : α)
  | stepLen (typeName : String) (ref step : α) (len offset : Nat)
  | lin (start stop : α) (len : Nat)
  | cartesian (ranges : List (RangeOut α)) (reversed : Bool)
  deriving Repr

structure Ops (α : Type) where
  neg : α → Result α
  negateStep : α → Result α
  add : α → α → Result α
  sub : α → α → Result α
  mul : α → α → Result α
  div : α → α → Result α
  ldiv : α → α → Result α
  big : α → Result α
  convertRef : α → Result α
  typeOf : α → Result String
  pairAdd : RangeView α → RangeView α → Result (RangeOut α)
  pairSub : RangeView α → RangeView α → Result (RangeOut α)

def m1176 (r : RangeView α) : RangeOut α := .original r
def P1176 : Prop := ∀ {α : Type} (r : RangeView α), m1176 r = .original r
theorem p1176 : P1176 := by simp [P1176, m1176]

def m1178 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.generic (← ops.neg r.first) (← ops.negateStep r.step) r.len)
def P1178 : Prop := ∀ {α} (ops : Ops α) r,
  m1178 ops r = do pure (.generic (← ops.neg r.first) (← ops.negateStep r.step) r.len)
theorem p1178 : P1178 := by simp [P1178, m1178]

def m1179 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.ordinal (← ops.neg r.first) (← ops.neg r.last) (← ops.negateStep r.step))
def P1179 : Prop := ∀ {α} (ops : Ops α) r,
  m1179 ops r = do pure (.ordinal (← ops.neg r.first) (← ops.neg r.last) (← ops.negateStep r.step))
theorem p1179 : P1179 := by simp [P1179, m1179]

def m1180 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.stepLen "inferred" (← ops.neg r.ref) (← ops.negateStep r.step) r.len r.offset)
def P1180 : Prop := ∀ {α} (ops : Ops α) r,
  m1180 ops r = do pure (.stepLen "inferred" (← ops.neg r.ref) (← ops.negateStep r.step) r.len r.offset)
theorem p1180 : P1180 := by simp [P1180, m1180]

def m1181 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.lin (← ops.neg r.start) (← ops.neg r.stop) r.len)
def P1181 : Prop := ∀ {α} (ops : Ops α) r,
  m1181 ops r = do pure (.lin (← ops.neg r.start) (← ops.neg r.stop) r.len)
theorem p1181 : P1181 := by simp [P1181, m1181]

def genericBinary (op : α → α → Result α) (left : Bool) (r : RangeView α) (x : α)
    (negateStep : Bool) (ops : Ops α) : Result (RangeOut α) := do
  let start ← if left then op x r.first else op r.first x
  let step ← if negateStep then ops.negateStep r.step else pure r.step
  pure (.generic start step r.len)

def ordinalBinary (op : α → α → Result α) (left : Bool) (r : RangeView α) (x : α)
    (negateStep : Bool) (ops : Ops α) : Result (RangeOut α) := do
  let first ← if left then op x r.first else op r.first x
  let last ← if left then op x r.last else op r.last x
  let step ← if negateStep then ops.negateStep r.step else pure r.step
  pure (.ordinal first last step)

def unitBinary (op : α → α → Result α) (left : Bool) (r : RangeView α) (x : α) : Result (RangeOut α) := do
  pure (.unit (← if left then op x r.first else op r.first x)
    (← if left then op x r.last else op r.last x))

def linBinary (op : α → α → Result α) (left : Bool) (r : RangeView α) (x : α) : Result (RangeOut α) := do
  pure (.lin (← if left then op x r.start else op r.start x)
    (← if left then op x r.stop else op r.stop x) r.len)

def stepBinary (op : α → α → Result α) (left : Bool) (r : RangeView α) (x : α)
    (stepOp : α → Result α) (ops : Ops α) : Result (RangeOut α) := do
  let converted ← ops.convertRef r.ref
  let probe ← if left then op x converted else op converted x
  let typeName ← ops.typeOf probe
  let ref ← if left then op x r.ref else op r.ref x
  pure (.stepLen typeName ref (← stepOp r.step) r.len r.offset)

def m1184 (ops : Ops α) (r : RangeView α) x := genericBinary ops.add false r x false ops
def m1185 (ops : Ops α) x (r : RangeView α) := genericBinary ops.add true r x false ops
def m1186 (ops : Ops α) (r : RangeView α) x := ordinalBinary ops.add false r x false ops
def m1187 (ops : Ops α) x (r : RangeView α) := ordinalBinary ops.add true r x false ops
def m1188 (ops : Ops α) (r : RangeView α) x := unitBinary ops.add false r x
def m1189 (ops : Ops α) x (r : RangeView α) := unitBinary ops.add true r x
def m1190 (ops : Ops α) (r : RangeView α) (x : α) : Result (RangeOut α) := do
  pure (.generic (← ops.add r.first x) r.step r.len)
def m1191 (ops : Ops α) (x : α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.generic (← ops.add x r.first) r.step r.len)
def m1192 (ops : Ops α) (r : RangeView α) x := stepBinary ops.add false r x pure ops
def m1194 (ops : Ops α) x (r : RangeView α) := stepBinary ops.add true r x pure ops
def m1196 (ops : Ops α) (r : RangeView α) x := linBinary ops.add false r x
def m1197 (ops : Ops α) x (r : RangeView α) := linBinary ops.add true r x
def m1198 (ops : Ops α) (r1 r2 : RangeView α) := ops.pairAdd r1 r2

def m1200 (ops : Ops α) (r : RangeView α) x := genericBinary ops.sub false r x false ops
def m1201 (ops : Ops α) x (r : RangeView α) := genericBinary ops.sub true r x true ops
def m1202 (ops : Ops α) (r : RangeView α) x := ordinalBinary ops.sub false r x false ops
def m1203 (ops : Ops α) x (r : RangeView α) := ordinalBinary ops.sub true r x true ops
def m1204 (ops : Ops α) (r : RangeView α) x := unitBinary ops.sub false r x
def m1205 (ops : Ops α) (r : RangeView α) (x : α) : Result (RangeOut α) := do
  pure (.generic (← ops.sub r.first x) r.step r.len)
def m1206 (ops : Ops α) (r : RangeView α) x := stepBinary ops.sub false r x pure ops
def m1208 (ops : Ops α) x (r : RangeView α) := stepBinary ops.sub true r x ops.negateStep ops
def m1210 (ops : Ops α) (r : RangeView α) x := linBinary ops.sub false r x
def m1211 (ops : Ops α) x (r : RangeView α) := linBinary ops.sub true r x
def m1212 (ops : Ops α) (r1 r2 : RangeView α) := ops.pairSub r1 r2

def mulGeneric (op : α → α → Result α) (left : Bool) (_ops : Ops α)
    (r : RangeView α) (x : α) : Result (RangeOut α) := do
  pure (.stepLen "inferred" (← if left then op x r.first else op r.first x)
    (← if left then op x r.step else op r.step x) r.len 1)
def m1215 (ops : Ops α) x (r : RangeView α) := mulGeneric ops.mul true ops r x
def m1216 (ops : Ops α) x (r : RangeView α) := stepBinary ops.mul true r x (ops.mul x) ops
def m1218 (ops : Ops α) x (r : RangeView α) := linBinary ops.mul true r x
def m1219 (ops : Ops α) x (r : RangeView α) := mulGeneric ops.mul true ops r x
def m1222 (ops : Ops α) (r : RangeView α) x := mulGeneric ops.mul false ops r x
def m1223 (ops : Ops α) (r : RangeView α) x := stepBinary ops.mul false r x (fun s => ops.mul s x) ops
def m1225 (ops : Ops α) (r : RangeView α) x := linBinary ops.mul false r x
def m1226 (ops : Ops α) (r : RangeView α) x := mulGeneric ops.mul false ops r x
def m1230 (ops : Ops α) (r : RangeView α) x := genericBinary ops.div false r x false ops
def m1231 (ops : Ops α) (r : RangeView α) x := stepBinary ops.div false r x (fun s => ops.div s x) ops
def m1233 (ops : Ops α) (r : RangeView α) x := linBinary ops.div false r x
def m1235 (ops : Ops α) x (r : RangeView α) := genericBinary ops.ldiv true r x false ops
def m1236 (ops : Ops α) (x : α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.stepLen "inferred" (← ops.ldiv x r.ref) (← ops.ldiv x r.step) r.len r.offset)
def m1237 (ops : Ops α) x (r : RangeView α) := linBinary ops.ldiv true r x

def m1239 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.unit (← ops.big r.start) (← ops.big r.last))
def m1240 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.ordinal (← ops.big r.start) (← ops.big r.last) (← ops.big r.step))
def m1241 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.stepLen "big" (← ops.big r.ref) (← ops.big r.step) r.len r.offset)
def m1242 (ops : Ops α) (r : RangeView α) : Result (RangeOut α) := do
  pure (.lin (← ops.big r.start) (← ops.big r.stop) r.len)

def mapRanges (op : α → α → Result α) (ranges : List (RangeView α))
    (offsets : List α) (left : Bool) : Result (List (RangeOut α)) :=
  (ranges.zip offsets).mapM fun pair => do
    pure (.generic (← if left then op pair.2 pair.1.first else op pair.1.first pair.2) pair.1.step pair.1.len)
def m1245 (ops : Ops α) (ranges : List (RangeView α)) (offsets : List α) : Result (RangeOut α) := do
  pure (.cartesian (← mapRanges ops.add ranges offsets false) false)
def m1247 (ops : Ops α) (offsets : List α) (ranges : List (RangeView α)) := m1245 ops ranges offsets
def m1249 (ops : Ops α) (ranges : List (RangeView α)) (offsets : List α) : Result (RangeOut α) := do
  pure (.cartesian (← mapRanges ops.sub ranges offsets false) false)
def diffrange (ops : Ops α) (offset : α) (range : RangeView α) : Result (RangeOut α) := do
  pure (.generic (← ops.sub offset range.last) range.step range.len)
def m1251 (ops : Ops α) (offsets : List α) (ranges : List (RangeView α)) : Result (RangeOut α) := do
  pure (.cartesian (← (offsets.zip ranges).mapM fun pair => diffrange ops pair.1 pair.2) true)
def m1252 (ops : Ops α) (offset : α) (range : RangeView α) := diffrange ops offset range

def P1184 : Prop := ∀ {α} (ops : Ops α) r x, m1184 ops r x = genericBinary ops.add false r x false ops
theorem p1184 : P1184 := by simp [P1184, m1184]
def P1185 : Prop := ∀ {α} (ops : Ops α) x r, m1185 ops x r = genericBinary ops.add true r x false ops
theorem p1185 : P1185 := by simp [P1185, m1185]
def P1186 : Prop := ∀ {α} (ops : Ops α) r x, m1186 ops r x = ordinalBinary ops.add false r x false ops
theorem p1186 : P1186 := by simp [P1186, m1186]
def P1187 : Prop := ∀ {α} (ops : Ops α) x r, m1187 ops x r = ordinalBinary ops.add true r x false ops
theorem p1187 : P1187 := by simp [P1187, m1187]
def P1188 : Prop := ∀ {α} (ops : Ops α) r x, m1188 ops r x = unitBinary ops.add false r x
theorem p1188 : P1188 := by simp [P1188, m1188]
def P1189 : Prop := ∀ {α} (ops : Ops α) x r, m1189 ops x r = unitBinary ops.add true r x
theorem p1189 : P1189 := by simp [P1189, m1189]
def P1190 : Prop := ∀ {α} (ops : Ops α) r x, m1190 ops r x = do pure (.generic (← ops.add r.first x) r.step r.len)
theorem p1190 : P1190 := by simp [P1190, m1190]
def P1191 : Prop := ∀ {α} (ops : Ops α) x r, m1191 ops x r = do pure (.generic (← ops.add x r.first) r.step r.len)
theorem p1191 : P1191 := by simp [P1191, m1191]
def P1192 : Prop := ∀ {α} (ops : Ops α) r x, m1192 ops r x = stepBinary ops.add false r x pure ops
theorem p1192 : P1192 := by simp [P1192, m1192]
def P1194 : Prop := ∀ {α} (ops : Ops α) x r, m1194 ops x r = stepBinary ops.add true r x pure ops
theorem p1194 : P1194 := by simp [P1194, m1194]
def P1196 : Prop := ∀ {α} (ops : Ops α) r x, m1196 ops r x = linBinary ops.add false r x
theorem p1196 : P1196 := by simp [P1196, m1196]
def P1197 : Prop := ∀ {α} (ops : Ops α) x r, m1197 ops x r = linBinary ops.add true r x
theorem p1197 : P1197 := by simp [P1197, m1197]
def P1198 : Prop := ∀ {α} (ops : Ops α) r1 r2, m1198 ops r1 r2 = ops.pairAdd r1 r2
theorem p1198 : P1198 := by simp [P1198, m1198]
def P1200 : Prop := ∀ {α} (ops : Ops α) r x, m1200 ops r x = genericBinary ops.sub false r x false ops
theorem p1200 : P1200 := by simp [P1200, m1200]
def P1201 : Prop := ∀ {α} (ops : Ops α) x r, m1201 ops x r = genericBinary ops.sub true r x true ops
theorem p1201 : P1201 := by simp [P1201, m1201]
def P1202 : Prop := ∀ {α} (ops : Ops α) r x, m1202 ops r x = ordinalBinary ops.sub false r x false ops
theorem p1202 : P1202 := by simp [P1202, m1202]
def P1203 : Prop := ∀ {α} (ops : Ops α) x r, m1203 ops x r = ordinalBinary ops.sub true r x true ops
theorem p1203 : P1203 := by simp [P1203, m1203]
def P1204 : Prop := ∀ {α} (ops : Ops α) r x, m1204 ops r x = unitBinary ops.sub false r x
theorem p1204 : P1204 := by simp [P1204, m1204]
def P1205 : Prop := ∀ {α} (ops : Ops α) r x, m1205 ops r x = do pure (.generic (← ops.sub r.first x) r.step r.len)
theorem p1205 : P1205 := by simp [P1205, m1205]
def P1206 : Prop := ∀ {α} (ops : Ops α) r x, m1206 ops r x = stepBinary ops.sub false r x pure ops
theorem p1206 : P1206 := by simp [P1206, m1206]
def P1208 : Prop := ∀ {α} (ops : Ops α) x r, m1208 ops x r = stepBinary ops.sub true r x ops.negateStep ops
theorem p1208 : P1208 := by simp [P1208, m1208]
def P1210 : Prop := ∀ {α} (ops : Ops α) r x, m1210 ops r x = linBinary ops.sub false r x
theorem p1210 : P1210 := by simp [P1210, m1210]
def P1211 : Prop := ∀ {α} (ops : Ops α) x r, m1211 ops x r = linBinary ops.sub true r x
theorem p1211 : P1211 := by simp [P1211, m1211]
def P1212 : Prop := ∀ {α} (ops : Ops α) r1 r2, m1212 ops r1 r2 = ops.pairSub r1 r2
theorem p1212 : P1212 := by simp [P1212, m1212]
def P1215 : Prop := ∀ {α} (ops : Ops α) x r, m1215 ops x r = mulGeneric ops.mul true ops r x
theorem p1215 : P1215 := by simp [P1215, m1215]
def P1216 : Prop := ∀ {α} (ops : Ops α) x r, m1216 ops x r = stepBinary ops.mul true r x (ops.mul x) ops
theorem p1216 : P1216 := by simp [P1216, m1216]
def P1218 : Prop := ∀ {α} (ops : Ops α) x r, m1218 ops x r = linBinary ops.mul true r x
theorem p1218 : P1218 := by simp [P1218, m1218]
def P1219 : Prop := ∀ {α} (ops : Ops α) x r, m1219 ops x r = mulGeneric ops.mul true ops r x
theorem p1219 : P1219 := by simp [P1219, m1219]
def P1222 : Prop := ∀ {α} (ops : Ops α) r x, m1222 ops r x = mulGeneric ops.mul false ops r x
theorem p1222 : P1222 := by simp [P1222, m1222]
def P1223 : Prop := ∀ {α} (ops : Ops α) r x, m1223 ops r x = stepBinary ops.mul false r x (fun s => ops.mul s x) ops
theorem p1223 : P1223 := by simp [P1223, m1223]
def P1225 : Prop := ∀ {α} (ops : Ops α) r x, m1225 ops r x = linBinary ops.mul false r x
theorem p1225 : P1225 := by simp [P1225, m1225]
def P1226 : Prop := ∀ {α} (ops : Ops α) r x, m1226 ops r x = mulGeneric ops.mul false ops r x
theorem p1226 : P1226 := by simp [P1226, m1226]
def P1230 : Prop := ∀ {α} (ops : Ops α) r x, m1230 ops r x = genericBinary ops.div false r x false ops
theorem p1230 : P1230 := by simp [P1230, m1230]
def P1231 : Prop := ∀ {α} (ops : Ops α) r x, m1231 ops r x = stepBinary ops.div false r x (fun s => ops.div s x) ops
theorem p1231 : P1231 := by simp [P1231, m1231]
def P1233 : Prop := ∀ {α} (ops : Ops α) r x, m1233 ops r x = linBinary ops.div false r x
theorem p1233 : P1233 := by simp [P1233, m1233]
def P1235 : Prop := ∀ {α} (ops : Ops α) x r, m1235 ops x r = genericBinary ops.ldiv true r x false ops
theorem p1235 : P1235 := by simp [P1235, m1235]
def P1236 : Prop := ∀ {α} (ops : Ops α) x r, m1236 ops x r = do
  pure (.stepLen "inferred" (← ops.ldiv x r.ref) (← ops.ldiv x r.step) r.len r.offset)
theorem p1236 : P1236 := by simp [P1236, m1236]
def P1237 : Prop := ∀ {α} (ops : Ops α) x r, m1237 ops x r = linBinary ops.ldiv true r x
theorem p1237 : P1237 := by simp [P1237, m1237]

def P1239 : Prop := ∀ {α} (ops : Ops α) r, m1239 ops r = do pure (.unit (← ops.big r.start) (← ops.big r.last))
theorem p1239 : P1239 := by simp [P1239, m1239]
def P1240 : Prop := ∀ {α} (ops : Ops α) r, m1240 ops r = do pure (.ordinal (← ops.big r.start) (← ops.big r.last) (← ops.big r.step))
theorem p1240 : P1240 := by simp [P1240, m1240]
def P1241 : Prop := ∀ {α} (ops : Ops α) r, m1241 ops r = do pure (.stepLen "big" (← ops.big r.ref) (← ops.big r.step) r.len r.offset)
theorem p1241 : P1241 := by simp [P1241, m1241]
def P1242 : Prop := ∀ {α} (ops : Ops α) r, m1242 ops r = do pure (.lin (← ops.big r.start) (← ops.big r.stop) r.len)
theorem p1242 : P1242 := by simp [P1242, m1242]
def P1245 : Prop := ∀ {α} (ops : Ops α) (ranges : List (RangeView α)) (offsets : List α),
  m1245 ops ranges offsets = do pure (.cartesian (← mapRanges ops.add ranges offsets false) false)
theorem p1245 : P1245 := by simp [P1245, m1245]
def P1247 : Prop := ∀ {α} (ops : Ops α) (offsets : List α) (ranges : List (RangeView α)),
  m1247 ops offsets ranges = m1245 ops ranges offsets
theorem p1247 : P1247 := by simp [P1247, m1247]
def P1249 : Prop := ∀ {α} (ops : Ops α) (ranges : List (RangeView α)) (offsets : List α),
  m1249 ops ranges offsets = do pure (.cartesian (← mapRanges ops.sub ranges offsets false) false)
theorem p1249 : P1249 := by simp [P1249, m1249]
def P1251 : Prop := ∀ {α} (ops : Ops α) (offsets : List α) (ranges : List (RangeView α)),
  m1251 ops offsets ranges = do
    pure (.cartesian (← (offsets.zip ranges).mapM fun pair => diffrange ops pair.1 pair.2) true)
theorem p1251 : P1251 := by simp [P1251, m1251]
def P1252 : Prop := ∀ {α} (ops : Ops α) offset range, m1252 ops offset range = diffrange ops offset range
theorem p1252 : P1252 := by simp [P1252, m1252]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement, source := s!"base/broadcast.jl:{line}; optimized range source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 1176 "+ range" "Unary plus returns every range unchanged." ``P1176 ``p1176,
  entry 1178 "- AbstractRange" "Generic negation reads and negates first, then step, and preserves length." ``P1178 ``p1178,
  entry 1179 "- OrdinalRange" "Ordinal negation transforms first, last, and step in order." ``P1179 ``p1179,
  entry 1180 "- StepRangeLen" "StepRangeLen negation transforms ref and step and preserves length and offset." ``P1180 ``p1180,
  entry 1181 "- LinRange" "LinRange negation transforms both endpoints and preserves length." ``P1181 ``p1181,
  entry 1184 "+ range scalar" "Right addition shifts first and preserves step and length." ``P1184 ``p1184,
  entry 1185 "+ scalar range" "Left addition preserves operand order while shifting first." ``P1185 ``p1185,
  entry 1186 "+ ordinal integer" "Ordinal right addition shifts both endpoints and preserves step." ``P1186 ``p1186,
  entry 1187 "+ integer ordinal" "Ordinal left addition shifts both endpoints in operand order." ``P1187 ``p1187,
  entry 1188 "+ unit integer" "Unit-range right addition shifts both endpoints." ``P1188 ``p1188,
  entry 1189 "+ integer unit" "Unit-range left addition shifts both endpoints in operand order." ``P1189 ``p1189,
  entry 1190 "+ unit real" "Mixed right addition uses shifted first and original length." ``P1190 ``p1190,
  entry 1191 "+ real unit" "Mixed left addition uses shifted first and original length." ``P1191 ``p1191,
  entry 1192 "+ step scalar" "Typed StepRangeLen right addition probes the converted ref type before constructing from the original ref." ``P1192 ``p1192,
  entry 1194 "+ scalar step" "Typed StepRangeLen left addition preserves operand order in type probing and construction." ``P1194 ``p1194,
  entry 1196 "+ lin scalar" "LinRange right addition shifts both endpoints." ``P1196 ``p1196,
  entry 1197 "+ scalar lin" "LinRange left addition shifts both endpoints in operand order." ``P1197 ``p1197,
  entry 1198 "+ range range" "Range-pair addition delegates to range addition." ``P1198 ``p1198,
  entry 1200 "- range scalar" "Right subtraction shifts first and preserves step and length." ``P1200 ``p1200,
  entry 1201 "- scalar range" "Left subtraction transforms first, negates step, and preserves length." ``P1201 ``p1201,
  entry 1202 "- ordinal integer" "Ordinal right subtraction shifts endpoints and preserves step." ``P1202 ``p1202,
  entry 1203 "- integer ordinal" "Ordinal left subtraction transforms both endpoints and negates step." ``P1203 ``p1203,
  entry 1204 "- unit integer" "Unit-range right subtraction shifts both endpoints." ``P1204 ``p1204,
  entry 1205 "- unit real" "Mixed right subtraction shifts first and preserves length." ``P1205 ``p1205,
  entry 1206 "- step scalar" "Typed StepRangeLen right subtraction probes type before constructing and preserves step, length, and offset." ``P1206 ``p1206,
  entry 1208 "- scalar step" "Typed left subtraction probes type, constructs ref, negates step, and preserves length and offset." ``P1208 ``p1208,
  entry 1210 "- lin scalar" "LinRange right subtraction transforms both endpoints." ``P1210 ``p1210,
  entry 1211 "- scalar lin" "LinRange left subtraction transforms both endpoints in operand order." ``P1211 ``p1211,
  entry 1212 "- range range" "Range-pair subtraction delegates to range subtraction." ``P1212 ``p1212,
  entry 1215 "* scalar range" "Generic left multiplication constructs StepRangeLen from scaled first and step." ``P1215 ``p1215,
  entry 1216 "* scalar step" "Typed left multiplication probes converted ref, then scales ref and step." ``P1216 ``p1216,
  entry 1218 "* scalar lin" "LinRange left multiplication scales both endpoints." ``P1218 ``p1218,
  entry 1219 "* float ordinal" "Float ordinal multiplication constructs from scaled first and step with original length." ``P1219 ``p1219,
  entry 1222 "* range scalar" "Generic right multiplication constructs StepRangeLen in operand order." ``P1222 ``p1222,
  entry 1223 "* step scalar" "Typed right multiplication probes converted ref, then scales ref and step in operand order." ``P1223 ``p1223,
  entry 1225 "* lin scalar" "LinRange right multiplication scales both endpoints." ``P1225 ``p1225,
  entry 1226 "* ordinal float" "Right float ordinal multiplication constructs from scaled first and step." ``P1226 ``p1226,
  entry 1230 "/ range scalar" "Generic division divides first and step and preserves length." ``P1230 ``p1230,
  entry 1231 "/ step scalar" "Typed division probes converted ref, divides ref and step, and preserves length and offset." ``P1231 ``p1231,
  entry 1233 "/ lin scalar" "LinRange division divides both endpoints." ``P1233 ``p1233,
  entry 1235 "left-div scalar range" "Generic left division transforms first and step and preserves length." ``P1235 ``p1235,
  entry 1236 "left-div scalar step" "StepRangeLen left division transforms ref and step and preserves length and offset." ``P1236 ``p1236,
  entry 1237 "left-div scalar lin" "LinRange left division transforms both endpoints." ``P1237 ``p1237,
  entry 1239 "big UnitRange" "UnitRange big conversion transforms start then last." ``P1239 ``p1239,
  entry 1240 "big StepRange" "StepRange big conversion transforms start, step, and last." ``P1240 ``p1240,
  entry 1241 "big StepRangeLen" "StepRangeLen big conversion transforms ref and step and preserves length and offset." ``P1241 ``p1241,
  entry 1242 "big LinRange" "LinRange big conversion transforms both endpoints and preserves length." ``P1242 ``p1242,
  entry 1245 "+ CartesianIndices CartesianIndex" "Cartesian addition maps range-plus-offset across every dimension." ``P1245 ``p1245,
  entry 1247 "+ CartesianIndex CartesianIndices" "Reversed Cartesian addition delegates with swapped operands." ``P1247 ``p1247,
  entry 1249 "- CartesianIndices CartesianIndex" "Cartesian subtraction maps range-minus-offset across every dimension." ``P1249 ``p1249,
  entry 1251 "- CartesianIndex CartesianIndices" "Reverse subtraction maps diffrange before constructing and reversing Cartesian iteration." ``P1251 ``p1251,
  entry 1252 "diffrange" "Diffrange subtracts last from offset and preserves length and step." ``P1252 ``p1252
]

end JuliaLean.MultidimCov.BroadcastRangeFaithful
