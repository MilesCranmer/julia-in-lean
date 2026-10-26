import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.RangeExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def field (rt : Runtime) (name : String) (x : Value) : M Value := call1 rt ("getfield:" ++ name) x
def len (rt : Runtime) (x : Value) : M Value := call1 rt "length" x

def m1176 (_rt : Runtime) (r : Value) : M Value := pure r
def P1176 : Prop := ∀ rt r, m1176 rt r = pure r
theorem p1176 : P1176 := by simp [P1176, m1176]

def m1178 (rt : Runtime) (r : Value) : M Value := do
  let first ← call1 rt "first" r; let first ← call1 rt "-" first
  let step ← call1 rt "step" r; let step ← call1 rt "negate" step
  let n ← len rt r; rt.call "range:start-step-length" [first, step, n]
def P1178 : Prop := ∀ rt r, m1178 rt r = do
  let first ← call1 rt "first" r; let first ← call1 rt "-" first
  let step ← call1 rt "step" r; let step ← call1 rt "negate" step
  let n ← len rt r; rt.call "range:start-step-length" [first, step, n]
theorem p1178 : P1178 := by simp [P1178, m1178, len]

def m1179 (rt : Runtime) (r : Value) : M Value := do
  let first ← call1 rt "-" (← call1 rt "first" r)
  let last ← call1 rt "-" (← call1 rt "last" r)
  let step ← call1 rt "negate" (← call1 rt "step" r)
  rt.call "range:start-stop-step" [first, last, step]
def P1179 : Prop := ∀ rt r, m1179 rt r = do
  let first ← call1 rt "-" (← call1 rt "first" r)
  let last ← call1 rt "-" (← call1 rt "last" r)
  let step ← call1 rt "negate" (← call1 rt "step" r)
  rt.call "range:start-stop-step" [first, last, step]
theorem p1179 : P1179 := by simp [P1179, m1179]

def m1180 (rt : Runtime) (r : Value) : M Value := do
  let ref ← call1 rt "-" (← field rt "ref" r)
  let step ← call1 rt "negate" (← field rt "step" r)
  let n ← len rt r; let offset ← field rt "offset" r
  rt.call "StepRangeLen" [ref, step, n, offset]
def P1180 : Prop := ∀ rt r, m1180 rt r = do
  let ref ← call1 rt "-" (← field rt "ref" r)
  let step ← call1 rt "negate" (← field rt "step" r)
  let n ← len rt r; let offset ← field rt "offset" r
  rt.call "StepRangeLen" [ref, step, n, offset]
theorem p1180 : P1180 := by simp [P1180, m1180, field, len]

def m1181 (rt : Runtime) (r : Value) : M Value := do
  let start ← call1 rt "-" (← field rt "start" r)
  let stop ← call1 rt "-" (← field rt "stop" r)
  let n ← len rt r; rt.call "LinRange" [start, stop, n]
def P1181 : Prop := ∀ rt r, m1181 rt r = do
  let start ← call1 rt "-" (← field rt "start" r)
  let stop ← call1 rt "-" (← field rt "stop" r)
  let n ← len rt r; rt.call "LinRange" [start, stop, n]
theorem p1181 : P1181 := by simp [P1181, m1181, field, len]

def addRangeRight (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "+" (← call1 rt "first" r) x
  let step ← call1 rt "step" r; let n ← len rt r
  rt.call "range:start-step-length" [start, step, n]
def addRangeLeft (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "+" x (← call1 rt "first" r)
  let step ← call1 rt "step" r; let n ← len rt r
  rt.call "range:start-step-length" [start, step, n]

def m1184 := addRangeRight
def P1184 : Prop := ∀ rt r x, m1184 rt r x = addRangeRight rt r x
theorem p1184 : P1184 := by simp [P1184, m1184]
def m1185 := addRangeLeft
def P1185 : Prop := ∀ rt x r, m1185 rt x r = addRangeLeft rt x r
theorem p1185 : P1185 := by simp [P1185, m1185]

def m1186 (rt : Runtime) (r x : Value) : M Value := do
  let first ← call2 rt "+" (← call1 rt "first" r) x
  let last ← call2 rt "+" (← call1 rt "last" r) x
  let step ← call1 rt "step" r; rt.call "range:start-stop-step" [first, last, step]
def P1186 : Prop := ∀ rt r x, m1186 rt r x = do
  let first ← call2 rt "+" (← call1 rt "first" r) x
  let last ← call2 rt "+" (← call1 rt "last" r) x
  let step ← call1 rt "step" r; rt.call "range:start-stop-step" [first, last, step]
theorem p1186 : P1186 := by simp [P1186, m1186]

def m1187 (rt : Runtime) (x r : Value) : M Value := do
  let first ← call2 rt "+" x (← call1 rt "first" r)
  let last ← call2 rt "+" x (← call1 rt "last" r)
  let step ← call1 rt "step" r; rt.call "range:start-stop-step" [first, last, step]
def P1187 : Prop := ∀ rt x r, m1187 rt x r = do
  let first ← call2 rt "+" x (← call1 rt "first" r)
  let last ← call2 rt "+" x (← call1 rt "last" r)
  let step ← call1 rt "step" r; rt.call "range:start-stop-step" [first, last, step]
theorem p1187 : P1187 := by simp [P1187, m1187]

def m1188 (rt : Runtime) (r x : Value) : M Value := do
  let first ← call2 rt "+" (← call1 rt "first" r) x
  let last ← call2 rt "+" (← call1 rt "last" r) x
  rt.call "range:start-stop" [first, last]
def P1188 : Prop := ∀ rt r x, m1188 rt r x = do
  let first ← call2 rt "+" (← call1 rt "first" r) x
  let last ← call2 rt "+" (← call1 rt "last" r) x
  rt.call "range:start-stop" [first, last]
theorem p1188 : P1188 := by simp [P1188, m1188]

def m1189 (rt : Runtime) (x r : Value) : M Value := do
  let first ← call2 rt "+" x (← call1 rt "first" r)
  let last ← call2 rt "+" x (← call1 rt "last" r)
  rt.call "range:start-stop" [first, last]
def P1189 : Prop := ∀ rt x r, m1189 rt x r = do
  let first ← call2 rt "+" x (← call1 rt "first" r)
  let last ← call2 rt "+" x (← call1 rt "last" r)
  rt.call "range:start-stop" [first, last]
theorem p1189 : P1189 := by simp [P1189, m1189]

def m1190 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "+" (← call1 rt "first" r) x
  let n ← len rt r; rt.call "range:start-length" [start, n]
def P1190 : Prop := ∀ rt r x, m1190 rt r x = do
  let start ← call2 rt "+" (← call1 rt "first" r) x
  let n ← len rt r; rt.call "range:start-length" [start, n]
theorem p1190 : P1190 := by simp [P1190, m1190, len]

def m1191 (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "+" x (← call1 rt "first" r)
  let n ← len rt r; rt.call "range:start-length" [start, n]
def P1191 : Prop := ∀ rt x r, m1191 rt x r = do
  let start ← call2 rt "+" x (← call1 rt "first" r)
  let n ← len rt r; rt.call "range:start-length" [start, n]
theorem p1191 : P1191 := by simp [P1191, m1191, len]

def m1192 (rt : Runtime) (r x T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let sumType ← call1 rt "typeof" (← call2 rt "+" refT x)
  let ref ← call2 rt "+" (← field rt "ref" r) x
  let step ← field rt "step" r; let n ← len rt r; let offset ← field rt "offset" r
  rt.call "StepRangeLen{sumType}" [sumType, ref, step, n, offset]
def P1192 : Prop := ∀ rt r x T, m1192 rt r x T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let sumType ← call1 rt "typeof" (← call2 rt "+" refT x)
  let ref ← call2 rt "+" (← field rt "ref" r) x
  let step ← field rt "step" r; let n ← len rt r; let offset ← field rt "offset" r
  rt.call "StepRangeLen{sumType}" [sumType, ref, step, n, offset]
theorem p1192 : P1192 := by simp [P1192, m1192, field, len]

def m1194 (rt : Runtime) (x r T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let sumType ← call1 rt "typeof" (← call2 rt "+" x refT)
  let ref ← call2 rt "+" x (← field rt "ref" r)
  let step ← field rt "step" r; let n ← len rt r; let offset ← field rt "offset" r
  rt.call "StepRangeLen{sumType}" [sumType, ref, step, n, offset]
def P1194 : Prop := ∀ rt x r T, m1194 rt x r T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let sumType ← call1 rt "typeof" (← call2 rt "+" x refT)
  let ref ← call2 rt "+" x (← field rt "ref" r)
  let step ← field rt "step" r; let n ← len rt r; let offset ← field rt "offset" r
  rt.call "StepRangeLen{sumType}" [sumType, ref, step, n, offset]
theorem p1194 : P1194 := by simp [P1194, m1194, field, len]

def m1196 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "+" (← field rt "start" r) x
  let stop ← call2 rt "+" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← len rt r)]
def P1196 : Prop := ∀ rt r x, m1196 rt r x = do
  let start ← call2 rt "+" (← field rt "start" r) x
  let stop ← call2 rt "+" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← len rt r)]
theorem p1196 : P1196 := by simp [P1196, m1196, field, len]

def m1197 (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "+" x (← field rt "start" r)
  let stop ← call2 rt "+" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← len rt r)]
def P1197 : Prop := ∀ rt x r, m1197 rt x r = do
  let start ← call2 rt "+" x (← field rt "start" r)
  let stop ← call2 rt "+" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← len rt r)]
theorem p1197 : P1197 := by simp [P1197, m1197, field, len]

def m1198 (rt : Runtime) (r1 r2 : Value) : M Value := call2 rt "+" r1 r2
def P1198 : Prop := ∀ rt r1 r2, m1198 rt r1 r2 = call2 rt "+" r1 r2
theorem p1198 : P1198 := by simp [P1198, m1198]

def subRangeRight (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "-" (← call1 rt "first" r) x
  let step ← call1 rt "step" r; let n ← len rt r
  rt.call "range:start-step-length" [start, step, n]
def subRangeLeft (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "-" x (← call1 rt "first" r)
  let step ← call1 rt "negate" (← call1 rt "step" r); let n ← len rt r
  rt.call "range:start-step-length" [start, step, n]
def m1200 := subRangeRight
def P1200 : Prop := ∀ rt r x, m1200 rt r x = subRangeRight rt r x
theorem p1200 : P1200 := by simp [P1200, m1200]
def m1201 := subRangeLeft
def P1201 : Prop := ∀ rt x r, m1201 rt x r = subRangeLeft rt x r
theorem p1201 : P1201 := by simp [P1201, m1201]

def m1202 (rt : Runtime) (r x : Value) : M Value := do
  let first ← call2 rt "-" (← call1 rt "first" r) x
  let last ← call2 rt "-" (← call1 rt "last" r) x
  let step ← call1 rt "step" r; rt.call "range:start-stop-step" [first, last, step]
def P1202 : Prop := ∀ rt r x, m1202 rt r x = do
  let first ← call2 rt "-" (← call1 rt "first" r) x
  let last ← call2 rt "-" (← call1 rt "last" r) x
  let step ← call1 rt "step" r; rt.call "range:start-stop-step" [first, last, step]
theorem p1202 : P1202 := by simp [P1202, m1202]

def m1203 (rt : Runtime) (x r : Value) : M Value := do
  let first ← call2 rt "-" x (← call1 rt "first" r)
  let last ← call2 rt "-" x (← call1 rt "last" r)
  let step ← call1 rt "negate" (← call1 rt "step" r)
  rt.call "range:start-stop-step" [first, last, step]
def P1203 : Prop := ∀ rt x r, m1203 rt x r = do
  let first ← call2 rt "-" x (← call1 rt "first" r)
  let last ← call2 rt "-" x (← call1 rt "last" r)
  let step ← call1 rt "negate" (← call1 rt "step" r)
  rt.call "range:start-stop-step" [first, last, step]
theorem p1203 : P1203 := by simp [P1203, m1203]

def m1204 (rt : Runtime) (r x : Value) : M Value := do
  let first ← call2 rt "-" (← call1 rt "first" r) x
  let last ← call2 rt "-" (← call1 rt "last" r) x
  rt.call "range:start-stop" [first, last]
def P1204 : Prop := ∀ rt r x, m1204 rt r x = do
  let first ← call2 rt "-" (← call1 rt "first" r) x
  let last ← call2 rt "-" (← call1 rt "last" r) x
  rt.call "range:start-stop" [first, last]
theorem p1204 : P1204 := by simp [P1204, m1204]

def m1205 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "-" (← call1 rt "first" r) x
  rt.call "range:start-length" [start, (← len rt r)]
def P1205 : Prop := ∀ rt r x, m1205 rt r x = do
  let start ← call2 rt "-" (← call1 rt "first" r) x
  rt.call "range:start-length" [start, (← len rt r)]
theorem p1205 : P1205 := by simp [P1205, m1205, len]

def m1206 (rt : Runtime) (r x T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "-" refT x)
  let ref ← call2 rt "-" (← field rt "ref" r) x
  rt.call "StepRangeLen{resultType}" [resultType, ref, (← field rt "step" r),
    (← len rt r), (← field rt "offset" r)]
def P1206 : Prop := ∀ rt r x T, m1206 rt r x T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "-" refT x)
  let ref ← call2 rt "-" (← field rt "ref" r) x
  rt.call "StepRangeLen{resultType}" [resultType, ref, (← field rt "step" r),
    (← len rt r), (← field rt "offset" r)]
theorem p1206 : P1206 := by simp [P1206, m1206, field, len]

def m1208 (rt : Runtime) (x r T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "-" x refT)
  let ref ← call2 rt "-" x (← field rt "ref" r)
  let step ← call1 rt "negate" (← field rt "step" r)
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
def P1208 : Prop := ∀ rt x r T, m1208 rt x r T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "-" x refT)
  let ref ← call2 rt "-" x (← field rt "ref" r)
  let step ← call1 rt "negate" (← field rt "step" r)
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
theorem p1208 : P1208 := by simp [P1208, m1208, field, len]

def m1210 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "-" (← field rt "start" r) x
  let stop ← call2 rt "-" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← len rt r)]
def P1210 : Prop := ∀ rt r x, m1210 rt r x = do
  let start ← call2 rt "-" (← field rt "start" r) x
  let stop ← call2 rt "-" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← len rt r)]
theorem p1210 : P1210 := by simp [P1210, m1210, field, len]

def m1211 (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "-" x (← field rt "start" r)
  let stop ← call2 rt "-" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← len rt r)]
def P1211 : Prop := ∀ rt x r, m1211 rt x r = do
  let start ← call2 rt "-" x (← field rt "start" r)
  let stop ← call2 rt "-" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← len rt r)]
theorem p1211 : P1211 := by simp [P1211, m1211, field, len]

def m1212 (rt : Runtime) (r1 r2 : Value) : M Value := call2 rt "-" r1 r2
def P1212 : Prop := ∀ rt r1 r2, m1212 rt r1 r2 = call2 rt "-" r1 r2
theorem p1212 : P1212 := by simp [P1212, m1212]

def genericMul (rt : Runtime) (left right r : Value) : M Value := do
  let first ← call2 rt "*" left (← call1 rt "first" r)
  let step ← call2 rt "*" right (← call1 rt "step" r)
  rt.call "StepRangeLen" [first, step, (← len rt r)]
def m1215 (rt : Runtime) (x r : Value) : M Value := genericMul rt x x r
def P1215 : Prop := ∀ rt x r, m1215 rt x r = genericMul rt x x r
theorem p1215 : P1215 := by simp [P1215, m1215]

def m1216 (rt : Runtime) (x r T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "*" x refT)
  let ref ← call2 rt "*" x (← field rt "ref" r)
  let step ← call2 rt "*" x (← field rt "step" r)
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
def P1216 : Prop := ∀ rt x r T, m1216 rt x r T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "*" x refT)
  let ref ← call2 rt "*" x (← field rt "ref" r)
  let step ← call2 rt "*" x (← field rt "step" r)
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
theorem p1216 : P1216 := by simp [P1216, m1216, field, len]

def m1218 (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "*" x (← field rt "start" r)
  let stop ← call2 rt "*" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
def P1218 : Prop := ∀ rt x r, m1218 rt x r = do
  let start ← call2 rt "*" x (← field rt "start" r)
  let stop ← call2 rt "*" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
theorem p1218 : P1218 := by simp [P1218, m1218, field]

def m1219 (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "*" x (← call1 rt "first" r)
  let step ← call2 rt "*" x (← call1 rt "step" r)
  rt.call "Base.range_start_step_length" [start, step, (← len rt r)]
def P1219 : Prop := ∀ rt x r, m1219 rt x r = do
  let start ← call2 rt "*" x (← call1 rt "first" r)
  let step ← call2 rt "*" x (← call1 rt "step" r)
  rt.call "Base.range_start_step_length" [start, step, (← len rt r)]
theorem p1219 : P1219 := by simp [P1219, m1219, len]

def m1222 (rt : Runtime) (r x : Value) : M Value := do
  let first ← call2 rt "*" (← call1 rt "first" r) x
  let step ← call2 rt "*" (← call1 rt "step" r) x
  rt.call "StepRangeLen" [first, step, (← len rt r)]
def P1222 : Prop := ∀ rt r x, m1222 rt r x = do
  let first ← call2 rt "*" (← call1 rt "first" r) x
  let step ← call2 rt "*" (← call1 rt "step" r) x
  rt.call "StepRangeLen" [first, step, (← len rt r)]
theorem p1222 : P1222 := by simp [P1222, m1222, len]

def m1223 (rt : Runtime) (r x T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "*" refT x)
  let ref ← call2 rt "*" (← field rt "ref" r) x
  let step ← call2 rt "*" (← field rt "step" r) x
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
def P1223 : Prop := ∀ rt r x T, m1223 rt r x T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "*" refT x)
  let ref ← call2 rt "*" (← field rt "ref" r) x
  let step ← call2 rt "*" (← field rt "step" r) x
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
theorem p1223 : P1223 := by simp [P1223, m1223, field, len]

def m1225 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "*" (← field rt "start" r) x
  let stop ← call2 rt "*" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
def P1225 : Prop := ∀ rt r x, m1225 rt r x = do
  let start ← call2 rt "*" (← field rt "start" r) x
  let stop ← call2 rt "*" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
theorem p1225 : P1225 := by simp [P1225, m1225, field]

def m1226 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "*" (← call1 rt "first" r) x
  let step ← call2 rt "*" (← call1 rt "step" r) x
  rt.call "Base.range_start_step_length" [start, step, (← len rt r)]
def P1226 : Prop := ∀ rt r x, m1226 rt r x = do
  let start ← call2 rt "*" (← call1 rt "first" r) x
  let step ← call2 rt "*" (← call1 rt "step" r) x
  rt.call "Base.range_start_step_length" [start, step, (← len rt r)]
theorem p1226 : P1226 := by simp [P1226, m1226, len]

def m1230 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "/" (← call1 rt "first" r) x
  let step ← call2 rt "/" (← call1 rt "step" r) x
  rt.call "range:start-step-length" [start, step, (← len rt r)]
def P1230 : Prop := ∀ rt r x, m1230 rt r x = do
  let start ← call2 rt "/" (← call1 rt "first" r) x
  let step ← call2 rt "/" (← call1 rt "step" r) x
  rt.call "range:start-step-length" [start, step, (← len rt r)]
theorem p1230 : P1230 := by simp [P1230, m1230, len]

def m1231 (rt : Runtime) (r x T : Value) : M Value := do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "/" refT x)
  let ref ← call2 rt "/" (← field rt "ref" r) x
  let step ← call2 rt "/" (← field rt "step" r) x
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
def P1231 : Prop := ∀ rt r x T, m1231 rt r x T = do
  let refT ← call2 rt "call" T (← field rt "ref" r)
  let resultType ← call1 rt "typeof" (← call2 rt "/" refT x)
  let ref ← call2 rt "/" (← field rt "ref" r) x
  let step ← call2 rt "/" (← field rt "step" r) x
  rt.call "StepRangeLen{resultType}" [resultType, ref, step, (← len rt r), (← field rt "offset" r)]
theorem p1231 : P1231 := by simp [P1231, m1231, field, len]

def m1233 (rt : Runtime) (r x : Value) : M Value := do
  let start ← call2 rt "/" (← field rt "start" r) x
  let stop ← call2 rt "/" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
def P1233 : Prop := ∀ rt r x, m1233 rt r x = do
  let start ← call2 rt "/" (← field rt "start" r) x
  let stop ← call2 rt "/" (← field rt "stop" r) x
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
theorem p1233 : P1233 := by simp [P1233, m1233, field]

def m1235 (rt : Runtime) (x r : Value) : M Value := do
  let first ← call2 rt "\\" x (← call1 rt "first" r)
  let step ← call2 rt "\\" x (← call1 rt "step" r)
  rt.call "range:start-step-length" [first, step, (← len rt r)]
def P1235 : Prop := ∀ rt x r, m1235 rt x r = do
  let first ← call2 rt "\\" x (← call1 rt "first" r)
  let step ← call2 rt "\\" x (← call1 rt "step" r)
  rt.call "range:start-step-length" [first, step, (← len rt r)]
theorem p1235 : P1235 := by simp [P1235, m1235, len]

def m1236 (rt : Runtime) (x r : Value) : M Value := do
  let ref ← call2 rt "\\" x (← field rt "ref" r)
  let step ← call2 rt "\\" x (← field rt "step" r)
  rt.call "StepRangeLen" [ref, step, (← len rt r), (← field rt "offset" r)]
def P1236 : Prop := ∀ rt x r, m1236 rt x r = do
  let ref ← call2 rt "\\" x (← field rt "ref" r)
  let step ← call2 rt "\\" x (← field rt "step" r)
  rt.call "StepRangeLen" [ref, step, (← len rt r), (← field rt "offset" r)]
theorem p1236 : P1236 := by simp [P1236, m1236, field, len]

def m1237 (rt : Runtime) (x r : Value) : M Value := do
  let start ← call2 rt "\\" x (← field rt "start" r)
  let stop ← call2 rt "\\" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
def P1237 : Prop := ∀ rt x r, m1237 rt x r = do
  let start ← call2 rt "\\" x (← field rt "start" r)
  let stop ← call2 rt "\\" x (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← field rt "len" r)]
theorem p1237 : P1237 := by simp [P1237, m1237, field]

def m1239 (rt : Runtime) (r : Value) : M Value := do
  let start ← call1 rt "big" (← field rt "start" r)
  let last ← call1 rt "big" (← call1 rt "last" r)
  rt.call "UnitRange" [start, last]
def P1239 : Prop := ∀ rt r, m1239 rt r = do
  let start ← call1 rt "big" (← field rt "start" r)
  let last ← call1 rt "big" (← call1 rt "last" r)
  rt.call "UnitRange" [start, last]
theorem p1239 : P1239 := by simp [P1239, m1239, field]

def m1240 (rt : Runtime) (r : Value) : M Value := do
  let start ← call1 rt "big" (← field rt "start" r)
  let step ← call1 rt "big" (← field rt "step" r)
  let last ← call1 rt "big" (← call1 rt "last" r)
  rt.call "StepRange" [start, step, last]
def P1240 : Prop := ∀ rt r, m1240 rt r = do
  let start ← call1 rt "big" (← field rt "start" r)
  let step ← call1 rt "big" (← field rt "step" r)
  let last ← call1 rt "big" (← call1 rt "last" r)
  rt.call "StepRange" [start, step, last]
theorem p1240 : P1240 := by simp [P1240, m1240, field]

def m1241 (rt : Runtime) (r : Value) : M Value := do
  let ref ← call1 rt "big" (← field rt "ref" r)
  let step ← call1 rt "big" (← field rt "step" r)
  rt.call "StepRangeLen" [ref, step, (← len rt r), (← field rt "offset" r)]
def P1241 : Prop := ∀ rt r, m1241 rt r = do
  let ref ← call1 rt "big" (← field rt "ref" r)
  let step ← call1 rt "big" (← field rt "step" r)
  rt.call "StepRangeLen" [ref, step, (← len rt r), (← field rt "offset" r)]
theorem p1241 : P1241 := by simp [P1241, m1241, field, len]

def m1242 (rt : Runtime) (r : Value) : M Value := do
  let start ← call1 rt "big" (← field rt "start" r)
  let stop ← call1 rt "big" (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← len rt r)]
def P1242 : Prop := ∀ rt r, m1242 rt r = do
  let start ← call1 rt "big" (← field rt "start" r)
  let stop ← call1 rt "big" (← field rt "stop" r)
  rt.call "LinRange" [start, stop, (← len rt r)]
theorem p1242 : P1242 := by simp [P1242, m1242, field, len]

def m1245 (rt : Runtime) (I j : Value) : M Value := do
  let ranges ← field rt "indices" I; let offsets ← call1 rt "Tuple" j
  let closure ← call0 rt "closure:(rng,offset)->rng.+offset"
  let mapped ← rt.call "map" [closure, ranges, offsets]
  call1 rt "CartesianIndices" mapped
def P1245 : Prop := ∀ rt I j, m1245 rt I j = do
  let ranges ← field rt "indices" I; let offsets ← call1 rt "Tuple" j
  let closure ← call0 rt "closure:(rng,offset)->rng.+offset"
  let mapped ← rt.call "map" [closure, ranges, offsets]
  call1 rt "CartesianIndices" mapped
theorem p1245 : P1245 := by simp [P1245, m1245, field]

def m1247 (rt : Runtime) (j I : Value) : M Value := call2 rt ".+" I j
def P1247 : Prop := ∀ rt j I, m1247 rt j I = call2 rt ".+" I j
theorem p1247 : P1247 := by simp [P1247, m1247]

def m1249 (rt : Runtime) (I j : Value) : M Value := do
  let ranges ← field rt "indices" I; let offsets ← call1 rt "Tuple" j
  let closure ← call0 rt "closure:(rng,offset)->rng.-offset"
  let mapped ← rt.call "map" [closure, ranges, offsets]
  call1 rt "CartesianIndices" mapped
def P1249 : Prop := ∀ rt I j, m1249 rt I j = do
  let ranges ← field rt "indices" I; let offsets ← call1 rt "Tuple" j
  let closure ← call0 rt "closure:(rng,offset)->rng.-offset"
  let mapped ← rt.call "map" [closure, ranges, offsets]
  call1 rt "CartesianIndices" mapped
theorem p1249 : P1249 := by simp [P1249, m1249, field]

def m1251 (rt : Runtime) (j I : Value) : M Value := do
  let offsets ← call1 rt "Tuple" j; let ranges ← field rt "indices" I
  let closure ← call0 rt "closure:diffrange"
  let mapped ← rt.call "map" [closure, offsets, ranges]
  let indices ← call1 rt "CartesianIndices" mapped
  call1 rt "Iterators.reverse" indices
def P1251 : Prop := ∀ rt j I, m1251 rt j I = do
  let offsets ← call1 rt "Tuple" j; let ranges ← field rt "indices" I
  let closure ← call0 rt "closure:diffrange"
  let mapped ← rt.call "map" [closure, offsets, ranges]
  let indices ← call1 rt "CartesianIndices" mapped
  call1 rt "Iterators.reverse" indices
theorem p1251 : P1251 := by simp [P1251, m1251, field]

def m1252 (rt : Runtime) (offset range : Value) : M Value := do
  let start ← call2 rt "-" offset (← call1 rt "last" range)
  let n ← len rt range; let step ← call1 rt "step" range
  rt.call "range:start-length-step" [start, n, step]
def P1252 : Prop := ∀ rt offset range, m1252 rt offset range = do
  let start ← call2 rt "-" offset (← call1 rt "last" range)
  let n ← len rt range; let step ← call1 rt "step" range
  rt.call "range:start-length-step" [start, n, step]
theorem p1252 : P1252 := by simp [P1252, m1252, len]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; exact optimized-constructor equation",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry 1176 "broadcasted(+,range)" "Unary plus returns the range unchanged." ``P1176 ``p1176,
  entry 1178 "broadcasted(-,AbstractRange)" "Generic negation constructs range from negated first and step with the original length." ``P1178 ``p1178,
  entry 1179 "broadcasted(-,OrdinalRange)" "Ordinal negation constructs from negated first, last and step." ``P1179 ``p1179,
  entry 1180 "broadcasted(-,StepRangeLen)" "StepRangeLen negation negates ref and step and preserves length and offset." ``P1180 ``p1180,
  entry 1181 "broadcasted(-,LinRange)" "LinRange negation negates both endpoints and preserves length." ``P1181 ``p1181,
  entry 1184 "broadcasted(+,range,x)" "Right scalar addition shifts first and preserves step and length." ``P1184 ``p1184,
  entry 1185 "broadcasted(+,x,range)" "Left scalar addition shifts first in operand order and preserves step and length." ``P1185 ``p1185,
  entry 1186 "broadcasted(+,OrdinalRange,Integer)" "Ordinal right addition shifts first and last and preserves step." ``P1186 ``p1186,
  entry 1187 "broadcasted(+,Integer,OrdinalRange)" "Ordinal left addition shifts endpoints in operand order." ``P1187 ``p1187,
  entry 1188 "broadcasted(+,UnitRange,Integer)" "UnitRange right addition shifts both endpoints." ``P1188 ``p1188,
  entry 1189 "broadcasted(+,Integer,UnitRange)" "UnitRange left addition shifts both endpoints in operand order." ``P1189 ``p1189,
  entry 1190 "broadcasted(+,UnitRange,Real)" "Mixed right addition uses shifted first and original length." ``P1190 ``p1190,
  entry 1191 "broadcasted(+,Real,UnitRange)" "Mixed left addition uses shifted first and original length." ``P1191 ``p1191,
  entry 1192 "broadcasted(+,StepRangeLen,x)" "StepRangeLen right addition computes result type from converted ref, then preserves step, length and offset." ``P1192 ``p1192,
  entry 1194 "broadcasted(+,x,StepRangeLen)" "StepRangeLen left addition preserves operand order in type and ref calculations." ``P1194 ``p1194,
  entry 1196 "broadcasted(+,LinRange,x)" "LinRange right addition shifts both endpoints." ``P1196 ``p1196,
  entry 1197 "broadcasted(+,x,LinRange)" "LinRange left addition shifts both endpoints in operand order." ``P1197 ``p1197,
  entry 1198 "broadcasted(+,range,range)" "Range pair addition delegates to range +." ``P1198 ``p1198,
  entry 1200 "broadcasted(-,range,x)" "Right subtraction shifts first and preserves step and length." ``P1200 ``p1200,
  entry 1201 "broadcasted(-,x,range)" "Left subtraction negates step and preserves length." ``P1201 ``p1201,
  entry 1202 "broadcasted(-,OrdinalRange,Integer)" "Ordinal right subtraction shifts endpoints and preserves step." ``P1202 ``p1202,
  entry 1203 "broadcasted(-,Integer,OrdinalRange)" "Ordinal left subtraction reverses endpoints and negates step." ``P1203 ``p1203,
  entry 1204 "broadcasted(-,UnitRange,Integer)" "UnitRange right subtraction shifts both endpoints." ``P1204 ``p1204,
  entry 1205 "broadcasted(-,UnitRange,Real)" "Mixed right subtraction shifts first and preserves length." ``P1205 ``p1205,
  entry 1206 "broadcasted(-,StepRangeLen,x)" "StepRangeLen right subtraction computes type and ref in source order and preserves other fields." ``P1206 ``p1206,
  entry 1208 "broadcasted(-,x,StepRangeLen)" "StepRangeLen left subtraction computes type and ref in operand order and negates step." ``P1208 ``p1208,
  entry 1210 "broadcasted(-,LinRange,x)" "LinRange right subtraction shifts both endpoints." ``P1210 ``p1210,
  entry 1211 "broadcasted(-,x,LinRange)" "LinRange left subtraction subtracts each endpoint from x." ``P1211 ``p1211,
  entry 1212 "broadcasted(-,range,range)" "Range pair subtraction delegates to range -." ``P1212 ``p1212,
  entry 1215 "broadcasted(*,x,range)" "Generic left multiplication constructs StepRangeLen from scaled first and step." ``P1215 ``p1215,
  entry 1216 "broadcasted(*,x,StepRangeLen)" "Typed left multiplication computes type, ref and step in source operand order." ``P1216 ``p1216,
  entry 1218 "broadcasted(*,x,LinRange)" "LinRange left multiplication scales both endpoints and preserves len." ``P1218 ``p1218,
  entry 1219 "broadcasted(*,AbstractFloat,OrdinalRange)" "Float ordinal multiplication delegates to range_start_step_length." ``P1219 ``p1219,
  entry 1222 "broadcasted(*,range,x)" "Generic right multiplication constructs StepRangeLen from scaled first and step." ``P1222 ``p1222,
  entry 1223 "broadcasted(*,StepRangeLen,x)" "Typed right multiplication computes type, ref and step in source operand order." ``P1223 ``p1223,
  entry 1225 "broadcasted(*,LinRange,x)" "LinRange right multiplication scales both endpoints and preserves len." ``P1225 ``p1225,
  entry 1226 "broadcasted(*,OrdinalRange,AbstractFloat)" "Right float ordinal multiplication delegates to range_start_step_length." ``P1226 ``p1226,
  entry 1230 "broadcasted(/,range,x)" "Generic division divides first and step and preserves length." ``P1230 ``p1230,
  entry 1231 "broadcasted(/,StepRangeLen,x)" "Typed division computes type, ref and step before preserving length and offset." ``P1231 ``p1231,
  entry 1233 "broadcasted(/,LinRange,x)" "LinRange division divides both endpoints and preserves len." ``P1233 ``p1233,
  entry 1235 "broadcasted(\\,x,range)" "Generic left division transforms first and step and preserves length." ``P1235 ``p1235,
  entry 1236 "broadcasted(\\,x,StepRangeLen)" "StepRangeLen left division transforms ref and step and preserves length and offset." ``P1236 ``p1236,
  entry 1237 "broadcasted(\\,x,LinRange)" "LinRange left division transforms both endpoints and preserves len." ``P1237 ``p1237,
  entry 1239 "broadcasted(big,UnitRange)" "UnitRange big conversion converts start and last." ``P1239 ``p1239,
  entry 1240 "broadcasted(big,StepRange)" "StepRange big conversion converts start, step and last." ``P1240 ``p1240,
  entry 1241 "broadcasted(big,StepRangeLen)" "StepRangeLen big conversion converts ref and step and preserves length and offset." ``P1241 ``p1241,
  entry 1242 "broadcasted(big,LinRange)" "LinRange big conversion converts both endpoints and preserves length." ``P1242 ``p1242,
  entry 1245 "broadcasted(+,CartesianIndices,CartesianIndex)" "Cartesian addition maps range-plus-offset before constructing indices." ``P1245 ``p1245,
  entry 1247 "broadcasted(+,CartesianIndex,CartesianIndices)" "Reversed Cartesian addition delegates to I .+ j." ``P1247 ``p1247,
  entry 1249 "broadcasted(-,CartesianIndices,CartesianIndex)" "Cartesian subtraction maps range-minus-offset before constructing indices." ``P1249 ``p1249,
  entry 1251 "broadcasted(-,CartesianIndex,CartesianIndices)" "Reverse subtraction maps diffrange, constructs indices, then reverses iteration." ``P1251 ``p1251,
  entry 1252 "diffrange(offset,range)" "diffrange subtracts last from offset and preserves length and step." ``P1252 ``p1252
]

end JuliaLean.BroadcastCov.RangeExact
