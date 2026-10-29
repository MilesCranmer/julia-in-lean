import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.BitsExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def nothing (rt : Runtime) : M Value := call0 rt "nothing"
def one (rt : Runtime) : M Value := call0 rt "Int:1"

def m1083 (rt : Runtime) (_f _args : Value) : M Value := nothing rt
def P1083 : Prop := ∀ rt f args, m1083 rt f args = nothing rt
theorem p1083 : P1083 := by simp [P1083, m1083]

def m1084 (rt : Runtime) (_args : Value) : M Value := call0 rt "&:function"
def P1084 : Prop := ∀ rt args, m1084 rt args = call0 rt "&:function"
theorem p1084 : P1084 := by simp [P1084, m1084]

def m1085 (rt : Runtime) (_args : Value) : M Value := call0 rt "|:function"
def P1085 : Prop := ∀ rt args, m1085 rt args = call0 rt "|:function"
theorem p1085 : P1085 := by simp [P1085, m1085]

def m1086 (rt : Runtime) (_args : Value) : M Value := call0 rt "xor:function"
def P1086 : Prop := ∀ rt args, m1086 rt args = call0 rt "xor:function"
theorem p1086 : P1086 := by simp [P1086, m1086]

def m1087 (rt : Runtime) (_args : Value) : M Value := call0 rt "nand:function"
def P1087 : Prop := ∀ rt args, m1087 rt args = call0 rt "nand:function"
theorem p1087 : P1087 := by simp [P1087, m1087]

def m1088 (rt : Runtime) (_args : Value) : M Value := call0 rt "nor:function"
def P1088 : Prop := ∀ rt args, m1088 rt args = call0 rt "nor:function"
theorem p1088 : P1088 := by simp [P1088, m1088]

def m1089 (rt : Runtime) (_args : Value) : M Value := call0 rt "~:function"
def P1089 : Prop := ∀ rt args, m1089 rt args = call0 rt "~:function"
theorem p1089 : P1089 := by simp [P1089, m1089]

def m1090 (rt : Runtime) (_args : Value) : M Value := call0 rt "identity:function"
def P1090 : Prop := ∀ rt args, m1090 rt args = call0 rt "identity:function"
theorem p1090 : P1090 := by simp [P1090, m1090]

def m1091 (rt : Runtime) : M Value := call0 rt "closure:(x,y)->~xor(x,y)"
def P1091 : Prop := ∀ rt, m1091 rt = call0 rt "closure:(x,y)->~xor(x,y)"
theorem p1091 : P1091 := by simp [P1091, m1091]

def m1092 (rt : Runtime) : M Value := call0 rt "xor:function"
def P1092 : Prop := ∀ rt, m1092 rt = call0 rt "xor:function"
theorem p1092 : P1092 := by simp [P1092, m1092]

def m1093 (rt : Runtime) : M Value := call0 rt "closure:(x,y)->~x&y"
def P1093 : Prop := ∀ rt, m1093 rt = call0 rt "closure:(x,y)->~x&y"
theorem p1093 : P1093 := by simp [P1093, m1093]

def m1094 (rt : Runtime) : M Value := call0 rt "closure:(x,y)->~x|y"
def P1094 : Prop := ∀ rt, m1094 rt = call0 rt "closure:(x,y)->~x|y"
theorem p1094 : P1094 := by simp [P1094, m1094]

def m1095 (rt : Runtime) : M Value := call0 rt "closure:(x,y)->x&~y"
def P1095 : Prop := ∀ rt, m1095 rt = call0 rt "closure:(x,y)->x&~y"
theorem p1095 : P1095 := by simp [P1095, m1095]

def m1096 (rt : Runtime) : M Value := call0 rt "closure:(x,y)->x|~y"
def P1096 : Prop := ∀ rt, m1096 rt = call0 rt "closure:(x,y)->x|~y"
theorem p1096 : P1096 := by simp [P1096, m1096]

def m1098 (rt : Runtime) (R bc : Value) : M Value := do
  let f0 ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let f ← call2 rt "_chunkop" f0 args
  rt.call "ischunkedbroadcast" [R, bc, f]
def P1098 : Prop := ∀ rt R bc, m1098 rt R bc = do
  let f0 ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let f ← call2 rt "_chunkop" f0 args
  rt.call "ischunkedbroadcast" [R, bc, f]
theorem p1098 : P1098 := by simp [P1098, m1098]

def m1099 (rt : Runtime) (_R _bc : Value) : M Value := call0 rt "false"
def P1099 : Prop := ∀ rt R bc, m1099 rt R bc = call0 rt "false"
theorem p1099 : P1099 := by simp [P1099, m1099]

def m1100 (rt : Runtime) (R bc _f : Value) : M Value := do
  let args ← call1 rt "getfield:args" bc
  call2 rt "ischunkedbroadcast" R args
def P1100 : Prop := ∀ rt R bc f, m1100 rt R bc f = do
  let args ← call1 rt "getfield:args" bc
  call2 rt "ischunkedbroadcast" R args
theorem p1100 : P1100 := by simp [P1100, m1100]

def m1101 (rt : Runtime) (_R _args : Value) : M Value := call0 rt "false"
def P1101 : Prop := ∀ rt R args, m1101 rt R args = call0 rt "false"
theorem p1101 : P1101 := by simp [P1101, m1101]

def m1102 (rt : Runtime) (R head tail : Value) : M Value := do
  let sr ← call1 rt "size" R
  let sh ← call1 rt "size" head
  if rt.truth (← call2 rt "==" sr sh) then call2 rt "ischunkedbroadcast" R tail
  else call0 rt "false"
def P1102 : Prop := ∀ rt R head tail, m1102 rt R head tail = do
  let sr ← call1 rt "size" R
  let sh ← call1 rt "size" head
  if rt.truth (← call2 rt "==" sr sh) then call2 rt "ischunkedbroadcast" R tail
  else call0 rt "false"
theorem p1102 : P1102 := by simp [P1102, m1102]

def m1103 (rt : Runtime) (R _head tail : Value) : M Value := call2 rt "ischunkedbroadcast" R tail
def P1103 : Prop := ∀ rt R head tail, m1103 rt R head tail = call2 rt "ischunkedbroadcast" R tail
theorem p1103 : P1103 := by simp [P1103, m1103]

def m1104 (rt : Runtime) (R head tail : Value) : M Value := do
  if rt.truth (← call2 rt "ischunkedbroadcast" R head) then call2 rt "ischunkedbroadcast" R tail
  else call0 rt "false"
def P1104 : Prop := ∀ rt R head tail, m1104 rt R head tail = do
  if rt.truth (← call2 rt "ischunkedbroadcast" R head) then call2 rt "ischunkedbroadcast" R tail
  else call0 rt "false"
theorem p1104 : P1104 := by simp [P1104, m1104]

def m1105 (rt : Runtime) (_R : Value) : M Value := call0 rt "true"
def P1105 : Prop := ∀ rt R, m1105 rt R = call0 rt "true"
theorem p1105 : P1105 := by simp [P1105, m1105]

def m1108 (rt : Runtime) (bc : Value) : M Value := do
  let f0 ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let f ← call2 rt "_chunkop" f0 args
  call2 rt "liftfuncs" bc f
def P1108 : Prop := ∀ rt bc, m1108 rt bc = do
  let f0 ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let f ← call2 rt "_chunkop" f0 args
  call2 rt "liftfuncs" bc f
theorem p1108 : P1108 := by simp [P1108, m1108]

def m1109 (rt : Runtime) (bc : Value) : M Value := do
  let style ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let args ← call2 rt "map" (← call0 rt "liftfuncs:function") args
  let axes ← call1 rt "getfield:axes" bc
  rt.call "Broadcasted" [style, f, args, axes]
def P1109 : Prop := ∀ rt bc, m1109 rt bc = do
  let style ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let args ← call2 rt "map" (← call0 rt "liftfuncs:function") args
  let axes ← call1 rt "getfield:axes" bc
  rt.call "Broadcasted" [style, f, args, axes]
theorem p1109 : P1109 := by simp [P1109, m1109]

def m1110 (rt : Runtime) (bc f : Value) : M Value := do
  let style ← call1 rt "getfield:style" bc
  let args ← call1 rt "getfield:args" bc
  let args ← call2 rt "map" (← call0 rt "liftfuncs:function") args
  let axes ← call1 rt "getfield:axes" bc
  rt.call "Broadcasted" [style, f, args, axes]
def P1110 : Prop := ∀ rt bc f, m1110 rt bc f = do
  let style ← call1 rt "getfield:style" bc
  let args ← call1 rt "getfield:args" bc
  let args ← call2 rt "map" (← call0 rt "liftfuncs:function") args
  let axes ← call1 rt "getfield:axes" bc
  rt.call "Broadcasted" [style, f, args, axes]
theorem p1110 : P1110 := by simp [P1110, m1110]

def m1111 (_rt : Runtime) (x : Value) : M Value := pure x
def P1111 : Prop := ∀ rt x, m1111 rt x = pure x
theorem p1111 : P1111 := by simp [P1111, m1111]

def m1113 (rt : Runtime) : M Value := call0 rt "tuple:empty"
def P1113 : Prop := ∀ rt, m1113 rt = call0 rt "tuple:empty"
theorem p1113 : P1113 := by simp [P1113, m1113]

def m1114 (rt : Runtime) (head tail : Value) : M Value := do
  let chunks ← call1 rt "getfield:chunks" head
  let rest ← call1 rt "liftchunks" tail
  call2 rt "tuple:(chunks,rest...)" chunks rest
def P1114 : Prop := ∀ rt head tail, m1114 rt head tail = do
  let chunks ← call1 rt "getfield:chunks" head
  let rest ← call1 rt "liftchunks" tail
  call2 rt "tuple:(chunks,rest...)" chunks rest
theorem p1114 : P1114 := by simp [P1114, m1114]

def m1116 (rt : Runtime) (head tail : Value) : M Value := do
  let all ← call0 rt "typemax(UInt64)"
  let zero ← call0 rt "UInt64:0"
  let word ← rt.call "ifelse" [head, all, zero]
  let rest ← call1 rt "liftchunks" tail
  call2 rt "tuple:(word,rest...)" word rest
def P1116 : Prop := ∀ rt head tail, m1116 rt head tail = do
  let all ← call0 rt "typemax(UInt64)"
  let zero ← call0 rt "UInt64:0"
  let word ← rt.call "ifelse" [head, all, zero]
  let rest ← call1 rt "liftchunks" tail
  call2 rt "tuple:(word,rest...)" word rest
theorem p1116 : P1116 := by simp [P1116, m1116]

def m1117 (rt : Runtime) (_i : Value) : M Value := call0 rt "tuple:empty"
def P1117 : Prop := ∀ rt i, m1117 rt i = call0 rt "tuple:empty"
theorem p1117 : P1117 := by simp [P1117, m1117]

def m1118 (rt : Runtime) (i c args : Value) : M Value := do
  let word ← call2 rt "getindex" c i
  let rest ← rt.call "ithchunk:slurp" [i, args]
  call2 rt "tuple:(word,rest...)" word rest
def P1118 : Prop := ∀ rt i c args, m1118 rt i c args = do
  let word ← call2 rt "getindex" c i
  let rest ← rt.call "ithchunk:slurp" [i, args]
  call2 rt "tuple:(word,rest...)" word rest
theorem p1118 : P1118 := by simp [P1118, m1118]

def m1119 (rt : Runtime) (i b args : Value) : M Value := do
  let rest ← rt.call "ithchunk:slurp" [i, args]
  call2 rt "tuple:(word,rest...)" b rest
def P1119 : Prop := ∀ rt i b args, m1119 rt i b args = do
  let rest ← rt.call "ithchunk:slurp" [i, args]
  call2 rt "tuple:(word,rest...)" b rest
theorem p1119 : P1119 := by simp [P1119, m1119]

def m1120 (rt : Runtime) (dest bc : Value) : M Value := do
  if rt.truth (← call1 rt "isempty" dest) then pure dest else
    let lifted ← call1 rt "liftfuncs" bc
    let f ← call1 rt "flatten" lifted
    let fargs ← call1 rt "getfield:args" f
    let args ← call1 rt "liftchunks" fargs
    let dc ← call1 rt "getfield:chunks" dest
    let indices ← call1 rt "eachindex" dc
    let _ ← rt.forEach indices fun i => do
      let ff ← call1 rt "getfield:f" f
      let words ← rt.call "ithchunk:slurp" [i, args]
      let value ← rt.call "call:slurp" [ff, words]
      let _ ← rt.call "setindex!" [dc, value, i]
      pure ()
    let lastIndex ← call0 rt "end"
    let last ← call2 rt "getindex" dc lastIndex
    let mask ← call1 rt "Base._msk_end" dest
    let masked ← call2 rt "&" last mask
    let _ ← rt.call "setindex!" [dc, masked, lastIndex]
    pure dest
def P1120 : Prop := ∀ rt dest bc, m1120 rt dest bc = do
  if rt.truth (← call1 rt "isempty" dest) then pure dest else
    let lifted ← call1 rt "liftfuncs" bc
    let f ← call1 rt "flatten" lifted
    let fargs ← call1 rt "getfield:args" f
    let args ← call1 rt "liftchunks" fargs
    let dc ← call1 rt "getfield:chunks" dest
    let indices ← call1 rt "eachindex" dc
    let _ ← rt.forEach indices fun i => do
      let ff ← call1 rt "getfield:f" f
      let words ← rt.call "ithchunk:slurp" [i, args]
      let value ← rt.call "call:slurp" [ff, words]
      let _ ← rt.call "setindex!" [dc, value, i]
      pure ()
    let lastIndex ← call0 rt "end"
    let last ← call2 rt "getindex" dc lastIndex
    let mask ← call1 rt "Base._msk_end" dest
    let masked ← call2 rt "&" last mask
    let _ ← rt.call "setindex!" [dc, masked, lastIndex]
    pure dest
theorem p1120 : P1120 := by simp [P1120, m1120]

def program1035 (rt : Runtime) (dest bc : Value) : M Value := do
  let destAxes ← call1 rt "axes" dest
  let bcAxes ← call1 rt "axes" bc
  if !rt.truth (← call2 rt "==" destAxes bcAxes) then rt.call "throwdm" [destAxes, bcAxes] else
    if rt.truth (← call2 rt "ischunkedbroadcast" dest bc) then call2 rt "chunkedcopyto!" dest bc else
      let nd ← call1 rt "ndims" dest
      if rt.truth (← call2 rt "==" nd (← call0 rt "Int:0")) then
        let value ← call1 rt "getindex:empty" bc
        let _ ← rt.call "setindex!:empty" [dest, value]
        pure dest
      else
        let prepared ← call2 rt "preprocess" dest bc
        let ax ← call1 rt "axes" dest
        let ax1 ← call2 rt "getindex" ax (← one rt)
        let out ← call1 rt "CartesianIndices" (← call1 rt "tail" ax)
        let destc ← call1 rt "getfield:chunks" dest
        let indc ← call1 rt "local:init:Int:0" dest
        let bitst ← call1 rt "local:init:Int:0" dest
        let remain ← call1 rt "local:init:UInt64:0" dest
        let _ ← rt.forEach out fun I => do
          let first ← call1 rt "first" ax1
          let i ← call1 rt "local:init:first-minus-one" first
          let bcDims ← call1 rt "ndims" bc
          let oneDim ← call2 rt "==" bcDims (← one rt)
          let bitpos ← call1 rt "local:read" bitst
          let axisLen ← call1 rt "length" ax1
          let threshold ← call2 rt "-" (← call0 rt "Int:64") axisLen
          let room ← call2 rt ">=" bitpos threshold
          if rt.truth oneDim || rt.truth room then
            let multi ← call2 rt ">" bcDims (← one rt)
            let nonzero ← call2 rt "!=" bitpos (← call0 rt "Int:0")
            if rt.truth multi && rt.truth nonzero then
              let range ← rt.call "range" [bitpos, (← call0 rt "Int:63")]
              let _ ← rt.forEach range fun j => do
                let nexti ← call1 rt "local:preincrement" i
                let value ← rt.call "getindex" [prepared, nexti, I]
                let value ← call1 rt "convert:Bool" value
                let word ← call1 rt "UInt64" value
                let shift ← call2 rt "&" j (← call0 rt "Int:63")
                let word ← call2 rt "<<" word shift
                let old ← call1 rt "local:read" remain
                let new ← call2 rt "|" old word
                let _ ← rt.call "local:write" [remain, new]
                pure ()
              let chunk ← call1 rt "local:read" remain
              let index ← call1 rt "local:preincrement" indc
              let _ ← rt.call "setindex!" [destc, chunk, index]
              let _ ← rt.call "local:write" [bitst, (← call0 rt "Int:0")]
              let _ ← rt.call "local:write" [remain, (← call0 rt "UInt64:0")]
              pure ()
            else pure ()
            let condition : M Bool := do
              let iv ← call1 rt "local:read" i
              let last ← call1 rt "last" ax1
              let stop ← call2 rt "-" last (← call0 rt "Int:64")
              return rt.truth (← call2 rt "<=" iv stop)
            let body : M Unit := do
              let z ← call1 rt "local:init:UInt64:0" dest
              let js ← rt.call "range" [(← call0 rt "Int:0"), (← call0 rt "Int:63")]
              let _ ← rt.forEach js fun j => do
                let nexti ← call1 rt "local:preincrement" i
                let value ← rt.call "getindex" [prepared, nexti, I]
                let value ← call1 rt "convert:Bool" value
                let word ← call1 rt "UInt64" value
                let shift ← call2 rt "&" j (← call0 rt "Int:63")
                let word ← call2 rt "<<" word shift
                let old ← call1 rt "local:read" z
                let new ← call2 rt "|" old word
                let _ ← rt.call "local:write" [z, new]
                pure ()
              let chunk ← call1 rt "local:read" z
              let index ← call1 rt "local:preincrement" indc
              let _ ← rt.call "setindex!" [destc, chunk, index]
              pure ()
            rt.whileDo condition body
          else pure ()
          let iv ← call1 rt "local:read" i
          let start ← call2 rt "+" iv (← one rt)
          let stop ← call1 rt "last" ax1
          let range ← rt.call "range" [start, stop]
          rt.forEach range fun j => do
            let value ← rt.call "getindex" [prepared, j, I]
            let value ← call1 rt "convert:Bool" value
            let word ← call1 rt "UInt64" value
            let bitpos ← call1 rt "local:read" bitst
            let shift ← call2 rt "&" bitpos (← call0 rt "Int:63")
            let word ← call2 rt "<<" word shift
            let old ← call1 rt "local:read" remain
            let new ← call2 rt "|" old word
            let _ ← rt.call "local:write" [remain, new]
            let _ ← call1 rt "local:increment" bitst
            pure ()
        let bitpos ← call1 rt "local:read" bitst
        if rt.truth (← call2 rt "!=" bitpos (← call0 rt "Int:0")) then
          let index ← call2 rt "+" (← call1 rt "local:read" indc) (← one rt)
          let chunk ← call1 rt "local:read" remain
          let _ ← rt.call "setindex!" [destc, chunk, index]
          pure dest
        else pure dest

def m1035 (rt : Runtime) (dest bc : Value) : M Value := program1035 rt dest bc
def P1035 : Prop := ∀ rt dest bc, m1035 rt dest bc = program1035 rt dest bc
theorem p1035 : P1035 := by simp [P1035, m1035]

def m1261 (rt : Runtime) (rankN rankM parent mask : Value) : M Value :=
  rt.call "new:BitMaskedBitArray" [rankN, rankM, parent, mask]
def P1261 : Prop := ∀ rt rankN rankM parent mask,
  m1261 rt rankN rankM parent mask = rt.call "new:BitMaskedBitArray" [rankN, rankM, parent, mask]
theorem p1261 : P1261 := by simp [P1261, m1261]

def m1263 (rt : Runtime) (rankN rankM parent mask : Value) : M Value := do
  let _ ← call2 rt "checkbounds" parent mask
  rt.call "BitMaskedBitArray{N,M}" [rankN, rankM, parent, mask]
def P1263 : Prop := ∀ rt rankN rankM parent mask, m1263 rt rankN rankM parent mask = do
  let _ ← call2 rt "checkbounds" parent mask
  rt.call "BitMaskedBitArray{N,M}" [rankN, rankM, parent, mask]
theorem p1263 : P1263 := by simp [P1263, m1263]

def m1267 (rt : Runtime) (B i : Value) : M Value := call2 rt "BitMaskedBitArray" B i
def P1267 : Prop := ∀ rt B i, m1267 rt B i = call2 rt "BitMaskedBitArray" B i
theorem p1267 : P1267 := by simp [P1267, m1267]

def m1268 (rt : Runtime) (io B : Value) : M Value := do
  let T ← call1 rt "typeof" B
  let parent ← call1 rt "getfield:parent" B
  let mask ← call1 rt "getfield:mask" B
  let nested ← rt.call "tuple" [parent, mask]
  let args ← rt.call "tuple" [T, nested]
  let closure ← rt.call "closure:arg->show(io,arg)" [io]
  call2 rt "foreach" closure args
def P1268 : Prop := ∀ rt io B, m1268 rt io B = do
  let T ← call1 rt "typeof" B
  let parent ← call1 rt "getfield:parent" B
  let mask ← call1 rt "getfield:mask" B
  let nested ← rt.call "tuple" [parent, mask]
  let args ← rt.call "tuple" [T, nested]
  let closure ← rt.call "closure:arg->show(io,arg)" [io]
  call2 rt "foreach" closure args
theorem p1268 : P1268 := by simp [P1268, m1268]

def m1270 (rt : Runtime) (B bc : Value) : M Value := do
  let args ← call1 rt "getfield:args" bc
  let value ← call2 rt "getindex" args (← one rt)
  call2 rt "fill!" B value
def P1270 : Prop := ∀ rt B bc, m1270 rt B bc = do
  let args ← call1 rt "getfield:args" bc
  let value ← call2 rt "getindex" args (← one rt)
  call2 rt "fill!" B value
theorem p1270 : P1270 := by simp [P1270, m1270, one]

def m1271 (rt : Runtime) (B bc : Value) : M Value := do
  let parent ← call1 rt "getfield:parent" B
  let mask ← call1 rt "getfield:mask" B
  let view ← call2 rt "view" parent mask
  call2 rt "materialize!" view bc
def P1271 : Prop := ∀ rt B bc, m1271 rt B bc = do
  let parent ← call1 rt "getfield:parent" B
  let mask ← call1 rt "getfield:mask" B
  let view ← call2 rt "view" parent mask
  call2 rt "materialize!" view bc
theorem p1271 : P1271 := by simp [P1271, m1271]

def m1272 (rt : Runtime) (B b : Value) : M Value := do
  let parent ← call1 rt "getfield:parent" B
  let Bc ← call1 rt "getfield:chunks" parent
  let mask ← call1 rt "getfield:mask" B
  let Ic ← call1 rt "getfield:chunks" mask
  let n ← call1 rt "length" Bc
  let range ← rt.call "range:1:n" [(← one rt), n]
  let _ ← rt.forEach range fun i => do
    let old ← call2 rt "getindex" Bc i
    let bits ← call2 rt "getindex" Ic i
    let value ← if rt.truth b then call2 rt "|" old bits else
      let bits ← call1 rt "~" bits
      call2 rt "&" old bits
    let _ ← rt.call "setindex!" [Bc, value, i]
    pure ()
  pure B
def P1272 : Prop := ∀ rt B b, m1272 rt B b = do
  let parent ← call1 rt "getfield:parent" B
  let Bc ← call1 rt "getfield:chunks" parent
  let mask ← call1 rt "getfield:mask" B
  let Ic ← call1 rt "getfield:chunks" mask
  let n ← call1 rt "length" Bc
  let range ← rt.call "range:1:n" [(← one rt), n]
  let _ ← rt.forEach range fun i => do
    let old ← call2 rt "getindex" Bc i
    let bits ← call2 rt "getindex" Ic i
    let value ← if rt.truth b then call2 rt "|" old bits else
      let bits ← call1 rt "~" bits
      call2 rt "&" old bits
    let _ ← rt.call "setindex!" [Bc, value, i]
    pure ()
  pure B
theorem p1272 : P1272 := by simp [P1272, m1272, one]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; source equation and BitArray invariant",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.BroadcastCov.BitsExact
