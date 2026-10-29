import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.StyleExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def m37 (rt : Runtime) : M Value := call0 rt "Unknown"
def P37 : Prop := ∀ rt, m37 rt = call0 rt "Unknown"
theorem p37 : P37 := by simp [P37, m37]

def m38 (rt : Runtime) (slurp : List Value) : M Value :=
  rt.call "throw:MethodError:BroadcastStyle" slurp
def P38 : Prop := ∀ rt slurp, m38 rt slurp = rt.call "throw:MethodError:BroadcastStyle" slurp
theorem p38 : P38 := by simp [P38, m38]

def m49 (rt : Runtime) : M Value := call0 rt "Style{Tuple}"
def P49 : Prop := ∀ rt, m49 rt = call0 rt "Style{Tuple}"
theorem p49 : P49 := by simp [P49, m49]

def m87 (rt : Runtime) (A val : Value) : M Value := call1 rt "ArrayStyle" A
def P87 : Prop := ∀ rt A val, m87 rt A val = call1 rt "ArrayStyle" A
theorem p87 : P87 := by simp [P87, m87]

def m98 (rt : Runtime) (N : Value) : M Value := call1 rt "DefaultArrayStyle" N
def P98 : Prop := ∀ rt N, m98 rt N = call1 rt "DefaultArrayStyle" N
theorem p98 : P98 := by simp [P98, m98]

def m99 (rt : Runtime) (oldRank newRank : Value) : M Value := call1 rt "DefaultArrayStyle" newRank
def P99 : Prop := ∀ rt oldRank newRank, m99 rt oldRank newRank = call1 rt "DefaultArrayStyle" newRank
theorem p99 : P99 := by simp [P99, m99]

def m102 (rt : Runtime) (N : Value) : M Value := call1 rt "DefaultArrayStyle" N
def P102 : Prop := ∀ rt N, m102 rt N = call1 rt "DefaultArrayStyle" N
theorem p102 : P102 := by simp [P102, m102]

def m103 (rt : Runtime) (T : Value) : M Value := do
  let n ← call1 rt "ndims" T
  call1 rt "DefaultArrayStyle" n
def P103 : Prop := ∀ rt T, m103 rt T = do
  let n ← call1 rt "ndims" T
  call1 rt "DefaultArrayStyle" n
theorem p103 : P103 := by simp [P103, m103]

def m111 (rt : Runtime) (_val : Value) : M Value := call0 rt "ArrayConflict"
def P111 : Prop := ∀ rt val, m111 rt val = call0 rt "ArrayConflict"
theorem p111 : P111 := by simp [P111, m111]

def m128 (rt : Runtime) (S : Value) : M Value := call1 rt "construct-type" S
def P128 : Prop := ∀ rt S, m128 rt S = call1 rt "construct-type" S
theorem p128 : P128 := by simp [P128, m128]

def m130 (rt : Runtime) : M Value := call0 rt "Unknown"
def P130 : Prop := ∀ rt, m130 rt = call0 rt "Unknown"
theorem p130 : P130 := by simp [P130, m130]

def m132 (rt : Runtime) : M Value := call0 rt "Unknown"
def P132 : Prop := ∀ rt, m132 rt = call0 rt "Unknown"
theorem p132 : P132 := by simp [P132, m132]

def m133 (rt : Runtime) (S : Value) : M Value := call1 rt "construct-type" S
def P133 : Prop := ∀ rt S, m133 rt S = call1 rt "construct-type" S
theorem p133 : P133 := by simp [P133, m133]

def m135 (_rt : Runtime) (_a b : Value) : M Value := pure b
def P135 : Prop := ∀ rt a b, m135 rt a b = pure b
theorem p135 : P135 := by simp [P135, m135]

def m136 (_rt : Runtime) (a : Value) (_tupleStyle : Value) : M Value := pure a
def P136 : Prop := ∀ rt a b, m136 rt a b = pure a
theorem p136 : P136 := by simp [P136, m136]

def m137 (rt : Runtime) (A : Value) : M Value := call1 rt "construct-type" A
def P137 : Prop := ∀ rt A, m137 rt A = call1 rt "construct-type" A
theorem p137 : P137 := by simp [P137, m137]

def m138 (rt : Runtime) : M Value := call0 rt "Unknown"
def P138 : Prop := ∀ rt, m138 rt = call0 rt "Unknown"
theorem p138 : P138 := by simp [P138, m138]

def m139 (rt : Runtime) (A : Value) : M Value := call1 rt "construct-type" A
def P139 : Prop := ∀ rt A, m139 rt A = call1 rt "construct-type" A
theorem p139 : P139 := by simp [P139, m139]

def m140 (rt : Runtime) (A B rankA rankB : Value) : M Value := do
  let ta ← call1 rt "Base.typename" A
  let tb ← call1 rt "Base.typename" B
  if rt.truth (← call2 rt "===" ta tb) then
    let rank ← call2 rt "max" rankA rankB
    let valRank ← call1 rt "Val" rank
    call2 rt "apply-type" A valRank
  else call0 rt "Unknown"
def P140 : Prop := ∀ rt A B rankA rankB, m140 rt A B rankA rankB = do
  let ta ← call1 rt "Base.typename" A
  let tb ← call1 rt "Base.typename" B
  if rt.truth (← call2 rt "===" ta tb) then
    let rank ← call2 rt "max" rankA rankB
    let valRank ← call1 rt "Val" rank
    call2 rt "apply-type" A valRank
  else call0 rt "Unknown"
theorem p140 : P140 := by simp [P140, m140]

def m147 (_rt : Runtime) (a : Value) (_default : Value) : M Value := pure a
def P147 : Prop := ∀ rt a b, m147 rt a b = pure a
theorem p147 : P147 := by simp [P147, m147]

def m148 (_rt : Runtime) (a : Value) (_default : Value) : M Value := pure a
def P148 : Prop := ∀ rt a b, m148 rt a b = pure a
theorem p148 : P148 := by simp [P148, m148]

def m149 (rt : Runtime) (a rankA rankB : Value) : M Value := do
  let A ← call1 rt "typeof" a
  let rank ← call2 rt "max" rankA rankB
  let valRank ← call1 rt "Val" rank
  call2 rt "apply-type" A valRank
def P149 : Prop := ∀ rt a rankA rankB, m149 rt a rankA rankB = do
  let A ← call1 rt "typeof" a
  let rank ← call2 rt "max" rankA rankB
  let valRank ← call1 rt "Val" rank
  call2 rt "apply-type" A valRank
theorem p149 : P149 := by simp [P149, m149]

def m431 (rt : Runtime) : M Value := call1 rt "DefaultArrayStyle" 0
def P431 : Prop := ∀ rt, m431 rt = call1 rt "DefaultArrayStyle" 0
theorem p431 : P431 := by simp [P431, m431]

def m432 (rt : Runtime) (c : Value) : M Value := do
  let T ← call1 rt "typeof" c
  let s ← call1 rt "BroadcastStyle" T
  call1 rt "result_style" s
def P432 : Prop := ∀ rt c, m432 rt c = do
  let T ← call1 rt "typeof" c
  let s ← call1 rt "BroadcastStyle" T
  call1 rt "result_style" s
theorem p432 : P432 := by simp [P432, m432]

def m433 (rt : Runtime) (bc : Value) : M Value := do
  let style ← call1 rt "getfield:style" bc
  let acceptable ← call2 rt "isa" style (← call0 rt "Union{Nothing,Unknown}")
  if !rt.truth acceptable then pure style else raise .argumentError
def P433 : Prop := ∀ rt bc, m433 rt bc = do
  let style ← call1 rt "getfield:style" bc
  let acceptable ← call2 rt "isa" style (← call0 rt "Union{Nothing,Unknown}")
  if !rt.truth acceptable then pure style else raise .argumentError
theorem p433 : P433 := by simp [P433, m433]

def m437 (rt : Runtime) (c1 c2 : Value) : M Value := do
  let s1 ← call1 rt "combine_styles" c1
  let s2 ← call1 rt "combine_styles" c2
  call2 rt "result_style" s1 s2
def P437 : Prop := ∀ rt c1 c2, m437 rt c1 c2 = do
  let s1 ← call1 rt "combine_styles" c1
  let s2 ← call1 rt "combine_styles" c2
  call2 rt "result_style" s1 s2
theorem p437 : P437 := by simp [P437, m437]

def m438 (rt : Runtime) (c1 c2 : Value) (cs : List Value) : M Value := do
  let s1 ← call1 rt "combine_styles" c1
  let rest ← rt.call "combine_styles" (c2 :: cs)
  call2 rt "result_style" s1 rest
def P438 : Prop := ∀ rt c1 c2 cs, m438 rt c1 c2 cs = do
  let s1 ← call1 rt "combine_styles" c1
  let rest ← rt.call "combine_styles" (c2 :: cs)
  call2 rt "result_style" s1 rest
theorem p438 : P438 := by simp [P438, m438]

def m458 (_rt : Runtime) (s : Value) : M Value := pure s
def P458 : Prop := ∀ rt s, m458 rt s = pure s
theorem p458 : P458 := by simp [P458, m458]

def m459 (rt : Runtime) (s1 s2 : Value) : M Value := do
  if rt.truth (← call2 rt "≡" s1 s2) then pure s1 else raise .errorException
def P459 : Prop := ∀ rt s1 s2, m459 rt s1 s2 = do
  if rt.truth (← call2 rt "≡" s1 s2) then pure s1 else raise .errorException
theorem p459 : P459 := by simp [P459, m459]

def m463 (rt : Runtime) (s1 s2 : Value) : M Value := do
  let forward ← call2 rt "BroadcastStyle" s1 s2
  let reverse ← call2 rt "BroadcastStyle" s2 s1
  call4 rt "result_join" s1 s2 forward reverse
def P463 : Prop := ∀ rt s1 s2, m463 rt s1 s2 = do
  let forward ← call2 rt "BroadcastStyle" s1 s2
  let reverse ← call2 rt "BroadcastStyle" s2 s1
  call4 rt "result_join" s1 s2 forward reverse
theorem p463 : P463 := by simp [P463, m463]

def m467 (rt : Runtime) : M Value := call0 rt "Unknown"
def P467 : Prop := ∀ rt, m467 rt = call0 rt "Unknown"
theorem p467 : P467 := by simp [P467, m467]

def m468 (_rt : Runtime) (s : Value) : M Value := pure s
def P468 : Prop := ∀ rt s, m468 rt s = pure s
theorem p468 : P468 := by simp [P468, m468]

def m469 (_rt : Runtime) (s : Value) : M Value := pure s
def P469 : Prop := ∀ rt s, m469 rt s = pure s
theorem p469 : P469 := by simp [P469, m469]

def m474 (rt : Runtime) : M Value := call0 rt "ArrayConflict"
def P474 : Prop := ∀ rt, m474 rt = call0 rt "ArrayConflict"
theorem p474 : P474 := by simp [P474, m474]

def m477 (rt : Runtime) (s1 s2 : Value) : M Value := call2 rt "result_style" s1 s2
def P477 : Prop := ∀ rt s1 s2, m477 rt s1 s2 = call2 rt "result_style" s1 s2
theorem p477 : P477 := by simp [P477, m477]

def m479 (rt : Runtime) (S T U V : Value) : M Value :=
  rt.call "error:conflicting broadcast rules" [S, T, U, V]
def P479 : Prop := ∀ rt S T U V,
  m479 rt S T U V = rt.call "error:conflicting broadcast rules" [S, T, U, V]
theorem p479 : P479 := by simp [P479, m479]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement := statement
    source := s!"base/broadcast.jl:{line}; source equation and dispatch invariant"
    status := .proven
    prop := prop
    thm := some thm }

def entries : List Entry := []

end JuliaLean.BroadcastCov.StyleExact
