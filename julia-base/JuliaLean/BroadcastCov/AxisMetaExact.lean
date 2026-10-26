import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.AxisMetaExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def m240 (rt : Runtime) (bc : Value) : M Value := do
  let stored ← call1 rt "getfield:axes" bc
  rt.call "_axes" [bc, stored]
def P240 : Prop := ∀ rt bc, m240 rt bc = do
  let stored ← call1 rt "getfield:axes" bc
  rt.call "_axes" [bc, stored]
theorem p240 : P240 := by simp [P240, m240]

def m241 (_rt : Runtime) (_bc axes : Value) : M Value := pure axes
def P241 : Prop := ∀ rt bc axes, m241 rt bc axes = pure axes
theorem p241 : P241 := by simp [P241, m241]

def m242 (rt : Runtime) (bc : Value) : M Value := do
  let args ← call1 rt "getfield:args" bc
  call1 rt "combine_axes:slurp" args
def P242 : Prop := ∀ rt bc, m242 rt bc = do
  let args ← call1 rt "getfield:args" bc
  call1 rt "combine_axes:slurp" args
theorem p242 : P242 := by simp [P242, m242]

def m243 (rt : Runtime) (_bc : Value) : M Value := call0 rt "tuple:empty"
def P243 : Prop := ∀ rt bc, m243 rt bc = call0 rt "tuple:empty"
theorem p243 : P243 := by simp [P243, m243]

def m245 (rt : Runtime) (bc N d : Value) : M Value := do
  if rt.truth (← call2 rt "<=" d N) then
    let ax ← call1 rt "axes" bc
    call2 rt "getindex" ax d
  else call1 rt "OneTo" (← call0 rt "Int:1")
def P245 : Prop := ∀ rt bc N d, m245 rt bc N d = do
  if rt.truth (← call2 rt "<=" d N) then
    let ax ← call1 rt "axes" bc
    call2 rt "getindex" ax d
  else call1 rt "OneTo" (← call0 rt "Int:1")
theorem p245 : P245 := by simp [P245, m245]

def m255 (rt : Runtime) (bc : Value) : M Value := do
  let style ← call1 rt "IndexStyle" bc
  rt.call "eachindex" [style, bc]
def P255 : Prop := ∀ rt bc, m255 rt bc = do
  let style ← call1 rt "IndexStyle" bc
  rt.call "eachindex" [style, bc]
theorem p255 : P255 := by simp [P255, m255]

def m256 (rt : Runtime) (style bc : Value) : M Value := do
  let ax ← call1 rt "axes" bc
  rt.call "_eachindex" [style, ax]
def P256 : Prop := ∀ rt style bc, m256 rt style bc = do
  let ax ← call1 rt "axes" bc
  rt.call "_eachindex" [style, ax]
theorem p256 : P256 := by simp [P256, m256]

def m257 (rt : Runtime) (tuple : Value) : M Value := call1 rt "CartesianIndices" tuple
def P257 : Prop := ∀ rt tuple, m257 rt tuple = call1 rt "CartesianIndices" tuple
theorem p257 : P257 := by simp [P257, m257]

def m258 (rt : Runtime) (style tuple : Value) : M Value := do
  let linear ← call1 rt "LinearIndices" tuple
  rt.call "eachindex" [style, linear]
def P258 : Prop := ∀ rt style tuple, m258 rt style tuple = do
  let linear ← call1 rt "LinearIndices" tuple
  rt.call "eachindex" [style, linear]
theorem p258 : P258 := by simp [P258, m258]

def m259 (rt : Runtime) (tuple : Value) : M Value :=
  call2 rt "getindex" tuple (0 : Value)
def P259 : Prop := ∀ rt tuple, m259 rt tuple = call2 rt "getindex" tuple (0 : Value)
theorem p259 : P259 := by simp [P259, m259]

def m261 (rt : Runtime) (bc : Value) : M Value := do
  let T ← call1 rt "typeof" bc
  call1 rt "IndexStyle" T
def P261 : Prop := ∀ rt bc, m261 rt bc = do
  let T ← call1 rt "typeof" bc
  call1 rt "IndexStyle" T
theorem p261 : P261 := by simp [P261, m261]

def m262 (rt : Runtime) : M Value := call0 rt "IndexLinear"
def P262 : Prop := ∀ rt, m262 rt = call0 rt "IndexLinear"
theorem p262 : P262 := by simp [P262, m262]

def m263 (rt : Runtime) : M Value := call0 rt "IndexCartesian"
def P263 : Prop := ∀ rt, m263 rt = call0 rt "IndexCartesian"
theorem p263 : P263 := by simp [P263, m263]

def m265 (rt : Runtime) (bc : Value) : M Value := do
  let ax ← call1 rt "axes" bc
  let linear ← call1 rt "LinearIndices" ax
  call2 rt "typeassert:LinearIndices{1}" linear (← call0 rt "LinearIndices{1}:type")
def P265 : Prop := ∀ rt bc, m265 rt bc = do
  let ax ← call1 rt "axes" bc
  let linear ← call1 rt "LinearIndices" ax
  call2 rt "typeassert:LinearIndices{1}" linear (← call0 rt "LinearIndices{1}:type")
theorem p265 : P265 := by simp [P265, m265]

def m267 (rt : Runtime) (bc : Value) : M Value := do
  let T ← call1 rt "typeof" bc
  call1 rt "ndims" T
def P267 : Prop := ∀ rt bc, m267 rt bc = do
  let T ← call1 rt "typeof" bc
  call1 rt "ndims" T
theorem p267 : P267 := by simp [P267, m267]

def m268 (_rt : Runtime) (N : Value) : M Value := pure N
def P268 : Prop := ∀ rt N, m268 rt N = pure N
theorem p268 : P268 := by simp [P268, m268]

def m269 (rt : Runtime) (BC : Value) : M Value := do
  let args ← call1 rt "argtype" BC
  call1 rt "_maxndims" args
def P269 : Prop := ∀ rt BC, m269 rt BC = do
  let args ← call1 rt "argtype" BC
  call1 rt "_maxndims" args
theorem p269 : P269 := by simp [P269, m269]

def m270 (rt : Runtime) (BC N : Value) : M Value := do
  let intType ← call0 rt "Int:type"
  if rt.truth (← call2 rt "isa" N intType) then pure N else
    let args ← call1 rt "argtype" BC
    call1 rt "_maxndims" args
def P270 : Prop := ∀ rt BC N, m270 rt BC N = do
  let intType ← call0 rt "Int:type"
  if rt.truth (← call2 rt "isa" N intType) then pure N else
    let args ← call1 rt "argtype" BC
    call1 rt "_maxndims" args
theorem p270 : P270 := by simp [P270, m270]

def m273 (rt : Runtime) : M Value := call0 rt "Int:0"
def P273 : Prop := ∀ rt, m273 rt = call0 rt "Int:0"
theorem p273 : P273 := by simp [P273, m273]

def m274 (rt : Runtime) (T : Value) : M Value := do
  let tupleType ← call0 rt "Tuple:type"
  if rt.truth (← call2 rt "<:" T tupleType) then call0 rt "Int:1" else
    let n ← call1 rt "ndims" T
    let n ← call1 rt "Int" n
    call2 rt "typeassert:Int" n (← call0 rt "Int:type")
def P274 : Prop := ∀ rt T, m274 rt T = do
  let tupleType ← call0 rt "Tuple:type"
  if rt.truth (← call2 rt "<:" T tupleType) then call0 rt "Int:1" else
    let n ← call1 rt "ndims" T
    let n ← call1 rt "Int" n
    call2 rt "typeassert:Int" n (← call0 rt "Int:type")
theorem p274 : P274 := by simp [P274, m274]

def m275 (rt : Runtime) (Args T : Value) : M Value := do
  let tupleType ← call0 rt "Tuple:type"
  let m ← if rt.truth (← call2 rt "<:" T tupleType) then call0 rt "Int:1" else
    let d ← call1 rt "ndims" T
    let d ← call1 rt "Int" d
    call2 rt "typeassert:Int" d (← call0 rt "Int:type")
  let tailType ← call1 rt "Base.tuple_type_tail" Args
  let n ← call1 rt "_maxndims" tailType
  call2 rt "max" m n
def P275 : Prop := ∀ rt Args T, m275 rt Args T = do
  let tupleType ← call0 rt "Tuple:type"
  let m ← if rt.truth (← call2 rt "<:" T tupleType) then call0 rt "Int:1" else
    let d ← call1 rt "ndims" T
    let d ← call1 rt "Int" d
    call2 rt "typeassert:Int" d (← call0 rt "Int:type")
  let tailType ← call1 rt "Base.tuple_type_tail" Args
  let n ← call1 rt "_maxndims" tailType
  call2 rt "max" m n
theorem p275 : P275 := by simp [P275, m275]

def m281 (rt : Runtime) (bc : Value) : M Value := do
  let ax ← call1 rt "axes" bc
  call2 rt "map" (← call0 rt "length:function") ax
def P281 : Prop := ∀ rt bc, m281 rt bc = do
  let ax ← call1 rt "axes" bc
  call2 rt "map" (← call0 rt "length:function") ax
theorem p281 : P281 := by simp [P281, m281]

def m282 (rt : Runtime) (bc : Value) : M Value := do
  let sz ← call1 rt "size" bc
  call1 rt "prod" sz
def P282 : Prop := ∀ rt bc, m282 rt bc = do
  let sz ← call1 rt "size" bc
  call1 rt "prod" sz
theorem p282 : P282 := by simp [P282, m282]

def m284 (rt : Runtime) (bc : Value) : M Value := do
  let iter ← call1 rt "eachindex" bc
  let state ← call1 rt "tuple:single" iter
  rt.call "iterate" [bc, state]
def P284 : Prop := ∀ rt bc, m284 rt bc = do
  let iter ← call1 rt "eachindex" bc
  let state ← call1 rt "tuple:single" iter
  rt.call "iterate" [bc, state]
theorem p284 : P284 := by simp [P284, m284]

def m288 (rt : Runtime) (bc state : Value) : M Value := do
  let y ← call1 rt "iterate:slurp" state
  let nothing ← call0 rt "nothing"
  if rt.truth (← call2 rt "===" y nothing) then pure nothing else
    let i ← call2 rt "getindex" y (← call0 rt "Int:1")
    let newstate ← call2 rt "getindex" y (← call0 rt "Int:2")
    let value ← call2 rt "getindex" bc i
    let iter ← call2 rt "getindex" state (← call0 rt "Int:1")
    let inner ← rt.call "tuple" [iter, newstate]
    rt.call "tuple" [value, inner]
def P288 : Prop := ∀ rt bc state, m288 rt bc state = do
  let y ← call1 rt "iterate:slurp" state
  let nothing ← call0 rt "nothing"
  if rt.truth (← call2 rt "===" y nothing) then pure nothing else
    let i ← call2 rt "getindex" y (← call0 rt "Int:1")
    let newstate ← call2 rt "getindex" y (← call0 rt "Int:2")
    let value ← call2 rt "getindex" bc i
    let iter ← call2 rt "getindex" state (← call0 rt "Int:1")
    let inner ← rt.call "tuple" [iter, newstate]
    rt.call "tuple" [value, inner]
theorem p288 : P288 := by simp [P288, m288]

def m295 (rt : Runtime) (T : Value) : M Value := do
  let n ← call1 rt "ndims" T
  call1 rt "Base.HasShape" n
def P295 : Prop := ∀ rt T, m295 rt T = do
  let n ← call1 rt "ndims" T
  call1 rt "Base.HasShape" n
theorem p295 : P295 := by simp [P295, m295]

def m296 (rt : Runtime) : M Value := call0 rt "Base.EltypeUnknown"
def P296 : Prop := ∀ rt, m296 rt = call0 rt "Base.EltypeUnknown"
theorem p296 : P296 := by simp [P296, m296]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; source equation and dispatch invariant",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry 240 "axes(::Broadcasted)" "axes reads the stored axes and dispatches to _axes." ``P240 ``p240,
  entry 241 "_axes(::Broadcasted,::Tuple)" "Stored tuple axes are returned unchanged." ``P241 ``p241,
  entry 242 "_axes(::Broadcasted,::Nothing)" "Missing axes are combined from the arguments." ``P242 ``p242,
  entry 243 "_axes(::Broadcasted{<:AbstractArrayStyle{0}},::Nothing)" "Zero-dimensional style has empty axes." ``P243 ``p243,
  entry 245 "axes(::Broadcasted,d)" "An in-rank dimension indexes axes and a trailing dimension returns OneTo(1)." ``P245 ``p245,
  entry 255 "eachindex(::Broadcasted)" "The default overload dispatches with IndexStyle(bc)." ``P255 ``p255,
  entry 256 "eachindex(::IndexStyle,::Broadcasted)" "Styled iteration delegates with axes(bc)." ``P256 ``p256,
  entry 257 "_eachindex(::IndexCartesian,tuple)" "Cartesian iteration constructs CartesianIndices." ``P257 ``p257,
  entry 258 "_eachindex(::IndexLinear,tuple)" "Linear iteration constructs LinearIndices before eachindex." ``P258 ``p258,
  entry 259 "_eachindex(::IndexLinear,::Tuple{Any})" "One-dimensional linear iteration returns the sole axis." ``P259 ``p259,
  entry 261 "IndexStyle(::Broadcasted)" "The value overload dispatches through typeof." ``P261 ``p261,
  entry 262 "IndexStyle(::Type{<:Broadcasted{...,Tuple{Any}}})" "A single-axis Broadcasted is IndexLinear." ``P262 ``p262,
  entry 263 "IndexStyle(::Type{<:Broadcasted})" "Other Broadcasted types are IndexCartesian." ``P263 ``p263,
  entry 265 "LinearIndices(::Broadcasted)" "LinearIndices constructs from axes and asserts rank one." ``P265 ``p265,
  entry 267 "ndims(::Broadcasted)" "The value overload dispatches through its type." ``P267 ``p267,
  entry 268 "ndims(::Type{<:Broadcasted{...,NTuple{N}}})" "Known tuple axes return N." ``P268 ``p268,
  entry 269 "ndims(::Type{<:Broadcasted{...,Nothing}})" "Unknown axes compute the maximum argument rank." ``P269 ``p269,
  entry 270 "ndims(::Type{<:Broadcasted{<:AbstractArrayStyle{N},Nothing}})" "Concrete integer N wins; other parameters use argument ranks." ``P270 ``p270,
  entry 273 "_maxndims(::Type{Tuple{}})" "An empty argument tuple has rank zero." ``P273 ``p273,
  entry 274 "_maxndims(::Type{Tuple{T}})" "A tuple argument counts as rank one and other values use ndims(T)." ``P274 ``p274,
  entry 275 "_maxndims(::Type{<:Tuple{T,Vararg}})" "The recursive maximum computes the head rank before the tail rank." ``P275 ``p275,
  entry 281 "size(::Broadcasted)" "Size maps length over the broadcast axes." ``P281 ``p281,
  entry 282 "length(::Broadcasted)" "Length is the product of size." ``P282 ``p282,
  entry 284 "iterate(::Broadcasted)" "Initial iteration creates and stores the eachindex iterator." ``P284 ``p284,
  entry 288 "iterate(::Broadcasted,state)" "State iteration advances the iterator, indexes bc, and packages the new state." ``P288 ``p288,
  entry 295 "IteratorSize(::Type{<:Broadcasted})" "IteratorSize is HasShape at the Broadcasted rank." ``P295 ``p295,
  entry 296 "IteratorEltype(::Type{<:Broadcasted})" "Broadcasted element type is declared unknown." ``P296 ``p296
]

end JuliaLean.BroadcastCov.AxisMetaExact
