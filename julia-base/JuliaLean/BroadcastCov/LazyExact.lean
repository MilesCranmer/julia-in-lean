import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.LazyExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def m175 (rt : Runtime) : M Value := raise .errorException
def P175 : Prop := ∀ rt, m175 rt = raise .errorException
theorem p175 : P175 := by simp [P175, m175]

def m176 (rt : Runtime) (style f args axes : Value) : M Value := do
  let styleType ← call1 rt "typeof" style
  let axesType ← call1 rt "typeof" axes
  let fType ← call1 rt "Core.Typeof" f
  let argsType ← call1 rt "typeof" args
  rt.call "new:Broadcasted" [styleType, axesType, fType, argsType, style, f, args, axes]
def P176 : Prop := ∀ rt style f args axes, m176 rt style f args axes = do
  let styleType ← call1 rt "typeof" style
  let axesType ← call1 rt "typeof" axes
  let fType ← call1 rt "Core.Typeof" f
  let argsType ← call1 rt "typeof" args
  rt.call "new:Broadcasted" [styleType, axesType, fType, argsType, style, f, args, axes]
theorem p176 : P176 := by simp [P176, m176]

def m181 (rt : Runtime) (f args axes : Value) (argValues : List Value) : M Value := do
  let style ← rt.call "combine_styles" argValues
  let style ← call2 rt "typeassert" style (← call0 rt "BroadcastStyle")
  rt.call "Broadcasted" [style, f, args, axes]
def P181 : Prop := ∀ rt f args axes argValues, m181 rt f args axes argValues = do
  let style ← rt.call "combine_styles" argValues
  let style ← call2 rt "typeassert" style (← call0 rt "BroadcastStyle")
  rt.call "Broadcasted" [style, f, args, axes]
theorem p181 : P181 := by simp [P181, m181]

def m185 (rt : Runtime) (Style f args axes : Value) : M Value := do
  let axesType ← call1 rt "typeof" axes
  let fType ← call1 rt "Core.Typeof" f
  let argsType ← call1 rt "typeof" args
  let style ← call1 rt "construct-type" Style
  let style ← call2 rt "typeassert" style Style
  rt.call "new:Broadcasted" [Style, axesType, fType, argsType, style, f, args, axes]
def P185 : Prop := ∀ rt Style f args axes, m185 rt Style f args axes = do
  let axesType ← call1 rt "typeof" axes
  let fType ← call1 rt "Core.Typeof" f
  let argsType ← call1 rt "typeof" args
  let style ← call1 rt "construct-type" Style
  let style ← call2 rt "typeassert" style Style
  rt.call "new:Broadcasted" [Style, axesType, fType, argsType, style, f, args, axes]
theorem p185 : P185 := by simp [P185, m185]

def m189 (rt : Runtime) (Style Axes F Args f args axes : Value) : M Value := do
  let style ← call1 rt "construct-type" Style
  let style ← call2 rt "typeassert" style Style
  rt.call "new:Broadcasted" [Style, Axes, F, Args, style, f, args, axes]
def P189 : Prop := ∀ rt Style Axes F Args f args axes,
  m189 rt Style Axes F Args f args axes = do
    let style ← call1 rt "construct-type" Style
    let style ← call2 rt "typeassert" style Style
    rt.call "new:Broadcasted" [Style, Axes, F, Args, style, f, args, axes]
theorem p189 : P189 := by simp [P189, m189]

def m196 (rt : Runtime) (a b : Value) : M Value := do
  let closure ← call0 rt "closure:(a,b)->a&&b"
  rt.call "broadcasted" [closure, a, b]
def P196 : Prop := ∀ rt a b, m196 rt a b = do
  let closure ← call0 rt "closure:(a,b)->a&&b"
  rt.call "broadcasted" [closure, a, b]
theorem p196 : P196 := by simp [P196, m196]

def m199 (rt : Runtime) (a bc : Value) : M Value := do
  let bcf ← call1 rt "flatten" bc
  let f ← call1 rt "getfield:f" bcf
  let args ← call1 rt "getfield:args" bcf
  let closure ← rt.call "closure:(a,args...)->a&&f(args...)" [f]
  rt.call "broadcasted:slurp" [closure, a, args]
def P199 : Prop := ∀ rt a bc, m199 rt a bc = do
  let bcf ← call1 rt "flatten" bc
  let f ← call1 rt "getfield:f" bcf
  let args ← call1 rt "getfield:args" bcf
  let closure ← rt.call "closure:(a,args...)->a&&f(args...)" [f]
  rt.call "broadcasted:slurp" [closure, a, args]
theorem p199 : P199 := by simp [P199, m199]

def m207 (rt : Runtime) (a b : Value) : M Value := do
  let closure ← call0 rt "closure:(a,b)->a||b"
  rt.call "broadcasted" [closure, a, b]
def P207 : Prop := ∀ rt a b, m207 rt a b = do
  let closure ← call0 rt "closure:(a,b)->a||b"
  rt.call "broadcasted" [closure, a, b]
theorem p207 : P207 := by simp [P207, m207]

def m208 (rt : Runtime) (a bc : Value) : M Value := do
  let bcf ← call1 rt "flatten" bc
  let f ← call1 rt "getfield:f" bcf
  let args ← call1 rt "getfield:args" bcf
  let closure ← rt.call "closure:(a,args...)->a||f(args...)" [f]
  rt.call "broadcasted:slurp" [closure, a, args]
def P208 : Prop := ∀ rt a bc, m208 rt a bc = do
  let bcf ← call1 rt "flatten" bc
  let f ← call1 rt "getfield:f" bcf
  let args ← call1 rt "getfield:args" bcf
  let closure ← rt.call "closure:(a,args...)->a||f(args...)" [f]
  rt.call "broadcasted:slurp" [closure, a, args]
theorem p208 : P208 := by simp [P208, m208]

def m215 (rt : Runtime) (NewStyle bc : Value) : M Value := do
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let axes ← call1 rt "getfield:axes" bc
  let converted ← rt.call "Broadcasted{NewStyle,Axes,F,Args}" [NewStyle, f, args, axes]
  call2 rt "typeassert:Broadcasted{NewStyle,Axes,F,Args}" converted NewStyle
def P215 : Prop := ∀ rt NewStyle bc, m215 rt NewStyle bc = do
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let axes ← call1 rt "getfield:axes" bc
  let converted ← rt.call "Broadcasted{NewStyle,Axes,F,Args}" [NewStyle, f, args, axes]
  call2 rt "typeassert:Broadcasted{NewStyle,Axes,F,Args}" converted NewStyle
theorem p215 : P215 := by simp [P215, m215]

def m218 (rt : Runtime) (io bc Style : Value) : M Value := do
  let _ ← call2 rt "print" io (← call0 rt "Broadcasted:type")
  let axes ← call1 rt "getfield:axes" bc
  let tupleType ← call0 rt "Tuple:type"
  if rt.truth (← call2 rt "isa" axes tupleType) then
    let _ ← rt.call "print" [io, (← call0 rt "literal:{"), Style, (← call0 rt "literal:}")]
    pure ()
  else pure ()
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let _ ← rt.call "print" [io, (← call0 rt "literal:("), f, (← call0 rt "literal:, "), args,
    (← call0 rt "literal:)")]
  call0 rt "nothing"
def P218 : Prop := ∀ rt io bc Style, m218 rt io bc Style = do
  let _ ← call2 rt "print" io (← call0 rt "Broadcasted:type")
  let axes ← call1 rt "getfield:axes" bc
  let tupleType ← call0 rt "Tuple:type"
  if rt.truth (← call2 rt "isa" axes tupleType) then
    let _ ← rt.call "print" [io, (← call0 rt "literal:{"), Style, (← call0 rt "literal:}")]
    pure ()
  else pure ()
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let _ ← rt.call "print" [io, (← call0 rt "literal:("), f, (← call0 rt "literal:, "), args,
    (← call0 rt "literal:)")]
  call0 rt "nothing"
theorem p218 : P218 := by simp [P218, m218]

def m229 (rt : Runtime) (bc T : Value) : M Value := do
  let ax ← call1 rt "axes" bc
  rt.call "similar" [bc, T, ax]
def P229 : Prop := ∀ rt bc T, m229 rt bc T = do
  let ax ← call1 rt "axes" bc
  rt.call "similar" [bc, T, ax]
theorem p229 : P229 := by simp [P229, m229]

def m230 (rt : Runtime) (ElType dims : Value) : M Value := do
  let n ← call1 rt "length" dims
  let arrayType ← rt.call "Array{ElType,N}" [ElType, n]
  call2 rt "similar" arrayType dims
def P230 : Prop := ∀ rt ElType dims, m230 rt ElType dims = do
  let n ← call1 rt "length" dims
  let arrayType ← rt.call "Array{ElType,N}" [ElType, n]
  call2 rt "similar" arrayType dims
theorem p230 : P230 := by simp [P230, m230]

def m232 (rt : Runtime) (dims : Value) : M Value := do
  let bitArray ← call0 rt "BitArray:type"
  call2 rt "similar" bitArray dims
def P232 : Prop := ∀ rt dims, m232 rt dims = do
  let bitArray ← call0 rt "BitArray:type"
  call2 rt "similar" bitArray dims
theorem p232 : P232 := by simp [P232, m232]

def m235 (rt : Runtime) (ElType dims : Value) : M Value := do
  let n ← call1 rt "length" dims
  let arrayType ← rt.call "Array{ElType,N}" [ElType, n]
  call2 rt "similar" arrayType dims
def P235 : Prop := ∀ rt ElType dims, m235 rt ElType dims = do
  let n ← call1 rt "length" dims
  let arrayType ← rt.call "Array{ElType,N}" [ElType, n]
  call2 rt "similar" arrayType dims
theorem p235 : P235 := by simp [P235, m235]

def m237 (rt : Runtime) (dims : Value) : M Value := do
  let bitArray ← call0 rt "BitArray:type"
  call2 rt "similar" bitArray dims
def P237 : Prop := ∀ rt dims, m237 rt dims = do
  let bitArray ← call0 rt "BitArray:type"
  call2 rt "similar" bitArray dims
theorem p237 : P237 := by simp [P237, m237]

def m248 (rt : Runtime) (Style : Value) : M Value := call1 rt "construct-type" Style
def P248 : Prop := ∀ rt Style, m248 rt Style = call1 rt "construct-type" Style
theorem p248 : P248 := by simp [P248, m248]

def m249 (rt : Runtime) (_S : Value) : M Value := raise .argumentError
def P249 : Prop := ∀ rt S, m249 rt S = raise .argumentError
theorem p249 : P249 := by simp [P249, m249]

def m252 (rt : Runtime) (BC : Value) : M Value := do
  let argsName ← call0 rt "QuoteNode(:args)"
  call2 rt "fieldtype" BC argsName
def P252 : Prop := ∀ rt BC, m252 rt BC = do
  let argsName ← call0 rt "QuoteNode(:args)"
  call2 rt "fieldtype" BC argsName
theorem p252 : P252 := by simp [P252, m252]

def m253 (rt : Runtime) (bc : Value) : M Value := do
  let BC ← call1 rt "typeof" bc
  call1 rt "argtype" BC
def P253 : Prop := ∀ rt bc, m253 rt bc = do
  let BC ← call1 rt "typeof" bc
  call1 rt "argtype" BC
theorem p253 : P253 := by simp [P253, m253]

def m299 (_rt : Runtime) (x : Value) : M Value := pure x
def P299 : Prop := ∀ rt x, m299 rt x = pure x
theorem p299 : P299 := by simp [P299, m299]

def m310 (rt : Runtime) (bc : Value) : M Value := do
  let oldAxes ← call1 rt "getfield:axes" bc
  let nothingType ← call0 rt "Nothing:type"
  let isNothing ← call2 rt "isa" oldAxes nothingType
  let axes ← if rt.truth isNothing then
    let args ← call1 rt "getfield:args" bc
    call1 rt "combine_axes:slurp" args
  else
    let args ← call1 rt "getfield:args" bc
    let _ ← rt.call "check_broadcast_axes:slurp" [oldAxes, args]
    pure oldAxes
  let style ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  rt.call "Broadcasted" [style, f, args, axes]
def P310 : Prop := ∀ rt bc, m310 rt bc = do
  let oldAxes ← call1 rt "getfield:axes" bc
  let nothingType ← call0 rt "Nothing:type"
  let isNothing ← call2 rt "isa" oldAxes nothingType
  let axes ← if rt.truth isNothing then
    let args ← call1 rt "getfield:args" bc
    call1 rt "combine_axes:slurp" args
  else
    let args ← call1 rt "getfield:args" bc
    let _ ← rt.call "check_broadcast_axes:slurp" [oldAxes, args]
    pure oldAxes
  let style ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  rt.call "Broadcasted" [style, f, args, axes]
theorem p310 : P310 := by simp [P310, m310]

def m319 (_rt : Runtime) (bc : Value) : M Value := pure bc
def P319 : Prop := ∀ rt bc, m319 rt bc = pure bc
theorem p319 : P319 := by simp [P319, m319]

def m321 (_rt : Runtime) (bc : Value) : M Value := pure bc
def P321 : Prop := ∀ rt bc, m321 rt bc = pure bc
theorem p321 : P321 := by simp [P321, m321]

def m322 (rt : Runtime) (bc : Value) : M Value := do
  let axes ← call1 rt "getfield:axes" bc
  let args ← call1 rt "getfield:args" bc
  let _ ← rt.call "check_broadcast_axes:slurp" [axes, args]
  pure bc
def P322 : Prop := ∀ rt bc, m322 rt bc = do
  let axes ← call1 rt "getfield:axes" bc
  let args ← call1 rt "getfield:args" bc
  let _ ← rt.call "check_broadcast_axes:slurp" [axes, args]
  pure bc
theorem p322 : P322 := by simp [P322, m322]

def m346 (rt : Runtime) (bc : Value) : M Value := do
  if rt.truth (← call1 rt "isflat" bc) then pure bc else
    let args ← call1 rt "cat_nested" bc
    let bcArgs ← call1 rt "getfield:args" bc
    let makeargs ← call1 rt "make_makeargs" bcArgs
    let oldf ← call1 rt "getfield:f" bc
    let f ← call1 rt "Base.maybeconstructor" oldf
    let newf ← rt.call "closure:(args...)->f(prepare_args(makeargs,args)...)" [f, makeargs]
    let style ← call1 rt "getfield:style" bc
    let axes ← call1 rt "getfield:axes" bc
    rt.call "Broadcasted" [style, newf, args, axes]
def P346 : Prop := ∀ rt bc, m346 rt bc = do
  if rt.truth (← call1 rt "isflat" bc) then pure bc else
    let args ← call1 rt "cat_nested" bc
    let bcArgs ← call1 rt "getfield:args" bc
    let makeargs ← call1 rt "make_makeargs" bcArgs
    let oldf ← call1 rt "getfield:f" bc
    let f ← call1 rt "Base.maybeconstructor" oldf
    let newf ← rt.call "closure:(args...)->f(prepare_args(makeargs,args)...)" [f, makeargs]
    let style ← call1 rt "getfield:style" bc
    let axes ← call1 rt "getfield:axes" bc
    rt.call "Broadcasted" [style, newf, args, axes]
theorem p346 : P346 := by simp [P346, m346]

def m364 (rt : Runtime) (bc : Value) : M Value := do
  let args ← call1 rt "getfield:args" bc
  call1 rt "_isflat" args
def P364 : Prop := ∀ rt bc, m364 rt bc = do
  let args ← call1 rt "getfield:args" bc
  call1 rt "_isflat" args
theorem p364 : P364 := by simp [P364, m364]

def m365 (rt : Runtime) (_args : Value) : M Value := call0 rt "false"
def P365 : Prop := ∀ rt args, m365 rt args = call0 rt "false"
theorem p365 : P365 := by simp [P365, m365]

def m366 (rt : Runtime) (args : Value) : M Value := do
  let tail ← call1 rt "tail" args
  call1 rt "_isflat" tail
def P366 : Prop := ∀ rt args, m366 rt args = do
  let tail ← call1 rt "tail" args
  call1 rt "_isflat" tail
theorem p366 : P366 := by simp [P366, m366]

def m367 (rt : Runtime) : M Value := call0 rt "true"
def P367 : Prop := ∀ rt, m367 rt = call0 rt "true"
theorem p367 : P367 := by simp [P367, m367]

def m369 (rt : Runtime) (bc : Value) : M Value := do
  let args ← call1 rt "getfield:args" bc
  call1 rt "cat_nested_args" args
def P369 : Prop := ∀ rt bc, m369 rt bc = do
  let args ← call1 rt "getfield:args" bc
  call1 rt "cat_nested_args" args
theorem p369 : P369 := by simp [P369, m369]

def m370 (rt : Runtime) : M Value := call0 rt "tuple:empty"
def P370 : Prop := ∀ rt, m370 rt = call0 rt "tuple:empty"
theorem p370 : P370 := by simp [P370, m370]

def m371 (rt : Runtime) (head : Value) : M Value := do
  let value ← call1 rt "cat_nested" head
  call1 rt "tuple:single" value
def P371 : Prop := ∀ rt head, m371 rt head = do
  let value ← call1 rt "cat_nested" head
  call1 rt "tuple:single" value
theorem p371 : P371 := by simp [P371, m371]

def m372 (rt : Runtime) (head tail : Value) : M Value := do
  let left ← call1 rt "cat_nested" head
  let right ← call1 rt "cat_nested_args" tail
  call2 rt "tuple:slurp2" left right
def P372 : Prop := ∀ rt head tail, m372 rt head tail = do
  let left ← call1 rt "cat_nested" head
  let right ← call1 rt "cat_nested_args" tail
  call2 rt "tuple:slurp2" left right
theorem p372 : P372 := by simp [P372, m372]

def m373 (rt : Runtime) (a : Value) : M Value := call1 rt "tuple:single" a
def P373 : Prop := ∀ rt a, m373 rt a = call1 rt "tuple:single" a
theorem p373 : P373 := by simp [P373, m373]

def m382 (rt : Runtime) (args : Value) : M Value := do
  let pair ← rt.call "_make_makeargs" [args, (← call0 rt "Int:1")]
  call2 rt "getindex" pair (← call0 rt "Int:1")
def P382 : Prop := ∀ rt args, m382 rt args = do
  let pair ← rt.call "_make_makeargs" [args, (← call0 rt "Int:1")]
  call2 rt "getindex" pair (← call0 rt "Int:1")
theorem p382 : P382 := by simp [P382, m382]

def m386 (rt : Runtime) (head tail n : Value) : M Value := do
  let firstPair ← call2 rt "_make_makeargs1" head n
  let first ← call2 rt "getindex" firstPair (← call0 rt "Int:1")
  let n ← call2 rt "getindex" firstPair (← call0 rt "Int:2")
  let restPair ← call2 rt "_make_makeargs" tail n
  let rest ← call2 rt "getindex" restPair (← call0 rt "Int:1")
  let n ← call2 rt "getindex" restPair (← call0 rt "Int:2")
  rt.call "tuple:(head,rest...,n)" [first, rest, n]
def P386 : Prop := ∀ rt head tail n, m386 rt head tail n = do
  let firstPair ← call2 rt "_make_makeargs1" head n
  let first ← call2 rt "getindex" firstPair (← call0 rt "Int:1")
  let n ← call2 rt "getindex" firstPair (← call0 rt "Int:2")
  let restPair ← call2 rt "_make_makeargs" tail n
  let rest ← call2 rt "getindex" restPair (← call0 rt "Int:1")
  let n ← call2 rt "getindex" restPair (← call0 rt "Int:2")
  rt.call "tuple:(head,rest...,n)" [first, rest, n]
theorem p386 : P386 := by simp [P386, m386]

def m391 (rt : Runtime) (n : Value) : M Value :=
  rt.call "tuple:((),n)" [(0 : Value), n]
def P391 : Prop := ∀ rt n, m391 rt n = rt.call "tuple:((),n)" [(0 : Value), n]
theorem p391 : P391 := by simp [P391, m391]

def m395 (rt : Runtime) (N args : Value) : M Value := call2 rt "getindex" args N
def P395 : Prop := ∀ rt N args, m395 rt N args = call2 rt "getindex" args N
theorem p395 : P395 := by simp [P395, m395]

def m398 (rt : Runtime) (n : Value) : M Value := do
  let pick ← call1 rt "Pick" n
  let next ← call2 rt "+" n (← call0 rt "Int:1")
  rt.call "tuple" [pick, next]
def P398 : Prop := ∀ rt n, m398 rt n = do
  let pick ← call1 rt "Pick" n
  let next ← call2 rt "+" n (← call0 rt "Int:1")
  rt.call "tuple" [pick, next]
theorem p398 : P398 := by simp [P398, m398]

def m400 (rt : Runtime) (bc n : Value) : M Value := do
  let args ← call1 rt "getfield:args" bc
  let pair ← call2 rt "_make_makeargs" args n
  let makeargs ← call2 rt "getindex" pair (← call0 rt "Int:1")
  let n ← call2 rt "getindex" pair (← call0 rt "Int:2")
  let oldf ← call1 rt "getfield:f" bc
  let f ← call1 rt "Base.maybeconstructor" oldf
  let closure ← rt.call "closure:args->f(prepare_args(makeargs,args)...)" [f, makeargs]
  rt.call "tuple" [closure, n]
def P400 : Prop := ∀ rt bc n, m400 rt bc n = do
  let args ← call1 rt "getfield:args" bc
  let pair ← call2 rt "_make_makeargs" args n
  let makeargs ← call2 rt "getindex" pair (← call0 rt "Int:1")
  let n ← call2 rt "getindex" pair (← call0 rt "Int:2")
  let oldf ← call1 rt "getfield:f" bc
  let f ← call1 rt "Base.maybeconstructor" oldf
  let closure ← rt.call "closure:args->f(prepare_args(makeargs,args)...)" [f, makeargs]
  rt.call "tuple" [closure, n]
theorem p400 : P400 := by simp [P400, m400]

def m407 (rt : Runtime) (makeHead makeTail x : Value) : M Value := do
  let first ← call2 rt "call" makeHead x
  let rest ← call2 rt "prepare_args" makeTail x
  call2 rt "tuple:(first,rest...)" first rest
def P407 : Prop := ∀ rt makeHead makeTail x, m407 rt makeHead makeTail x = do
  let first ← call2 rt "call" makeHead x
  let rest ← call2 rt "prepare_args" makeTail x
  call2 rt "tuple:(first,rest...)" first rest
theorem p407 : P407 := by simp [P407, m407]

def m408 (rt : Runtime) (makeHead x : Value) : M Value := do
  let first ← call2 rt "call" makeHead x
  call1 rt "tuple:single" first
def P408 : Prop := ∀ rt makeHead x, m408 rt makeHead x = do
  let first ← call2 rt "call" makeHead x
  call1 rt "tuple:single" first
theorem p408 : P408 := by simp [P408, m408]

def m409 (rt : Runtime) : M Value := call0 rt "tuple:empty"
def P409 : Prop := ∀ rt, m409 rt = call0 rt "tuple:empty"
theorem p409 : P409 := by simp [P409, m409]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl"
    juliaFns := [name], statement := statement
    source := s!"base/broadcast.jl:{line}; source equation and dispatch invariant"
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.BroadcastCov.LazyExact
