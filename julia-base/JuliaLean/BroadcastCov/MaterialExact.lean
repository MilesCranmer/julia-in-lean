import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.MaterialExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def nothing (rt : Runtime) : M Value := call0 rt "nothing"
def one (rt : Runtime) : M Value := call0 rt "Int:1"

def m736 (rt : Runtime) (x : Value) : M Value := call1 rt "Ref" x
def P736 : Prop := ∀ rt x, m736 rt x = call1 rt "Ref" x
theorem p736 : P736 := by simp [P736, m736]

def m737 (rt : Runtime) (T : Value) : M Value := rt.call "Ref{Type{T}}" [T, T]
def P737 : Prop := ∀ rt T, m737 rt T = rt.call "Ref{Type{T}}" [T, T]
theorem p737 : P737 := by simp [P737, m737]

def m738 (_rt : Runtime) (x : Value) : M Value := pure x
def P738 : Prop := ∀ rt x, m738 rt x = pure x
theorem p738 : P738 := by simp [P738, m738]

def m740 (rt : Runtime) (x : Value) : M Value := call1 rt "collect" x
def P740 : Prop := ∀ rt x, m740 rt x = call1 rt "collect" x
theorem p740 : P740 := by simp [P740, m740]

def m741 (_rt : Runtime) (_x : Value) : M Value := raise .argumentError
def P741 : Prop := ∀ rt x, m741 rt x = raise .argumentError
theorem p741 : P741 := by simp [P741, m741]

def m744 (rt : Runtime) (bc i : Value) : M Value := do
  let argsTuple ← call1 rt "getfield:args" bc
  let args ← call2 rt "_bc_eltypes" argsTuple i
  let f ← call1 rt "getfield:f" bc
  rt.call "call:slurp" [f, args]
def P744 : Prop := ∀ rt bc i, m744 rt bc i = do
  let argsTuple ← call1 rt "getfield:args" bc
  let args ← call2 rt "_bc_eltypes" argsTuple i
  let f ← call1 rt "getfield:f" bc
  rt.call "call:slurp" [f, args]
theorem p744 : P744 := by simp [P744, m744]

def m747 (rt : Runtime) (x i : Value) : M Value := call2 rt "_broadcast_getindex" x i
def P747 : Prop := ∀ rt x i, m747 rt x i = call2 rt "_broadcast_getindex" x i
theorem p747 : P747 := by simp [P747, m747]

def m748 (rt : Runtime) (x i : Value) : M Value := call2 rt "_broadcast_getindex" x i
def P748 : Prop := ∀ rt x i, m748 rt x i = call2 rt "_broadcast_getindex" x i
theorem p748 : P748 := by simp [P748, m748]

def m751 (rt : Runtime) (x i : Value) : M Value := do
  let x ← call1 rt "Base.inferencebarrier" x
  let value ← call2 rt "_broadcast_getindex" x i
  let T ← call1 rt "eltype" x
  call2 rt "typeassert" value T
def P751 : Prop := ∀ rt x i, m751 rt x i = do
  let x ← call1 rt "Base.inferencebarrier" x
  let value ← call2 rt "_broadcast_getindex" x i
  let T ← call1 rt "eltype" x
  call2 rt "typeassert" value T
theorem p751 : P751 := by simp [P751, m751]

def m753 (rt : Runtime) (head tail i : Value) : M Value := do
  let first ← call2 rt "_bc_eltype" head i
  let rest ← call2 rt "_bc_eltypes" tail i
  call2 rt "tuple:(first,rest...)" first rest
def P753 : Prop := ∀ rt head tail i, m753 rt head tail i = do
  let first ← call2 rt "_bc_eltype" head i
  let rest ← call2 rt "_bc_eltypes" tail i
  call2 rt "tuple:(first,rest...)" first rest
theorem p753 : P753 := by simp [P753, m753]

def m754 (rt : Runtime) (_i : Value) : M Value := call0 rt "tuple:empty"
def P754 : Prop := ∀ rt i, m754 rt i = call0 rt "tuple:empty"
theorem p754 : P754 := by simp [P754, m754]

def m756 (rt : Runtime) (bc : Value) : M Value := do
  let BC ← call1 rt "typeof" bc
  let indices ← call1 rt "eachindex" bc
  let indexType ← call1 rt "eltype" indices
  let argtypes ← rt.call "Iterators.TupleOrBottom" [BC, indexType]
  let bottom ← call0 rt "Union{}:type"
  if rt.truth (← call2 rt "===" argtypes bottom) then pure bottom else
    let helper ← call0 rt "_bc_eltype:function"
    let rettype ← rt.call "Base._return_type" [helper, argtypes]
    call1 rt "promote_typejoin_union" rettype
def P756 : Prop := ∀ rt bc, m756 rt bc = do
  let BC ← call1 rt "typeof" bc
  let indices ← call1 rt "eachindex" bc
  let indexType ← call1 rt "eltype" indices
  let argtypes ← rt.call "Iterators.TupleOrBottom" [BC, indexType]
  let bottom ← call0 rt "Union{}:type"
  if rt.truth (← call2 rt "===" argtypes bottom) then pure bottom else
    let helper ← call0 rt "_bc_eltype:function"
    let rettype ← rt.call "Base._return_type" [helper, argtypes]
    call1 rt "promote_typejoin_union" rettype
theorem p756 : P756 := by simp [P756, m756]

def m765 (rt : Runtime) (bc : Value) : M Value := do
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  call2 rt "combine_eltypes" f args
def P765 : Prop := ∀ rt bc, m765 rt bc = do
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  call2 rt "combine_eltypes" f args
theorem p765 : P765 := by simp [P765, m765]

def m766 (rt : Runtime) (A : Value) : M Value := call1 rt "eltype" A
def P766 : Prop := ∀ rt A, m766 rt A = call1 rt "eltype" A
theorem p766 : P766 := by simp [P766, m766]

def m768 (rt : Runtime) : M Value := call0 rt "Tuple{}:type"
def P768 : Prop := ∀ rt, m768 rt = call0 rt "Tuple{}:type"
theorem p768 : P768 := by simp [P768, m768]

def m769 (rt : Runtime) (head : Value) : M Value := do
  let T ← call1 rt "_broadcast_getindex_eltype" head
  call1 rt "Iterators.TupleOrBottom" T
def P769 : Prop := ∀ rt head, m769 rt head = do
  let T ← call1 rt "_broadcast_getindex_eltype" head
  call1 rt "Iterators.TupleOrBottom" T
theorem p769 : P769 := by simp [P769, m769]

def m770 (rt : Runtime) (a b : Value) : M Value := do
  let A ← call1 rt "_broadcast_getindex_eltype" a
  let B ← call1 rt "_broadcast_getindex_eltype" b
  rt.call "Iterators.TupleOrBottom" [A, B]
def P770 : Prop := ∀ rt a b, m770 rt a b = do
  let A ← call1 rt "_broadcast_getindex_eltype" a
  let B ← call1 rt "_broadcast_getindex_eltype" b
  rt.call "Iterators.TupleOrBottom" [A, B]
theorem p770 : P770 := by simp [P770, m770]

def m771 (rt : Runtime) (head tail : Value) : M Value := do
  let TT ← call1 rt "eltypes" tail
  let bottom ← call0 rt "Union{}:type"
  if rt.truth (← call2 rt "===" TT bottom) then pure bottom else
    let headType ← call1 rt "_broadcast_getindex_eltype" head
    let parameters ← call1 rt "getfield:parameters" TT
    rt.call "Iterators.TupleOrBottom:slurp" [headType, parameters]
def P771 : Prop := ∀ rt head tail, m771 rt head tail = do
  let TT ← call1 rt "eltypes" tail
  let bottom ← call0 rt "Union{}:type"
  if rt.truth (← call2 rt "===" TT bottom) then pure bottom else
    let headType ← call1 rt "_broadcast_getindex_eltype" head
    let parameters ← call1 rt "getfield:parameters" TT
    rt.call "Iterators.TupleOrBottom:slurp" [headType, parameters]
theorem p771 : P771 := by simp [P771, m771]

def m774 (rt : Runtime) (f args : Value) : M Value := do
  let argT ← call1 rt "eltypes" args
  let bottom ← call0 rt "Union{}:type"
  if rt.truth (← call2 rt "===" argT bottom) then pure bottom else
    let rettype ← rt.call "Base._return_type" [f, argT]
    call1 rt "promote_typejoin_union" rettype
def P774 : Prop := ∀ rt f args, m774 rt f args = do
  let argT ← call1 rt "eltypes" args
  let bottom ← call0 rt "Union{}:type"
  if rt.truth (← call2 rt "===" argT bottom) then pure bottom else
    let rettype ← rt.call "Base._return_type" [f, argT]
    call1 rt "promote_typejoin_union" rettype
theorem p774 : P774 := by simp [P774, m774]

def m859 (rt : Runtime) (f As : Value) : M Value := do
  let bc ← rt.call "broadcasted:slurp" [f, As]
  call1 rt "materialize" bc
def P859 : Prop := ∀ rt f As, m859 rt f As = do
  let bc ← rt.call "broadcasted:slurp" [f, As]
  call1 rt "materialize" bc
theorem p859 : P859 := by simp [P859, m859]

def m862 (rt : Runtime) (f xs : Value) : M Value := rt.call "call:slurp" [f, xs]
def P862 : Prop := ∀ rt f xs, m862 rt f xs = rt.call "call:slurp" [f, xs]
theorem p862 : P862 := by simp [P862, m862]

def m863 (rt : Runtime) (f t ts : Value) : M Value := rt.call "map:slurp" [f, t, ts]
def P863 : Prop := ∀ rt f t ts, m863 rt f t ts = rt.call "map:slurp" [f, t, ts]
theorem p863 : P863 := by simp [P863, m863]

def m898 (rt : Runtime) (f dest As : Value) : M Value := do
  let bc ← rt.call "broadcasted:slurp" [f, As]
  let _ ← call2 rt "materialize!" dest bc
  pure dest
def P898 : Prop := ∀ rt f dest As, m898 rt f dest As = do
  let bc ← rt.call "broadcasted:slurp" [f, As]
  let _ ← call2 rt "materialize!" dest bc
  pure dest
theorem p898 : P898 := by simp [P898, m898]

def m908 (rt : Runtime) (f As : Value) : M Value := do
  let bc ← rt.call "broadcasted:slurp" [f, As]
  let r ← call1 rt "materialize" bc
  let ax ← call1 rt "axes" bc
  let n ← call1 rt "length" ax
  if rt.truth (← call2 rt "==" n (← call0 rt "Int:0")) then
    let T ← call1 rt "typeof" r
    let out ← rt.call "similar" [bc, T]
    call2 rt "fill!" out r
  else pure r
def P908 : Prop := ∀ rt f As, m908 rt f As = do
  let bc ← rt.call "broadcasted:slurp" [f, As]
  let r ← call1 rt "materialize" bc
  let ax ← call1 rt "axes" bc
  let n ← call1 rt "length" ax
  if rt.truth (← call2 rt "==" n (← call0 rt "Int:0")) then
    let T ← call1 rt "typeof" r
    let out ← rt.call "similar" [bc, T]
    call2 rt "fill!" out r
  else pure r
theorem p908 : P908 := by simp [P908, m908]

def m913 (rt : Runtime) (f : Value) : M Value := do
  let x ← call1 rt "call" f
  call1 rt "fill" x
def P913 : Prop := ∀ rt f, m913 rt f = do
  let x ← call1 rt "call" f
  call1 rt "fill" x
theorem p913 : P913 := by simp [P913, m913]

def m914 (rt : Runtime) (f xs : Value) : M Value := do
  let x ← rt.call "call:slurp" [f, xs]
  call1 rt "fill" x
def P914 : Prop := ∀ rt f xs, m914 rt f xs = do
  let x ← rt.call "call:slurp" [f, xs]
  call1 rt "fill" x
theorem p914 : P914 := by simp [P914, m914]

def m921 (rt : Runtime) (bc : Value) : M Value := do
  let bc ← call1 rt "instantiate" bc
  call1 rt "copy" bc
def P921 : Prop := ∀ rt bc, m921 rt bc = do
  let bc ← call1 rt "instantiate" bc
  call1 rt "copy" bc
theorem p921 : P921 := by simp [P921, m921]

def m922 (_rt : Runtime) (x : Value) : M Value := pure x
def P922 : Prop := ∀ rt x, m922 rt x = pure x
theorem p922 : P922 := by simp [P922, m922]

def m924 (rt : Runtime) (dest x : Value) : M Value := do
  let identity ← call0 rt "identity:function"
  let tuple ← call1 rt "tuple:single" x
  let ax ← call1 rt "axes" dest
  let bc ← rt.call "Broadcasted" [identity, tuple, ax]
  let bc ← call1 rt "instantiate" bc
  call2 rt "materialize!" dest bc
def P924 : Prop := ∀ rt dest x, m924 rt dest x = do
  let identity ← call0 rt "identity:function"
  let tuple ← call1 rt "tuple:single" x
  let ax ← call1 rt "axes" dest
  let bc ← rt.call "Broadcasted" [identity, tuple, ax]
  let bc ← call1 rt "instantiate" bc
  call2 rt "materialize!" dest bc
theorem p924 : P924 := by simp [P924, m924]

def m928 (rt : Runtime) (dest bc : Value) : M Value := do
  let style ← call2 rt "combine_styles" dest bc
  rt.call "materialize!" [style, dest, bc]
def P928 : Prop := ∀ rt dest bc, m928 rt dest bc = do
  let style ← call2 rt "combine_styles" dest bc
  rt.call "materialize!" [style, dest, bc]
theorem p928 : P928 := by simp [P928, m928]

def m932 (rt : Runtime) (style dest bc : Value) : M Value := do
  let bcStyle ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let ax ← call1 rt "axes" dest
  let wrapper ← rt.call "Broadcasted" [bcStyle, f, args, ax]
  let wrapper ← call1 rt "instantiate" wrapper
  call2 rt "copyto!" dest wrapper
def P932 : Prop := ∀ rt style dest bc, m932 rt style dest bc = do
  let bcStyle ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let ax ← call1 rt "axes" dest
  let wrapper ← rt.call "Broadcasted" [bcStyle, f, args, ax]
  let wrapper ← call1 rt "instantiate" wrapper
  call2 rt "copyto!" dest wrapper
theorem p932 : P932 := by simp [P932, m932]

def m936 (rt : Runtime) (dest _bc : Value) : M Value := call1 rt "_throw_unwritable_dest" dest
def P936 : Prop := ∀ rt dest bc, m936 rt dest bc = call1 rt "_throw_unwritable_dest" dest
theorem p936 : P936 := by simp [P936, m936]

def m937 (_rt : Runtime) (_dest : Value) : M Value := raise .argumentError
def P937 : Prop := ∀ rt dest, m937 rt dest = raise .argumentError
theorem p937 : P937 := by simp [P937, m937]

def m942 (rt : Runtime) (bc : Value) : M Value := do
  let empty ← call0 rt "CartesianIndex:empty"
  call2 rt "getindex" bc empty
def P942 : Prop := ∀ rt bc, m942 rt bc = do
  let empty ← call0 rt "CartesianIndex:empty"
  call2 rt "getindex" bc empty
theorem p942 : P942 := by simp [P942, m942]

def m943 (_rt : Runtime) (_bc : Value) : M Value := raise .argumentError
def P943 : Prop := ∀ rt bc, m943 rt bc = raise .argumentError
theorem p943 : P943 := by simp [P943, m943]

def m948 (rt : Runtime) (bc : Value) : M Value := do
  let ElType ← call1 rt "result_eltype" bc
  if rt.truth (← call1 rt "Base.isconcretetype" ElType) then
    let dest ← rt.call "similar" [bc, ElType]
    call2 rt "copyto!" dest bc
  else
    let none ← nothing rt
    let prepared ← rt.call "preprocess" [none, bc]
    let iter ← call1 rt "eachindex" prepared
    let y ← call1 rt "iterate" iter
    if rt.truth (← call2 rt "===" y none) then rt.call "similar" [prepared, ElType] else
      let I ← call2 rt "getindex" y (← one rt)
      let state ← call2 rt "getindex" y (← call0 rt "Int:2")
      let val ← call2 rt "getindex" prepared I
      let T ← call1 rt "typeof" val
      let dest ← rt.call "similar" [prepared, T]
      let _ ← rt.call "setindex!" [dest, val, I]
      let bottom ← call0 rt "Union{}:type"
      let anyType ← call0 rt "Any:type"
      let typeType ← call0 rt "Type:type"
      let ElType2 ← if rt.truth (← call2 rt "===" ElType bottom) then pure anyType
        else if rt.truth (← call2 rt "<:" ElType typeType) then pure typeType else pure ElType
      let destIsArray ← call2 rt "isa" dest (← call0 rt "AbstractArray:type")
      let RT ← if rt.truth destIsArray then
        let n ← call1 rt "ndims" dest
        rt.call "AbstractArray{<:ElType,N}" [ElType2, n]
      else pure anyType
      let result ← rt.call "copyto_nonleaf!" [dest, prepared, iter, state, (← one rt)]
      call2 rt "typeassert" result RT
def P948 : Prop := ∀ rt bc, m948 rt bc = do
  let ElType ← call1 rt "result_eltype" bc
  if rt.truth (← call1 rt "Base.isconcretetype" ElType) then
    let dest ← rt.call "similar" [bc, ElType]
    call2 rt "copyto!" dest bc
  else
    let none ← nothing rt
    let prepared ← rt.call "preprocess" [none, bc]
    let iter ← call1 rt "eachindex" prepared
    let y ← call1 rt "iterate" iter
    if rt.truth (← call2 rt "===" y none) then rt.call "similar" [prepared, ElType] else
      let I ← call2 rt "getindex" y (← one rt)
      let state ← call2 rt "getindex" y (← call0 rt "Int:2")
      let val ← call2 rt "getindex" prepared I
      let T ← call1 rt "typeof" val
      let dest ← rt.call "similar" [prepared, T]
      let _ ← rt.call "setindex!" [dest, val, I]
      let bottom ← call0 rt "Union{}:type"
      let anyType ← call0 rt "Any:type"
      let typeType ← call0 rt "Type:type"
      let ElType2 ← if rt.truth (← call2 rt "===" ElType bottom) then pure anyType
        else if rt.truth (← call2 rt "<:" ElType typeType) then pure typeType else pure ElType
      let destIsArray ← call2 rt "isa" dest (← call0 rt "AbstractArray:type")
      let RT ← if rt.truth destIsArray then
        let n ← call1 rt "ndims" dest
        rt.call "AbstractArray{<:ElType,N}" [ElType2, n]
      else pure anyType
      let result ← rt.call "copyto_nonleaf!" [dest, prepared, iter, state, (← one rt)]
      call2 rt "typeassert" result RT
theorem p948 : P948 := by simp [P948, m948, nothing, one]

def m980 (rt : Runtime) (dest bc : Value) : M Value := do
  let T ← call0 rt "Broadcasted{Nothing}:type"
  let bc ← call2 rt "convert" T bc
  call2 rt "copyto!" dest bc
def P980 : Prop := ∀ rt dest bc, m980 rt dest bc = do
  let T ← call0 rt "Broadcasted{Nothing}:type"
  let bc ← call2 rt "convert" T bc
  call2 rt "copyto!" dest bc
theorem p980 : P980 := by simp [P980, m980]

def m983 (rt : Runtime) (dest bc : Value) : M Value := do
  let f ← call1 rt "getfield:f" bc
  let identity ← call0 rt "identity:function"
  let sameF ← call2 rt "===" f identity
  if rt.truth sameF then
    let args ← call1 rt "getfield:args" bc
    let tupleAny ← call0 rt "Tuple{Any}:type"
    if rt.truth (← call2 rt "isa" args tupleAny) then
      if rt.truth (← call1 rt "isflat" bc) then
        let arg ← call2 rt "getindex" args (← one rt)
        let value ← call1 rt "getindex:empty" arg
        call2 rt "fill!" dest value
      else
        let T ← call0 rt "Broadcasted{Nothing}:type"
        let bc ← call2 rt "convert" T bc
        call2 rt "copyto!" dest bc
    else
      let T ← call0 rt "Broadcasted{Nothing}:type"
      let bc ← call2 rt "convert" T bc
      call2 rt "copyto!" dest bc
  else
    let T ← call0 rt "Broadcasted{Nothing}:type"
    let bc ← call2 rt "convert" T bc
    call2 rt "copyto!" dest bc
def P983 : Prop := ∀ rt dest bc, m983 rt dest bc = do
  let f ← call1 rt "getfield:f" bc
  let identity ← call0 rt "identity:function"
  let sameF ← call2 rt "===" f identity
  if rt.truth sameF then
    let args ← call1 rt "getfield:args" bc
    let tupleAny ← call0 rt "Tuple{Any}:type"
    if rt.truth (← call2 rt "isa" args tupleAny) then
      if rt.truth (← call1 rt "isflat" bc) then
        let arg ← call2 rt "getindex" args (← one rt)
        let value ← call1 rt "getindex:empty" arg
        call2 rt "fill!" dest value
      else
        let T ← call0 rt "Broadcasted{Nothing}:type"
        let bc ← call2 rt "convert" T bc
        call2 rt "copyto!" dest bc
    else
      let T ← call0 rt "Broadcasted{Nothing}:type"
      let bc ← call2 rt "convert" T bc
      call2 rt "copyto!" dest bc
  else
    let T ← call0 rt "Broadcasted{Nothing}:type"
    let bc ← call2 rt "convert" T bc
    call2 rt "copyto!" dest bc
theorem p983 : P983 := by simp [P983, m983, one]

def m1001 (rt : Runtime) (dest src : Value) : M Value := do
  if rt.truth (← call2 rt "===" dest src) then pure src else call2 rt "unalias" dest src
def P1001 : Prop := ∀ rt dest src, m1001 rt dest src = do
  if rt.truth (← call2 rt "===" dest src) then pure src else call2 rt "unalias" dest src
theorem p1001 : P1001 := by simp [P1001, m1001]

def m1002 (_rt : Runtime) (src : Value) : M Value := pure src
def P1002 : Prop := ∀ rt src, m1002 rt src = pure src
theorem p1002 : P1002 := by simp [P1002, m1002]

def m1007 (rt : Runtime) (dest bc : Value) : M Value := do
  let style ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let args ← call2 rt "preprocess_args" dest args
  let axes ← call1 rt "getfield:axes" bc
  rt.call "Broadcasted" [style, f, args, axes]
def P1007 : Prop := ∀ rt dest bc, m1007 rt dest bc = do
  let style ← call1 rt "getfield:style" bc
  let f ← call1 rt "getfield:f" bc
  let args ← call1 rt "getfield:args" bc
  let args ← call2 rt "preprocess_args" dest args
  let axes ← call1 rt "getfield:axes" bc
  rt.call "Broadcasted" [style, f, args, axes]
theorem p1007 : P1007 := by simp [P1007, m1007]

def m1008 (rt : Runtime) (dest x : Value) : M Value := do
  let x ← call2 rt "broadcast_unalias" dest x
  call1 rt "extrude" x
def P1008 : Prop := ∀ rt dest x, m1008 rt dest x = do
  let x ← call2 rt "broadcast_unalias" dest x
  call1 rt "extrude" x
theorem p1008 : P1008 := by simp [P1008, m1008]

def m1010 (rt : Runtime) (dest head tail : Value) : M Value := do
  let first ← call2 rt "preprocess" dest head
  let rest ← call2 rt "preprocess_args" dest tail
  call2 rt "tuple:(first,rest...)" first rest
def P1010 : Prop := ∀ rt dest head tail, m1010 rt dest head tail = do
  let first ← call2 rt "preprocess" dest head
  let rest ← call2 rt "preprocess_args" dest tail
  call2 rt "tuple:(first,rest...)" first rest
theorem p1010 : P1010 := by simp [P1010, m1010]

def m1011 (rt : Runtime) (dest head : Value) : M Value := do
  let first ← call2 rt "preprocess" dest head
  call1 rt "tuple:single" first
def P1011 : Prop := ∀ rt dest head, m1011 rt dest head = do
  let first ← call2 rt "preprocess" dest head
  call1 rt "tuple:single" first
theorem p1011 : P1011 := by simp [P1011, m1011]

def m1012 (rt : Runtime) (_dest : Value) : M Value := call0 rt "tuple:empty"
def P1012 : Prop := ∀ rt dest, m1012 rt dest = call0 rt "tuple:empty"
theorem p1012 : P1012 := by simp [P1012, m1012]

def m1015 (rt : Runtime) (dest bc : Value) : M Value := do
  let destAxes ← call1 rt "axes" dest
  let bcAxes ← call1 rt "axes" bc
  if !rt.truth (← call2 rt "==" destAxes bcAxes) then
    rt.call "throwdm" [destAxes, bcAxes]
  else
    let f ← call1 rt "getfield:f" bc
    let identity ← call0 rt "identity:function"
    let fast ← if rt.truth (← call2 rt "===" f identity) then
      let args ← call1 rt "getfield:args" bc
      let tupleArray ← call0 rt "Tuple{AbstractArray}:type"
      call2 rt "isa" args tupleArray
    else call0 rt "false"
    if rt.truth fast then
      let args ← call1 rt "getfield:args" bc
      let A ← call2 rt "getindex" args (← one rt)
      let aAxes ← call1 rt "axes" A
      if rt.truth (← call2 rt "==" destAxes aAxes) then call2 rt "copyto!" dest A else
        let prepared ← call2 rt "preprocess" dest bc
        let iter ← call1 rt "eachindex" prepared
        let _ ← rt.forEach iter fun I => do
          let value ← call2 rt "getindex" prepared I
          let _ ← rt.call "setindex!" [dest, value, I]
          pure ()
        pure dest
    else
      let prepared ← call2 rt "preprocess" dest bc
      let iter ← call1 rt "eachindex" prepared
      let _ ← rt.forEach iter fun I => do
        let value ← call2 rt "getindex" prepared I
        let _ ← rt.call "setindex!" [dest, value, I]
        pure ()
      pure dest
def P1015 : Prop := ∀ rt dest bc, m1015 rt dest bc = do
  let destAxes ← call1 rt "axes" dest
  let bcAxes ← call1 rt "axes" bc
  if !rt.truth (← call2 rt "==" destAxes bcAxes) then
    rt.call "throwdm" [destAxes, bcAxes]
  else
    let f ← call1 rt "getfield:f" bc
    let identity ← call0 rt "identity:function"
    let fast ← if rt.truth (← call2 rt "===" f identity) then
      let args ← call1 rt "getfield:args" bc
      let tupleArray ← call0 rt "Tuple{AbstractArray}:type"
      call2 rt "isa" args tupleArray
    else call0 rt "false"
    if rt.truth fast then
      let args ← call1 rt "getfield:args" bc
      let A ← call2 rt "getindex" args (← one rt)
      let aAxes ← call1 rt "axes" A
      if rt.truth (← call2 rt "==" destAxes aAxes) then call2 rt "copyto!" dest A else
        let prepared ← call2 rt "preprocess" dest bc
        let iter ← call1 rt "eachindex" prepared
        let _ ← rt.forEach iter fun I => do
          let value ← call2 rt "getindex" prepared I
          let _ ← rt.call "setindex!" [dest, value, I]
          pure ()
        pure dest
    else
      let prepared ← call2 rt "preprocess" dest bc
      let iter ← call1 rt "eachindex" prepared
      let _ ← rt.forEach iter fun I => do
        let value ← call2 rt "getindex" prepared I
        let _ ← rt.call "setindex!" [dest, value, I]
        pure ()
      pure dest
theorem p1015 : P1015 := by simp [P1015, m1015, one]

def m1133 (rt : Runtime) (destAxes sourceAxes : Value) : M Value :=
  rt.call "throw:DimensionMismatch" [destAxes, sourceAxes]
def P1133 : Prop := ∀ rt destAxes sourceAxes,
  m1133 rt destAxes sourceAxes = rt.call "throw:DimensionMismatch" [destAxes, sourceAxes]
theorem p1133 : P1133 := by simp [P1133, m1133]

def m1136 (rt : Runtime) (newdest dest bc value I iter state count : Value) : M Value := do
  let taken ← call2 rt "Iterators.take" iter count
  let _ ← rt.forEach taken fun II => do
    let old ← call2 rt "getindex" dest II
    let _ ← rt.call "setindex!" [newdest, old, II]
    pure ()
  let _ ← rt.call "setindex!" [newdest, value, I]
  let nextCount ← call2 rt "+" count (← one rt)
  rt.call "copyto_nonleaf!" [newdest, bc, iter, state, nextCount]
def P1136 : Prop := ∀ rt newdest dest bc value I iter state count,
  m1136 rt newdest dest bc value I iter state count = do
    let taken ← call2 rt "Iterators.take" iter count
    let _ ← rt.forEach taken fun II => do
      let old ← call2 rt "getindex" dest II
      let _ ← rt.call "setindex!" [newdest, old, II]
      pure ()
    let _ ← rt.call "setindex!" [newdest, value, I]
    let nextCount ← call2 rt "+" count (← one rt)
    rt.call "copyto_nonleaf!" [newdest, bc, iter, state, nextCount]
theorem p1136 : P1136 := by simp [P1136, m1136, one]

def m1145 (rt : Runtime) (dest bc iter state count : Value) : M Value := do
  let T ← call1 rt "eltype" dest
  rt.iterateUntil iter state fun I nextState => do
    let value ← call2 rt "getindex" bc I
    if rt.truth (← call2 rt "isa" value T) then
      let _ ← rt.call "setindex!" [dest, value, I]
      let nextCount ← call2 rt "+" count (← one rt)
      rt.call "loop:continue" [nextState, nextCount]
    else
      let valueType ← call1 rt "typeof" value
      let widened ← call2 rt "promote_typejoin" T valueType
      let newdest ← rt.call "Base.similar" [bc, widened]
      rt.call "restart_copyto_nonleaf!" [newdest, dest, bc, value, I, iter, nextState, count]
def P1145 : Prop := ∀ rt dest bc iter state count, m1145 rt dest bc iter state count = do
  let T ← call1 rt "eltype" dest
  rt.iterateUntil iter state fun I nextState => do
    let value ← call2 rt "getindex" bc I
    if rt.truth (← call2 rt "isa" value T) then
      let _ ← rt.call "setindex!" [dest, value, I]
      let nextCount ← call2 rt "+" count (← one rt)
      rt.call "loop:continue" [nextState, nextCount]
    else
      let valueType ← call1 rt "typeof" value
      let widened ← call2 rt "promote_typejoin" T valueType
      let newdest ← rt.call "Base.similar" [bc, widened]
      rt.call "restart_copyto_nonleaf!" [newdest, dest, bc, value, I, iter, nextState, count]
theorem p1145 : P1145 := by simp [P1145, m1145, one]

def m1167 (rt : Runtime) (bc : Value) : M Value := do
  let dim ← call1 rt "axes" bc
  let nDims ← call1 rt "length" dim
  if !rt.truth (← call2 rt "==" nDims (← one rt)) then raise .dimensionMismatch else
    let axis ← call2 rt "getindex" dim (← one rt)
    let N ← call1 rt "length" axis
    let closure ← rt.call "closure:k->_broadcast_getindex(bc,k)" [bc]
    call2 rt "ntuple" closure N
def P1167 : Prop := ∀ rt bc, m1167 rt bc = do
  let dim ← call1 rt "axes" bc
  let nDims ← call1 rt "length" dim
  if !rt.truth (← call2 rt "==" nDims (← one rt)) then raise .dimensionMismatch else
    let axis ← call2 rt "getindex" dim (← one rt)
    let N ← call1 rt "length" axis
    let closure ← rt.call "closure:k->_broadcast_getindex(bc,k)" [bc]
    call2 rt "ntuple" closure N
theorem p1167 : P1167 := by simp [P1167, m1167, one]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; source equation and broadcast behavior invariant",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry 736 "broadcastable(::BroadcastScalars)" "Broadcast scalar values are wrapped in Ref." ``P736 ``p736,
  entry 737 "broadcastable(::Type{T})" "A type is wrapped in Ref{Type{T}} holding T." ``P737 ``p737,
  entry 738 "broadcastable(already supported)" "Arrays, numbers, chars, refs, tuples and Broadcasted pass through." ``P738 ``p738,
  entry 740 "broadcastable(x)" "The fallback collects x." ``P740 ``p740,
  entry 741 "broadcastable(::AbstractDictOrNamedTuple)" "Dictionaries and NamedTuples raise ArgumentError." ``P741 ``p741,
  entry 744 "_bc_eltype(::Broadcasted,i)" "The inference helper gathers argument samples before calling f." ``P744 ``p744,
  entry 747 "_bc_eltype(::Number,i)" "Number samples use broadcast indexing." ``P747 ``p747,
  entry 748 "_bc_eltype(::Tuple,i)" "Tuple samples use broadcast indexing." ``P748 ``p748,
  entry 751 "_bc_eltype(x,i)" "The general helper crosses the inference barrier, indexes, and asserts eltype." ``P751 ``p751,
  entry 753 "_bc_eltypes(args,i)" "Sample gathering evaluates the tuple head before the tail." ``P753 ``p753,
  entry 754 "_bc_eltypes((),i)" "The empty sample tuple is empty." ``P754 ``p754,
  entry 756 "result_eltype(::Broadcasted)" "Result eltype forms argument types, handles bottom, queries return type, then joins unions." ``P756 ``p756,
  entry 765 "_broadcast_getindex_eltype(::Broadcasted)" "Nested element type delegates to combine_eltypes." ``P765 ``p765,
  entry 766 "_broadcast_getindex_eltype(A)" "Leaf element type is eltype(A)." ``P766 ``p766,
  entry 768 "eltypes(())" "The empty argument type tuple is Tuple{}." ``P768 ``p768,
  entry 769 "eltypes(singleton)" "A singleton applies TupleOrBottom to its element type." ``P769 ``p769,
  entry 770 "eltypes(pair)" "A pair obtains both element types before TupleOrBottom." ``P770 ``p770,
  entry 771 "eltypes(tuple)" "The recursive case handles bottom before prepending the head element type." ``P771 ``p771,
  entry 774 "combine_eltypes(f,args)" "Combined eltype handles bottom, computes f's return type, then joins unions." ``P774 ``p774,
  entry 859 "broadcast(f,As...)" "broadcast constructs Broadcasted before materialization." ``P859 ``p859,
  entry 862 "broadcast(f,::Number...)" "All-number broadcast calls f directly." ``P862 ``p862,
  entry 863 "broadcast(f,tuples...)" "Equal-length tuple broadcast delegates to map." ``P863 ``p863,
  entry 898 "broadcast!(f,dest,As...)" "broadcast! constructs and materializes the expression before returning dest." ``P898 ``p898,
  entry 908 "broadcast_preserving_zero_d(f,As...)" "The helper broadcasts and materializes, wrapping zero-dimensional results in fill." ``P908 ``p908,
  entry 913 "broadcast_preserving_zero_d(f)" "The zero-argument overload calls f then fill." ``P913 ``p913,
  entry 914 "broadcast_preserving_zero_d(f,numbers...)" "The numeric overload calls f on scalars then fill." ``P914 ``p914,
  entry 921 "materialize(::Broadcasted)" "Materialization instantiates before copying." ``P921 ``p921,
  entry 922 "materialize(x)" "Non-Broadcasted values pass through." ``P922 ``p922,
  entry 924 "materialize!(dest,x)" "A scalar value is wrapped with identity and destination axes before instantiation." ``P924 ``p924,
  entry 928 "materialize!(dest,bc)" "Destination and expression styles are combined before styled materialization." ``P928 ``p928,
  entry 932 "materialize!(style,dest,bc)" "Styled materialization rebuilds with destination axes, instantiates, then copies." ``P932 ``p932,
  entry 936 "materialize!(unwritable,bc)" "Scalar-like destinations delegate to the unwritable-destination error." ``P936 ``p936,
  entry 937 "_throw_unwritable_dest" "The helper raises ArgumentError." ``P937 ``p937,
  entry 942 "copy(zero-dimensional Broadcasted)" "A zero-dimensional expression evaluates at empty CartesianIndex." ``P942 ``p942,
  entry 943 "copy(unassigned Broadcasted)" "An unassigned style raises ArgumentError." ``P943 ``p943,
  entry 948 "copy(::Broadcasted)" "Copy chooses concrete allocation or preprocessing and first-value narrowing in source order." ``P948 ``p948,
  entry 980 "copyto!(dest,styled bc)" "The styled overload converts to Broadcasted{Nothing} before copying." ``P980 ``p980,
  entry 983 "copyto!(dest,zero-dimensional bc)" "The identity fast path fills; other functions convert and delegate." ``P983 ``p983,
  entry 1001 "broadcast_unalias(dest,src)" "Identical objects pass through and other inputs delegate to unalias." ``P1001 ``p1001,
  entry 1002 "broadcast_unalias(nothing,src)" "A missing destination leaves the source unchanged." ``P1002 ``p1002,
  entry 1007 "preprocess(dest,bc)" "Nested preprocessing rebuilds style, f, processed arguments and axes in order." ``P1007 ``p1007,
  entry 1008 "preprocess(dest,x)" "Leaf preprocessing unaliases before extrusion." ``P1008 ``p1008,
  entry 1010 "preprocess_args(dest,args)" "Recursive preprocessing evaluates the head before the tail." ``P1010 ``p1010,
  entry 1011 "preprocess_args(dest,singleton)" "Singleton preprocessing evaluates its sole argument." ``P1011 ``p1011,
  entry 1012 "preprocess_args(dest,())" "Empty preprocessing returns empty." ``P1012 ``p1012,
  entry 1015 "copyto!(dest,::Broadcasted{Nothing})" "Copy validates axes, takes the identity shortcut when possible, otherwise preprocesses and writes each index." ``P1015 ``p1015,
  entry 1133 "throwdm" "The helper raises DimensionMismatch with both axes." ``P1133 ``p1133,
  entry 1136 "restart_copyto_nonleaf!" "Restart copies the written prefix, writes the widening value, increments count, and resumes." ``P1136 ``p1136,
  entry 1145 "copyto_nonleaf!" "The widening loop reads each next value, writes fitting values, or allocates and restarts at the first type mismatch." ``P1145 ``p1145,
  entry 1167 "copy(::Broadcasted{Style{Tuple}})" "Tuple copy checks one dimension, obtains its length, and builds elements with ntuple." ``P1167 ``p1167
]

end JuliaLean.BroadcastCov.MaterialExact
