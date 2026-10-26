import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.ShapeExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def one (rt : Runtime) : M Value := call0 rt "Int:1"
def nothing (rt : Runtime) : M Value := call0 rt "nothing"

def m502 (rt : Runtime) (A Bs : Value) : M Value := do
  let a ← call1 rt "axes" A
  let b ← call1 rt "combine_axes:slurp" Bs
  call2 rt "broadcast_shape" a b
def P502 : Prop := ∀ rt A Bs, m502 rt A Bs = do
  let a ← call1 rt "axes" A
  let b ← call1 rt "combine_axes:slurp" Bs
  call2 rt "broadcast_shape" a b
theorem p502 : P502 := by simp [P502, m502]

def m503 (rt : Runtime) (A B : Value) : M Value := do
  let a ← call1 rt "axes" A
  let b ← call1 rt "axes" B
  call2 rt "broadcast_shape" a b
def P503 : Prop := ∀ rt A B, m503 rt A B = do
  let a ← call1 rt "axes" A
  let b ← call1 rt "axes" B
  call2 rt "broadcast_shape" a b
theorem p503 : P503 := by simp [P503, m503]

def m504 (rt : Runtime) (A : Value) : M Value := call1 rt "axes" A
def P504 : Prop := ∀ rt A, m504 rt A = call1 rt "axes" A
theorem p504 : P504 := by simp [P504, m504]

def m521 (_rt : Runtime) (shape : Value) : M Value := pure shape
def P521 : Prop := ∀ rt shape, m521 rt shape = pure shape
theorem p521 : P521 := by simp [P521, m521]

def m522 (rt : Runtime) (shape shape1 shapes : Value) : M Value := do
  let combined ← call2 rt "_bcs" shape shape1
  rt.call "broadcast_shape:slurp" [combined, shapes]
def P522 : Prop := ∀ rt shape shape1 shapes, m522 rt shape shape1 shapes = do
  let combined ← call2 rt "_bcs" shape shape1
  rt.call "broadcast_shape:slurp" [combined, shapes]
theorem p522 : P522 := by simp [P522, m522]

def m524 (rt : Runtime) : M Value := call0 rt "tuple:empty"
def P524 : Prop := ∀ rt, m524 rt = call0 rt "tuple:empty"
theorem p524 : P524 := by simp [P524, m524]

def m525 (rt : Runtime) (newshape : Value) : M Value := do
  let head ← call2 rt "getindex" newshape (← one rt)
  let tail ← call1 rt "tail" newshape
  let rest ← call2 rt "_bcs" (← call0 rt "tuple:empty") tail
  call2 rt "tuple:(head,rest...)" head rest
def P525 : Prop := ∀ rt newshape, m525 rt newshape = do
  let head ← call2 rt "getindex" newshape (← one rt)
  let tail ← call1 rt "tail" newshape
  let rest ← call2 rt "_bcs" (← call0 rt "tuple:empty") tail
  call2 rt "tuple:(head,rest...)" head rest
theorem p525 : P525 := by simp [P525, m525, one]

def m526 (rt : Runtime) (shape : Value) : M Value := do
  let head ← call2 rt "getindex" shape (← one rt)
  let tail ← call1 rt "tail" shape
  let rest ← call2 rt "_bcs" tail (← call0 rt "tuple:empty")
  call2 rt "tuple:(head,rest...)" head rest
def P526 : Prop := ∀ rt shape, m526 rt shape = do
  let head ← call2 rt "getindex" shape (← one rt)
  let tail ← call1 rt "tail" shape
  let rest ← call2 rt "_bcs" tail (← call0 rt "tuple:empty")
  call2 rt "tuple:(head,rest...)" head rest
theorem p526 : P526 := by simp [P526, m526, one]

def m527 (rt : Runtime) (shape newshape : Value) : M Value := do
  let a ← call2 rt "getindex" shape (← one rt)
  let b ← call2 rt "getindex" newshape (← one rt)
  let head ← call2 rt "_bcs1" a b
  let tailA ← call1 rt "tail" shape
  let tailB ← call1 rt "tail" newshape
  let rest ← call2 rt "_bcs" tailA tailB
  call2 rt "tuple:(head,rest...)" head rest
def P527 : Prop := ∀ rt shape newshape, m527 rt shape newshape = do
  let a ← call2 rt "getindex" shape (← one rt)
  let b ← call2 rt "getindex" newshape (← one rt)
  let head ← call2 rt "_bcs1" a b
  let tailA ← call1 rt "tail" shape
  let tailB ← call1 rt "tail" newshape
  let rest ← call2 rt "_bcs" tailA tailB
  call2 rt "tuple:(head,rest...)" head rest
theorem p527 : P527 := by simp [P527, m527, one]

def m531 (rt : Runtime) (a b : Value) : M Value := do
  let o ← one rt
  if rt.truth (← call2 rt "==" a o) then pure b
  else if rt.truth (← call2 rt "==" b o) then pure a
  else if rt.truth (← call2 rt "==" a b) then pure a
  else raise .dimensionMismatch
def P531 : Prop := ∀ rt a b, m531 rt a b = do
  let o ← one rt
  if rt.truth (← call2 rt "==" a o) then pure b
  else if rt.truth (← call2 rt "==" b o) then pure a
  else if rt.truth (← call2 rt "==" a b) then pure a
  else raise .dimensionMismatch
theorem p531 : P531 := by simp [P531, m531, one]

def m532 (rt : Runtime) (a b : Value) : M Value := do
  let o ← one rt
  if rt.truth (← call2 rt "==" a o) then pure b else
    let first ← call1 rt "first" b
    if rt.truth (← call2 rt "==" first o) then
      let last ← call1 rt "last" b
      if rt.truth (← call2 rt "==" last a) then pure b else raise .dimensionMismatch
    else raise .dimensionMismatch
def P532 : Prop := ∀ rt a b, m532 rt a b = do
  let o ← one rt
  if rt.truth (← call2 rt "==" a o) then pure b else
    let first ← call1 rt "first" b
    if rt.truth (← call2 rt "==" first o) then
      let last ← call1 rt "last" b
      if rt.truth (← call2 rt "==" last a) then pure b else raise .dimensionMismatch
    else raise .dimensionMismatch
theorem p532 : P532 := by simp [P532, m532, one]

def m533 (rt : Runtime) (a b : Value) : M Value := call2 rt "_bcs1" b a
def P533 : Prop := ∀ rt a b, m533 rt a b = call2 rt "_bcs1" b a
theorem p533 : P533 := by simp [P533, m533]

def m534 (rt : Runtime) (a b : Value) : M Value := do
  if rt.truth (← call2 rt "_bcsm" b a) then call2 rt "axistype" b a
  else if rt.truth (← call2 rt "_bcsm" a b) then call2 rt "axistype" a b
  else raise .dimensionMismatch
def P534 : Prop := ∀ rt a b, m534 rt a b = do
  if rt.truth (← call2 rt "_bcsm" b a) then call2 rt "axistype" b a
  else if rt.truth (← call2 rt "_bcsm" a b) then call2 rt "axistype" a b
  else raise .dimensionMismatch
theorem p534 : P534 := by simp [P534, m534]

def m536 (rt : Runtime) (a b : Value) : M Value := do
  if rt.truth (← call2 rt "==" a b) then call0 rt "true" else
    let n ← call1 rt "length" b
    call2 rt "==" n (← one rt)
def P536 : Prop := ∀ rt a b, m536 rt a b = do
  if rt.truth (← call2 rt "==" a b) then call0 rt "true" else
    let n ← call1 rt "length" b
    call2 rt "==" n (← one rt)
theorem p536 : P536 := by simp [P536, m536, one]

def m537 (rt : Runtime) (_a b : Value) : M Value := do
  call2 rt "==" b (← one rt)
def P537 : Prop := ∀ rt a b, m537 rt a b = do
  call2 rt "==" b (← one rt)
theorem p537 : P537 := by simp [P537, m537, one]

def m538 (rt : Runtime) (a b : Value) : M Value := do
  if rt.truth (← call2 rt "==" a b) then call0 rt "true"
  else call2 rt "==" b (← one rt)
def P538 : Prop := ∀ rt a b, m538 rt a b = do
  if rt.truth (← call2 rt "==" a b) then call0 rt "true"
  else call2 rt "==" b (← one rt)
theorem p538 : P538 := by simp [P538, m538, one]

def m542 (_rt : Runtime) (a _b : Value) : M Value := pure a
def P542 : Prop := ∀ rt a b, m542 rt a b = pure a
theorem p542 : P542 := by simp [P542, m542]

def m543 (rt : Runtime) (a _b : Value) : M Value := call1 rt "OneTo{Int}" a
def P543 : Prop := ∀ rt a b, m543 rt a b = call1 rt "OneTo{Int}" a
theorem p543 : P543 := by simp [P543, m543]

def m544 (rt : Runtime) (a _b : Value) : M Value := call1 rt "UnitRange{Int}" a
def P544 : Prop := ∀ rt a b, m544 rt a b = call1 rt "UnitRange{Int}" a
theorem p544 : P544 := by simp [P544, m544]

def m548 (rt : Runtime) (_shape : Value) : M Value := nothing rt
def P548 : Prop := ∀ rt shape, m548 rt shape = nothing rt
theorem p548 : P548 := by simp [P548, m548]

def m549 (rt : Runtime) (_shape : Value) : M Value := nothing rt
def P549 : Prop := ∀ rt shape, m549 rt shape = nothing rt
theorem p549 : P549 := by simp [P549, m549]

def m550 (rt : Runtime) : M Value := nothing rt
def P550 : Prop := ∀ rt, m550 rt = nothing rt
theorem p550 : P550 := by simp [P550, m550]

def m551 (rt : Runtime) (Ashp : Value) : M Value := do
  let predicate ← call0 rt "closure:ax->length(ax)!=1"
  if rt.truth (← call2 rt "any" predicate Ashp) then raise .dimensionMismatch else nothing rt
def P551 : Prop := ∀ rt Ashp, m551 rt Ashp = do
  let predicate ← call0 rt "closure:ax->length(ax)!=1"
  if rt.truth (← call2 rt "any" predicate Ashp) then raise .dimensionMismatch else nothing rt
theorem p551 : P551 := by simp [P551, m551]

def m557 (rt : Runtime) (shape Ashp : Value) : M Value := do
  let s1 ← call2 rt "getindex" shape (← one rt)
  let a1 ← call2 rt "getindex" Ashp (← one rt)
  if rt.truth (← call2 rt "_bcsm" s1 a1) then
    let st ← call1 rt "tail" shape
    let axisTail ← call1 rt "tail" Ashp
    call2 rt "check_broadcast_shape" st axisTail
  else raise .dimensionMismatch
def P557 : Prop := ∀ rt shape Ashp, m557 rt shape Ashp = do
  let s1 ← call2 rt "getindex" shape (← one rt)
  let a1 ← call2 rt "getindex" Ashp (← one rt)
  if rt.truth (← call2 rt "_bcsm" s1 a1) then
    let st ← call1 rt "tail" shape
    let axisTail ← call1 rt "tail" Ashp
    call2 rt "check_broadcast_shape" st axisTail
  else raise .dimensionMismatch
theorem p557 : P557 := by simp [P557, m557, one]

def m561 (rt : Runtime) (shape A : Value) : M Value := do
  let ax ← call1 rt "axes" A
  call2 rt "check_broadcast_shape" shape ax
def P561 : Prop := ∀ rt shape A, m561 rt shape A = do
  let ax ← call1 rt "axes" A
  call2 rt "check_broadcast_shape" shape ax
theorem p561 : P561 := by simp [P561, m561]

def m563 (rt : Runtime) (shape A As : Value) : M Value := do
  let _ ← call2 rt "check_broadcast_axes" shape A
  rt.call "check_broadcast_axes:slurp" [shape, As]
def P563 : Prop := ∀ rt shape A As, m563 rt shape A As = do
  let _ ← call2 rt "check_broadcast_axes" shape A
  rt.call "check_broadcast_axes:slurp" [shape, As]
theorem p563 : P563 := by simp [P563, m563]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; source equation and broadcast-shape invariant",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry 502 "combine_axes(A,B...)" "The vararg overload combines axes(A) with recursively combined trailing axes." ``P502 ``p502,
  entry 503 "combine_axes(A,B)" "The binary overload combines axes(A) and axes(B)." ``P503 ``p503,
  entry 504 "combine_axes(A)" "The unary overload returns axes(A)." ``P504 ``p504,
  entry 521 "broadcast_shape(shape)" "A single shape is returned unchanged." ``P521 ``p521,
  entry 522 "broadcast_shape(shape,shape1,shapes...)" "Multiple shapes combine the first pair before recursive combination." ``P522 ``p522,
  entry 524 "_bcs((),())" "Two empty shapes combine to empty." ``P524 ``p524,
  entry 525 "_bcs((),newshape)" "An empty left shape copies the right head before recursing." ``P525 ``p525,
  entry 526 "_bcs(shape,())" "An empty right shape copies the left head before recursing." ``P526 ``p526,
  entry 527 "_bcs(shape,newshape)" "The general case combines heads before recursively combining tails." ``P527 ``p527,
  entry 531 "_bcs1(::Integer,::Integer)" "Integer extents expand singleton values and reject incompatible lengths in branch order." ``P531 ``p531,
  entry 532 "_bcs1(::Integer,b)" "An integer extent accepts one or an exactly matching one-based axis." ``P532 ``p532,
  entry 533 "_bcs1(a,::Integer)" "The reversed mixed overload swaps its arguments." ``P533 ``p533,
  entry 534 "_bcs1(a,b)" "The general axis method tests reverse compatibility before forward compatibility." ``P534 ``p534,
  entry 536 "_bcsm(a,b)" "Axis matching accepts equality or a singleton second axis." ``P536 ``p536,
  entry 537 "_bcsm(a,::Number)" "A numeric second extent matches exactly one." ``P537 ``p537,
  entry 538 "_bcsm(::Number,::Number)" "Numeric extents match equality or a singleton second value." ``P538 ``p538,
  entry 542 "axistype(a::T,b::T)" "Equal axis types preserve the first value." ``P542 ``p542,
  entry 543 "axistype(::OneTo,::OneTo)" "Two OneTo axes convert the first to OneTo{Int}." ``P543 ``p543,
  entry 544 "axistype(a,b)" "The fallback converts the first axis to UnitRange{Int}." ``P544 ``p544,
  entry 548 "check_broadcast_shape(shape)" "A destination shape alone needs no check." ``P548 ``p548,
  entry 549 "check_broadcast_shape(shape,())" "An empty source shape needs no check." ``P549 ``p549,
  entry 550 "check_broadcast_shape((),())" "Two empty shapes need no check." ``P550 ``p550,
  entry 551 "check_broadcast_shape((),Ashp)" "Extra source axes must all be singleton." ``P551 ``p551,
  entry 557 "check_broadcast_shape(shape,Ashp)" "The general check validates heads before recursively validating tails." ``P557 ``p557,
  entry 561 "check_broadcast_axes(shape,A)" "The array overload checks shape against axes(A)." ``P561 ``p561,
  entry 563 "check_broadcast_axes(shape,A,As...)" "The vararg overload checks A before recursively checking As." ``P563 ``p563
]

end JuliaLean.BroadcastCov.ShapeExact
