import JuliaLean.BroadcastCov.ExactRuntime
import JuliaLean.Registry.Types

namespace JuliaLean.BroadcastCov.IndexExact

open JuliaLean.BroadcastCov.Exact
open JuliaLean.Registry

def one (rt : Runtime) : M Value := call0 rt "Int:1"
def nothing (rt : Runtime) : M Value := call0 rt "nothing"

def m585 (rt : Runtime) (arg I : Value) : M Value := do
  let ax ← call1 rt "axes" arg
  let tuple ← call1 rt "getfield:I" I
  let mapped ← call2 rt "_newindex" ax tuple
  call1 rt "to_index" mapped
def P585 : Prop := ∀ rt arg I, m585 rt arg I = do
  let ax ← call1 rt "axes" arg
  let tuple ← call1 rt "getfield:I" I
  let mapped ← call2 rt "_newindex" ax tuple
  call1 rt "to_index" mapped
theorem p585 : P585 := by simp [P585, m585]

def m586 (rt : Runtime) (arg I : Value) : M Value := do
  let ax ← call1 rt "axes" arg
  let tuple ← call1 rt "tuple:single" I
  let mapped ← call2 rt "_newindex" ax tuple
  call1 rt "to_index" mapped
def P586 : Prop := ∀ rt arg I, m586 rt arg I = do
  let ax ← call1 rt "axes" arg
  let tuple ← call1 rt "tuple:single" I
  let mapped ← call2 rt "_newindex" ax tuple
  call1 rt "to_index" mapped
theorem p586 : P586 := by simp [P586, m586]

def m587 (rt : Runtime) (ax I : Value) : M Value := do
  let ax1 ← call2 rt "getindex" ax (← one rt)
  let n ← call1 rt "length" ax1
  let cond ← call2 rt "==" n (← one rt)
  let first ← call2 rt "getindex:begin" ax1 (← call0 rt "begin")
  let i1 ← call2 rt "getindex" I (← one rt)
  let head ← rt.call "ifelse" [cond, first, i1]
  let axisTail ← call1 rt "tail" ax
  let it ← call1 rt "tail" I
  let rest ← call2 rt "_newindex" axisTail it
  call2 rt "tuple:(head,rest...)" head rest
def P587 : Prop := ∀ rt ax I, m587 rt ax I = do
  let ax1 ← call2 rt "getindex" ax (← one rt)
  let n ← call1 rt "length" ax1
  let cond ← call2 rt "==" n (← one rt)
  let first ← call2 rt "getindex:begin" ax1 (← call0 rt "begin")
  let i1 ← call2 rt "getindex" I (← one rt)
  let head ← rt.call "ifelse" [cond, first, i1]
  let axisTail ← call1 rt "tail" ax
  let it ← call1 rt "tail" I
  let rest ← call2 rt "_newindex" axisTail it
  call2 rt "tuple:(head,rest...)" head rest
theorem p587 : P587 := by simp [P587, m587, one]

def m588 (rt : Runtime) (_I : Value) : M Value := call0 rt "tuple:empty"
def P588 : Prop := ∀ rt I, m588 rt I = call0 rt "tuple:empty"
theorem p588 : P588 := by simp [P588, m588]

def m589 (rt : Runtime) (ax : Value) : M Value := do
  let ax1 ← call2 rt "getindex" ax (← one rt)
  let first ← call2 rt "getindex:begin" ax1 (← call0 rt "begin")
  let axisTail ← call1 rt "tail" ax
  let rest ← call2 rt "_newindex" axisTail (← call0 rt "tuple:empty")
  call2 rt "tuple:(head,rest...)" first rest
def P589 : Prop := ∀ rt ax, m589 rt ax = do
  let ax1 ← call2 rt "getindex" ax (← one rt)
  let first ← call2 rt "getindex:begin" ax1 (← call0 rt "begin")
  let axisTail ← call1 rt "tail" ax
  let rest ← call2 rt "_newindex" axisTail (← call0 rt "tuple:empty")
  call2 rt "tuple:(head,rest...)" first rest
theorem p589 : P589 := by simp [P589, m589, one]

def m590 (rt : Runtime) : M Value := call0 rt "tuple:empty"
def P590 : Prop := ∀ rt, m590 rt = call0 rt "tuple:empty"
theorem p590 : P590 := by simp [P590, m590]

def m593 (rt : Runtime) (I keep defaults : Value) : M Value := do
  let tuple ← call1 rt "getfield:I" I
  let mapped ← rt.call "_newindex" [tuple, keep, defaults]
  call1 rt "to_index" mapped
def P593 : Prop := ∀ rt I keep defaults, m593 rt I keep defaults = do
  let tuple ← call1 rt "getfield:I" I
  let mapped ← rt.call "_newindex" [tuple, keep, defaults]
  call1 rt "to_index" mapped
theorem p593 : P593 := by simp [P593, m593]

def m594 (rt : Runtime) (I keep defaults : Value) : M Value := do
  let tuple ← call1 rt "getfield:I" I
  let i ← call2 rt "getindex" tuple (← one rt)
  rt.call "newindex" [i, keep, defaults]
def P594 : Prop := ∀ rt I keep defaults, m594 rt I keep defaults = do
  let tuple ← call1 rt "getfield:I" I
  let i ← call2 rt "getindex" tuple (← one rt)
  rt.call "newindex" [i, keep, defaults]
theorem p594 : P594 := by simp [P594, m594, one]

def m595 (rt : Runtime) (i keep defaults : Value) : M Value := do
  let k ← call2 rt "getindex" keep (← one rt)
  let left ← call1 rt "Int" i
  let d1 ← call2 rt "getindex" defaults (← one rt)
  let right ← call1 rt "Int" d1
  let chosen ← rt.call "ifelse" [k, left, right]
  let d2 ← call2 rt "getindex" defaults (← call0 rt "Int:2")
  rt.call "CartesianIndex" [chosen, d2]
def P595 : Prop := ∀ rt i keep defaults, m595 rt i keep defaults = do
  let k ← call2 rt "getindex" keep (← one rt)
  let left ← call1 rt "Int" i
  let d1 ← call2 rt "getindex" defaults (← one rt)
  let right ← call1 rt "Int" d1
  let chosen ← rt.call "ifelse" [k, left, right]
  let d2 ← call2 rt "getindex" defaults (← call0 rt "Int:2")
  rt.call "CartesianIndex" [chosen, d2]
theorem p595 : P595 := by simp [P595, m595, one]

def m596 (rt : Runtime) (i keep defaults : Value) : M Value := do
  let k ← call2 rt "getindex" keep (← one rt)
  let d ← call2 rt "getindex" defaults (← one rt)
  rt.call "ifelse" [k, i, d]
def P596 : Prop := ∀ rt i keep defaults, m596 rt i keep defaults = do
  let k ← call2 rt "getindex" keep (← one rt)
  let d ← call2 rt "getindex" defaults (← one rt)
  rt.call "ifelse" [k, i, d]
theorem p596 : P596 := by simp [P596, m596, one]

def m597 (rt : Runtime) (_i _keep _defaults : Value) : M Value := call0 rt "CartesianIndex:empty"
def P597 : Prop := ∀ rt i keep defaults, m597 rt i keep defaults = call0 rt "CartesianIndex:empty"
theorem p597 : P597 := by simp [P597, m597]

def m598 (rt : Runtime) (I keep defaults : Value) : M Value := do
  let k ← call2 rt "getindex" keep (← one rt)
  let i ← call2 rt "getindex" I (← one rt)
  let d ← call2 rt "getindex" defaults (← one rt)
  let head ← rt.call "ifelse" [k, i, d]
  let it ← call1 rt "tail" I
  let kt ← call1 rt "tail" keep
  let dt ← call1 rt "tail" defaults
  let rest ← rt.call "_newindex" [it, kt, dt]
  call2 rt "tuple:(head,rest...)" head rest
def P598 : Prop := ∀ rt I keep defaults, m598 rt I keep defaults = do
  let k ← call2 rt "getindex" keep (← one rt)
  let i ← call2 rt "getindex" I (← one rt)
  let d ← call2 rt "getindex" defaults (← one rt)
  let head ← rt.call "ifelse" [k, i, d]
  let it ← call1 rt "tail" I
  let kt ← call1 rt "tail" keep
  let dt ← call1 rt "tail" defaults
  let rest ← rt.call "_newindex" [it, kt, dt]
  call2 rt "tuple:(head,rest...)" head rest
theorem p598 : P598 := by simp [P598, m598, one]

def m600 (rt : Runtime) (_I _defaults : Value) : M Value := call0 rt "tuple:empty"
def P600 : Prop := ∀ rt I defaults, m600 rt I defaults = call0 rt "tuple:empty"
theorem p600 : P600 := by simp [P600, m600]

def m601 (rt : Runtime) (_keep _defaults : Value) : M Value := call0 rt "tuple:empty"
def P601 : Prop := ∀ rt keep defaults, m601 rt keep defaults = call0 rt "tuple:empty"
theorem p601 : P601 := by simp [P601, m601]

def m602 (rt : Runtime) (_defaults : Value) : M Value := call0 rt "tuple:empty"
def P602 : Prop := ∀ rt defaults, m602 rt defaults = call0 rt "tuple:empty"
theorem p602 : P602 := by simp [P602, m602]

def m606 (rt : Runtime) (A : Value) : M Value := do
  let ax ← call1 rt "axes" A
  call1 rt "shapeindexer" ax
def P606 : Prop := ∀ rt A, m606 rt A = do
  let ax ← call1 rt "axes" A
  call1 rt "shapeindexer" ax
theorem p606 : P606 := by simp [P606, m606]

def m607 (rt : Runtime) (ax : Value) : M Value := call1 rt "_newindexer" ax
def P607 : Prop := ∀ rt ax, m607 rt ax = call1 rt "_newindexer" ax
theorem p607 : P607 := by simp [P607, m607]

def m608 (rt : Runtime) : M Value :=
  rt.call "tuple" [(0 : Value), (0 : Value)]
def P608 : Prop := ∀ rt, m608 rt = rt.call "tuple" [(0 : Value), (0 : Value)]
theorem p608 : P608 := by simp [P608, m608]

def m609 (rt : Runtime) (indsA : Value) : M Value := do
  let ind1 ← call2 rt "getindex" indsA (← one rt)
  let tail ← call1 rt "tail" indsA
  let pair ← call1 rt "_newindexer" tail
  let keep ← call2 rt "getindex" pair (← one rt)
  let defaults ← call2 rt "getindex" pair (← call0 rt "Int:2")
  let n ← call1 rt "Base.length" ind1
  let flag ← call2 rt "!=" n (← one rt)
  let keep ← call2 rt "tuple:(flag,keep...)" flag keep
  let first ← call1 rt "first" ind1
  let defaults ← call2 rt "tuple:(first,defaults...)" first defaults
  rt.call "tuple" [keep, defaults]
def P609 : Prop := ∀ rt indsA, m609 rt indsA = do
  let ind1 ← call2 rt "getindex" indsA (← one rt)
  let tail ← call1 rt "tail" indsA
  let pair ← call1 rt "_newindexer" tail
  let keep ← call2 rt "getindex" pair (← one rt)
  let defaults ← call2 rt "getindex" pair (← call0 rt "Int:2")
  let n ← call1 rt "Base.length" ind1
  let flag ← call2 rt "!=" n (← one rt)
  let keep ← call2 rt "tuple:(flag,keep...)" flag keep
  let first ← call1 rt "first" ind1
  let defaults ← call2 rt "tuple:(first,defaults...)" first defaults
  rt.call "tuple" [keep, defaults]
theorem p609 : P609 := by simp [P609, m609, one]

def m615 (rt : Runtime) (bc Is : Value) : M Value := do
  let flat ← call1 rt "Base.IteratorsMD.flatten" Is
  let I ← call1 rt "to_index" flat
  let style ← call1 rt "IndexStyle" bc
  rt.call "_getindex" [style, bc, I]
def P615 : Prop := ∀ rt bc Is, m615 rt bc Is = do
  let flat ← call1 rt "Base.IteratorsMD.flatten" Is
  let I ← call1 rt "to_index" flat
  let style ← call1 rt "IndexStyle" bc
  rt.call "_getindex" [style, bc, I]
theorem p615 : P615 := by simp [P615, m615]

def m619 (rt : Runtime) (style bc I : Value) : M Value := do
  let _ ← call2 rt "checkbounds" bc I
  call2 rt "_broadcast_getindex" bc I
def P619 : Prop := ∀ rt style bc I, m619 rt style bc I = do
  let _ ← call2 rt "checkbounds" bc I
  call2 rt "_broadcast_getindex" bc I
theorem p619 : P619 := by simp [P619, m619]

def m623 (rt : Runtime) (style bc I : Value) : M Value := do
  let ax ← call1 rt "axes" bc
  let C ← call1 rt "CartesianIndices" ax
  let CI ← call2 rt "getindex" C I
  rt.call "_getindex" [style, bc, CI]
def P623 : Prop := ∀ rt style bc I, m623 rt style bc I = do
  let ax ← call1 rt "axes" bc
  let C ← call1 rt "CartesianIndices" ax
  let CI ← call2 rt "getindex" C I
  rt.call "_getindex" [style, bc, CI]
theorem p623 : P623 := by simp [P623, m623]

def m627 (rt : Runtime) (style bc I : Value) : M Value := do
  let ax ← call1 rt "axes" bc
  let L ← call1 rt "LinearIndices" ax
  let LI ← call2 rt "getindex" L I
  rt.call "_getindex" [style, bc, LI]
def P627 : Prop := ∀ rt style bc I, m627 rt style bc I = do
  let ax ← call1 rt "axes" bc
  let L ← call1 rt "LinearIndices" ax
  let LI ← call2 rt "getindex" L I
  rt.call "_getindex" [style, bc, LI]
theorem p627 : P627 := by simp [P627, m627]

def m631 (rt : Runtime) : M Value := call0 rt "CartesianIndex:empty"
def P631 : Prop := ∀ rt, m631 rt = call0 rt "CartesianIndex:empty"
theorem p631 : P631 := by simp [P631, m631]

def m632 (rt : Runtime) (Is : Value) : M Value := do
  call2 rt "getindex" Is (← one rt)
def P632 : Prop := ∀ rt Is, m632 rt Is = do
  call2 rt "getindex" Is (← one rt)
theorem p632 : P632 := by simp [P632, m632, one]

def m633 (rt : Runtime) (Is : Value) : M Value := call1 rt "CartesianIndex" Is
def P633 : Prop := ∀ rt Is, m633 rt Is = call1 rt "CartesianIndex" Is
theorem p633 : P633 := by simp [P633, m633]

def m635 (rt : Runtime) (bc I : Value) : M Value := do
  let boolType ← call0 rt "Bool:type"
  let ax ← call1 rt "axes" bc
  let tupleI ← call1 rt "tuple:single" I
  let ok ← rt.call "Base.checkbounds_indices" [boolType, ax, tupleI]
  if rt.truth ok then nothing rt else call2 rt "Base.throw_boundserror" bc I
def P635 : Prop := ∀ rt bc I, m635 rt bc I = do
  let boolType ← call0 rt "Bool:type"
  let ax ← call1 rt "axes" bc
  let tupleI ← call1 rt "tuple:single" I
  let ok ← rt.call "Base.checkbounds_indices" [boolType, ax, tupleI]
  if rt.truth ok then nothing rt else call2 rt "Base.throw_boundserror" bc I
theorem p635 : P635 := by simp [P635, m635]

def m640 (rt : Runtime) (bc I : Value) : M Value := do
  let boolType ← call0 rt "Bool:type"
  let linearStyle ← call0 rt "IndexLinear"
  let indices ← rt.call "eachindex" [linearStyle, bc]
  let ok ← rt.call "Base.checkindex" [boolType, indices, I]
  if rt.truth ok then nothing rt else call2 rt "Base.throw_boundserror" bc I
def P640 : Prop := ∀ rt bc I, m640 rt bc I = do
  let boolType ← call0 rt "Bool:type"
  let linearStyle ← call0 rt "IndexLinear"
  let indices ← rt.call "eachindex" [linearStyle, bc]
  let ok ← rt.call "Base.checkindex" [boolType, indices, I]
  if rt.truth ok then nothing rt else call2 rt "Base.throw_boundserror" bc I
theorem p640 : P640 := by simp [P640, m640]

def m651 (rt : Runtime) (A _I : Value) : M Value := call1 rt "getindex:empty" A
def P651 : Prop := ∀ rt A I, m651 rt A I = call1 rt "getindex:empty" A
theorem p651 : P651 := by simp [P651, m651]

def m652 (_rt : Runtime) (T _I : Value) : M Value := pure T
def P652 : Prop := ∀ rt T I, m652 rt T I = pure T
theorem p652 : P652 := by simp [P652, m652]

def m654 (rt : Runtime) (A _I : Value) : M Value := do
  call2 rt "getindex" A (← one rt)
def P654 : Prop := ∀ rt A I, m654 rt A I = do
  call2 rt "getindex" A (← one rt)
theorem p654 : P654 := by simp [P654, m654, one]

def m655 (rt : Runtime) (A I : Value) : M Value := do
  let i1 ← call2 rt "getindex" I (← one rt)
  call2 rt "getindex" A i1
def P655 : Prop := ∀ rt A I, m655 rt A I = do
  let i1 ← call2 rt "getindex" I (← one rt)
  call2 rt "getindex" A i1
theorem p655 : P655 := by simp [P655, m655, one]

def m657 (rt : Runtime) (A I : Value) : M Value := do
  let index ← call2 rt "newindex" A I
  call2 rt "getindex" A index
def P657 : Prop := ∀ rt A I, m657 rt A I = do
  let index ← call2 rt "newindex" A I
  call2 rt "getindex" A index
theorem p657 : P657 := by simp [P657, m657]

def m669 (rt : Runtime) (b : Value) : M Value := do
  let x ← call1 rt "getfield:x" b
  call1 rt "axes" x
def P669 : Prop := ∀ rt b, m669 rt b = do
  let x ← call1 rt "getfield:x" b
  call1 rt "axes" x
theorem p669 : P669 := by simp [P669, m669]

def m670 (rt : Runtime) (b i : Value) : M Value := do
  let x ← call1 rt "getfield:x" b
  let keeps ← call1 rt "getfield:keeps" b
  let defaults ← call1 rt "getfield:defaults" b
  let index ← rt.call "newindex" [i, keeps, defaults]
  call2 rt "getindex" x index
def P670 : Prop := ∀ rt b i, m670 rt b i = do
  let x ← call1 rt "getfield:x" b
  let keeps ← call1 rt "getfield:keeps" b
  let defaults ← call1 rt "getfield:defaults" b
  let index ← rt.call "newindex" [i, keeps, defaults]
  call2 rt "getindex" x index
theorem p670 : P670 := by simp [P670, m670]

def m671 (rt : Runtime) (x : Value) : M Value := do
  let pair ← call1 rt "newindexer" x
  rt.call "Extruded:slurp" [x, pair]
def P671 : Prop := ∀ rt x, m671 rt x = do
  let pair ← call1 rt "newindexer" x
  rt.call "Extruded:slurp" [x, pair]
theorem p671 : P671 := by simp [P671, m671]

def m672 (_rt : Runtime) (x : Value) : M Value := pure x
def P672 : Prop := ∀ rt x, m672 rt x = pure x
theorem p672 : P672 := by simp [P672, m672]

def m675 (rt : Runtime) (bc I : Value) : M Value := do
  let tuple ← call1 rt "getfield:args" bc
  let args ← call2 rt "_getindex" tuple I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, args]
def P675 : Prop := ∀ rt bc I, m675 rt bc I = do
  let tuple ← call1 rt "getfield:args" bc
  let args ← call2 rt "_getindex" tuple I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, args]
theorem p675 : P675 := by simp [P675, m675]

def m685 (rt : Runtime) (bc T I : Value) : M Value := do
  let tuple ← call1 rt "getfield:args" bc
  let tail ← call1 rt "tail" tuple
  let args ← call2 rt "_getindex" tail I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, T, args]
def P685 : Prop := ∀ rt bc T I, m685 rt bc T I = do
  let tuple ← call1 rt "getfield:args" bc
  let tail ← call1 rt "tail" tuple
  let args ← call2 rt "_getindex" tail I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, T, args]
theorem p685 : P685 := by simp [P685, m685]

def m689 (rt : Runtime) (bc T I : Value) : M Value := do
  let tuple ← call1 rt "getfield:args" bc
  let first ← call2 rt "getindex" tuple (← one rt)
  let arg1 ← call2 rt "_broadcast_getindex" first I
  let tail ← call1 rt "tail" tuple
  let tail ← call1 rt "tail" tail
  let args ← call2 rt "_getindex" tail I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, arg1, T, args]
def P689 : Prop := ∀ rt bc T I, m689 rt bc T I = do
  let tuple ← call1 rt "getfield:args" bc
  let first ← call2 rt "getindex" tuple (← one rt)
  let arg1 ← call2 rt "_broadcast_getindex" first I
  let tail ← call1 rt "tail" tuple
  let tail ← call1 rt "tail" tail
  let args ← call2 rt "_getindex" tail I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, arg1, T, args]
theorem p689 : P689 := by simp [P689, m689, one]

def m694 (rt : Runtime) (bc T S I : Value) : M Value := do
  let tuple ← call1 rt "getfield:args" bc
  let tail ← call1 rt "tail" tuple
  let tail ← call1 rt "tail" tail
  let args ← call2 rt "_getindex" tail I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, T, S, args]
def P694 : Prop := ∀ rt bc T S I, m694 rt bc T S I = do
  let tuple ← call1 rt "getfield:args" bc
  let tail ← call1 rt "tail" tuple
  let tail ← call1 rt "tail" tail
  let args ← call2 rt "_getindex" tail I
  let f ← call1 rt "getfield:f" bc
  rt.call "_broadcast_getindex_evalf:slurp" [f, T, S, args]
theorem p694 : P694 := by simp [P694, m694]

def m700 (rt : Runtime) (head tail I : Value) : M Value := do
  let first ← call2 rt "_broadcast_getindex" head I
  let rest ← call2 rt "_getindex" tail I
  call2 rt "tuple:(first,rest...)" first rest
def P700 : Prop := ∀ rt head tail I, m700 rt head tail I = do
  let first ← call2 rt "_broadcast_getindex" head I
  let rest ← call2 rt "_getindex" tail I
  call2 rt "tuple:(first,rest...)" first rest
theorem p700 : P700 := by simp [P700, m700]

def m701 (rt : Runtime) (head I : Value) : M Value := do
  let first ← call2 rt "_broadcast_getindex" head I
  call1 rt "tuple:single" first
def P701 : Prop := ∀ rt head I, m701 rt head I = do
  let first ← call2 rt "_broadcast_getindex" head I
  call1 rt "tuple:single" first
theorem p701 : P701 := by simp [P701, m701]

def m702 (rt : Runtime) (_I : Value) : M Value := call0 rt "tuple:empty"
def P702 : Prop := ∀ rt I, m702 rt I = call0 rt "tuple:empty"
theorem p702 : P702 := by simp [P702, m702]

def m704 (rt : Runtime) (f args : Value) : M Value := rt.call "call:slurp" [f, args]
def P704 : Prop := ∀ rt f args, m704 rt f args = rt.call "call:slurp" [f, args]
theorem p704 : P704 := by simp [P704, m704]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"broadcastcov-broadcast-{line}", juliaFile := "base/broadcast.jl",
    juliaFns := [name], statement := statement,
    source := s!"base/broadcast.jl:{line}; source equation and indexing invariant",
    status := .proven, prop := prop, thm := some thm }

def entries : List Entry := [
  entry 585 "newindex(arg,::CartesianIndex)" "Cartesian newindex reads axes and index tuple before remapping and conversion." ``P585 ``p585,
  entry 586 "newindex(arg,::Integer)" "Scalar newindex wraps the index as a singleton tuple before remapping." ``P586 ``p586,
  entry 587 "_newindex(ax::Tuple,I::Tuple)" "The recursive mapper eagerly computes singleton and supplied indices before recursing." ``P587 ``p587,
  entry 588 "_newindex((),I)" "No axes produce no indices." ``P588 ``p588,
  entry 589 "_newindex(ax,())" "Missing supplied indices use each remaining axis first value." ``P589 ``p589,
  entry 590 "_newindex((),())" "Two empty tuples map to empty." ``P590 ``p590,
  entry 593 "newindex(::CartesianIndex,keep,defaults)" "The Cartesian overload remaps its tuple then converts the result." ``P593 ``p593,
  entry 594 "newindex(::CartesianIndex{1},keep,defaults)" "The one-dimensional Cartesian overload delegates as a scalar." ``P594 ``p594,
  entry 595 "newindex(::Integer,keep,defaults)" "Scalar remapping eagerly converts both branches and constructs CartesianIndex." ``P595 ``p595,
  entry 596 "newindex(::Integer,::Tuple{Bool},defaults)" "The singleton keep tuple selects the scalar or default." ``P596 ``p596,
  entry 597 "newindex(::Integer,(),defaults)" "An empty keep tuple yields an empty CartesianIndex." ``P597 ``p597,
  entry 598 "_newindex(I,keep,defaults)" "Recursive keep remapping computes the head before all tails." ``P598 ``p598,
  entry 600 "_newindex(I,(),defaults)" "An empty keep tuple truncates the result." ``P600 ``p600,
  entry 601 "_newindex((),keep,defaults)" "An empty index tuple truncates the result." ``P601 ``p601,
  entry 602 "_newindex((),(),defaults)" "Two empty tuples yield empty." ``P602 ``p602,
  entry 606 "newindexer(A)" "newindexer applies shapeindexer to axes(A)." ``P606 ``p606,
  entry 607 "shapeindexer(ax)" "shapeindexer delegates to _newindexer." ``P607 ``p607,
  entry 608 "_newindexer(())" "Empty axes produce empty keep and default tuples." ``P608 ``p608,
  entry 609 "_newindexer(indsA)" "The recursive indexer processes the tail, computes length and first, then prepends both outputs." ``P609 ``p609,
  entry 615 "getindex(::Broadcasted,Is...)" "Broadcasted indexing flattens indices, converts them, chooses IndexStyle, then dispatches." ``P615 ``p615,
  entry 619 "_getindex(style,bc,I)" "The common getter checks bounds before unchecked broadcast evaluation." ``P619 ``p619,
  entry 623 "_getindex(::IndexCartesian,bc,::Integer)" "Cartesian style converts a linear integer through CartesianIndices." ``P623 ``p623,
  entry 627 "_getindex(::IndexLinear,bc,::CartesianIndex)" "Linear style converts a Cartesian index through LinearIndices." ``P627 ``p627,
  entry 631 "to_index(())" "An empty tuple becomes an empty CartesianIndex." ``P631 ``p631,
  entry 632 "to_index(::Tuple{Any})" "A singleton tuple returns its element." ``P632 ``p632,
  entry 633 "to_index(::Tuple)" "A general tuple becomes a CartesianIndex." ``P633 ``p633,
  entry 635 "checkbounds(::Broadcasted,::CartesianIndex)" "Cartesian bounds use checkbounds_indices and throw before returning nothing." ``P635 ``p635,
  entry 640 "checkbounds(::Broadcasted,::Integer)" "Linear bounds use eachindex(IndexLinear(),bc) and checkindex before throwing or returning." ``P640 ``p640,
  entry 651 "_broadcast_getindex(scalar-like,I)" "Scalar-like arguments ignore I and index with empty brackets." ``P651 ``p651,
  entry 652 "_broadcast_getindex(::Ref{Type{T}},I)" "A Ref holding a type returns T." ``P652 ``p652,
  entry 654 "_broadcast_getindex(::Tuple{Any},I)" "A singleton tuple returns its sole element." ``P654 ``p654,
  entry 655 "_broadcast_getindex(::Tuple,I)" "A tuple indexes with the first broadcast index." ``P655 ``p655,
  entry 657 "_broadcast_getindex(A,I)" "An array-like argument computes newindex before indexing A." ``P657 ``p657,
  entry 669 "axes(::Extruded)" "Extruded axes forward to the wrapped value." ``P669 ``p669,
  entry 670 "_broadcast_getindex(::Extruded,i)" "Extruded indexing remaps with keeps and defaults before reading x." ``P670 ``p670,
  entry 671 "extrude(::AbstractArray)" "Array extrusion computes newindexer and constructs Extruded." ``P671 ``p671,
  entry 672 "extrude(x)" "Non-array arguments pass through unchanged." ``P672 ``p672,
  entry 675 "_broadcast_getindex(::Broadcasted,I)" "Nested broadcast evaluation gathers arguments before calling the function." ``P675 ``p675,
  entry 685 "_broadcast_getindex(type-first Broadcasted,I)" "A leading Ref{Type} is supplied directly before indexed trailing arguments." ``P685 ``p685,
  entry 689 "_broadcast_getindex(type-second Broadcasted,I)" "The first argument is indexed, the type is supplied directly, then trailing arguments are indexed." ``P689 ``p689,
  entry 694 "_broadcast_getindex(two-types Broadcasted,I)" "Two leading Ref types are supplied directly before indexed trailing arguments." ``P694 ``p694,
  entry 700 "_getindex(args::Tuple,I)" "Tuple argument gathering evaluates the head before recursively gathering the tail." ``P700 ``p700,
  entry 701 "_getindex(args::Tuple{Any},I)" "The singleton gather evaluates its one argument." ``P701 ``p701,
  entry 702 "_getindex((),I)" "The empty argument tuple gathers empty." ``P702 ``p702,
  entry 704 "_broadcast_getindex_evalf(f,args...)" "The final evaluator calls f with all gathered arguments." ``P704 ``p704
]

end JuliaLean.BroadcastCov.IndexExact
