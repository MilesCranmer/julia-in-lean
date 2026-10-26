import JuliaLean.AbstractArrayCov.Rows.Basic
import JuliaLean.AbstractArrayCov.Rows.Iteration
import JuliaLean.AbstractArrayCov.Rows.BoundsShape
import JuliaLean.AbstractArrayCov.Rows.Copy
import JuliaLean.AbstractArrayCov.Rows.Index
import JuliaLean.AbstractArrayCov.Rows.AliasGet
import JuliaLean.AbstractArrayCov.Rows.ConcatDirect
import JuliaLean.AbstractArrayCov.Rows.ConcatComplex
import JuliaLean.AbstractArrayCov.Rows.Hvncat
import JuliaLean.AbstractArrayCov.Rows.Stack
import JuliaLean.AbstractArrayCov.Rows.OrderIndex
import JuliaLean.AbstractArrayCov.Rows.MapMut

namespace JuliaLean.AbstractArrayCov

/-- Method-specific registry entries for `base/abstractarray.jl`. -/
def entries : List JuliaLean.Registry.Entry :=
  Rows.Basic.entries ++ Rows.Iteration.entries ++ Rows.BoundsShape.entries ++
    Rows.Copy.entries ++ Rows.Index.entries ++ Rows.AliasGet.entries ++
    Rows.ConcatDirect.entries ++ Rows.ConcatComplex.entries ++ Rows.Hvncat.entries ++
    Rows.Stack.entries ++ Rows.OrderIndex.entries ++ Rows.MapMut.entries

end JuliaLean.AbstractArrayCov
