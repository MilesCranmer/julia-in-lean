import JuliaLean.Proofs.base.abstractarray.rows.basic
import JuliaLean.Proofs.base.abstractarray.rows.iteration
import JuliaLean.Proofs.base.abstractarray.rows.bounds_shape
import JuliaLean.Proofs.base.abstractarray.rows.copy
import JuliaLean.Proofs.base.abstractarray.rows.index
import JuliaLean.Proofs.base.abstractarray.rows.alias_get
import JuliaLean.Proofs.base.abstractarray.rows.concat_direct
import JuliaLean.Proofs.base.abstractarray.rows.concat_complex
import JuliaLean.Proofs.base.abstractarray.rows.hvncat
import JuliaLean.Proofs.base.abstractarray.rows.stack
import JuliaLean.Proofs.base.abstractarray.rows.order_index
import JuliaLean.Proofs.base.abstractarray.rows.map_mut

namespace JuliaLean.AbstractArrayCov

/-- Method-specific registry entries for `base/abstractarray.jl`. -/
def entries : List JuliaLean.Registry.Entry :=
  Rows.Basic.entries ++ Rows.Iteration.entries ++ Rows.BoundsShape.entries ++
    Rows.Copy.entries ++ Rows.Index.entries ++ Rows.AliasGet.entries ++
    Rows.ConcatDirect.entries ++ Rows.ConcatComplex.entries ++ Rows.Hvncat.entries ++
    Rows.Stack.entries ++ Rows.OrderIndex.entries ++ Rows.MapMut.entries

end JuliaLean.AbstractArrayCov
