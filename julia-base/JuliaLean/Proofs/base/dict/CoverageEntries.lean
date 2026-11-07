import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.dict.DictIterProofs
import JuliaLean.Proofs.base.abstractdict.IdMapBug
import JuliaLean.Proofs.base.abstractdict.AbsBugs
import JuliaLean.Proofs.base.deepcopy.MethodRows
import JuliaLean.Proofs.base.deepcopy.CoverageEntries
import JuliaLean.Proofs.base.hamt.MethodRows
import JuliaLean.Proofs.base.iddict.MethodRows
import JuliaLean.Proofs.base.abstractdict.MethodRows
import JuliaLean.Proofs.base.dict.MethodRows
import JuliaLean.Proofs.base.weakdict.MethodRows
import JuliaLean.Proofs.base.dict.MethodProjections

namespace JuliaLean.DictsCov

open JuliaLean.Registry

def entries : List Entry :=
  coreEntries ++ DeepcopyRows.entries ++ HamtRows.entries ++ IdDictRows.entries
    ++ AbstractDictRows.entries
    ++ DictRows.entries
    ++ WeakDictRows.entries
    ++ DictSplitRows.entries

end JuliaLean.DictsCov
