import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.DictsCov.DictIterProofs
import JuliaLean.DictsCov.IdMapBug
import JuliaLean.DictsCov.AbsBugs
import JuliaLean.DictsCov.DeepcopyRows
import JuliaLean.DictsCov.HamtRows
import JuliaLean.DictsCov.IdDictRows
import JuliaLean.DictsCov.AbstractDictRows
import JuliaLean.DictsCov.DictRows
import JuliaLean.DictsCov.WeakDictRows
import JuliaLean.DictsCov.DictSplitRows

namespace JuliaLean.DictsCov

open JuliaLean.Registry

def DeepcopyWeakRegistered : Prop := DeepcopyRows.DeepcopyWeakRegistered

theorem deepcopyWeakRegistered_refuted : ¬ DeepcopyWeakRegistered :=
  DeepcopyRows.deepcopyWeakRegistered_refuted

/-- Registry entries of this area. -/
def coreEntries : List Entry := [
  { id := "dictscov-deepcopy-weakref", juliaFile := "base/deepcopy.jl"
    juliaFns := ["deepcopy(@nospecialize x)", "deepcopy_internal(@nospecialize(x), stackdict::IdDict)"]
    statement := "deepcopy of a WeakRef returns a registered weak reference whose value is cleared when its copied referent is collected."
    source := "deepcopy docstring base/deepcopy.jl:11-17; WeakRef docstring base/gcutils.jl:9-10"
    status := .refuted, prop := ``DeepcopyWeakRegistered,
    thm := some ``deepcopyWeakRegistered_refuted, issue := "#62597"
    notes := "Both versions: the generic mutable-object path allocates an unregistered WeakRef, so GC frees the copied referent without clearing the copied WeakRef field. P0." }
]

def entries : List Entry :=
  coreEntries ++ DeepcopyRows.entries ++ HamtRows.entries ++ IdDictRows.entries
    ++ AbstractDictRows.entries
    ++ DictRows.entries
    ++ WeakDictRows.entries
    ++ DictSplitRows.entries

end JuliaLean.DictsCov
