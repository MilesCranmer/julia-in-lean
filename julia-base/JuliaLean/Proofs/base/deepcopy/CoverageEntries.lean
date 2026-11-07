import JuliaLean.Proofs.base.deepcopy.MethodRows
import JuliaLean.Registry.Types

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

end JuliaLean.DictsCov
