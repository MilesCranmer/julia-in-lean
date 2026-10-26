import JuliaLean.Loading.CoverageRequire

namespace JuliaLean.Loading.Coverage.Require

open JuliaLean.Registry

private def methodNamespace : Lean.Name := (``method2677).getPrefix
private def methodEntry (line : Nat) : Entry :=
  { id := s!"loading-method-{line}", juliaFile := "base/loading.jl"
    juliaFns := [s!"method beginning at base/loading.jl:{line}"]
    statement := "The method satisfies the caller-visible result or state invariant stated by its method-specific property."
    source := s!"base/loading.jl:{line}; caller-visible contract"
    status := .proven, prop := methodNamespace.str s!"Property{line}"
    thm := some (methodNamespace.str s!"property{line}") }

private def lines : List Nat := [
  2677,2682,2721,2758,2781,2788,2791,2792,2793,2803,2847,2855,2867,2919,2948,2970,
  2977,2994,3032,3039,3041,3051,3056,3079,3102,3103,3108,3109,3111,3115,3126,3140,
  3305,3367,3368,3421,3444,3472,3475,3486,3512,3559,3568,3570,3593,3672,3679,3680,
  3681,3682,3688,3772,3775,3782,3790,3795,3831,3840,4004
]

def entries : List Entry := lines.map methodEntry

end JuliaLean.Loading.Coverage.Require
