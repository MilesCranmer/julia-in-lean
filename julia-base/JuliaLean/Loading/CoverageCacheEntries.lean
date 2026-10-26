import JuliaLean.Loading.CoverageCache

namespace JuliaLean.Loading.Coverage.Cache

open JuliaLean.Registry

private def methodNamespace : Lean.Name := (``method4025).getPrefix
private def methodEntry (line : Nat) : Entry :=
  { id := s!"loading-method-{line}", juliaFile := "base/loading.jl"
    juliaFns := [s!"method beginning at base/loading.jl:{line}"]
    statement := "The method satisfies the caller-visible result or state invariant stated by its method-specific property."
    source := s!"base/loading.jl:{line}; caller-visible contract"
    status := .proven, prop := methodNamespace.str s!"Property{line}"
    thm := some (methodNamespace.str s!"property{line}") }

private def lines : List Nat := [
  4025,4036,4047,4049,4061,4063,4070,4086,4119,4144,4148,4158,4171,4175,4188,4202,
  4265,4359,4370,4371,4383,4388,4398,4405,4428,4438,4456,4483,4490,4498,4541,4566,
  4577,4604,4612,4642,4657,4669,4692,4695,4733,4744,4768,4773,4792,4794,4802,4859,
  4866,4868,4876,4885,4913,4916,4919,5149,5184,5190,5196,5199,5207,5211,5220,5225,
  5234,5244,5248
]

def entries : List Entry := lines.map methodEntry

end JuliaLean.Loading.Coverage.Cache
