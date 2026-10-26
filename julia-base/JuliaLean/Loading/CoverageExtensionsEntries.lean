import JuliaLean.Loading.CoverageExtensions

namespace JuliaLean.Loading.Coverage.Extensions

open JuliaLean.Registry

private def methodNamespace : Lean.Name := (``method1475).getPrefix
private def methodEntry (line : Nat) : Entry :=
  { id := s!"loading-method-{line}", juliaFile := "base/loading.jl"
    juliaFns := [s!"method beginning at base/loading.jl:{line}"]
    statement := "The method satisfies the caller-visible result or state invariant stated by its method-specific property."
    source := s!"base/loading.jl:{line}; caller-visible contract"
    status := .proven, prop := methodNamespace.str s!"Property{line}"
    thm := some (methodNamespace.str s!"property{line}") }

private def lines : List Nat := [
  1475,1548,1571,1592,1612,1645,1670,1720,1753,1761,1807,1838,1868,1893,1925,1944,1945,
  1969,1971,1979,1980,2000,2004,2012,2022,2036,2044,2053,2062,2067,2069,2073,2096,2104,
  2126,2156,2171,2181,2186,2206,2289,2303,2324,2344,2372,2411,2568,2638,2653
]

def entries : List Entry := lines.map methodEntry

end JuliaLean.Loading.Coverage.Extensions
