import JuliaLean.Platforms.Lemmas

/-!
# The constructor's defaults
-/

namespace JuliaLean.Platforms

open JuliaLean

/-- The tags the constructor builds from `arch` and `os` alone (after normalisation). -/
def defaultTags (A O : Str) : Tags :=
  let t0 : Tags := [(s% "arch", A), (s% "os", O)]
  let t1 := if O == s% "linux" && !haskey t0 (s% "libc") then dset t0 (s% "libc") (s% "glibc") else t0
  let t2 := if O == s% "windows" && !haskey t1 (s% "libc") then dset t1 (s% "libc") (s% "msvcrt") else t1
  if O == s% "linux" && [s% "armv7l", s% "armv6l"].contains A && !haskey t2 (s% "call_abi") then
    dset t2 (s% "call_abi") (s% "eabihf") else t2

theorem platform_nil (lc : Char → Char) (a o : Str) (p : Platform)
    (h : platform lc a o [] false = .ok p) : p.tags = defaultTags (normalizeArch lc a) (lower lc o) := by
  have h' := Except.ok.inj h
  rw [← h']
  rfl

theorem constructorDefaults_proven : ConstructorDefaults := by
  intro lc _ a o p h
  have ht := platform_nil lc a o p h
  simp only [arch, os, libc, callAbi, tget, ht]
  generalize normalizeArch lc a = A
  generalize lower lc o = O
  unfold defaultTags
  by_cases hl : O = s% "linux"
  · subst hl
    by_cases harm : [s% "armv7l", s% "armv6l"].contains A = true
    · simp only [harm]
      simp (config := { decide := true }) [haskey, dget, dset]
    · have harm' : [s% "armv7l", s% "armv6l"].contains A = false := by simpa using harm
      simp only [harm']
      simp (config := { decide := true }) [haskey, dget, dset]
  · by_cases hw : O = s% "windows"
    · subst hw
      simp (config := { decide := true }) [haskey, dget, dset]
    · simp (config := { decide := true }) [hl, hw, haskey, dget, dset]

end JuliaLean.Platforms
