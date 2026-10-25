import JuliaLean.Platforms.Lemmas

/-!
# The finitely many platforms behind `CoreTripletRoundtrip`

With `validate_strict = true`, the constructor accepts only the architectures in
`archs`, the operating systems in `oses`, the `libc` values in `libcOpts` and the
`call_abi` values in `cavOpts` (after lowercasing and normalisation). This file
computes the round trip `parse(Platform, triplet(p))` for every such combination
by kernel evaluation, with `asciiLower` as the lowercase mapping;
`CoreRoundtrip.lean` shows that the mapping does not matter.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (matchRe capture)

/-! ## The arguments `parsePlatform` hands to the constructor -/

/-- `parsePlatform` up to its final constructor call (`base/binaryplatforms.jl:760-825`):
the architecture, the OS and the tag list it passes to `platform`. -/
def parseArgs (t : Str) : Jl (Str × Str × List (Str × TagVal)) := do
  match matchRe tripletRe t with
  | none => throw (.argumentError "not an officially supported platform")
  | some m =>
    let archF ← getField m archMapping
    let osF ← getField m osMapping
    let (a, o) ← match archF, osF with
      | .key a, .key o => pure (a, o)
      | _, _ => throw (.methodError "Platform")
    let d : Dict TagVal := []
    let d := dput d (s% "libc") (fieldVal (← getField m libcMapping))
    let d := dput d (s% "call_abi") (fieldVal (← getField m callAbiMapping))
    let d := dput d (s% "libgfortran_version") (fieldVal (← getField m libgfortranMapping))
    let d := dput d (s% "libstdcxx_version") (fieldVal (← getField m libstdcxxMapping))
    let d := dput d (s% "cxxstring_abi") (fieldVal (← getField m cxxstringMapping))
    let ext ← splitTags ((capture m tagsGroup).getD [])
    let d := ext.foldl (fun d kv => dput d kv.1 (.str kv.2)) d
    let osv ← if o == s% "macos" then extractOsVersion ((capture m 10).getD []) (s% "darwin")
      else if o == s% "freebsd" then extractOsVersion ((capture m 13).getD []) (s% "freebsd")
      else if o == s% "openbsd" then extractOsVersion ((capture m 11).getD []) (s% "openbsd")
      else pure none
    let d := dput d (s% "os_version") (match osv with | some v => .ver v | none => .none)
    let isStd (e : Str × TagVal) : Bool := e.1 == s% "libstdcxx_version"
    pure (a, o, d.filter (!isStd ·) ++ d.filter isStd)

/-! ## Inputs on which the lowercase mapping only meets ASCII characters -/

/-- Every character is ASCII. -/
def asc (s : Str) : Bool := s.all fun c => decide (c.toNat < 128)

/-- Lowercased tag names for which `add_platform_tag!` passes the value to
`add_tag!` unchanged. -/
def plainTag (tag : Str) : Bool :=
  !(tag == s% "libstdcxx_version") && !(tag == s% "cxxstring_abi") &&
    ![s% "libgfortran_version", s% "cxxlib_version", s% "os_version"].contains tag

/-- A constructor argument whose processing lowercases only ASCII strings, when
`lc'` maps ASCII to ASCII on it. -/
def safeEntry (lc' : Char → Char) : Str × TagVal → Bool
  | (k, .none) => asc k
  | (k, .str s) => asc k && asc (lower lc' k) && plainTag (lower lc' (lower lc' k)) && asc s
  | (_, .ver _) => false

/-! ## The constructor on the core tags -/

/-- The defaults the constructor adds after the tag loop (`base/binaryplatforms.jl:71-83`). -/
def finTags (A O : Str) (tags : Tags) : Tags :=
  let tags := if O == s% "linux" && !haskey tags (s% "libc") then dset tags (s% "libc") (s% "glibc") else tags
  let tags := if O == s% "windows" && !haskey tags (s% "libc") then dset tags (s% "libc") (s% "msvcrt") else tags
  if O == s% "linux" && [s% "armv7l", s% "armv6l"].contains A && !haskey tags (s% "call_abi") then
    dset tags (s% "call_abi") (s% "eabihf") else tags

/-- The comparison strategies the constructor stores when the caller passes none
(`base/binaryplatforms.jl:90-96`). -/
def ctorStrats (tags : Tags) : Dict Strat :=
  if haskey tags (s% "julia_version") && !haskey ([] : Dict Strat) (s% "julia_version") then
    dset ([] : Dict Strat) (s% "julia_version") Strat.juliaMinor else []

/-- `tags[k] = v` when a value is given. -/
def setOpt (t : Tags) (k : Str) : Option Str → Tags
  | none => t
  | some v => dset t k v

def coreTags (A O : Str) (L C : Option Str) : Tags :=
  finTags A O (setOpt (setOpt [(s% "arch", A), (s% "os", O)] (s% "libc") L) (s% "call_abi") C)

def corePlatform (A O : Str) (L C : Option Str) : Platform :=
  ⟨coreTags A O L C, ctorStrats (coreTags A O L C)⟩

def archs : List Str :=
  [s% "x86_64", s% "i686", s% "armv7l", s% "armv6l", s% "aarch64", s% "powerpc64le", s% "riscv64"]

def oses : List Str := [s% "linux", s% "macos", s% "freebsd", s% "openbsd", s% "windows"]

def libcOpts : List (Option Str) :=
  [none, some (s% "glibc"), some (s% "musl"), some (s% "msvcrt"), some (s% "ucrt")]

def cavOpts : List (Option Str) := [none, some (s% "eabi"), some (s% "eabihf")]

/-! ## The round trip on each combination -/

/-- `parse(Platform, triplet(p)) == p` with `asciiLower`, and the constructor call
inside the parse lowercases only ASCII strings. -/
def roundtripB (p : Platform) : Bool :=
  match triplet p with
  | .error _ => false
  | .ok t =>
    match parseArgs t with
    | .error _ => false
    | .ok (a, o, D) =>
      asc a && asc o && D.all (safeEntry asciiLower) &&
        match platform asciiLower a o D false with
        | .ok q => peq p q
        | .error _ => false

/-- The round trip holds whenever the tags pass `validate_tags`. -/
def checkCase (A O : Str) (L C : Option Str) : Bool :=
  match validateTags (coreTags A O L C) with
  | .ok _ => roundtripB (corePlatform A O L C)
  | .error _ => true

theorem cases_linux : ∀ A ∈ archs, ∀ L ∈ libcOpts, ∀ C ∈ cavOpts, checkCase A (s% "linux") L C = true := by
  decide +kernel

theorem cases_macos : ∀ A ∈ archs, ∀ L ∈ libcOpts, ∀ C ∈ cavOpts, checkCase A (s% "macos") L C = true := by
  decide +kernel

theorem cases_freebsd : ∀ A ∈ archs, ∀ L ∈ libcOpts, ∀ C ∈ cavOpts, checkCase A (s% "freebsd") L C = true := by
  decide +kernel

theorem cases_openbsd : ∀ A ∈ archs, ∀ L ∈ libcOpts, ∀ C ∈ cavOpts, checkCase A (s% "openbsd") L C = true := by
  decide +kernel

theorem cases_windows : ∀ A ∈ archs, ∀ L ∈ libcOpts, ∀ C ∈ cavOpts, checkCase A (s% "windows") L C = true := by
  decide +kernel

theorem core_cases : ∀ A ∈ archs, ∀ O ∈ oses, ∀ L ∈ libcOpts, ∀ C ∈ cavOpts, checkCase A O L C = true := by
  intro A hA O hO
  simp only [oses, List.mem_cons, List.not_mem_nil, or_false] at hO
  rcases hO with rfl | rfl | rfl | rfl | rfl
  · exact cases_linux A hA
  · exact cases_macos A hA
  · exact cases_freebsd A hA
  · exact cases_openbsd A hA
  · exact cases_windows A hA

end JuliaLean.Platforms
