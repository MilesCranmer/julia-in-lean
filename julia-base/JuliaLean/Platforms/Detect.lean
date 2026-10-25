import JuliaLean.Platforms.Basic

/-!
# `detect_libstdcxx_version` (`base/binaryplatforms.jl:931-1027`)

The process state the function observes is an explicit `Proc`.
-/

namespace JuliaLean.Platforms

open JuliaLean
open JuliaLean.VersionNumbers (VersionNumber)

/-- What `detect_libstdcxx_version` observes of the running process. -/
structure Proc where
  /-- `get_csl_member(:libstdcxx) !== nothing`: `CompilerSupportLibraries_jll` is
  loaded and defines `libstdcxx`. -/
  cslLibstdcxx : Bool
  /-- `Libdl.dllist()`. -/
  dllist : List Str
  /-- `dlsym(h, "GLIBCXX_3.4.$m"; throw_error=false) !== nothing` for the loaded
  libstdc++ (the one `dlopen(path, RTLD_NOLOAD)` returns a handle to). -/
  glibcxx : Nat → Bool

/-- `occursin(needle, s)`. -/
def occursIn (needle s : Str) : Bool :=
  (List.range (s.length + 1)).any fun i => startsWith (s.drop i) needle

/-- `_get_libstdcxx_handle()`, `base/binaryplatforms.jl:965-980`; the handle is
represented by the path it was opened from. -/
def getLibstdcxxHandle (p : Proc) : Option Str :=
  if p.cslLibstdcxx then none
  else (p.dllist.filter (occursIn (s% "libstdc++"))).head?

/-- The loop `for minor_version in max_minor_version:-1:18`, from `m` down. -/
def searchMinor (p : Proc) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, m => if m < 18 then none else if p.glibcxx m then some m else searchMinor p fuel (m - 1)

/-- `detect_libstdcxx_version(max_minor_version)`, `base/binaryplatforms.jl:1013-1027`. -/
def detectLibstdcxxVersion (p : Proc) (maxMinor : Nat) : Jl (Option VersionNumber) :=
  match getLibstdcxxHandle p with
  | none => pure none
  | some _ =>
    match searchMinor p (maxMinor + 1) maxMinor with
    | none => pure none
    | some m => some <$> VersionNumbers.parse (s% "3.4." ++ showNat m)

end JuliaLean.Platforms
