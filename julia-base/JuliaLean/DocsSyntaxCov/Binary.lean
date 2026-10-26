import JuliaLean.Platforms
import JuliaLean.Platforms.Lit
import JuliaLean.DocsSyntaxCov.Ast

/-!
# Remaining method models for `base/binaryplatforms.jl`

Core construction, parsing, triplet, dynamic-library and matching behavior is reused from
`JuliaLean.Platforms`.  This module models the thin overloads, mutation wrappers, display,
host detection and nested helpers that the original area did not register separately.
-/

namespace JuliaLean.DocsSyntaxCov.Binary

open JuliaLean JuliaLean.Platforms
open JuliaLean.VersionNumbers (VersionNumber)

def joinStr (sep : Str) : List Str → Str
  | [] => []
  | [x] => x
  | x :: xs => x ++ sep ++ joinStr sep xs

def tagvalueString (v : Str) : TagVal := .str v
def tagvalueSymbol (v : Str) : TagVal := .str v
def tagvalueAbstractString (convertString : Str → Str) (v : Str) : TagVal := .str (convertString v)

def tags (p : Platform) : Tags := p.tags
def getindex (p : Platform) (k : Str) : DJ Str := match dget p.tags k with
  | some v => .ok v | none => .error (.keyError (String.mk k))
def haskeyP (p : Platform) (k : Str) : Bool := haskey p.tags k

/-- `setindex!` delegates to `add_platform_tag!` and returns the platform. -/
def setindex (lc : Char → Char) (p : Platform) (v k : Str) : Jl Platform := do
  let tags ← addPlatformTag lc p.tags k (TagVal.str v)
  pure { p with tags := tags }

def platformHash (hashTags : Tags → Nat → Nat) (hashStrats : Dict Strat → Nat → Nat)
    (p : Platform) (h : Nat) : Nat :=
  let h := Nat.xor h 0x506c6174666f726d
  let h := hashTags p.tags h
  hashStrats p.strats h

def platformEq (a b : Platform) : Bool := peq a b

def showPair (p : Str × Str) : Str := p.1 ++ s% " = \"" ++ p.2 ++ s% "\""

/-- The serializing `show(::IO, ::Platform)`, lines 199-209. -/
def showPlatform (p : Platform) : Str :=
  let others := sortBy (fun a b => strLt a.1 b.1) (p.tags.filter fun kv => kv.1 != s% "arch" && kv.1 != s% "os")
  s% "Platform(\"" ++ (arch p).getD [] ++ s% "\", \"" ++ (os p).getD [] ++ s% "\"; " ++
    joinStr (s% ", ") (others.map showPair) ++ [')']

def platformNames : List (Option Str × Str) :=
  [(some (s% "linux"), s% "Linux"), (some (s% "macos"), s% "macOS"),
   (some (s% "windows"), s% "Windows"), (some (s% "freebsd"), s% "FreeBSD"),
   (some (s% "openbsd"), s% "OpenBSD"), (none, s% "Unknown")]

def platformName (p : Platform) : DJ Str := match platformNames.find? (·.1 == os p) with
  | some x => .ok x.2 | none => .error (.keyError (String.mk ((os p).getD [])))

/-- The text/plain display, lines 212-220. -/
def showPlatformPlain (p : Platform) : DJ Str := do
  let name ← platformName p
  let others := sortBy (fun a b => strLt a.1 b.1)
    (p.tags.filter fun kv => kv.1 != s% "os" && kv.1 != s% "arch")
  let suffix := if others.isEmpty then [] else
    s% " {" ++ joinStr (s% ", ") (others.map fun kv => kv.1 ++ ['='] ++ kv.2) ++ ['}']
  pure (name ++ [' '] ++ (arch p).getD [] ++ suffix)

def throwInvalidKey (tags : Tags) (k : Str) : Jl Unit :=
  .error (.argumentError ("invalid key " ++ String.mk k))
def throwOsMismatch (_tags : Tags) : Jl Unit := .error (.argumentError "invalid os/arch combination")
def throwLibcMismatch (_tags : Tags) : Jl Unit := .error (.argumentError "invalid os/libc combination")
def throwCallAbiMismatch (_tags : Tags) : Jl Unit := .error (.argumentError "invalid os/call_abi combination")
def throwVersionNumber (_tags : Tags) (k : Str) : Jl Unit :=
  .error (.argumentError ("invalid version " ++ String.mk k))

def setCompareStrategy (p : Platform) (key : Str) (f : Strat) : Jl Platform :=
  if !haskey p.tags key then .error (.argumentError "nonexistent tag")
  else .ok { p with strats := dset p.strats key f }

def getCompareStrategy (p : Platform) (key : Str) (dflt : Strat := .dflt) : Jl Strat :=
  if !haskey p.tags key then .error (.argumentError "nonexistent tag")
  else .ok ((dget p.strats key).getD dflt)

def getCompareStrategyAbstract (_p : Tags) (_key : Str) (dflt : Strat := .dflt) : Strat := dflt

def compareDefault (a b : Str) (_ar _br : Bool) : Bool := a == b

/-- `HostPlatform(p)`, lines 370-378. -/
def hostPlatform (p : Platform) : Platform :=
  let p := if haskey p.tags (s% "os_version") then
    { p with strats := dset p.strats (s% "os_version") .cap } else p
  if dget p.tags (s% "cxxlib") == some (s% "libstdcxx") && haskey p.tags (s% "cxxlib_version") then
    { p with strats := dset p.strats (s% "cxxlib_version") .cap } else p

structure CurrentOS where
  windows : Bool
  apple : Bool
  freebsd : Bool
  openbsd : Bool

def currentOs (s : CurrentOS) : Str := if s.windows then s% "windows" else if s.apple then s% "macos"
  else if s.freebsd then s% "freebsd" else if s.openbsd then s% "openbsd" else s% "linux"

def cxxstringAbi (p : Platform) : Option Str := tget p (s% "cxxstring_abi")
def wordsize (p : Platform) : Nat := if [s% "i686", s% "armv6l", s% "armv7l"].contains ((arch p).getD []) then 32 else 64

def isapple (p : Platform) : Bool := os p == some (s% "macos")
def islinux (p : Platform) : Bool := os p == some (s% "linux")
def iswindows (p : Platform) : Bool := os p == some (s% "windows")
def isfreebsd (p : Platform) : Bool := os p == some (s% "freebsd")
def isopenbsd (p : Platform) : Bool := os p == some (s% "openbsd")
def isbsd (p : Platform) : Bool := [s% "freebsd", s% "openbsd", s% "macos"].contains ((os p).getD [])
def isunix (p : Platform) : Bool := isbsd p || islinux p

/-- Nested `get_set`, lines 671-674. -/
def getSet {S : Type} (families : Dict (List (Str × S))) (arch name : Str) : DJ S := do
  let all ← match dget families arch with | some x => .ok x | none => .error (.keyError (String.mk arch))
  match all.find? (fun x => x.1 == name) with | some x => .ok x.2 | none => .error (.errorException "not found")

/-- Nested regex helper `c(mapping)`, line 736. -/
def collapseMapping (mapping : List (Str × Str)) : Str :=
  ['('] ++ joinStr (s% "|") (mapping.map fun kv => s% "(?<" ++ kv.1 ++ s% ">" ++ kv.2 ++ [')']) ++ [')']

def parseAbstract (convertString : Str → Str) (validate : Bool) (triplet : Str) : Jl Platform :=
  parsePlatform asciiLower validate (convertString triplet)

def tryparsePlatform (parse : Str → Jl Platform) (triplet : Str) : Option Platform :=
  match parse triplet with | .ok p => some p | .error _ => none

def thisOsName (windows apple : Bool) : Str := if windows then s% "windows" else if apple then s% "macos" else s% "other"

def parseDlAbstract (toString : Str → Str) (path os : Str) : Jl (Str × Option VersionNumber) :=
  parseDlNameVersion (toString path) (toString os)

structure LoadedModule where
  name : String
  members : List (String × Str)

def getCslMember (mods : List LoadedModule) (member : String) : Option Str :=
  match mods.find? (·.name == "CompilerSupportLibraries_jll") with
  | none => none
  | some m => (m.members.find? (·.1 == member)).map Prod.snd

def occursInStr (needle hay : Str) : Bool :=
  (List.range (hay.length + 1)).any fun i => ((hay.drop i).take needle.length == needle)

def getLibgfortranPath (mods : List LoadedModule) (dllist : List Str) : Option Str :=
  (getCslMember mods "libgfortran_path").orElse fun _ => dllist.find? (occursInStr (s% "libgfortran"))

def getLibstdcxxHandle (mods : List LoadedModule) (dllist : List Str) (openFn : Str → Option Nat) : Option Nat :=
  match getCslMember mods "libstdcxx" with
  | some _ => none
  | none => (dllist.find? (occursInStr (s% "libstdc++"))).bind openFn

def detectLibgfortranVersion (path : Option Str) (os : Str) : Jl (Option VersionNumber) := match path with
  | none => .error (.methodError "parse_dl_name_version(nothing)")
  | some p => (parseDlNameVersion p os).map Prod.snd

def openLibllvm {A : Type} (names : List Str) (openFn : Str → Option Nat) (closeFn : Nat → Unit)
    (f : Nat → A) : DJ A :=
  match names.findSome? openFn with
  | none => .error (.errorException "Unable to open libLLVM!")
  | some h =>
    let r := f h
    let _ := closeFn h
    .ok r

def detectCxxstringAbi (dllist : List Str) (openFn : Str → Option Nat) (hasSymbol : Nat → Str → Bool)
    (closeFn : Nat → Unit) (names : List Str) : DJ (Option Str) :=
  if !(dllist.any (occursInStr (s% "libstdc++"))) then .ok none
  else openLibllvm names openFn closeFn fun h =>
    if hasSymbol h (s% "_ZN4llvm3sys16getProcessTripleEv") then some (s% "cxx03")
    else if hasSymbol h (s% "_ZN4llvm3sys16getProcessTripleB5cxx11Ev") then some (s% "cxx11") else none

structure HostVersions where
  gfortran : Option Nat
  cxxabi : Option Str
  libstdcxx : Option Nat
  julia : VersionNumber

def hostTriplet (build ext : Str) (v : HostVersions) : Str :=
  let s := if occursInStr (s% "-libgfortran") build then build else
    match v.gfortran with | none => build | some n => build ++ s% "-libgfortran" ++ Nat.toDigits 10 n
  let s := if occursInStr (s% "-cxx") s then s else match v.cxxabi with | none => s | some a => s ++ ['-'] ++ a
  let s := if occursInStr (s% "-libstdcxx") s then s else
    match v.libstdcxx with | none => s | some n => s ++ s% "-libstdcxx" ++ Nat.toDigits 10 n
  let s := s ++ ext
  if occursInStr (s% "-julia_version+") s then s else s ++ s% "-julia_version+" ++
    Nat.toDigits 10 v.julia.major.val.toNat ++ ['.'] ++ Nat.toDigits 10 v.julia.minor.val.toNat ++
    ['.'] ++ Nat.toDigits 10 v.julia.patch.val.toNat

def hostPlatform0 (parse : Str → Jl Platform) (triplet : Str) : Jl Platform := do
  pure (hostPlatform (← parse triplet))

def matchStringLeft (parse : Str → Jl Platform) (usem : UserSem) (order : Platform → Platform → List Str)
    (a : Str) (b : Platform) : Jl Bool := do platformsMatch usem (order (← parse a) b) (← parse a) b

def matchStringRight (parse : Str → Jl Platform) (usem : UserSem) (order : Platform → Platform → List Str)
    (a : Platform) (b : Str) : Jl Bool := do platformsMatch usem (order a (← parse b)) a (← parse b)

def matchStrings (parse : Str → Jl Platform) (usem : UserSem) (order : Platform → Platform → List Str)
    (a b : Str) : Jl Bool := do
  let a ← parse a; let b ← parse b; platformsMatch usem (order a b) a b

def matchAbstractStrings (toString : Str → Str) (f : Str → Str → Jl Bool) (a b : Str) : Jl Bool :=
  f (toString a) (toString b)

def matchLoss (a b : Platform) : Nat :=
  let union := (keys a.tags ++ keys b.tags).eraseDups
  let inter := (keys a.tags).filter (keys b.tags).contains
  union.length - inter.length

end JuliaLean.DocsSyntaxCov.Binary
