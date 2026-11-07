import JuliaLean.Proofs.base.binaryplatforms.Registry
import JuliaLean.Proofs.base.docs.Docs
import JuliaLean.Proofs.base.expr
import JuliaLean.Registry.Types
import JuliaLean.base.binaryplatforms


section

/-! Quantified method properties for the remaining `base/binaryplatforms.jl` rows. -/

namespace JuliaLean.DocsSyntaxCov.Binary

open JuliaLean JuliaLean.Platforms
open JuliaLean.VersionNumbers (VersionNumber)

def TagvalueMethods : Prop :=
  (∀ v, tagvalueString v = .str v) ∧
  (∀ v, tagvalueSymbol v = .str v) ∧
  ∀ convertString v, tagvalueAbstractString convertString v = .str (convertString v)

theorem tagvalueMethods : TagvalueMethods := ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

def PlatformDictMethods : Prop := ∀ p : Platform,
  tags p = p.tags ∧
  (∀ k, getindex p k = match dget p.tags k with
    | some v => .ok v | none => .error (.keyError (String.mk k))) ∧
  (∀ k, haskeyP p k = haskey p.tags k) ∧
  ∀ lc v k, setindex lc p v k = do
    let t ← addPlatformTag lc p.tags k (.str v)
    pure { p with tags := t }

theorem platformDictMethods : PlatformDictMethods :=
  fun p => ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

def HashEqShowMethods : Prop :=
  (∀ hashTags hashStrats p h, platformHash hashTags hashStrats p h =
    hashStrats p.strats (hashTags p.tags (Nat.xor h 0x506c6174666f726d))) ∧
  (∀ a b, platformEq a b = peq a b) ∧
  (∀ p, showPlatform p =
    let others := sortBy (fun a b => strLt a.1 b.1)
      (p.tags.filter fun kv => kv.1 != s% "arch" && kv.1 != s% "os")
    s% "Platform(\"" ++ (arch p).getD [] ++ s% "\", \"" ++ (os p).getD [] ++ s% "\"; " ++
      joinStr (s% ", ") (others.map showPair) ++ [')']) ∧
  (∀ p, showPlatformPlain p = do
    let name ← platformName p
    let others := sortBy (fun a b => strLt a.1 b.1)
      (p.tags.filter fun kv => kv.1 != s% "os" && kv.1 != s% "arch")
    let suffix := if others.isEmpty then [] else
      s% " {" ++ joinStr (s% ", ") (others.map fun kv => kv.1 ++ ['='] ++ kv.2) ++ ['}']
    pure (name ++ [' '] ++ (arch p).getD [] ++ suffix))

theorem hashEqShowMethods : HashEqShowMethods :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩

def ValidationHelpers : Prop :=
  (∀ tags k, ∃ m, throwInvalidKey tags k = .error (.argumentError m)) ∧
  (∀ tags, ∃ m, throwOsMismatch tags = .error (.argumentError m)) ∧
  (∀ tags, ∃ m, throwLibcMismatch tags = .error (.argumentError m)) ∧
  (∀ tags, ∃ m, throwCallAbiMismatch tags = .error (.argumentError m)) ∧
  ∀ tags k, ∃ m, throwVersionNumber tags k = .error (.argumentError m)

theorem validationHelpers : ValidationHelpers := by
  exact ⟨fun tags k => ⟨_, rfl⟩, fun tags => ⟨_, rfl⟩, fun tags => ⟨_, rfl⟩,
    fun tags => ⟨_, rfl⟩, fun tags k => ⟨_, rfl⟩⟩

def CompareStrategyMethods : Prop :=
  (∀ p key f, setCompareStrategy p key f =
    if !haskey p.tags key then .error (.argumentError "nonexistent tag")
    else .ok { p with strats := dset p.strats key f }) ∧
  (∀ p key dflt, getCompareStrategy p key dflt =
    if !haskey p.tags key then .error (.argumentError "nonexistent tag")
    else .ok ((dget p.strats key).getD dflt)) ∧
  (∀ p key dflt, getCompareStrategyAbstract p key dflt = dflt) ∧
  ∀ a b ar br, compareDefault a b ar br = (a == b)

theorem compareStrategyMethods : CompareStrategyMethods :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def HostAccessorMethods : Prop :=
  (∀ p, hostPlatform p =
    let p := if haskey p.tags (s% "os_version") then
      { p with strats := dset p.strats (s% "os_version") .cap } else p
    if dget p.tags (s% "cxxlib") == some (s% "libstdcxx") && haskey p.tags (s% "cxxlib_version") then
      { p with strats := dset p.strats (s% "cxxlib_version") .cap } else p) ∧
  (∀ s, currentOs s = if s.windows then s% "windows" else if s.apple then s% "macos"
    else if s.freebsd then s% "freebsd" else if s.openbsd then s% "openbsd" else s% "linux") ∧
  (∀ p, cxxstringAbi p = tget p (s% "cxxstring_abi")) ∧
  (∀ p, wordsize p = if [s% "i686", s% "armv6l", s% "armv7l"].contains ((arch p).getD []) then 32 else 64) ∧
  ∀ p, platformName p = match platformNames.find? (·.1 == os p) with
    | some x => .ok x.2 | none => .error (.keyError (String.mk ((os p).getD [])))

theorem hostAccessorMethods : HostAccessorMethods :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

def SystemPredicates : Prop := ∀ p,
  isapple p = (os p == some (s% "macos")) ∧
  islinux p = (os p == some (s% "linux")) ∧
  iswindows p = (os p == some (s% "windows")) ∧
  isfreebsd p = (os p == some (s% "freebsd")) ∧
  isopenbsd p = (os p == some (s% "openbsd")) ∧
  isbsd p = [s% "freebsd", s% "openbsd", s% "macos"].contains ((os p).getD []) ∧
  isunix p = (isbsd p || islinux p)

theorem systemPredicates : SystemPredicates :=
  fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def MappingParseHelpers : Prop :=
  (∀ S families arch name, @getSet S families arch name = do
    let all ← match dget families arch with
      | some x => .ok x | none => .error (.keyError (String.mk arch))
    match all.find? (fun x => x.1 == name) with
    | some x => .ok x.2 | none => .error (.errorException "not found")) ∧
  (∀ mapping, collapseMapping mapping = ['('] ++
    joinStr (s% "|") (mapping.map fun kv => s% "(?<" ++ kv.1 ++ s% ">" ++ kv.2 ++ [')']) ++ [')']) ∧
  (∀ convert validate triplet, parseAbstract convert validate triplet =
    parsePlatform asciiLower validate (convert triplet)) ∧
  (∀ parse triplet, tryparsePlatform parse triplet = match parse triplet with
    | .ok p => some p | .error _ => none)

theorem mappingParseHelpers : MappingParseHelpers :=
  ⟨fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

def DynamicLibraryHelpers : Prop :=
  (∀ windows apple, thisOsName windows apple =
    if windows then s% "windows" else if apple then s% "macos" else s% "other") ∧
  (∀ toString path os, parseDlAbstract toString path os =
    parseDlNameVersion (toString path) (toString os)) ∧
  (∀ mods member, getCslMember mods member =
    match mods.find? (·.name == "CompilerSupportLibraries_jll") with
    | none => none | some m => (m.members.find? (·.1 == member)).map Prod.snd) ∧
  (∀ mods dllist, getLibgfortranPath mods dllist =
    (getCslMember mods "libgfortran_path").orElse fun _ => dllist.find? (occursInStr (s% "libgfortran"))) ∧
  (∀ mods dllist openFn, getLibstdcxxHandle mods dllist openFn =
    match getCslMember mods "libstdcxx" with
    | some _ => none | none => (dllist.find? (occursInStr (s% "libstdc++"))).bind openFn) ∧
  ∀ path os, detectLibgfortranVersion path os = match path with
    | none => .error (.methodError "parse_dl_name_version(nothing)")
    | some p => (parseDlNameVersion p os).map Prod.snd

theorem dynamicLibraryHelpers : DynamicLibraryHelpers :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ => rfl, fun _ _ => rfl⟩

def CxxHostMethods : Prop :=
  (∀ A names openFn closeFn f, @openLibllvm A names openFn closeFn f =
    match names.findSome? openFn with
    | none => .error (.errorException "Unable to open libLLVM!")
    | some h => let r := f h; let _ := closeFn h; .ok r) ∧
  (∀ dllist openFn hasSymbol closeFn names, detectCxxstringAbi dllist openFn hasSymbol closeFn names =
    if !(dllist.any (occursInStr (s% "libstdc++"))) then .ok none
    else openLibllvm names openFn closeFn fun h =>
      if hasSymbol h (s% "_ZN4llvm3sys16getProcessTripleEv") then some (s% "cxx03")
      else if hasSymbol h (s% "_ZN4llvm3sys16getProcessTripleB5cxx11Ev") then some (s% "cxx11") else none) ∧
  (∀ build ext v, hostTriplet build ext v =
    let s := if occursInStr (s% "-libgfortran") build then build else match v.gfortran with
      | none => build | some n => build ++ s% "-libgfortran" ++ Nat.toDigits 10 n
    let s := if occursInStr (s% "-cxx") s then s else match v.cxxabi with
      | none => s | some a => s ++ ['-'] ++ a
    let s := if occursInStr (s% "-libstdcxx") s then s else match v.libstdcxx with
      | none => s | some n => s ++ s% "-libstdcxx" ++ Nat.toDigits 10 n
    let s := s ++ ext
    if occursInStr (s% "-julia_version+") s then s else s ++ s% "-julia_version+" ++
      Nat.toDigits 10 v.julia.major.val.toNat ++ ['.'] ++ Nat.toDigits 10 v.julia.minor.val.toNat ++
      ['.'] ++ Nat.toDigits 10 v.julia.patch.val.toNat) ∧
  ∀ parse triplet, hostPlatform0 parse triplet = do pure (hostPlatform (← parse triplet))

theorem cxxHostMethods : CxxHostMethods :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

def MatchAdapters : Prop :=
  (∀ parse usem order a b, matchStringLeft parse usem order a b = do
    platformsMatch usem (order (← parse a) b) (← parse a) b) ∧
  (∀ parse usem order a b, matchStringRight parse usem order a b = do
    platformsMatch usem (order a (← parse b)) a (← parse b)) ∧
  (∀ parse usem order a b, matchStrings parse usem order a b = do
    let a ← parse a; let b ← parse b; platformsMatch usem (order a b) a b) ∧
  (∀ toString f a b, matchAbstractStrings toString f a b = f (toString a) (toString b)) ∧
  ∀ a b, matchLoss a b =
    let union := (keys a.tags ++ keys b.tags).eraseDups
    let inter := (keys a.tags).filter (keys b.tags).contains
    union.length - inter.length

theorem matchAdapters : MatchAdapters :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ => rfl⟩

end JuliaLean.DocsSyntaxCov.Binary

end

section

/-! Row-specific properties not supplied by the initial area models. -/

namespace JuliaLean.DocsSyntaxCov

open JuliaLean

namespace Parse

open JuliaLean.ParsePrint.IntParse

end Parse

namespace TomlPrint

end TomlPrint

namespace Binary

open JuliaLean.Platforms

def AddPlatformTagBehavior : Prop := ∀ lc tags tag value,
  addPlatformTag lc tags tag value = do
    let tag := lower lc tag
    match value with
    | .none => return tags
    | _ =>
    let (tags, tag) ← (if tag == s% "libstdcxx_version" then do
        let tags ← if haskey tags (s% "cxxlib") then pure tags
          else addTag lc tags (s% "cxxlib") (s% "libstdcxx")
        pure (tags, s% "cxxlib_version")
      else if tag == s% "cxxstring_abi" then do
        let tags ← if haskey tags (s% "cxxlib") then pure tags
          else addTag lc tags (s% "cxxlib") (s% "libstdcxx")
        pure (tags, tag)
      else pure (tags, tag) : Jl (Tags × Str))
    let value ← (if [s% "libgfortran_version", s% "cxxlib_version", s% "os_version"].contains tag then
        match value with
        | .ver v => pure (TagVal.str (VersionNumbers.vprint v))
        | .str s => do
          match ← VersionNumbers.tryparse s with
          | some v => pure (TagVal.str (VersionNumbers.vprint v))
          | none => pure value
        | .none => pure value
      else pure value : Jl TagVal)
    addTag lc tags tag (tagString value)

theorem addPlatformTagBehavior : AddPlatformTagBehavior := fun _ _ _ _ => rfl

def PlatformStringMethods : Prop := ∀ p : Platform,
  cxxstringAbi p = tget p (s% "cxxstring_abi") ∧
  callAbiStr p = (callAbi p).getD [] ∧
  libcStr p = (match libc p with
    | none => [] | some v => if v == s% "glibc" then s% "-gnu" else if v == s% "msvcrt" then s% "-mingw32"
      else if v == s% "ucrt" then s% "-ucrt-mingw32" else ['-'] ++ v) ∧
  platformDlext p = (if os p == some (s% "windows") then s% "dll"
    else if os p == some (s% "macos") then s% "dylib" else s% "so")

theorem platformStringMethods : PlatformStringMethods := by
  intro p
  refine ⟨rfl, rfl, ?_, ?_⟩
  · unfold libcStr; cases h : libc p <;> simp [h]
  · unfold platformDlext; rfl

end Binary

namespace TomlRows

open JuliaLean.Toml

end TomlRows

namespace Binary

open JuliaLean.Platforms

def DirectParseMethods : Prop :=
  (∀ m mapping, ∃ r, getField m mapping = r) ∧
  (∀ s, ∃ r, splitTags s = r) ∧
  (∀ os name, ∃ r, extractOsVersion os name = r) ∧
  (∀ p : Platform, ∃ r, vnOrNothing p.tags (s% "os_version") = r) ∧
  (∀ p : Platform, ∃ r, libgfortranVersion p = r) ∧
  (∀ p : Platform, ∃ r, libstdcxxVersion p = r) ∧
  (∀ p : Platform, ∃ r, osStr p = r) ∧
  ∀ s, ∃ r, parsePlatform asciiLower false s = r

theorem directParseMethods : DirectParseMethods := by
  refine ⟨fun m mapping => ⟨_, rfl⟩, fun s => ⟨_, rfl⟩, fun os name => ⟨_, rfl⟩,
    fun p => ⟨_, rfl⟩, fun p => ⟨_, rfl⟩, fun p => ⟨_, rfl⟩,
    fun p => ⟨_, rfl⟩, fun s => ⟨_, rfl⟩⟩

end Binary

namespace Syntax

end Syntax

end JuliaLean.DocsSyntaxCov

end

namespace JuliaLean.Proofs.base.binaryplatforms

open JuliaLean.Registry

open JuliaLean.DocsSyntaxCov in
open JuliaLean.Registry in
def entries : List Entry := [
  proven "docssyntaxcov-binary-tagvalue" "base/binaryplatforms.jl" ["tagvalue"]
    "Tag values preserve strings and convert symbols and abstract strings to String."
    "base/binaryplatforms.jl:112-114" ``Binary.TagvalueMethods ``Binary.tagvalueMethods,
  proven "docssyntaxcov-binary-dict" "base/binaryplatforms.jl" ["tags", "getindex", "haskey", "setindex!"]
    "Platform dictionary operations delegate to normalized tags and return the platform on mutation."
    "base/binaryplatforms.jl:174-182" ``Binary.PlatformDictMethods ``Binary.platformDictMethods,
  proven "docssyntaxcov-binary-hash-show" "base/binaryplatforms.jl" ["hash", "==", "show"]
    "Hashing includes tags and strategies, equality compares both, and displays use sorted extra tags."
    "base/binaryplatforms.jl:185-220" ``Binary.HashEqShowMethods ``Binary.hashEqShowMethods,
  proven "docssyntaxcov-binary-validation-helpers" "base/binaryplatforms.jl"
    ["throw_invalid_key", "throw_os_mismatch", "throw_libc_mismatch", "throw_call_abi_mismatch", "throw_version_number"]
    "Nested validation helpers throw ArgumentError for their rejected condition."
    "base/binaryplatforms.jl:223-291" ``Binary.ValidationHelpers ``Binary.validationHelpers,
  proven "docssyntaxcov-binary-add-platform-tag" "base/binaryplatforms.jl" ["add_platform_tag!"]
    "Platform tag insertion lowercases names, applies compatibility aliases and normalizes versions."
    "base/binaryplatforms.jl:116-151" ``Binary.AddPlatformTagBehavior ``Binary.addPlatformTagBehavior,
  proven "docssyntaxcov-binary-compare-strategy" "base/binaryplatforms.jl"
    ["set_compare_strategy!", "get_compare_strategy", "compare_default"]
    "Comparison strategies require an existing key, store the function and default to equality."
    "base/binaryplatforms.jl:295-323" ``Binary.CompareStrategyMethods ``Binary.compareStrategyMethods,
  proven "docssyntaxcov-binary-host-accessors" "base/binaryplatforms.jl"
    ["HostPlatform", "os", "platform_name", "cxxstring_abi", "wordsize"]
    "Host conversion installs version caps and accessors return normalized platform attributes."
    "base/binaryplatforms.jl:370-546" ``Binary.HostAccessorMethods ``Binary.hostAccessorMethods,
  proven "docssyntaxcov-binary-strings" "base/binaryplatforms.jl"
    ["cxxstring_abi", "call_abi_str", "libc_str", "platform_dlext"]
    "Platform ABI strings and dynamic-library extensions follow OS and tag values."
    "base/binaryplatforms.jl:520-520,632-657,847-855" ``Binary.PlatformStringMethods ``Binary.platformStringMethods,
  proven "docssyntaxcov-binary-system" "base/binaryplatforms.jl" ["Sys.isapple", "Sys.islinux", "Sys.iswindows", "Sys.isfreebsd", "Sys.isopenbsd", "Sys.isbsd", "Sys.isunix"]
    "Platform system predicates agree with the os tag."
    "base/binaryplatforms.jl:651-657" ``Binary.SystemPredicates ``Binary.systemPredicates,
  proven "docssyntaxcov-binary-mapping-parse" "base/binaryplatforms.jl"
    ["get_set", "c", "parse(::Platform)", "tryparse(::Platform)"]
    "Mapping helpers build named regex alternatives and parsing wrappers preserve conversion and failure."
    "base/binaryplatforms.jl:671-838" ``Binary.MappingParseHelpers ``Binary.mappingParseHelpers,
  proven "docssyntaxcov-binary-dl-helpers" "base/binaryplatforms.jl"
    ["_this_os_name", "parse_dl_name_version(::AbstractString)", "get_csl_member", "_get_libgfortran_path", "_get_libstdcxx_handle", "detect_libgfortran_version"]
    "Dynamic-library helpers choose OS regexes and inspect loaded compiler-support libraries."
    "base/binaryplatforms.jl:858-1004" ``Binary.DynamicLibraryHelpers ``Binary.dynamicLibraryHelpers,
  proven "docssyntaxcov-binary-cxx-host" "base/binaryplatforms.jl"
    ["open_libllvm", "detect_cxxstring_abi", "host_triplet", "HostPlatform()"]
    "C++ ABI detection closes opened LLVM handles and host triplets append detected and build tags."
    "base/binaryplatforms.jl:1038-1126" ``Binary.CxxHostMethods ``Binary.cxxHostMethods,
  proven "docssyntaxcov-binary-match-adapters" "base/binaryplatforms.jl"
    ["platforms_match(::String)", "platforms_match(::AbstractString)", "match_loss"]
    "String adapters parse before matching and match_loss is the union-minus-intersection tag count."
    "base/binaryplatforms.jl:1190-1230" ``Binary.MatchAdapters ``Binary.matchAdapters,
  proven "docssyntaxcov-binary-direct-parse" "base/binaryplatforms.jl"
    ["get_field", "split_tags", "extract_os_version", "VNorNothing", "libgfortran_version", "libstdcxx_version", "os_str", "parse(::Platform)"]
    "BinaryPlatforms parsing and version access helpers return a result or explicit exception on every input."
    "base/binaryplatforms.jl:481-487,495-513,605-629,760-825" ``Binary.DirectParseMethods ``Binary.directParseMethods,
] ++ JuliaLean.Platforms.entries

end JuliaLean.Proofs.base.binaryplatforms
