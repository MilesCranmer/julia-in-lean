import JuliaLean.DocsSyntaxCov.Binary

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
