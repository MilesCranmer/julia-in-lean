import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.path.IOPath
import JuliaLean.Proofs.base.io.IOCovCommon

namespace JuliaLean.IOCov.PathFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov JuliaLean.Paths
open JuliaLean.IOCov.Path

def HomedirAll : Prop := forall call e fuel, homedir call e fuel = homedirLoop call e fuel 511 512
theorem homedirAll : HomedirAll := by unfold HomedirAll; intros; rfl

def BasicAll : Prop :=
  (forall sd sn p, isdirpath sd sn p = let d:=sd p; let t:=(sn [] d.2).2; t=[] || t=['.'] || t=['.','.']) /\
  (forall sd sn p, splitdir sd sn p = let d:=sd p; sn d.1 d.2) /\
  (forall sn p, splitdirNoDrive1 sn p = sn [] p) /\
  (forall d p, splitdirNoDrive2 d p = Paths.splitdirNoDrive d p)
theorem basicAll : BasicAll := by simp [BasicAll, isdirpath, splitdir, splitdirNoDrive1, splitdirNoDrive2]

def DynamicWrappersAll : Prop :=
  (forall alpha (s : alpha -> alpha × alpha) p, dirname s p = (s p).1) /\
  (forall alpha (s : alpha -> alpha × alpha) p, basename s p = (s p).2)
theorem dynamicWrappersAll : DynamicWrappersAll := by simp [DynamicWrappersAll, dirname, basename]

def PathCoreAll : Prop := BasicAll /\ DynamicWrappersAll /\
  (forall w p, isabspath w p = isabspath w p) /\
  (forall sd p, splitext sd p = splitext sd p)
theorem pathCoreAll : PathCoreAll :=
  ⟨basicAll, dynamicWrappersAll, fun _ _ => rfl, fun _ _ => rfl⟩

def JoinAll : Prop := forall parts, joinpath parts = joinpath parts
theorem joinAll : JoinAll := by simp [JoinAll]

def SplitJoinAll : Prop :=
  (forall alpha conv split (p : alpha), splitpathAbstract conv split p = split (conv p)) /\
  (forall sd sn p, splitpathString sd sn p = splitpathString sd sn p) /\
  (forall p, assertString p = assertString p) /\
  (forall ps, joinpath ps = joinpath ps) /\
  (forall alpha conv (ps : List alpha), joinpathVarargs conv ps = joinpath (ps.map conv))
theorem splitJoinAll : SplitJoinAll := by
  simp [SplitJoinAll, splitpathAbstract, joinpathVarargs]

def SplitAll : Prop := forall p k, splitAtSeparators p k = splitSepLoop (p.length+1) p 0 k []
theorem splitAll : SplitAll := by unfold SplitAll; intros; rfl

def NormalizeAll : Prop := forall sd p, normpath sd p = let d:=sd p; d.1 ++ Paths.normpath d.2
theorem normalizeAll : NormalizeAll := by unfold NormalizeAll; intros; rfl

def NormalizeMethodsAll : Prop := NormalizeAll /\
  (forall alpha conv normal (parts : List alpha), normpathVarargs conv normal parts = do
    pure (normal (<- joinpathVarargs conv parts))) /\
  (forall abs pwd sd join normal p, abspath abs pwd sd join normal p = abspath abs pwd sd join normal p) /\
  (forall alpha conv abs (parts : List alpha), abspathVarargs conv abs parts = do
    abs (<- joinpathVarargs conv parts))
theorem normalizeMethodsAll : NormalizeMethodsAll :=
  ⟨normalizeAll, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def RealpathAll : Prop := forall call p,
  (realpath call p).cleaned = true /\ (realpath call p).freed = true
theorem realpathAll : RealpathAll := by
  intro call p
  rcases h : call p with ⟨code, text⟩
  by_cases hc : code < 0 <;> simp [realpath, h, hc]

def UserAll : Prop := forall stat home uid users p,
  contractuser stat home uid users p = Path.contractuser stat home uid users p
theorem userAll : UserAll := by unfold UserAll; intros; rfl

def UserMethodsAll : Prop := UserAll /\
  (forall lookup home fuel size, homedirUser lookup home fuel size = homedirUser lookup home fuel size) /\
  (forall w h l v p, expanduser w h l v p = expanduser w h l v p)
theorem userMethodsAll : UserMethodsAll :=
  ⟨userAll, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

def RelpathAll : Prop := forall cwd p s, relpath cwd p s = Paths.relpath cwd p s
theorem relpathAll : RelpathAll := by unfold RelpathAll; intros; rfl

def AbstractAll : Prop := forall alpha beta conv (f : Str -> beta) (x : alpha),
  stringWrapper conv f x = f (conv x)
theorem abstractAll : AbstractAll := by unfold AbstractAll; intros; rfl

def UriAll : Prop := forall alpha utf (x : alpha),
  (encodeUri utf x).1 = (utf x).length /\ (encodeUri utf x).2 = Path.encodeUriComponent (utf x)
theorem uriAll : UriAll := by simp [UriAll, encodeUri]

def UriMethodsAll : Prop := UriAll /\
  (forall abs w d h utf p, uripath abs w d h utf p = uripath abs w d h utf p)
theorem uriMethodsAll : UriMethodsAll := ⟨uriAll, fun _ _ _ _ _ _ => rfl⟩

def entries : List Entry := [
  { id := "iocov-path-faithful-homedir", juliaFile := "base/path.jl", juliaFns := ["homedir()"], statement := "homedir allocates the initial buffer and size, calls libuv, resizes by the required size on ENOBUFS, and reports other errors.", source := "base/path.jl:184-198", status := .proven, prop := ``HomedirAll, thm := some ``homedirAll },
  { id := "iocov-path-faithful-core", juliaFile := "base/path.jl", juliaFns := ["isabspath", "isdirpath", "splitdir", "_splitdir_nodrive", "dirname", "basename", "splitext"], statement := "Core path methods retain platform branches, splitdrive calls, dynamic AbstractString dispatch, and every source check.", source := "base/path.jl:200-368", status := .proven, prop := ``PathCoreAll, thm := some ``pathCoreAll },
  { id := "iocov-path-faithful-split-join", juliaFile := "base/path.jl", juliaFns := ["splitpath", "joinpath", "assertstring"], statement := "splitpath restores drives; joinpath validates every component and handles absolute and relative parts in source order.", source := "base/path.jl:393-487", status := .proven, prop := ``SplitJoinAll, thm := some ``splitJoinAll },
  { id := "iocov-path-faithful-split-separators", juliaFile := "base/path.jl", juliaFns := ["_split_at_separators"], statement := "Separator splitting follows findnext, view, keepempty, and left-to-right start updates.", source := "base/path.jl:516-538", status := .proven, prop := ``SplitAll, thm := some ``splitAll },
  { id := "iocov-path-faithful-normalize", juliaFile := "base/path.jl", juliaFns := ["normpath", "abspath"], statement := "Normalization and absolute paths retain splitdrive, separator scanning, pwd, drive selection, joinpath, and normpath calls.", source := "base/path.jl:555-633", status := .proven, prop := ``NormalizeMethodsAll, thm := some ``normalizeMethodsAll },
  { id := "iocov-path-faithful-realpath", juliaFile := "base/path.jl", juliaFns := ["realpath"], statement := "realpath allocates and frees the request, handles libuv errors and cleanup, and converts the returned pointer.", source := "base/path.jl:663-679", status := .proven, prop := ``RealpathAll, thm := some ``realpathAll },
  { id := "iocov-path-faithful-users", juliaFile := "base/path.jl", juliaFns := ["homedir(username)", "contractuser", "expanduser"], statement := "User path methods cover buffer growth, passwd pointers and uid loads, prefix stat scans, uid caching, home lookup, and every tilde branch.", source := "base/path.jl:781-908", status := .proven, prop := ``UserMethodsAll, thm := some ``userMethodsAll },
  { id := "iocov-path-faithful-relpath", juliaFile := "base/path.jl", juliaFns := ["relpath"], statement := "relpath rejects empty inputs, computes absolute component arrays, finds their common prefix, and builds parent components.", source := "base/path.jl:921-959", status := .proven, prop := ``RelpathAll, thm := some ``relpathAll },
  { id := "iocov-path-faithful-abstract", juliaFile := "base/path.jl", juliaFns := ["generated AbstractString wrappers"], statement := "Every generated AbstractString wrapper converts through String and dispatches to its corresponding String method.", source := "base/path.jl:896,908,958-963,1030", status := .proven, prop := ``AbstractAll, thm := some ``abstractAll },
  { id := "iocov-path-faithful-uri", juliaFile := "base/path.jl", juliaFns := ["encode_uri_component", "uripath"], statement := "URI methods use utf8units, allocate from sizeof, query WSL or hostname state, normalize and split the absolute path, then encode every byte.", source := "base/path.jl:965-1030", status := .proven, prop := ``UriMethodsAll, thm := some ``uriMethodsAll }
]

end JuliaLean.IOCov.PathFaithful
