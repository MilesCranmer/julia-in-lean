import JuliaLean.IOCov.Common
import JuliaLean.Paths.Model

set_option linter.unusedSimpArgs false

/-!
Models of the Unix branch of `base/path.jl` at master `bbfa0ce4150` not already
covered by `JuliaLean.Paths`, reusing its string model (`Paths.Str`, a list of
characters) and its mirrors of `isabspath`, `_splitdir_nodrive`, `joinpath`,
`_split_at_separators`, `normpath`, `abspath`, `relpath` and `expanduser`.
File-system and libuv results (`pwd`, `stat`, `uv_os_homedir`, `getpwnam_r`,
`uv_fs_realpath`) are arguments.
-/

namespace JuliaLean.IOCov.Path

open JuliaLean JuliaLean.IOCov JuliaLean.Paths

/-! ## Separators and drives, lines 26-31, 371 -/

/-- `isseparator(c::UInt8) = c === UInt8('/')`, `base/path.jl:28`. -/
def isSepByte (c : UInt8) : Bool := c == 47
/-- `splitdrive(path::String) = ("", path)`, `base/path.jl:30`. -/
def splitdrive (path : Str) : Str × Str := ([], path)
/-- `pathsep() = path_separator`, `base/path.jl:371`. -/
def pathsep : Str := ['/']

def SeparatorsCorrect : Prop :=
  (∀ c : Char, isSep c = true ↔ c = '/') ∧
  (∀ c : UInt8, isSepByte c = true ↔ c = 47) ∧
  (∀ p, splitdrive p = ([], p) ∧ (splitdrive p).1 ++ (splitdrive p).2 = p) ∧
  pathsep = ['/'] ∧
  (∀ p : Str, Paths.isabspath p = true ↔ p.head? = some '/')

theorem separatorsCorrect : SeparatorsCorrect := by
  refine ⟨fun c => by unfold isSep; exact beq_iff_eq, fun c => by unfold isSepByte; exact beq_iff_eq,
    fun p => ⟨rfl, rfl⟩, rfl, ?_⟩
  intro p
  cases p with
  | nil => simp [Paths.isabspath]
  | cons c cs => simp only [Paths.isabspath, List.head?_cons, Option.some.injEq]; unfold isSep; exact beq_iff_eq

/-! ## `homedir()`, lines 184-198 -/

/-- `homedir()`, `base/path.jl:184-198`: `uv_os_homedir` fills a buffer of `AVG_PATH`
bytes; on `UV_ENOBUFS` the buffer is resized to the size it reports and the call is
retried. `call size = (rc, needed, text)`; `fuel` bounds the retries. -/
def homedir (call : Nat → Int × Nat × Str) (enobufs : Int) : Nat → Nat → R Str
  | 0, _ => .error (.errorException "out of fuel")
  | fuel + 1, size =>
    let (rc, needed, text) := call size
    if rc == 0 then .ok text
    else if rc == enobufs then homedir call enobufs fuel needed
    else .error (.uvError "homedir()")

def HomedirCorrect : Prop :=
  (∀ call e fuel size, (call size).1 = 0 → homedir call e (fuel + 1) size = .ok (call size).2.2) ∧
  (∀ call e fuel size, (call size).1 ≠ 0 → (call size).1 ≠ e →
      homedir call e (fuel + 1) size = .error (.uvError "homedir()")) ∧
  (∀ call e fuel size, (call size).1 = e → e ≠ 0 →
      homedir call e (fuel + 1) size = homedir call e fuel (call size).2.1)

theorem homedirCorrect : HomedirCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro call e fuel size h
    simp only [homedir]; rcases hc : call size with ⟨rc, n, t⟩; rw [hc] at h; simp at h; simp [h]
  · intro call e fuel size h1 h2
    simp only [homedir]; rcases hc : call size with ⟨rc, n, t⟩; rw [hc] at h1 h2; simp at h1 h2
    simp [h1, h2]
  · intro call e fuel size h1 h2
    simp only [homedir]; rcases hc : call size with ⟨rc, n, t⟩; rw [hc] at h1; simp at h1
    subst h1; simp [h2]

/-! ## Wrappers, lines 279, 393, 487, 595, 633, 896-962 -/

/-- `_splitdir_nodrive(path::String) = _splitdir_nodrive("", path)`, `base/path.jl:279`. -/
def splitdirNoDrive1 (path : Str) : Str × Str := Paths.splitdirNoDrive [] path
/-- `splitpath(p::AbstractString) = splitpath(String(p))`, `base/path.jl:393`. -/
def splitpathAbs (p : Str) : List Str := Paths.splitpath p
/-- `joinpath(paths::AbstractString...) = joinpath(paths)`, `base/path.jl:487`. -/
def joinpathVar (paths : List Str) : Jl Str := Paths.joinpath paths
/-- `normpath(a, b...) = normpath(joinpath(a, b...))`, `base/path.jl:595`. -/
def normpathVar (a : Str) (bs : List Str) : Jl Str := do
  let j ← Paths.joinpath (a :: bs)
  pure (Paths.normpath j)
/-- `abspath(a, b...) = abspath(joinpath(a, b...))`, `base/path.jl:633`. -/
def abspathVar (cwd a : Str) (bs : List Str) : Jl Str := do
  let j ← Paths.joinpath (a :: bs)
  pure (Paths.abspath cwd j)
/-- `relpath(path::AbstractString, startpath::AbstractString)`, `base/path.jl:958-959`. -/
def relpathAbs (cwd path startpath : Str) : Jl Str := Paths.relpath cwd path startpath
/-- The `for f in (:isdirpath, :splitdir, :splitdrive, :splitext, :normpath, :abspath,
:isabspath)` loop, `base/path.jl:961-963`: each `f(path::AbstractString)` converts to
`String` and calls the `String` method; here the `String` results paired up. -/
def stringWrappers (cwd p : Str) : Bool × (Str × Str) × (Str × Str) × (Str × Str) × Str × Str × Bool :=
  (Paths.isdirpath p, Paths.splitdir p, splitdrive p, Paths.splitext p, Paths.normpath p,
    Paths.abspath cwd p, Paths.isabspath p)

def WrappersCorrect : Prop :=
  (∀ p, splitdirNoDrive1 p = Paths.splitdir p) ∧
  (∀ p, splitpathAbs p = Paths.splitpath p) ∧
  (∀ ps, joinpathVar ps = Paths.joinpath ps) ∧
  (∀ a b : Str, ¬ Paths.isabspath b → a ≠ [] → a.getLast? ≠ some '/' →
      normpathVar a [b] = .ok (Paths.normpath (a ++ '/' :: b))) ∧
  (∀ a b : Str, Paths.isabspath b → normpathVar a [b] = .ok (Paths.normpath b)) ∧
  (∀ cwd a : Str, abspathVar cwd a [] = .ok (Paths.abspath cwd a)) ∧
  (∀ cwd a b : Str, Paths.isabspath b → abspathVar cwd a [b] = .ok (Paths.abspath cwd b)) ∧
  (∀ cwd p s, relpathAbs cwd p s = Paths.relpath cwd p s) ∧
  (∀ cwd p, (stringWrappers cwd p).2.2.1 = ([], p) ∧ (stringWrappers cwd p).1 = Paths.isdirpath p)

theorem wrappersCorrect : WrappersCorrect := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, fun _ _ => rfl, ?_, fun _ _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩
  · intro a b hb ha hl
    cases a with
    | nil => exact absurd rfl ha
    | cons x xs => simp [normpathVar, Paths.joinpath, Paths.joinStep, hb, hl, bind, Except.bind, pure, Except.pure]
  · intro a b hb
    simp [normpathVar, Paths.joinpath, Paths.joinStep, hb, bind, Except.bind, pure, Except.pure]
  · intro cwd a b hb
    simp [abspathVar, Paths.joinpath, Paths.joinStep, hb, bind, Except.bind, pure, Except.pure]

/-! ## `_split_at_separators`, lines 516-538 -/

theorem splitRuns_ne_nil (p : Str) : Paths.splitRuns p ≠ [] := by
  cases p with
  | nil => simp [Paths.splitRuns]
  | cons c cs =>
    simp only [Paths.splitRuns]
    split
    · simp
    · split
      · split <;> simp
      · simp

theorem splitRuns_noSep (p : Str) : ∀ w ∈ Paths.splitRuns p, '/' ∉ w := by
  induction p with
  | nil => simp [Paths.splitRuns]
  | cons c cs ih =>
    simp only [Paths.splitRuns]
    cases h : Paths.splitRuns cs with
    | nil => exact absurd h (splitRuns_ne_nil cs)
    | cons w ws =>
      rw [h] at ih
      intro v hv
      by_cases hs : isSep c = true
      · simp only [hs, if_true] at hv
        split at hv
        · exact ih v hv
        · simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · simp
          · exact ih v (by simpa using hv)
      · simp only [hs, Bool.false_eq_true, if_false, List.mem_cons] at hv
        rcases hv with rfl | hv
        · intro hm
          simp only [List.mem_cons] at hm
          rcases hm with hc | hm
          · subst hc; simp [isSep] at hs
          · exact ih w (by simp) hm
        · exact ih v (by simp [hv])

def SplitAtSeparatorsCorrect : Prop :=
  ∀ p : Str, (∀ w ∈ Paths.splitAtSeps p true, '/' ∉ w) ∧
    (∀ w ∈ Paths.splitAtSeps p false, w ≠ [] ∧ '/' ∉ w)

theorem splitAtSeparatorsCorrect : SplitAtSeparatorsCorrect := by
  intro p
  refine ⟨by simpa [Paths.splitAtSeps] using splitRuns_noSep p, ?_⟩
  intro w hw
  simp [Paths.splitAtSeps, List.mem_filter] at hw
  exact ⟨hw.2, splitRuns_noSep p w hw.1⟩

/-! ## `realpath`, lines 663-679 -/

/-- `realpath(path)`, `base/path.jl:663-679`: `uv_fs_realpath` result code and text;
a negative code throws `IOError`. -/
def realpath (call : Str → Int × Str) (path : Str) : R Str :=
  let (ret, text) := call path
  if ret < 0 then .error (.uvError "realpath") else .ok text

def RealpathCorrect : Prop :=
  ∀ call path, realpath call path =
    if (call path).1 < 0 then .error (.uvError "realpath") else .ok (call path).2

theorem realpathCorrect : RealpathCorrect := by
  intro call path; unfold realpath; rcases call path with ⟨r, t⟩; rfl

/-! ## `homedir(username)`, lines 781-808 -/

/-- `homedir(username::AbstractString)` on Unix, `base/path.jl:781-808`: `getpwnam_r`
with a string buffer that doubles on `ERANGE` (34) up to 65536 bytes; on success the
uid is looked up again with `getpwuid(uid, false)` and its `homedir` returned.
`getpwnam buflen = (ret, found uid)`. -/
def homedirUser (getpwnam : Nat → Int × Option Nat) (getpwuidHome : Nat → Option Str) :
    Nat → Nat → Option Str
  | 0, _ => none
  | fuel + 1, buflen =>
    if buflen ≤ 65536 then
      let (ret, res) := getpwnam buflen
      if ret == 34 then homedirUser getpwnam getpwuidHome fuel (buflen * 2)
      else match ret, res with
        | 0, some uid => getpwuidHome uid
        | _, _ => none
    else none

def HomedirUserCorrect : Prop :=
  (∀ g h fuel b, 65536 < b → homedirUser g h fuel b = none) ∧
  (∀ g h fuel b uid, b ≤ 65536 → g b = (0, some uid) → homedirUser g h (fuel + 1) b = h uid) ∧
  (∀ g h fuel b, b ≤ 65536 → (g b).2 = none → (g b).1 ≠ 34 → homedirUser g h (fuel + 1) b = none) ∧
  (∀ g h fuel b, b ≤ 65536 → (g b).1 = 34 → homedirUser g h (fuel + 1) b = homedirUser g h fuel (2 * b))

theorem homedirUser_big (g : Nat → Int × Option Nat) (h : Nat → Option Str) :
    ∀ fuel b, 65536 < b → homedirUser g h fuel b = none := by
  intro fuel b hb; cases fuel <;> simp [homedirUser, show ¬ b ≤ 65536 by omega]

theorem homedirUserCorrect : HomedirUserCorrect := by
  refine ⟨homedirUser_big, ?_, ?_, ?_⟩
  · intro g h fuel b uid hb hg; simp [homedirUser, hb, hg]
  · intro g h fuel b hb h1 h2
    simp only [homedirUser, hb, if_true]
    rcases hc : g b with ⟨ret, res⟩; rw [hc] at h1 h2; simp at h1 h2; subst h1
    simp [h2]
  · intro g h fuel b hb h1
    simp only [homedirUser, hb, if_true]
    rcases hc : g b with ⟨ret, res⟩; rw [hc] at h1; simp at h1; subst h1; simp [Nat.mul_comm]

/-! ## `contractuser`, lines 809-850 -/

/-- File identity by `stat`: `none` when the path does not exist (`!ispath(st)`). -/
structure StatInfo where
  ino : Nat
  uid : Nat
  deriving DecidableEq

/-- Prefixes of `path` ending just before each `'/'` after the first one (the order the
`findnext(path_separator_re, ...)` loop visits them), each with the rest from that
separator on. -/
def sepPrefixes (path : Str) : List (Str × Str) :=
  let idxs := (List.range path.length).filter (fun i => path[i]? = some '/')
  (idxs.drop 1).map (fun i => (path.take i, path.drop i))

/-- The prefix loop of `contractuser`, `base/path.jl:820-848`, with the uid cache
(`cacheUid`, and `cache` = `(cache_uname, inode of cache_home_st)`); `uidHome uid` is
`(username, homedir(username))` when `getpwuid(uid, false)` finds a user with a nonempty
name whose `homedir` is not `nothing`. -/
def contractGo (stat : Str → Option StatInfo) (hino : Nat) (uidHome : Nat → Option (Str × Str))
    (path : Str) : Nat → Option (Str × Option Nat) → List (Str × Str) → Str
  | _, _, [] => path
  | cacheUid, cache, (pre, rest) :: more =>
    match stat pre with
    | none => path
    | some st =>
      if st.ino == hino then '~' :: rest else
      let cu := if st.uid != cacheUid then st.uid else cacheUid
      let c := if st.uid != cacheUid then
          (uidHome st.uid).map (fun uh => (uh.1, (stat uh.2).map (·.ino))) else cache
      match c with
      | some (uname, some hi) =>
        if hi == st.ino then '~' :: uname ++ rest else contractGo stat hino uidHome path cu c more
      | _ => contractGo stat hino uidHome path cu c more

/-- `contractuser(path)` on Unix, `base/path.jl:809-850`: `stat p` gives the file identity
(`none` when `!ispath`), `home` is `homedir()`, `myUid` is `getuid()`. -/
def contractuser (stat : Str → Option StatInfo) (home : Str) (myUid : Nat)
    (uidHome : Nat → Option (Str × Str)) (path : Str) : Str :=
  match stat home with
  | none => path
  | some hst =>
    if (stat path).map (·.ino) == some hst.ino then ['~']
    else contractGo stat hst.ino uidHome path myUid none (sepPrefixes path)

/-- Documented (`contractuser` docstring, lines 898-906): the result is `path` unchanged,
`"~"`, or `"~"`/`"~user"` followed by a suffix of `path` that starts at a separator. -/
def ContractuserShape : Prop :=
  ∀ stat home myUid uidHome (path : Str),
    let r := contractuser stat home myUid uidHome path
    r = path ∨ r = ['~'] ∨ ∃ rest, rest <:+ path ∧ rest.head? = some '/' ∧
      ((r = '~' :: rest) ∨ ∃ uname, r = '~' :: uname ++ rest)

theorem sepPrefixes_rest (path : Str) : ∀ p ∈ sepPrefixes path, p.2 <:+ path ∧ p.2.head? = some '/' := by
  intro p hp
  simp only [sepPrefixes, List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hmem := List.mem_of_mem_drop hi
  simp only [List.mem_filter, decide_eq_true_eq] at hmem
  refine ⟨⟨path.take i, List.take_append_drop i path⟩, ?_⟩
  rw [List.head?_drop]; exact hmem.2

theorem contractGo_shape (stat : Str → Option StatInfo) (hino : Nat) (uidHome : Nat → Option (Str × Str))
    (path : Str) : ∀ (l : List (Str × Str)) cu c, (∀ p ∈ l, p.2 <:+ path ∧ p.2.head? = some '/') →
    let r := contractGo stat hino uidHome path cu c l
    r = path ∨ r = ['~'] ∨ ∃ rest, rest <:+ path ∧ rest.head? = some '/' ∧
      ((r = '~' :: rest) ∨ ∃ uname, r = '~' :: uname ++ rest) := by
  intro l
  induction l with
  | nil => intro cu c _; left; rfl
  | cons p more ih =>
    intro cu c hl
    obtain ⟨pre, rest⟩ := p
    have hp := hl (pre, rest) (by simp)
    have ih' := fun cu c => ih cu c (fun q hq => hl q (by simp [hq]))
    simp only [contractGo]
    split
    · left; rfl
    · rename_i st _
      by_cases hi : (st.ino == hino) = true
      · simp only [hi, if_true]; right; right; exact ⟨rest, hp.1, hp.2, Or.inl rfl⟩
      · simp only [hi, Bool.false_eq_true, if_false]
        split
        · split
          · right; right; exact ⟨rest, hp.1, hp.2, Or.inr ⟨_, rfl⟩⟩
          · exact ih' _ _
        · exact ih' _ _

theorem contractuserShape : ContractuserShape := by
  intro stat home myUid uidHome path
  simp only [contractuser]
  split
  · left; rfl
  · split
    · right; left; rfl
    · exact contractGo_shape stat _ uidHome path _ _ _ (sepPrefixes_rest path)

/-- `expanduser(path::AbstractString) = expanduser(String(path))`, `contractuser(path::
AbstractString) = contractuser(String(path))`, `base/path.jl:896, 908`. -/
def expanduserAbs (home : Str) (lookup : Str → Option Str) (userChar : Char → Bool) (p : Str) : Str :=
  Paths.expanduser home lookup userChar p
def contractuserAbs (stat : Str → Option StatInfo) (home : Str) (myUid : Nat)
    (uidHome : Nat → Option (Str × Str)) (p : Str) : Str := contractuser stat home myUid uidHome p

def ContractExpandWrappers : Prop :=
  (∀ h l u p, expanduserAbs h l u p = Paths.expanduser h l u p) ∧
  (∀ s h m uh p, contractuserAbs s h m uh p = contractuser s h m uh p) ∧
  -- the current user's home directory itself contracts to "~"
  (∀ stat (home : Str) m uh st, stat home = some st → contractuser stat home m uh home = ['~'])

theorem contractExpandWrappers : ContractExpandWrappers := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_⟩
  intro stat home m uh st h
  simp [contractuser, h]

/-! ## `encode_uri_component` and `uripath`, lines 965-1030 -/

/-- Uppercase hexadecimal digit. -/
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

/-- `uppercase(string(cu, base = 16))` for a byte: no leading zeros. -/
def hexNoPad (b : UInt8) : List Char :=
  if b.toNat < 16 then [hexDigit b.toNat] else [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def unreservedByte (cu : UInt8) : Bool :=
  (65 ≤ cu && cu ≤ 90) || (97 ≤ cu && cu ≤ 122) || (48 ≤ cu && cu ≤ 57) ||
    cu == 45 || cu == 95 || cu == 46 || cu == 126 || cu == 47

/-- `encode_uri_component(s)`, `base/path.jl:965-982`, over the UTF-8 bytes of `s`. -/
def encodeUriComponent (s : List UInt8) : List Char :=
  (s.map fun cu => if unreservedByte cu then [Char.ofNat cu.toNat] else '%' :: hexNoPad cu).flatten

/-- RFC 3986 section 2.1: every encoded byte is `%` and two hex digits. -/
def EncodeUriTwoDigits : Prop :=
  ∀ b : UInt8, unreservedByte b = false →
    encodeUriComponent [b] = ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

theorem encodeUriTwoDigits_refuted : ¬ EncodeUriTwoDigits := by
  intro h
  have := h 9 (by decide)
  revert this; decide

def EncodeUriBytes : Prop :=
  (∀ b : UInt8, unreservedByte b = true → encodeUriComponent [b] = [Char.ofNat b.toNat]) ∧
  (∀ b : UInt8, unreservedByte b = false → 16 ≤ b.toNat →
      encodeUriComponent [b] = ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]) ∧
  (∀ s t, encodeUriComponent (s ++ t) = encodeUriComponent s ++ encodeUriComponent t)

theorem encodeUriBytes : EncodeUriBytes := by
  refine ⟨?_, ?_, ?_⟩
  · intro b h; simp [encodeUriComponent, h]
  · intro b h h16; simp [encodeUriComponent, h, hexNoPad, show ¬ b.toNat < 16 by omega]
  · intro s t; simp [encodeUriComponent]

/-- `uripath(path::String)` on Unix, `base/path.jl:1018-1027`, with `host` the WSL host
or `gethostname()`. -/
def uripath (cwd : Str) (host : List UInt8) (utf8 : Str → List UInt8) (path : Str) : List Char :=
  let localpath := Paths.joinSep (Paths.splitAtSeps (Paths.abspath cwd path) false)
  "file://".toList ++ encodeUriComponent host ++ ['/'] ++ encodeUriComponent (utf8 localpath)

/-- `uripath(path::AbstractString) = uripath(String(path))`, `base/path.jl:1030`. -/
def uripathAbs (cwd : Str) (host : List UInt8) (utf8 : Str → List UInt8) (p : Str) : List Char :=
  uripath cwd host utf8 p

def UripathShape : Prop :=
  (∀ cwd host utf8 p, "file://".toList <+: uripath cwd host utf8 p) ∧
  (∀ cwd host utf8 p, uripathAbs cwd host utf8 p = uripath cwd host utf8 p) ∧
  -- the local path has no empty component, so it never starts or ends with '/' or has "//"
  (∀ cwd p, ∀ w ∈ Paths.splitAtSeps (Paths.abspath cwd p) false, w ≠ [] ∧ '/' ∉ w)

theorem uripathShape : UripathShape := by
  refine ⟨?_, fun _ _ _ _ => rfl, fun cwd p => (splitAtSeparatorsCorrect _).2⟩
  intro cwd host utf8 p
  simp only [uripath, List.append_assoc]
  exact List.prefix_append _ _

end JuliaLean.IOCov.Path
