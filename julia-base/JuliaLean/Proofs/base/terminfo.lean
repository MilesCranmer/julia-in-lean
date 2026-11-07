import JuliaLean.Registry.Types
import JuliaLean.base.terminfo

namespace JuliaLean.Proofs.base.terminfo
open JuliaLean JuliaLean.Registry JuliaLean.base.terminfo
open JuliaLean.base.io (M Error)

private instance {W : Type} : LawfulMonad (M W) := by
  refine LawfulMonad.mk' _ ?_ ?_ ?_
  · intro A action
    funext w
    cases h : action w with
    | none => simp [Functor.map, bind, pure, h]
    | some result => cases result <;> simp [Functor.map, bind, pure, h]
  · intros; rfl
  · intro A B C action f g
    funext w
    cases h : action w with
    | none => simp [bind, h]
    | some result =>
      cases result with
      | error err => simp [bind, h]
      | ok result =>
        rcases result with ⟨a, w'⟩
        simp [bind, h, Option.bind_assoc]

def EmptySpec : Prop :=
  empty.names = [] ∧ empty.flags = [] ∧ empty.numbers = [] ∧
  empty.strings = [] ∧ empty.extensions = none ∧ empty.aliases = []

theorem empty_proven : EmptySpec := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact reads retain the length promised by allocation and read! dispatch. -/
def ReadBytesSpec : Prop :=
  ∀ {World Stream Integer Buffer : Type}
    (allocate : Integer → M World Buffer) (readInto : Stream → Buffer → M World Buffer)
    (size : Buffer → Nat) (count : Integer → Nat) (stream : Stream) (n : Integer)
    (world : World),
    (∀ b w, allocate n world = some (.ok (b, w)) → size b = count n) →
    (∀ b w out w', readInto stream b w = some (.ok (out, w')) → size out = size b) →
    ∀ out w', readBytes allocate readInto stream n world = some (.ok (out, w')) →
      size out = count n

/-- Neither raw format accepts a header with an unrecognized magic number. -/
def RawMagicSpec : Prop :=
  ∀ {World Stream : Type} (ops : ParserOps World Stream) (stream : Stream)
    (w w' : World) (magic : JInt .u16),
    ops.readUInt16LE stream w = some (.ok (magic, w')) →
    magic.val ≠ 282 → magic.val ≠ 542 →
    readRaw ops stream w = some (.error
      (.jl (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"), w'))

/-- Alignment bytes preceding an extended header must be zero. -/
def ExtendedAlignmentSpec : Prop :=
  ∀ {World Stream : Type} (ops : ParserOps World Stream) (stream : Stream)
    (format : NumberFormat) (w w' w'' : World) (position : I) (byte : JInt .u8),
    ops.position stream w = some (.ok (position, w')) → position.val % 2 ≠ 0 →
    ops.readByte stream w' = some (.ok (byte, w'')) → byte.val ≠ 0 →
    extendedterminfo ops stream format w = some (.error
      (.jl (.argumentError "Terminfo did not contain a null byte before the extended section; expected to position the start on an even byte"), w''))

/-- Absent string capabilities preserve their positions and perform no table reads. -/
def AbsentStringsSpec : Prop :=
  ∀ {World Stream : Type} (ops : ParserOps World Stream) (table : Bytes)
    (indices : List (JInt .i16)) (w : World),
    (∀ idx ∈ indices, idx.val = -1 ∨ idx.val = -2) →
    readStrings ops table indices w = some (.ok (indices.map (fun _ => none), w))

/-- Construction preserves terminal names, including an empty name list. -/
def ConstructorNamesSpec : Prop :=
  ∀ (tables : Tables) (raw : TermInfoRaw), (fromRaw tables raw).names = raw.names

theorem constructorNames_proven : ConstructorNamesSpec := by
  intro tables raw
  simp only [fromRaw, Id.run, bind, pure] <;>
    repeat' first | rfl | split

/-- A user capability alias is available exactly when its typed lookup supplies one. -/
def LongAliasSpec : Prop :=
  ∀ (tables : Tables) (key : String) (value : Capability) (alias : Option String),
    tables.userAlias key value = alias → longalias tables key value = alias

theorem longAlias_proven : LongAliasSpec := by
  intro tables key value alias h
  exact h

/-- Typed lookups resolve aliases, return matching values and otherwise retain defaults. -/
def TypedGetSpec : Prop :=
  ∀ (ti : TermInfo) (key resolved : String),
    (lookup ti.aliases key).getD key = resolved →
    (∀ (default : Bool), getBool ti key default = (lookup ti.flags resolved).getD default) ∧
    (∀ (default : I), getInt ti key default = (lookup ti.numbers resolved).getD default) ∧
    (∀ (default : JString), getString ti key default = (lookup ti.strings resolved).getD default)

theorem typedGet_proven : TypedGetSpec := by
  intro ti key resolved h
  refine ⟨?_, ?_, ?_⟩ <;> intro default <;> simp only [getBool, getInt, getString, h]

/-- A TermInfo key exists exactly when one of its typed dictionaries or aliases contains it. -/
def HasKeySpec : Prop :=
  ∀ (ti : TermInfo) (key : String), haskey ti key = true ↔
    (lookup ti.flags key).isSome = true ∨ (lookup ti.numbers key).isSome = true ∨
    (lookup ti.strings key).isSome = true ∨ (lookup ti.aliases key).isSome = true

theorem hasKey_proven : HasKeySpec := by
  intro ti key
  simp [haskey, or_assoc]

/-- Direct capability lookup gives flags precedence over numbers and strings. -/
def GetindexSpec : Prop :=
  ∀ {World : Type} (ti : TermInfo) (key : String) (w : World),
    (∀ b, lookup ti.flags key = some b →
      getindex ti key w = some (.ok (.flag b, w))) ∧
    (lookup ti.flags key = none → ∀ n, lookup ti.numbers key = some n →
      getindex ti key w = some (.ok (.number n, w))) ∧
    (lookup ti.flags key = none → lookup ti.numbers key = none →
      ∀ s, lookup ti.strings key = some s → getindex ti key w = some (.ok (.string s, w))) ∧
    (haskey ti key = false → getindex ti key w = some (.error (.foreignError "KeyError" key, w)))

/-- keys reports the union of capability names and alias names, without duplicates. -/
def KeysSpec : Prop :=
  ∀ (ti : TermInfo) (key : String), (keys ti).Nodup ∧
    (key ∈ keys ti ↔ key ∈ ti.flags.map Prod.fst ∨ key ∈ ti.numbers.map Prod.fst ∨
      key ∈ ti.strings.map Prod.fst ∨ key ∈ ti.aliases.map Prod.fst)

/-- The display includes terminal names, every capability count and any extension count. -/
def ShowSpec : Prop :=
  ∀ (ti : TermInfo) (showNames : List JString → String),
    let print : Unit → String → M String Unit := fun _ text output =>
      some (.ok ((), output ++ text))
    showTermInfo print showNames () ti "" = some (.ok ((),
      "TermInfo(" ++ showNames ti.names ++ "; " ++ toString ti.flags.length ++ " flags, " ++
      toString ti.numbers.length ++ " numbers, " ++ toString ti.strings.length ++ " strings" ++
      (match ti.extensions with
       | none => ""
       | some names => ", " ++ toString names.length ++ " extended capabilities") ++ ")"))

/-- Stat errors classified as IOError are treated as an absent path; other errors survive. -/
def StatCheckSpec : Prop :=
  ∀ {World : Type} (isIO : Error → Bool) (check : String → M World Bool)
    (path : String) (w w' : World) (err : Error),
    check path w = some (.error (err, w')) →
    statCheck isIO check path w =
      if isIO err then some (.ok (false, w')) else some (.error (err, w'))

/-- Terminal names cannot escape the database directories. -/
def FindFileSpec : Prop :=
  ∀ {World : Type} (ops : FilesystemOps World) (term : String) (w : World),
    (term.isEmpty = true ∨ term.toList.any ops.isseparator = true) →
    findTerminfoFile ops term w = some (.ok (none, w))

/-- A terminal with no database file loads an empty capability set. -/
def LoadSpec : Prop :=
  ∀ {World : Type} (ops : FilesystemOps World) (tables : Tables)
    (read : String → M World TermInfoRaw) (term : String) (w w' : World),
    findTerminfoFile ops term w = some (.ok (none, w')) →
    loadTerminfo ops tables read term w = some (.ok (empty, w'))

/-- Windows supports color; Unix tests the terminal's foreground-color capability. -/
def ColorSpec : Prop :=
  ttyhascolorWindows = true ∧
  (∀ {World : Type} (ti : TermInfo) (w : World),
    ttyhascolorUnix (pure ti : M World TermInfo) w = some (.ok (haskey ti "setaf", w)))

/-- Both documented COLORTERM spellings enable true color before any later checks. -/
def TruecolorSpec : Prop :=
  ∀ {World : Type} (env : String → M World (Option String)) (current : M World TermInfo)
    (unix windows : Bool) (version : M World Bool) (parse : String → Option I)
    (w w' : World) (name : String),
    env "COLORTERM" w = some (.ok (some name, w')) →
    (name = "truecolor" ∨ name = "24bit") →
    ttyhastruecolor env current unix windows version parse w = some (.ok (true, w'))

/-- Cached detection is returned without running the detector or changing the cache. -/
def CachedColorSpec : Prop :=
  ∀ {World : Type} (b : Bool) (write : Bool → M World Unit) (detect : M World Bool)
    (w : World),
    getHaveColor (pure (some b)) write detect w = some (.ok (b, w)) ∧
    getHaveTruecolor (pure (some b)) write detect w = some (.ok (b, w))

/-- TTY supports only the color key; a missing key returns its default or raises KeyError. -/
def TTYSpec : Prop :=
  (∀ key : String, haskeyTTY key = true ↔ key = "color") ∧
  (∀ {World : Type} (detect : M World Bool) (key : String) (b : Bool) (w : World),
    key ≠ "color" → containsTTY detect (key, b) w = some (.ok (false, w)) ∧
      getindexTTY detect key w = some (.error (.foreignError "KeyError" key, w))) ∧
  (∀ {World Value : Type} (cast : Bool → Value) (detect : M World Bool)
      (key : String) (default : Value) (w : World), key ≠ "color" →
    getTTY cast detect key default w = some (.ok (default, w)))

theorem readBytes_proven : ReadBytesSpec := by
  intro W S N B allocate readInto size count stream n world ha hr out w' h
  change (do
    match ← allocate n world with
    | .error e => pure (.error e)
    | .ok (b, w) => readInto stream b w) = some (.ok (out, w')) at h
  cases he : allocate n world with
  | none => simp [he] at h
  | some result =>
    cases result with
    | error err => simp [he] at h
    | ok result =>
      rcases result with ⟨b, w⟩
      simp only [he] at h
      exact (hr b w out w' h).trans (ha b w he)

theorem rawMagic_proven : RawMagicSpec := by
  intro W S ops stream w w' magic h h282 h542
  simp [readRaw, bind, h, h282, h542, pure, throw, throwThe, MonadExceptOf.throw]

theorem extendedAlignment_proven : ExtendedAlignmentSpec := by
  intro W S ops stream format w w' w'' position byte hp hodd hb hnonzero
  simp [extendedterminfo, requireNull, bind, hp, hodd, hb, hnonzero, pure,
    throw, throwThe, MonadExceptOf.throw]

theorem statCheck_proven : StatCheckSpec := by
  intro W isIO check path w w' err h
  cases hi : isIO err <;>
    simp [statCheck, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, h, hi, pure,
      throw, throwThe, MonadExceptOf.throw]

theorem findFile_proven : FindFileSpec := by
  intro W ops term w h
  rcases h with h | h <;> simp [findTerminfoFile, h, pure, bind]

theorem load_proven : LoadSpec := by
  intro W ops tables read term w w' h
  simp [loadTerminfo, bind, tryCatch, tryCatchThe, MonadExceptOf.tryCatch, h, pure,
    throw, throwThe, MonadExceptOf.throw, ExceptT.pure, ExceptT.run, ExceptT.mk, EarlyReturn.runK]

theorem color_proven : ColorSpec := by
  refine ⟨rfl, ?_⟩
  intros
  rfl

theorem truecolor_proven : TruecolorSpec := by
  intro W env current unix windows version parse w w' name h hn
  rcases hn with hn | hn <;> subst name <;>
    simp [ttyhastruecolor, bind, h, pure]

theorem cachedColor_proven : CachedColorSpec := by
  intro W b write detect w
  exact ⟨rfl, rfl⟩

theorem tty_proven : TTYSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intros; simp [haskeyTTY]
  · intro W detect key b w h
    simp [containsTTY, getindexTTY, h, pure, throw, throwThe, MonadExceptOf.throw]
  · intro W V cast detect key default w h
    simp [getTTY, h, pure]


theorem show_proven : ShowSpec := by
  intro ti showNames
  cases he : ti.extensions <;>
    simp [showTermInfo, he, bind, pure, String.append_assoc]

theorem getindex_proven : GetindexSpec := by
  intro W ti key w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [getindex, JuliaLean.base.io.whileLoop.eq_def]
    simp [hb, pure]
  · intro hb n hn
    rw [getindex, JuliaLean.base.io.whileLoop.eq_def]
    simp [hb, hn, pure]
  · intro hb hn s hs
    rw [getindex, JuliaLean.base.io.whileLoop.eq_def]
    simp [hb, hn, hs, pure]
  · intro h
    cases hb : lookup ti.flags key <;> cases hn : lookup ti.numbers key <;>
      cases hs : lookup ti.strings key <;> cases ha : lookup ti.aliases key <;>
      simp [haskey, hb, hn, hs, ha] at h
    rw [getindex, JuliaLean.base.io.whileLoop.eq_def]
    simp [hb, hn, hs, ha, throw, throwThe, MonadExceptOf.throw]

private theorem mapM_absent {World α β : Type} (f : α → M World (Option β))
    (xs : List α) (h : ∀ x ∈ xs, f x = pure none) :
    xs.mapM f = pure (xs.map (fun _ => none)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.mapM_cons, List.map_cons, hx, ht, pure_bind]

theorem absentStrings_proven : AbsentStringsSpec := by
  intro W S ops table indices w allAbsent
  apply congrFun (mapM_absent _ indices ?_) w
  intro idx hi
  have hx := allAbsent idx hi
  have hneg : ¬idx.val ≥ 0 := by rcases hx with h | h <;> omega
  have hsentinel : (idx.val == -1 || idx.val == -2) = true := by
    rcases hx with h | h <;> simp [h]
  simp only [hneg, ite_false, hsentinel, ite_true]

private theorem keyUnionFold (xs acc : List String) (hacc : acc.Nodup) :
    let result := xs.foldl (fun acc key => if acc.contains key then acc else acc ++ [key]) acc
    result.Nodup ∧ ∀ key, key ∈ result ↔ key ∈ acc ∨ key ∈ xs := by
  induction xs generalizing acc with
  | nil =>
    refine ⟨hacc, ?_⟩
    intro key
    simp
  | cons x xs ih =>
    dsimp only [List.foldl_cons]
    by_cases hx : x ∈ acc
    · simp only [List.contains_iff_mem.mpr hx, ite_true]
      obtain ⟨hn, hm⟩ := ih acc hacc
      refine ⟨hn, ?_⟩
      intro key
      rw [hm]
      simp only [List.mem_cons]
      constructor
      · rintro (ha | ht)
        · exact Or.inl ha
        · exact Or.inr (Or.inr ht)
      · rintro (ha | he | ht)
        · exact Or.inl ha
        · subst key; exact Or.inl hx
        · exact Or.inr ht
    · have hx' : acc.contains x = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ite_false]
      have hnew : (acc ++ [x]).Nodup := by
        apply List.nodup_append.mpr
        refine ⟨hacc, by simp, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst b
        intro heq
        subst a
        exact hx ha
      obtain ⟨hn, hm⟩ := ih (acc ++ [x]) hnew
      refine ⟨hn, ?_⟩
      intro key
      rw [hm]
      simp only [List.mem_append, List.mem_singleton, List.mem_cons]
      simp [or_assoc]

theorem keys_proven : KeysSpec := by
  intro ti key
  have h := keyUnionFold (ti.flags.map Prod.fst ++ ti.numbers.map Prod.fst ++
    ti.strings.map Prod.fst ++ ti.aliases.map Prod.fst) [] (by simp)
  refine ⟨h.1, ?_⟩
  simpa [keys, or_assoc] using h.2 key

def entries : List Entry := [
  { id := "terminfo-empty-capabilities", juliaFile := "base/terminfo.jl"
    juliaFns := ["TermInfo()"]
    statement := "The empty constructor contains no names, capabilities, aliases or extended capabilities."
    source := "base/terminfo.jl:69", status := .proven, prop := ``EmptySpec, thm := some ``empty_proven },
  { id := "terminfo-read-exact-size", juliaFile := "base/terminfo.jl"
    juliaFns := ["_terminfo_read_bytes(data::IO, nbytes::Integer)"]
    statement := "Successful exact reads retain the byte count promised by allocation and read! dispatch."
    source := "base/terminfo.jl:72", status := .proven, prop := ``ReadBytesSpec, thm := some ``readBytes_proven },
  { id := "terminfo-reject-unknown-magic", juliaFile := "base/terminfo.jl"
    juliaFns := ["read(data::IO, ::Type{TermInfoRaw})"]
    statement := "Raw parsing rejects every magic value other than the two terminfo format signatures."
    source := "base/terminfo.jl:74", status := .proven, prop := ``RawMagicSpec, thm := some ``rawMagic_proven },
  { id := "terminfo-extended-alignment", juliaFile := "base/terminfo.jl"
    juliaFns := ["extendedterminfo(data::IO, NumInt::Union{Type{Int16}, Type{Int32}})"]
    statement := "An extended header at an odd position requires a preceding zero byte and reports the exact alignment diagnostic otherwise."
    source := "base/terminfo.jl:117", status := .proven, prop := ``ExtendedAlignmentSpec, thm := some ``extendedAlignment_proven },
  { id := "terminfo-absent-string-slots", juliaFile := "base/terminfo.jl"
    juliaFns := ["_terminfo_read_strings(table::Vector{UInt8}, indices::Vector{Int16})"]
    statement := "Absent string capabilities retain their positions and do not access the string table."
    source := "base/terminfo.jl:163", status := .proven, prop := ``AbsentStringsSpec, thm := some ``absentStrings_proven },
  { id := "terminfo-constructor-names", juliaFile := "base/terminfo.jl"
    juliaFns := ["TermInfo(raw::TermInfoRaw)"]
    statement := "TermInfo construction preserves the terminal name list."
    source := "base/terminfo.jl:185", status := .proven, prop := ``ConstructorNamesSpec, thm := some ``constructorNames_proven },
  { id := "terminfo-user-alias", juliaFile := "base/terminfo.jl"
    juliaFns := ["longalias(key, value)"]
    statement := "A user capability alias is supplied exactly by its typed capability-name lookup."
    source := "base/terminfo.jl:209", status := .proven, prop := ``LongAliasSpec, thm := some ``longAlias_proven },
  { id := "terminfo-typed-capability-get", juliaFile := "base/terminfo.jl"
    juliaFns := ["get(ti::TermInfo, key::Symbol, default::Bool)", "get(ti::TermInfo, key::Symbol, default::Int)", "get(ti::TermInfo, key::Symbol, default::String)"]
    statement := "Typed capability get resolves aliases, returns matching values, and preserves defaults when no value is present."
    source := "base/terminfo.jl:229,230,231", status := .proven, prop := ``TypedGetSpec, thm := some ``typedGet_proven },
  { id := "terminfo-key-membership", juliaFile := "base/terminfo.jl"
    juliaFns := ["haskey(ti::TermInfo, key::Symbol)"]
    statement := "Key membership covers all capability dictionaries and aliases."
    source := "base/terminfo.jl:233", status := .proven, prop := ``HasKeySpec, thm := some ``hasKey_proven },
  { id := "terminfo-index-lookup", juliaFile := "base/terminfo.jl"
    juliaFns := ["getindex(ti::TermInfo, key::Symbol)"]
    statement := "Capability lookup gives flags precedence over numbers and strings and raises KeyError for absent keys."
    source := "base/terminfo.jl:236", status := .proven, prop := ``GetindexSpec, thm := some ``getindex_proven },
  { id := "terminfo-keys-union", juliaFile := "base/terminfo.jl"
    juliaFns := ["keys(ti::TermInfo)"]
    statement := "The key set is the union of capability names and alias names without duplicates."
    source := "base/terminfo.jl:244", status := .proven, prop := ``KeysSpec, thm := some ``keys_proven },
  { id := "terminfo-display-counts", juliaFile := "base/terminfo.jl"
    juliaFns := ["show(io::IO, ::MIME\"text/plain\", ti::TermInfo)"]
    statement := "Text display includes terminal names, every capability count, and the extension count when present."
    source := "base/terminfo.jl:246", status := .proven, prop := ``ShowSpec, thm := some ``show_proven },
  { id := "terminfo-stat-errors", juliaFile := "base/terminfo.jl"
    juliaFns := ["_terminfo_stat_check(check::Function, path::String)"]
    statement := "Inaccessible paths classified by IOError are absent; other filesystem errors propagate."
    source := "base/terminfo.jl:255", status := .proven, prop := ``StatCheckSpec, thm := some ``statCheck_proven },
  { id := "terminfo-reject-path-escape", juliaFile := "base/terminfo.jl"
    juliaFns := ["find_terminfo_file(term::String)"]
    statement := "Empty terminal names and names containing path separators are rejected before filesystem access."
    source := "base/terminfo.jl:273", status := .proven, prop := ``FindFileSpec, thm := some ``findFile_proven },
  { id := "terminfo-missing-file-fallback", juliaFile := "base/terminfo.jl"
    juliaFns := ["load_terminfo(term::String)"]
    statement := "A terminal with no database file loads an empty capability set."
    source := "base/terminfo.jl:312", status := .proven, prop := ``LoadSpec, thm := some ``load_proven },
  { id := "terminfo-color-detection", juliaFile := "base/terminfo.jl"
    juliaFns := ["ttyhascolor()", "ttyhascolor()"]
    statement := "Windows enables color; Unix tests the terminal's foreground-color capability."
    source := "base/terminfo.jl:343,345", status := .proven, prop := ``ColorSpec, thm := some ``color_proven },
  { id := "terminfo-colorterm-truecolor", juliaFile := "base/terminfo.jl"
    juliaFns := ["ttyhastruecolor()"]
    statement := "Both documented COLORTERM spellings enable true color before later environment or capability checks."
    source := "base/terminfo.jl:383", status := .proven, prop := ``TruecolorSpec, thm := some ``truecolor_proven },
  { id := "terminfo-cached-color", juliaFile := "base/terminfo.jl"
    juliaFns := ["get_have_color()", "get_have_truecolor()"]
    statement := "Cached color results are returned without running the detector or changing the cache."
    source := "base/terminfo.jl:402,408", status := .proven, prop := ``CachedColorSpec, thm := some ``cachedColor_proven },
  { id := "terminfo-tty-color-key", juliaFile := "base/terminfo.jl"
    juliaFns := ["in(key_value::Pair{Symbol,Bool}, ::TTY)", "haskey(::TTY, key::Symbol)", "getindex(::TTY, key::Symbol)", "get(::TTY, key::Symbol, default)"]
    statement := "TTY supports only the color key, returning defaults or KeyError for missing keys."
    source := "base/terminfo.jl:414,415,416,417", status := .proven, prop := ``TTYSpec, thm := some ``tty_proven }
]

end JuliaLean.Proofs.base.terminfo
