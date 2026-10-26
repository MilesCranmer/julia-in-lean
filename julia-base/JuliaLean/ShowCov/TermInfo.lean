import JuliaLean.ShowCov.Basic

/-!
# `base/terminfo.jl`

The terminfo reader runs on an `IOBuffer` over a byte list (`Rd`): `position`
is the number of bytes consumed, `read(io, nb)` returns
`min(nb, bytesavailable(io))` bytes, and reading a fixed-size integer past the
end throws `EOFError`. Integers are little-endian (`ltoh` is the identity on
the little-endian hosts Julia supports).

A `TermInfo` keeps its dictionaries as association lists in insertion order;
`setKey` overwrites an existing key in place, as `Dict` assignment does.
The capability tables `TERM_FLAGS`, `TERM_NUMBERS`, `TERM_STRINGS` (name,
capname pairs) and `TERM_USER` are parameters.
-/

namespace JuliaLean.ShowCov.TermInfo

open JuliaLean.ShowCov

/-- An `IOBuffer` over `data`, positioned after `pos` bytes. -/
structure Rd where
  data : List UInt8
  pos : Nat
  deriving DecidableEq, Repr

def Rd.rest (r : Rd) : List UInt8 := r.data.drop r.pos

/-- `eof(data)`. -/
def Rd.eof (r : Rd) : Bool := r.data.length ≤ r.pos

/-- `read(data, nb)` on an `IOBuffer`: `read!(io, StringVector(min(nb, bytesavailable(io))))`.
A negative length fails converting to the `UInt` allocation size
(`InexactError`, observed on both pinned versions). -/
def readN (r : Rd) (nb : Int) : R (List UInt8 × Rd) :=
  let k := min nb (r.data.length - r.pos : Nat)
  if k < 0 then .error (.inexactError "convert")
  else .ok (r.rest.take k.toNat, { r with pos := r.pos + k.toNat })

/-- `read(data, UInt8)`. -/
def readU8 (r : Rd) : R (UInt8 × Rd) :=
  match r.rest with
  | b :: _ => .ok (b, { r with pos := r.pos + 1 })
  | [] => .error .eofError

/-- Little-endian signed value of a byte list of width `w` bytes. -/
def leSigned (w : Nat) (bs : List UInt8) : Int :=
  let u : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0
  if u < 2 ^ (8 * w - 1) then u else (u : Int) - 2 ^ (8 * w)

/-- `read(data, Int16)`, `read(data, UInt16)` (unsigned), with `EOFError` when
fewer than two bytes remain. -/
def readI16 (r : Rd) : R (Int × Rd) :=
  match r.rest with
  | a :: b :: _ => .ok (leSigned 2 [a, b], { r with pos := r.pos + 2 })
  | _ => .error .eofError
def readU16 (r : Rd) : R (Nat × Rd) :=
  match r.rest with
  | a :: b :: _ => .ok (a.toNat + 256 * b.toNat, { r with pos := r.pos + 2 })
  | _ => .error .eofError

/-- `reinterpret(NumInt, bytes)` for a `Vector{UInt8}`: chunks of `w` bytes; a
length that is not a multiple of `w` is an `ArgumentError`. -/
def reinterpretIntsF (w : Nat) : Nat → List UInt8 → R (List Int)
  | _, [] => .ok []
  | 0, _ :: _ => .error (.argumentError "cannot reinterpret")
  | fuel + 1, b :: bs =>
    if w = 0 then .error (.argumentError "cannot reinterpret")
    else if (b :: bs).length < w then .error (.argumentError "cannot reinterpret")
    else do
      let rest ← reinterpretIntsF w fuel ((b :: bs).drop w)
      pure (leSigned w ((b :: bs).take w) :: rest)

/-- Each chunk consumes at least one byte, so `length` rounds of fuel suffice. -/
def reinterpretInts (w : Nat) (bytes : List UInt8) : R (List Int) :=
  reinterpretIntsF w bytes.length bytes

/-- `split(s, '|')` on the bytes of a `String` (all pieces kept). -/
def splitBar : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: bs =>
    let rest := splitBar bs
    if b = 0x7C then [] :: rest
    else match rest with
      | p :: ps => (b :: p) :: ps
      | [] => [[b]]

/-- The bytes of `table` from 0-based offset `idx` up to (not including) the
first NUL, if there is one. -/
def cstringAt (table : List UInt8) (idx : Nat) : Option (List UInt8) :=
  let tail := table.drop idx
  if (0 : UInt8) ∈ tail then some (tail.takeWhile (· ≠ 0)) else none

/-- `_terminfo_read_strings(table, indices)`, `base/terminfo.jl:148-162`:
`none` is `nothing`. -/
def readString (table : List UInt8) (idx : Int) : R (Option (List UInt8)) :=
  if idx ≥ 0 then
    match cstringAt table idx.toNat with
    | some s => .ok (some s)
    | none => .error (.argumentError "Terminfo table entry does not terminate with a null byte")
  else if idx = -1 ∨ idx = -2 then .ok none
  else .error (.argumentError "Terminfo table index is invalid")

def readStrings (table : List UInt8) (indices : List Int) : R (List (Option (List UInt8))) :=
  indices.mapM (readString table)

/-- Values of an extended capability. -/
inductive Val where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : List UInt8)
  | nothing
  deriving DecidableEq, Repr

/-- `TermInfoRaw`, `base/terminfo.jl:33-39`. -/
structure Raw where
  names : List (List UInt8)
  flags : List Bool
  numbers : List Int
  strings : List (Option (List UInt8))
  extended : Option (List (List UInt8 × Val))
  deriving DecidableEq, Repr

/-- If `position(data)` is odd, read the pad byte, which must be NUL. -/
def alignEven (r : Rd) (msg : String) : R Rd :=
  if r.pos % 2 ≠ 0 then do
    let (b, r) ← readU8 r
    if b = 0 then pure r else .error (.argumentError msg)
  else pure r

/-- `Dict(zip(labels, values))`: later duplicates overwrite earlier ones. -/
def dictOfPairs (ps : List (List UInt8 × Val)) : List (List UInt8 × Val) :=
  ps.foldl (fun d (k, v) => if d.any (·.1 == k) then d.map (fun e => if e.1 == k then (k, v) else e) else d ++ [(k, v)]) []

/-- `extendedterminfo(data, NumInt)`, `base/terminfo.jl:112-139`; `w` is
`sizeof(NumInt)`. -/
def extendedterminfo (r : Rd) (w : Nat) : R (List (List UInt8 × Val) × Rd) := do
  let r ← (if r.pos % 2 ≠ 0 then do
      let (b, r) ← readU8 r
      if b = 0 then pure r else .error (.argumentError "Terminfo did not contain a null byte before the extended section")
    else pure r)
  let (flagBytes, r) ← readI16 r
  let (numbersCount, r) ← readI16 r
  let (stringCount, r) ← readI16 r
  let (tableCount, r) ← readI16 r
  let (tableBytes, r) ← readI16 r
  let (fb, r) ← readN r flagBytes
  let flags := fb.map (· == 1)
  let r ← (if flagBytes % 2 ≠ 0 then do
      let (b, r) ← readU8 r
      if b = 0 then pure r else .error (.argumentError "Terminfo did not contain a null byte after the extended flag section")
    else pure r)
  let (nb, r) ← readN r (numbersCount * (w : Int))
  let numbers ← reinterpretInts w nb
  let (ib, r) ← readN r (tableCount * 2)
  let tableIndices ← reinterpretInts 2 ib
  let (tableData, r) ← readN r tableBytes
  if stringCount < 0 ∨ tableIndices.length < stringCount.toNat then .error .boundsError else
  let strings ← readStrings tableData (tableIndices.take stringCount.toNat)
  -- `get(table_indices, string_count, 0)`: index out of `1:length` gives 0
  let lastIdx : Int := if 1 ≤ stringCount then tableIndices.getD (stringCount.toNat - 1) 0 else 0
  let lastLen : Nat := match strings.getLast? with
    | some (some s) => s.length
    | _ => 0
  let halfoffset : Int := lastIdx + lastLen + 1
  let labelIdx := (tableIndices.drop stringCount.toNat).map (· + halfoffset)
  let labels ← readStrings tableData labelIdx
  let values : List Val := flags.map Val.bool ++ numbers.map Val.int ++
    strings.map (fun s => match s with | some s => Val.str s | none => Val.nothing)
  -- `map(Symbol, ...)` of a `nothing` label is a `MethodError`
  let labels ← labels.mapM (fun l => match l with | some l => .ok l | none => .error (.methodError "Symbol"))
  pure (dictOfPairs (labels.zip values), r)

/-- `read(data::IO, ::Type{TermInfoRaw})`, `base/terminfo.jl:71-101`. -/
def readRaw (data : List UInt8) : R Raw := do
  let r : Rd := ⟨data, 0⟩
  let (magic, r) ← readU16 r
  let w : Nat ← (if magic = 0o432 then pure 2 else if magic = 0o1036 then pure 4 else
    .error (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"))
  let (nameBytes, r) ← readI16 r
  let (flagBytes, r) ← readI16 r
  let (numbersCount, r) ← readI16 r
  let (stringCount, r) ← readI16 r
  let (tableBytes, r) ← readI16 r
  let (nm, r) ← readN r (nameBytes - 1)
  let termNames := splitBar nm
  let (z, r) ← readU8 r
  if z ≠ 0 then .error (.argumentError "Terminfo data did not contain a null byte after the terminal names section") else
  let (fb, r) ← readN r flagBytes
  let flags := fb.map (· == 1)
  let r ← alignEven r "Terminfo did not contain a null byte after the flag section"
  let (nb, r) ← readN r (numbersCount * (w : Int))
  let numbers ← reinterpretInts w nb
  let (sb, r) ← readN r (stringCount * 2)
  let stringIndices ← reinterpretInts 2 sb
  let (table, r) ← readN r tableBytes
  let strings ← readStrings table stringIndices
  let ext ← (if !r.eof then do let (e, _) ← extendedterminfo r w; pure (some e) else pure none)
  pure ⟨termNames, flags, numbers, strings, ext⟩

/-! ## `TermInfo` -/

/-- One `TermCapability`: long name and short capname. -/
structure Cap where
  name : String
  capname : String
  deriving DecidableEq, Repr

/-- `TermInfo`, `base/terminfo.jl:60-67`. Keys are capability names. -/
structure TI where
  names : List (List UInt8)
  flags : List (String × Bool)
  numbers : List (String × Int)
  strings : List (String × List UInt8)
  extensions : Option (List String)
  aliases : List (String × String)
  deriving DecidableEq, Repr

/-- `TermInfo()`, `base/terminfo.jl:69`. -/
def blank : TI := ⟨[], [], [], [], none, []⟩

/-- `d[k] = v`. -/
def setKey {β} (d : List (String × β)) (k : String) (v : β) : List (String × β) :=
  if d.any (·.1 == k) then d.map (fun e => if e.1 == k then (k, v) else e) else d ++ [(k, v)]

/-- `get(d, k, default)`. -/
def getKey {β} (d : List (String × β)) (k : String) (default : β) : β :=
  match d.find? (·.1 == k) with
  | some (_, v) => v
  | none => default

def hasKey {β} (d : List (String × β)) (k : String) : Bool := d.any (·.1 == k)

/-- `push!(s, k)` on a `Set`. -/
def pushSet (s : List String) (k : String) : List String := if k ∈ s then s else s ++ [k]

/-- The string form of a terminfo label (`Symbol(bytes)`); labels and keys are
compared as these strings. -/
def keyOf (bs : List UInt8) : String := String.ofList (bs.map (fun b => Char.ofNat b.toNat))

/-- `TermInfo(raw::TermInfoRaw)`, `base/terminfo.jl:170-212`, including
`longalias(key, value) = first(get(TERM_USER, (typeof(value), key), (nothing, "")))`
(`base/terminfo.jl:194`); `termUser kind short` is that lookup, with `kind`
`0`/`1`/`2`/`3` for `Bool`/`Int`/`String`/`Nothing`. -/
def ofRaw (termFlags termNumbers termStrings : List Cap)
    (termUser : Nat → String → Option String) (raw : Raw) : TI :=
  -- `for (flag, value) in zip(TERM_FLAGS, raw.flags)`
  let (flags, aliases) := (termFlags.zip raw.flags).foldl
    (fun (fl, al) (flag, value) => (setKey fl flag.name value, setKey al flag.capname flag.name))
    (([] : List (String × Bool)), ([] : List (String × String)))
  -- `for (num, value) in zip(TERM_NUMBERS, raw.numbers)`
  let (numbers, aliases) := (termNumbers.zip raw.numbers).foldl
    (fun (nu, al) (num, value) => (setKey nu num.name value, setKey al num.capname num.name))
    (([] : List (String × Int)), aliases)
  -- `for (str, value) in zip(TERM_STRINGS, raw.strings)`, skipping `nothing`
  let (strings, aliases) := (termStrings.zip raw.strings).foldl
    (fun (st, al) (str, value) => match value with
      | some v => (setKey st str.name v, setKey al str.capname str.name)
      | none => (st, al))
    (([] : List (String × List UInt8)), aliases)
  match raw.extended with
  | none => ⟨raw.names, flags, numbers, strings, none, aliases⟩
  | some ext =>
    -- `for (short, value) in raw.extended`
    let (fl, nu, st, al, exts) := ext.foldl
      (fun (fl, nu, st, al, exts) (shortB, value) =>
        let short := keyOf shortB
        let kind := match value with | .bool _ => 0 | .int _ => 1 | .str _ => 2 | .nothing => 3
        let long := termUser kind short
        let key := long.getD short
        let exts := pushSet exts key
        let (fl, nu, st) := match value with
          | .bool b => (setKey fl key b, nu, st)
          | .int n => (fl, setKey nu key n, st)
          | .str s => (fl, nu, setKey st key s)
          | .nothing => (fl, nu, st)
        let al := match long with
          | some l => setKey al short l
          | none => al
        (fl, nu, st, al, exts))
      (flags, numbers, strings, aliases, ([] : List String))
    ⟨raw.names, fl, nu, st, some exts, al⟩

/-- Capability values a lookup can return. -/
inductive CapVal where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : List UInt8)
  deriving DecidableEq, Repr

/-- `get(ti, key, default::Bool)`, `::Int`, `::String`, `base/terminfo.jl:214-216`. -/
def getBool (ti : TI) (key : String) (default : Bool) : Bool :=
  getKey ti.flags (getKey ti.aliases key key) default
def getInt (ti : TI) (key : String) (default : Int) : Int :=
  getKey ti.numbers (getKey ti.aliases key key) default
def getStr (ti : TI) (key : String) (default : List UInt8) : List UInt8 :=
  getKey ti.strings (getKey ti.aliases key key) default

/-- `haskey(ti::TermInfo, key)`, `base/terminfo.jl:218-219`. -/
def haskey (ti : TI) (key : String) : Bool :=
  hasKey ti.flags key || hasKey ti.numbers key || hasKey ti.strings key || hasKey ti.aliases key

/-- `getindex(ti::TermInfo, key)`, `base/terminfo.jl:221-227`, with fuel for the
alias recursion (Julia recurses without a bound; running out of fuel stands
for a stack overflow). -/
def getindex : Nat → TI → String → R CapVal
  | 0, _, _ => .error .boundsError
  | fuel + 1, ti, key =>
    if hasKey ti.flags key then .ok (.bool (getKey ti.flags key false))
    else if hasKey ti.numbers key then .ok (.int (getKey ti.numbers key 0))
    else if hasKey ti.strings key then .ok (.str (getKey ti.strings key []))
    else if hasKey ti.aliases key then getindex fuel ti (getKey ti.aliases key key)
    else .error (.keyError key)

/-- `keys(ti) = keys(ti.flags) ∪ keys(ti.numbers) ∪ keys(ti.strings) ∪ keys(ti.aliases)`,
`base/terminfo.jl:229`. -/
def keys (ti : TI) : List String :=
  (ti.flags.map (·.1) ++ ti.numbers.map (·.1) ++ ti.strings.map (·.1) ++ ti.aliases.map (·.1)).foldl pushSet []

/-- `show(io, ::MIME"text/plain", ti::TermInfo)`, `base/terminfo.jl:231-237`;
`namesRepr` is what `print(io, ti.names)` prints. -/
def showTI (namesRepr : String) (ti : TI) : Out :=
  ["TermInfo(", namesRepr, "; ", intStr ti.flags.length, " flags, ",
   intStr ti.numbers.length, " numbers, ", intStr ti.strings.length, " strings"] ++
  (match ti.extensions with
   | some e => [", ", intStr e.length, " extended capabilities"]
   | none => []) ++ [")"]

/-! ## Locating and loading -/

/-- The environment and file system `find_terminfo_file` consults. -/
structure Env where
  env : String → Option String
  homedir : String
  isdir : String → Bool
  isfile : String → Bool
  /-- `normpath(Sys.BINDIR, DATAROOTDIR, "julia", "terminfo")`. -/
  bundled : String
  isunix : Bool

/-- `joinpath` of path components (`/`-separated). -/
def joinpath (parts : List String) : String := "/".intercalate parts

/-- `split(s, ':')` with empty entries replaced by `/usr/share/terminfo`. -/
def terminfoDirsList (s : String) : List String :=
  (s.splitOn ":").map (fun d => if d = "" then "/usr/share/terminfo" else d)

/-- The directories `find_terminfo_file` searches, in order, `base/terminfo.jl:251-264`. -/
def searchDirs (e : Env) : List String :=
  let first := match e.env "TERMINFO" with
    | some d => [d]
    | none => if e.isdir (joinpath [e.homedir, ".terminfo"]) then [joinpath [e.homedir, ".terminfo"]] else []
  let fromDirs := match e.env "TERMINFO_DIRS" with
    | some s => terminfoDirsList s
    | none => []
  first ++ fromDirs ++ [e.bundled] ++
    (if e.isunix then ["/etc/terminfo", "/lib/terminfo", "/usr/share/terminfo"] else [])

/-- The three candidates tried in one directory: first character, its hex
code, and the lowercased forms, `base/terminfo.jl:266-276`. -/
def candidates (dir chr chrcode lchr lterm term : String) : List String :=
  [joinpath [dir, chr, term], joinpath [dir, chrcode, term], joinpath [dir, lchr, lterm]]

/-- `find_terminfo_file(term)`, `base/terminfo.jl:248-279`. `chr`, `chrcode`,
`lower` are `string(first(term))`, `string(Int(first(term)), base=16)` and
`lowercase`. -/
def findTerminfoFile (e : Env) (lower : String → String) (term : String) : Option String :=
  match term.toList with
  | [] => none
  | c :: _ =>
    let chr := String.singleton c
    let chrcode := String.ofList (Nat.toDigits 16 c.toNat)
    let rec go : List String → Option String
      | [] => none
      | dir :: dirs =>
        if e.isfile (joinpath [dir, chr, term]) then some (joinpath [dir, chr, term])
        else if e.isfile (joinpath [dir, chrcode, term]) then some (joinpath [dir, chrcode, term])
        else if e.isfile (joinpath [dir, lower chr, lower term]) then some (joinpath [dir, lower chr, lower term])
        else go dirs
    go (searchDirs e)

/-- How reading a terminfo file can end: parsed, or an exception of a kind. -/
inductive ReadResult where
  | ok (raw : Raw)
  | argumentError
  | ioError
  | otherError
  deriving DecidableEq, Repr

/-- Outcome of `load_terminfo`: a `TermInfo`, or a rethrown exception. -/
inductive Loaded where
  | info (ti : TI)
  | rethrown
  deriving DecidableEq, Repr

/-- `load_terminfo(term)`, `base/terminfo.jl:286-298`. `readFile path` is
`read(file, TermInfoRaw)`; `conv` is `TermInfo(raw)`. -/
def loadTerminfo (e : Env) (lower : String → String) (readFile : String → ReadResult)
    (conv : Raw → TI) (term : String) : Loaded :=
  match findTerminfoFile e lower term with
  | none => .info blank
  | some file =>
    match readFile file with
    | .ok raw => .info (conv raw)
    | .argumentError => .info blank
    | .ioError => .info blank
    | .otherError => .rethrown

/-! ## Colour detection -/

/-- `ttyhascolor()` on Unix: `haskey(current_terminfo(), :setaf)`; on Windows
`true`, `base/terminfo.jl:316-322`. -/
def ttyhascolor (windows : Bool) (ti : TI) : Bool :=
  if windows then true else haskey ti "setaf"

/-- The facts `ttyhastruecolor()` reads, `base/terminfo.jl:357-374`. -/
structure ColorEnv where
  env : String → Option String
  isunix : Bool
  /-- `Sys.iswindows() && Sys.windows_version() ≥ v"10.0.14931"`. -/
  windowsTrueColor : Bool
  /-- `tryparse(Int, get(ENV, "VTE_VERSION", ""))`. -/
  vteVersion : Option Int

/-- `ttyhastruecolor()`, `base/terminfo.jl:357-374`. -/
def ttyhastruecolor (c : ColorEnv) (ti : TI) : Bool :=
  (c.env "COLORTERM" = some "truecolor" || c.env "COLORTERM" = some "24bit") ||
  getBool ti "RGB" false || getBool ti "Tc" false ||
  (haskey ti "setrgbf" && haskey ti "setrgbb") ||
  (if c.isunix then decide (getInt ti "colors" 0 > 256) else false) ||
  c.windowsTrueColor ||
  decide ((c.vteVersion.getD 0) ≥ 3600) ||
  (c.env "XTERM_VERSION").isSome ||
  c.env "TERMINAL_PROGRAM" = some "iTerm.app" ||
  (c.env "KONSOLE_PROFILE_NAME").isSome ||
  (c.env "KONSOLE_DBUS_SESSION").isSome ||
  (let term := (c.env "TERM").getD ""
   term.startsWith "linux" || term.startsWith "rxvt" || term.startsWith "st")

/-- `get_have_color()` / `get_have_truecolor()`, `base/terminfo.jl:376-386`: the
global cache `have_color` (`none` is `nothing`) is filled on first use. Returns
the value and the new cache. -/
def getHaveCached (cache : Option Bool) (compute : Bool) : Bool × Option Bool :=
  match cache with
  | some v => (v, some v)
  | none => (compute, some compute)

/-- The `TTY` property methods, `base/terminfo.jl:388-391`; `haveColor` is
`get_have_color()`. `in` only has a method for `Pair{Symbol,Bool}`; other pairs
reach `in(::Pair, ::IO) = false`. -/
def inTTY (haveColor : Bool) (key : String) (value : Option Bool) : Bool :=
  match value with
  | some b => key == "color" && b == haveColor
  | none => false
def haskeyTTY (key : String) : Bool := key == "color"
def getindexTTY (haveColor : Bool) (key : String) : R Bool :=
  if key == "color" then .ok haveColor else .error (.keyError key)
def getTTY {α} (haveColor : α) (key : String) (default : α) : α :=
  if key == "color" then haveColor else default

end JuliaLean.ShowCov.TermInfo
