import Lean.Data.Json
import Std.Data.HashMap
import JuliaLean.base.loading

/-!
`loadingdiff`: differential-testing driver for the cache-file part of the `base/loading.jl` model
(`JuliaLean/base/loading.lean`). `difftest/base/loading.jl` writes the input and reads the output.

Reads JSON lines on stdin and prints one JSON line per case.

* Environment lines update the state the model's callees answer from: `F` registers a file's bytes
  with the results of `jl_read_verify_header` and `_crc32c` on it, `FS` upserts `stat` results,
  `RD` upserts `readdir(dir, sort=false)` listings, `ENV` replaces other callee answers (loaded
  modules, `identify_package`, `locate_package_load_spec`, preferences, `fixup_stdlib_path`, ...),
  and `MCF`/`MCC` give the `jl_match_cache_flags`/`jl_match_cache_coverage` tables.
* `{"id": k, "op": "...", ..., "exp": {...}}` runs one model function and compares its encoded
  result with `exp`, which the pinned Julia computed in the same state.

Callees are answered only from these tables. A query the tables do not cover fails the case with
`UNMODELLED ...`, so a model that queries a path or package Julia did not is reported, not guessed.
The open stream's position is kept in `World.timing_imports`, which no function under test reads;
at most one cache file is open at a time in these functions.
-/

open Lean (Json)
open JuliaLean JuliaLean.base.loading
open JuliaLean.base.pkgid (PkgId)
open JuliaLean.base.uuid (UUID)

namespace LoadingDiff

abbrev I64 := JInt .i64

abbrev U := Unit
abbrev W := World U U U U

/-! ## Default values for the parameters the functions under test never use -/

set_option maxHeartbeats 2000000 in
def files0 : JuliaLean.base.path.FileBindings W :=
  { Handle := Unit, CString := Unit, StatMemory := Unit, IOBuf := Unit, User := Unit,
    Group := Unit, Req := Unit, StrBuf := Unit, SizeRef := Unit, Dirent := Unit, Stream := Unit,
    WString := Unit, Chan := Unit, Cmd := Unit, Pipe := Unit, IterObj := Unit, DirPtr := Unit,
    DiskBuf := Unit, DiskStatRaw := Unit, PathVal := Unit
    ops := by repeat (first | exact default | intro _ | constructor) }

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
def baseOps0 : LOps U U U U U U U := by
  constructor
  case pathFiles => exact files0
  all_goals repeat (first | exact default | intro _ | constructor)

set_option maxHeartbeats 2000000 in
def world0 : W := by
  repeat (first | exact default | intro _ | exact Unit | constructor)

/-! ## Bytes, JSON -/

def B (s : String) : Bytes := s.toUTF8.toList

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexNat (s : String) : Except String Nat :=
  s.foldl (fun acc c => do
    let a ← acc
    match hexDigit c with
    | some d => pure (a * 16 + d)
    | none => throw s!"bad hex {s}") (pure 0)

def hexBytes (s : String) : Except String ByteArray := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then throw "odd hex"
  let mut out := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match hexDigit cs[2*i]!, hexDigit cs[2*i+1]! with
    | some a, some b => out := out.push (UInt8.ofNat (a * 16 + b))
    | _, _ => throw "bad hex"
  return out

def hexChars : Array Char := "0123456789abcdef".toList.toArray
def toHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexChars[b.toNat / 16]!, hexChars[b.toNat % 16]!])
/-- The table key of a path: its text, or `hex:` and its bytes when they are not UTF-8. -/
def S (b : Bytes) : String :=
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => s
  | none => "hex:" ++ toHex b
def natHex (n : Nat) : String :=
  if n == 0 then "0" else String.ofList (Nat.toDigits 16 n)

def getK (j : Json) (k : String) : Except String Json := j.getObjVal? k
def getS (j : Json) (k : String) : Except String String := getK j k >>= Json.getStr?
def getN (j : Json) (k : String) : Except String Nat := getK j k >>= Json.getNat?
def getI (j : Json) (k : String) : Except String Int := getK j k >>= Json.getInt?
def getB (j : Json) (k : String) : Except String Bool := getK j k >>= Json.getBool?
def getA (j : Json) (k : String) : Except String (List Json) := do
  return (← (← getK j k).getArr?).toList
def arr (j : Json) : Except String (List Json) := do return (← j.getArr?).toList
def at! (xs : List Json) (i : Nat) : Except String Json :=
  match xs[i]? with | some x => pure x | none => throw s!"missing index {i}"
def has (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

/-- Paths and other strings: a JSON string, or `{"hex": ...}` for bytes that are not UTF-8. -/
def encBytes (b : Bytes) : Json :=
  match String.fromUTF8? ⟨b.toArray⟩ with
  | some s => Json.str s
  | none => Json.mkObj [("hex", Json.str (toHex b))]
def decBytes (j : Json) : Except String Bytes := do
  if let .ok s := j.getStr? then return B s
  return (← hexBytes (← getS j "hex")).toList

def u128 (n : Nat) : JInt .u128 := JInt.wrap .u128 n
def uuidOf (n : Nat) : UUID := ⟨u128 n⟩

/-- `PkgId`: `[uuid-hex or null, name]`. -/
def decPkg (j : Json) : Except String PkgId := do
  let xs ← arr j
  let u ← at! xs 0
  let name ← decBytes (← at! xs 1)
  if u.isNull then return ⟨none, name⟩
  return ⟨some (uuidOf (← hexNat (← u.getStr?))), name⟩
def encPkg (p : PkgId) : Json :=
  Json.arr #[match p.uuid with
    | none => Json.null
    | some u => Json.str (natHex u.value.val.toNat), encBytes p.name]

def encFloat (x : JuliaLean.base.float.FV .f64) : Json := Json.str (natHex x.toBits)

def decSpec (j : Json) : Except String PkgLoadSpec := do
  let xs ← arr j
  return { path := ← decBytes (← at! xs 0)
           julia_edition := (i64 (← (← at! xs 1).getInt?), i64 (← (← at! xs 2).getInt?)) }
def encSpec (s : PkgLoadSpec) : Json :=
  Json.arr #[encBytes s.path, Json.num s.julia_edition.1.val, Json.num s.julia_edition.2.val]

/-- `CacheFlags`: `[use_pkgimages, debug_level, check_bounds, inline, opt_level, coverage,
coverage_path or null]`. -/
def decFlags (j : Json) : Except String CacheFlags := do
  let xs ← arr j
  let cp ← at! xs 6
  return { use_pkgimages := ← (← at! xs 0).getBool?, debug_level := i64 (← (← at! xs 1).getInt?)
           check_bounds := i64 (← (← at! xs 2).getInt?), inline := ← (← at! xs 3).getBool?
           opt_level := i64 (← (← at! xs 4).getInt?), coverage := i64 (← (← at! xs 5).getInt?)
           coverage_path := ← if cp.isNull then pure none else some <$> decBytes cp }
def encFlags (f : CacheFlags) : Json :=
  Json.arr #[Json.bool f.use_pkgimages, Json.num f.debug_level.val, Json.num f.check_bounds.val,
    Json.bool f.inline, Json.num f.opt_level.val, Json.num f.coverage.val,
    match f.coverage_path with | none => Json.null | some p => encBytes p]

def encReasons : Option (AMap Bytes I64) → Json
  | none => Json.null
  | some m => Json.mkObj (m.map fun (k, v) => (S k, Json.num v.val))

/-- Exception classes, matching `errclass` in `difftest/base/loading.jl`. -/
def errName : LErr U → String
  | .jl .eofError => "EOFError"
  | .jl (.inexactError _) => "InexactError"
  | .jl .boundsError => "BoundsError"
  | .jl (.argumentError _) => "ArgumentError"
  | .jl _ => "Other"
  | .argumentError _ => "ArgumentError"
  | .assertionError _ => "AssertionError"
  | .boundsError => "BoundsError"
  | .typeError => "TypeError"
  | .ioError _ => "IOError"
  | .path (.ioError _) => "IOError"
  | .errorException m => if m.startsWith "UNMODELLED" then m else "ErrorException"
  | .errorExceptionBytes _ => "ErrorException"
  | .keyError | .keyErrorPkgId _ | .keyErrorSymbol _ => "KeyError"
  | .concurrencyViolation | .concurrencyViolationMessage _ => "ConcurrencyViolationError"
  | _ => "Other"

/-! ## Callee tables -/

structure FsEnt where
  isPath : Bool
  isFile : Bool
  isDir : Bool
  readable : Bool
  size : Int
  mtime : Nat
  mode : Nat
  dev : Nat
  ino : Nat
  hash : Nat
  /-- The exception class `stat(path)` throws, if it throws. -/
  err : Option String := none
  deriving Inhabited

/-- An exception of the class `errName` names, for callee answers that are exceptions. -/
def fsErr : String → LErr U
  | "ArgumentError" => .argumentError "callee"
  | "IOError" => .ioError "callee"
  | "TypeError" => .typeError
  | "KeyError" => .keyError
  | "BoundsError" => .boundsError
  | "Other" => .jl (.domainError "callee")
  | other => .errorException s!"UNMODELLED callee error {other}"

def checkEnt (e : FsEnt) : Except (LErr U) FsEnt :=
  match e.err with
  | some c => .error (fsErr c)
  | none => .ok e

structure FileReg where
  bytes : ByteArray
  status : Int
  flags : Nat
  checksum : Nat
  pos : Nat
  crcBody : Nat
  deriving Inhabited

structure DMod where
  pkg : PkgId
  hi : Nat
  lo : Nat
  deriving DecidableEq

instance : Inhabited PkgId := ⟨⟨none, []⟩⟩
instance : Inhabited DMod := ⟨⟨default, 0, 0⟩⟩
instance : BEq PkgId := ⟨fun a b => decide (a = b)⟩

structure Env where
  files : Std.HashMap String FileReg := {}
  fs : Std.HashMap String FsEnt := {}
  readdirs : Std.HashMap String (List Bytes) := {}
  depotPath : List String := []
  stdlib : String := ""
  dlext : String := "so"
  vmajor : String := "1"
  vminor : String := "15"
  edition : Int × Int := (1, 15)
  mcf : Std.HashMap (Nat × Nat) Nat := {}
  mcc : Std.HashMap (Nat × Nat) Bool := {}
  imageCov : Nat := 0
  sysimageCov : Nat := 0
  jlCacheFlags : Nat := 0
  usePkgimages : Bool := true
  debugBuild : Bool := false
  /-- the largest position `seek` reaches in the depot's file system -/
  maxSeek : Int := 2 ^ 63 - 1
  /-- clone-target bytes (hex) → whether `jl_check_pkgimage_clones` rejects them -/
  clones : Std.HashMap String Bool := {}
  fixup : Std.HashMap String Bytes := {}
  identify : List ((PkgId × Bytes) × Option PkgId) := []
  locate : List (PkgId × Option PkgLoadSpec) := []
  identifyErr : List ((PkgId × Bytes) × String) := []
  locateErr : List (PkgId × String) := []
  loaded : List (PkgId × DMod) := []
  precomp : List (PkgId × List DMod) := []
  insys : List PkgId := []
  concrete : List (PkgId × Nat) := []
  prefs : List (Nat × List (Bytes × Json)) := []
  prefsParsed : Std.HashMap String
    (List (Bytes × List (Bytes × Json)) × Option (List (Bytes × List Bytes))) := {}
  /-- blobs `stale_prefs` throws on, with the exception class -/
  prefsBad : Std.HashMap String String := {}
  core : DMod := ⟨⟨none, B "Core"⟩, 0, 0⟩
  uuidcrc : List (Nat × Nat) := []

def unm (what : String) : LErr U := .errorException s!"UNMODELLED {what}"

def lookupL {K V : Type} [BEq K] (xs : List (K × V)) (k : K) : Option V :=
  (xs.find? (fun p => p.1 == k)).map (·.2)

def mkFs (env : Env) : FsOps U :=
  let ent := fun (p : Bytes) => match env.fs.get? (S p) with
    | some e => checkEnt e
    | none => .error (unm s!"stat {S p}")
  { isfile := fun p => do return (← ent p).isFile
    isdir := fun p => do return (← ent p).isDir
    ispath := fun p => do return (← ent p).isPath
    readdir := fun p => match env.readdirs.get? (S p) with
      | some xs => .ok (xs.toArray.qsort (fun a b => S a < S b)).toList
      | none => .error (unm s!"readdir {S p}")
    readdir_unsorted := fun p => match env.readdirs.get? (S p) with
      | some xs => .ok xs
      | none => .error (unm s!"readdir {S p}")
    touch := fun _ => .ok ()
    stat := fun p => do
      let e ← ent p
      return { inode := JInt.wrap .u64 e.ino, mtime := JuliaLean.Promotion.Fl.ofBits e.mtime
               size := i64 e.size }
    read := fun p => .error (unm s!"read {S p}") }

def mkO (env : Env) : LOps U U U U U U U :=
  { baseOps0 with
    pathKernel := "Linux"
    fs := mkFs env
    sys := { isunix := true, islinux := true, isbsd := false, isapple := false,
             iswindows := false, isfreebsd := false, isopenbsd := false, isnetbsd := false,
             isdragonfly := false, isjsvm := false }
    STDLIB := B env.stdlib
    version_major := B env.vmajor
    version_minor := B env.vminor
    crc32c_UUID := fun u => JInt.wrap .u32 ((lookupL env.uuidcrc u.value.val.toNat).getD 0)
    VERSION_EDITION := (i64 env.edition.1, i64 env.edition.2) }

def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0

abbrev O (env : Env) := mkO env
abbrev M (env : Env) (α : Type) := LM (O env) α

section Ops
variable (env : Env)

def getPos : M env Nat := do return (← getW (O env)).timing_imports.val.toNat
def setPos (n : Nat) : M env Unit :=
  modifyW (O env) fun w => { w with timing_imports := i64 n }

def fsEnt (p : Bytes) : M env FsEnt :=
  match env.fs.get? (S p) with
  | some e => liftL (O env) (checkEnt e)
  | none => throwL (O env) (unm s!"stat {S p}")

def fileOf (p : Bytes) : M env FileReg :=
  match env.files.get? (S p) with
  | some f => pure f
  | none => throwL (O env) (unm s!"file {S p}")

/-- `read(io, T)` of `n` bytes: `EOFError` when fewer remain. -/
def readExact (p : Bytes) (n : Nat) : M env (List UInt8) := do
  let f ← fileOf env p
  let pos ← getPos env
  if pos + n > f.bytes.size then
    setPos env f.bytes.size
    throwL (O env) (.jl .eofError)
  setPos env (pos + n)
  return (f.bytes.extract pos (pos + n)).toList

def statOf (p : Bytes) : M env CacheFileStat := do
  let e ← fsEnt env p
  return { device := JInt.wrap .u64 e.dev, inode := JInt.wrap .u64 e.ino
           mode := JInt.wrap .u64 e.mode, size := i64 e.size
           mtime := JuliaLean.Promotion.Fl.ofBits e.mtime
           ctime := JuliaLean.Promotion.Fl.ofBits 0, isPath := e.isPath, isDirectory := e.isDir }

/-- `binunpack(s)` (base/pkgid.jl:38-45). -/
def binunpack (s : Bytes) : M env PkgId := do
  match s with
  | [] => throwL (O env) (.jl .eofError)
  | z :: rest =>
    if z != 0 then throwL (O env) (.assertionError "unexpected data")
    if rest.length < 16 then throwL (O env) (.jl .eofError)
    let uuid := leNat (rest.take 16)
    return JuliaLean.base.pkgid.PkgId_UUID (fun x => x) (uuidOf uuid) (rest.drop 16)

def ioOps : CacheIOOps (O env) Bytes :=
  { openRead := fun p => do
      let e ← fsEnt env p
      if !e.isFile then throwL (O env) (.ioError "could not open")
      let _ ← fileOf env p
      setPos env 0
      return p
    openReadWrite := fun p => throwL (O env) (unm s!"openReadWrite {S p}")
    close := fun _ => pure ()
    readU8 := fun p => do return JInt.wrap .u8 (leNat (← readExact env p 1))
    readU32 := fun p => do return JInt.wrap .u32 (leNat (← readExact env p 4))
    readU64 := fun p => do return JInt.wrap .u64 (leNat (← readExact env p 8))
    readI32 := fun p => do return JInt.wrap .i32 (leNat (← readExact env p 4))
    readI64 := fun p => do return JInt.wrap .i64 (leNat (← readExact env p 8))
    readF64 := fun p => do return JuliaLean.Promotion.Fl.ofBits (leNat (← readExact env p 8))
    u64ToI64 := fun x => do
      if x.val ≥ 2 ^ 63 then throwL (O env) (.jl (.inexactError "Int64"))
      return i64 x.val
    readBytes := fun p n => do
      if n.val < 0 then throwL (O env) (.argumentError "negative length")
      let f ← fileOf env p
      let pos ← getPos env
      let stop := min f.bytes.size (pos + n.val.toNat)
      setPos env (max pos stop)
      return (f.bytes.extract pos stop).toList
    seek := fun _ n => do
      -- `ios_seek` fails for a negative position and beyond the file system's largest offset
      if n.val < 0 || n.val > env.maxSeek then throwL (O env) (.ioError "seek")
      setPos env n.val.toNat
    seekStart := fun _ => setPos env 0
    seekEnd := fun p => do setPos env (← fileOf env p).bytes.size
    position := fun _ => do return i64 (← getPos env)
    filesizeStream := fun p => do return i64 (← fileOf env p).bytes.size
    eof := fun p => do return (← getPos env) ≥ (← fileOf env p).bytes.size
    crc32cStream := fun p len seed => do
      let f ← fileOf env p
      let pos ← getPos env
      if pos != 0 || len.val != f.bytes.size - 4 || seed.val != 0 then
        throwL (O env) (unm s!"crc32c {S p} at {pos} for {len.val}")
      setPos env (pos + len.val.toNat)
      return JInt.wrap .u32 f.crcBody
    crc32cPath := fun p seed => do
      let e ← fsEnt env p
      if !e.isFile then throwL (O env) (.ioError "could not open")
      if seed.val != 0 then throwL (O env) (unm "crc32c seed")
      return JInt.wrap .u32 e.hash
    readVerifyHeader := fun p => do
      let f ← fileOf env p
      if (← getPos env) != 0 then throwL (O env) (unm "verify header not at start")
      setPos env f.pos
      return { status := JInt.wrap .i32 f.status, flags := JInt.wrap .u32 f.flags
               checksum := JInt.wrap .u32 f.checksum }
    statPath := statOf env
    statStream := statOf env
    removeRecursive := fun p => throwL (O env) (unm s!"rm {S p}")
    isFile := fun p => do return (← fsEnt env p).isFile
    isReadable := fun p => do return (← fsEnt env p).readable
    sameFile := fun a b => do
      let x ← fsEnt env a
      let y ← fsEnt env b
      return x.isPath && y.isPath && x.dev == y.dev && x.ino == y.ino
    readdir := fun p => liftL (O env) ((mkFs env).readdir p)
    fileMode := fun st => st.mode
    isSystemError := fun _ => false
    isIOError := fun e => e.isIOError
    float64OfU64 := fun x => JInt.wrap .u64 (JuliaLean.base.float.uitofp .f64 x).toBits
    float64OfI64 := fun x => JInt.wrap .u64 (JuliaLean.base.float.sitofp .f64 x).toBits
    filemodePath := fun p => do return JInt.wrap .u64 (← fsEnt env p).mode
    chmod := fun p _ => throwL (O env) (unm s!"chmod {S p}")
    remove := fun p _ => throwL (O env) (unm s!"rm {S p}")
    move := fun p _ _ => throwL (O env) (unm s!"mv {S p}")
    isDirPath := fun p => p.getLast? == some 47
    pathsep := [47]
    binunpack := binunpack env
    showStringVector := fun _ => []
    bytesToString := S
    logDebug := fun _ => pure () }

def coverageOps : CoverageOps (O env) :=
  { codeCoverage := pure (i64 0)
    mallocLog := pure (i64 0)
    trackedPath := throwL (O env) (unm "tracked path")
    imageCoverageConfig := pure (JInt.wrap .u8 env.imageCov)
    sysimageCoverageConfig := pure (JInt.wrap .u8 env.sysimageCov)
    matchCacheCoverage := fun a b => match env.mcc.get? (a.val.toNat, b.val.toNat) with
      | some r => pure r
      | none => throwL (O env) (unm s!"jl_match_cache_coverage {a.val} {b.val}")
    acceptPlainCoverageCache := fun _ _ => pure ()
    plainCoverageCacheAccepted := fun _ _ => pure false
    pathIsTrackedBy := fun _ _ => throwL (O env) (unm "path_is_tracked")
    convertUInt8 := fun x => do
      if x.val < 0 || x.val > 255 then throwL (O env) (.jl (.inexactError "UInt8"))
      return JInt.wrap .u8 x.val
    sysimageSources := pure none
    isDebugBuild := env.debugBuild }

def validationOps : CacheValidationOps (O env) :=
  { checksumIsValid := fun _ => throwL (O env) (unm "checksums_valid")
    rememberChecksum := fun _ => pure ()
    forgetChecksum := fun _ => pure ()
    generatingOutput := pure false
    objectCachePath := fun p =>
      let stem := if cacheBytesEndsWith p (B ".ji") then p.take (p.length - 3) else p
      pure (stem ++ B "." ++ B env.dlext) }

end Ops

/-- `toml_egal` on the tagged encoding `{"t": type, "v": value}` of the TOML values in
preferences; arrays elementwise, dictionaries as sets of pairs. -/
partial def tomlEgal (a b : Json) : Bool :=
  match (a.getObjVal? "t").toOption, (b.getObjVal? "t").toOption with
  | some (.str "array"), some (.str "array") =>
    match (a.getObjVal? "v" >>= Json.getArr?).toOption, (b.getObjVal? "v" >>= Json.getArr?).toOption with
    | some xs, some ys => xs.size == ys.size && (xs.zip ys).all fun (x, y) => tomlEgal x y
    | _, _ => false
  | some (.str "dict"), some (.str "dict") =>
    match (a.getObjVal? "v" >>= Json.getArr?).toOption, (b.getObjVal? "v" >>= Json.getArr?).toOption with
    | some xs, some ys =>
      let pair := fun (p : Json) => match p.getArr? with
        | .ok ps => (ps[0]!, ps[1]!)
        | .error _ => (Json.null, Json.null)
      xs.size == ys.size && xs.all fun x =>
        let (k, v) := pair x
        ys.any fun y => let (k', v') := pair y; k == k' && tomlEgal v v'
    | _, _ => false
  | _, _ => a == b

def parseUUIDString (s : Bytes) : Option Nat :=
  let str := S s
  let parts := str.splitOn "-"
  if str.length != 36 || parts.map String.length != [8, 4, 4, 4, 12] then none
  else (hexNat (String.join parts)).toOption

section Ops2
variable (env : Env)

def prefOps : PreferenceStalenessOps (O env) Json :=
  { parseBlob := fun blob => match env.prefsParsed.get? (toHex blob) with
      | some r => pure r
      | none => match env.prefsBad.get? (toHex blob) with
        | some c => throwL (O env) (fsErr c)
        | none => throwL (O env) (unm "prefs blob")
    uuidFromString := fun s => match parseUUIDString s with
      | some n => pure (uuidOf n)
      | none => throwL (O env) (.argumentError "invalid UUID")
    preferences := fun u => pure ((lookupL env.prefs u.value.val.toNat).getD [])
    tomlEqual := fun a b => pure (tomlEgal a b) }

def regOps : ModuleRegistryOps (O env) DMod :=
  { moduleUuid := fun m => match m.pkg.uuid with
      | none => (JInt.wrap .u64 0, JInt.wrap .u64 0)
      | some u => (JInt.wrap .u64 (u.value.val.toNat / 2 ^ 64),
                   JInt.wrap .u64 (u.value.val.toNat % 2 ^ 64))
    moduleName := fun m => m.pkg.name
    moduleroot := id
    sameModule := fun a b => decide (a = b)
    moduleBuildIdWords := fun m => pure (JInt.wrap .u64 m.hi, JInt.wrap .u64 m.lo)
    loadedModule := fun p => pure (lookupL env.loaded p)
    setLoadedModule := fun _ _ => throwL (O env) (unm "setLoadedModule")
    popLoadedModule := fun _ => throwL (O env) (unm "popLoadedModule")
    loadedPrecompiles := fun p => pure (lookupL env.precomp p)
    pushLoadedPrecompile := fun _ _ => throwL (O env) (unm "pushLoadedPrecompile")
    loadedModulesOrder := throwL (O env) (unm "loadedModulesOrder")
    pushLoadedModulesOrder := fun _ => throwL (O env) (unm "pushLoadedModulesOrder")
    isRootModule := fun _ => true
    generatingOutput := fun _ => pure false
    disableParallelPrecompile := pure false
    setDisableParallelPrecompile := fun _ => pure ()
    warn := fun _ => pure ()
    identifyPackage := fun _ _ => throwL (O env) (unm "registry identify") }

def fixupOp (p : Bytes) : M env Bytes :=
  match env.fixup.get? (S p) with
  | some q => pure q
  | none => throwL (O env) (unm s!"fixup {S p}")

def staleOps : CacheStalenessOps (O env) Bytes DMod Unit Json :=
  { io := ioOps env
    coverage := coverageOps env
    validation := validationOps env
    includes := { io := ioOps env
                  fixupStdlibPath := fixupOp env
                  directoryHash := fun p => do return JInt.wrap .u32 (← fsEnt env p).hash
                  fileHash := fun p => do
                    let e ← fsEnt env p
                    if !e.isFile then throwL (O env) (.ioError "could not open")
                    return JInt.wrap .u32 e.hash }
    preferences := prefOps env
    registry := regOps env
    cloneTargets := { checkPkgimageClones := fun c => match env.clones.get? (toHex c) with
      | some true => pure (some ())
      | some false => pure none
      | none => throwL (O env) (unm "clone targets") }
    jlMatchCacheFlags := fun a b => match env.mcf.get? (a.val.toNat, b.val.toNat) with
      | some r => pure (JInt.wrap .u8 r)
      | none => throwL (O env) (unm s!"jl_match_cache_flags {a.val} {b.val}")
    usePkgimages := pure env.usePkgimages
    coreModule := env.core
    inSysimage := fun p => pure (env.insys.contains p)
    locatePackageLoadSpec := fun p => match lookupL env.locate p, lookupL env.locateErr p with
      | some r, _ => pure r
      | none, some c => throwL (O env) (fsErr c)
      | none, none => throwL (O env) (unm s!"locate {S p.name}")
    concreteDependencies := pure (env.concrete.map fun (p, b) => (p, u128 b))
    identifyPackage := fun m n =>
      match lookupL env.identify (m, n), lookupL env.identifyErr (m, n) with
      | some r, _ => pure r
      | none, some c => throwL (O env) (fsErr c)
      | none, none => throwL (O env) (unm s!"identify {S m.name} {S n}")
    fixupStdlibPath := fixupOp env
    runtimeFlags := { jlCacheFlags := pure (JInt.wrap .u8 env.jlCacheFlags) } }

/-- Stable `sortperm` returning one-based indices; `rev` orders by `lt(b, a)`. -/
def stableSortperm {K : Type} (lt : K → K → Bool) (rev : Bool) (keys : List K) : List I64 :=
  let lt' := fun (a b : K) => if rev then lt b a else lt a b
  let insert := fun (sorted : List (K × Nat)) (x : K × Nat) =>
    let (before, after) := sorted.span fun y => !lt' x.1 y.1
    before ++ x :: after
  (keys.zipIdx.foldl insert []).map fun (_, i) => i64 (i + 1)

def candidateOps : CacheCandidateOps (O env) :=
  { usePkgimages := pure env.usePkgimages
    sortperm := fun lt rev keys => pure (stableSortperm lt rev keys)
    chopSuffix := fun s suf => if cacheBytesEndsWith s suf then s.take (s.length - suf.length) else s
    libdlExtension := B env.dlext }

def freshestOps : CacheFreshestOps (O env) Bytes DMod Unit Json :=
  { candidates := candidateOps env
    staleness := staleOps env
    cachePathsGet := fun _ => pure none
    staleCacheGet := fun _ => pure none
    staleCacheSet := fun _ _ => pure ()
    beginLoadingCache := pure true
    endLoadingCache := fun _ => pure ()
    updateReasons := fun _ _ => pure ()
    updateUnverified := fun _ _ => pure ()
    formatPkgId := fun p => p.name }

end Ops2

/-! ## Encoding results -/

def encInclude (i : CacheHeaderIncludes) : Json :=
  Json.arr #[encPkg i.id, encBytes i.filename, Json.str (natHex i.fsize.val.toNat),
    Json.num i.hash.val, encFloat i.mtime, Json.arr (i.modpath.map encBytes).toArray]

def encMods (ms : List (PkgId × CacheU128)) : Json :=
  Json.arr (ms.map fun (p, b) => Json.arr #[encPkg p, Json.str (natHex b.val.toNat)]).toArray

def sortStrings (xs : List Bytes) : List Bytes :=
  (xs.toArray.qsort (fun a b => S a < S b)).toList

def encHeader (full : Bool) (h : ParsedCacheHeader) : Json :=
  Json.mkObj [
    ("modules", encMods h.modules),
    ("includes", Json.arr (h.includes.map encInclude).toArray),
    ("srcinc", if full then Json.arr (h.includesSrcFiles.map encInclude).toArray
               else Json.arr ((sortStrings h.srcfiles).map encBytes).toArray),
    ("requires", Json.arr (h.requiredPackages.map fun (a, b) =>
      Json.arr #[encPkg a, encPkg b]).toArray),
    ("req", encMods h.requiredModules),
    ("srcpos", Json.num h.sourceTextPosition.val),
    ("prefs", Json.str (toHex h.preferencesBlob)),
    ("clone", Json.str (toHex h.cloneTargets)),
    ("flags", encFlags h.flags),
    ("syntax", Json.num h.syntaxVersion.val)]

def encDecision (d : CacheStaleDecision DMod) : Json :=
  if d.stale then Json.mkObj [("stale", Json.bool true), ("reasons", encReasons d.reasons)]
  else Json.mkObj [("stale", Json.bool false), ("reasons", encReasons d.reasons),
    ("oc", match d.objectCache with | none => Json.null | some p => encBytes p),
    ("id", Json.str (natHex d.buildId.val.toNat)),
    ("deps", Json.arr (d.dependencies.map fun dep => match dep.loadedModule, dep.loadSpec with
      | some m, _ => Json.mkObj [("m", encPkg m.pkg)]
      | none, some s => Json.mkObj [("k", encPkg dep.package),
          ("b", Json.str (natHex dep.buildId.val.toNat)), ("spec", encSpec s)]
      | none, none => Json.mkObj [("bad", Json.null)]).toArray)]

def runIn (env : Env) {α : Type} (x : M env α) (enc : α → Json) : Json :=
  let w : W := { world0 with depot_path := env.depotPath.map B }
  match (ExceptT.run x).run w with
  | none => Json.mkObj [("err", Json.str "NONTERMINATION")]
  | some (.ok a, _) => enc a
  | some (.error e, _) => Json.mkObj [("err", Json.str (errName e))]

def encOptBytes : Option Bytes → Json
  | none => Json.null
  | some p => encBytes p

def encResolution : CacheDepotResolution → Json
  | .notRelocatable => Json.mkObj [("r", Json.str "not_relocatable")]
  | .noDepotFound => Json.mkObj [("r", Json.str "no_depot_found")]
  | .found d => Json.mkObj [("d", encBytes d)]

/-! ## Cases -/

def runCase (env : Env) (j : Json) : Except String Json := do
  let op ← getS j "op"
  let o := O env
  match op with
  | "replace" =>
    let path ← decBytes (← getK j "path")
    let depots ← getK j "depots"
    let ds ← if depots.isNull then pure none else some <$> ((← arr depots).mapM decBytes)
    return runIn env (replace_depot_path o path ds) encBytes
  | "restore" =>
    let path ← decBytes (← getK j "path")
    let depot ← decBytes (← getK j "depot")
    return runIn env (restore_depot_path o path depot) encBytes
  | "resolve" =>
    let hint ← getK j "hint"
    let h ← if hint.isNull then pure none else some <$> decBytes hint
    let inc ← decBytes (← getK j "inc")
    return runIn env (resolve_depot o inc h) encResolution
  | "normalize" =>
    return runIn env (normalize_depots_for_relocation o)
      fun ds => Json.arr (ds.map encBytes).toArray
  | "flags_from" =>
    return encFlags (CacheFlags_fromUInt8 (JInt.wrap .u8 (← getN j "byte")) (i64 (← getI j "cov")))
  | "flags_to" =>
    let f ← decFlags (← getK j "flags")
    return runIn env (_cacheflag_to_uint8 o (coverageOps env) f) fun b => Json.num b.val
  | "header" =>
    let file ← decBytes (← getK j "file")
    if ← getB j "full" then
      return runIn env (parse_cache_header_file o (ioOps env) file) (encHeader true)
    else
      return runIn env (withValidCacheHeader o (ioOps env) file
        (fun s => _parse_cache_header o (ioOps env) s file)) (encHeader false)
  | "deps" =>
    let file ← decBytes (← getK j "file")
    return runIn env (cache_dependencies_file o (ioOps env) file) fun (mods, files) =>
      Json.arr #[encMods mods, Json.arr (files.map encBytes).toArray]
  | "srctext" =>
    let file ← decBytes (← getK j "file")
    let name ← decBytes (← getK j "name")
    return runIn env (read_dependency_src_file o (ioOps env) file name)
      fun b => Json.str (toHex b)
  | "stale" =>
    let modkey ← decPkg (← getK j "modkey")
    let build := u128 (← hexNat (← getS j "build"))
    let spec ← decSpec (← getK j "spec")
    let file ← decBytes (← getK j "file")
    let flags ← decFlags (← getK j "flags")
    let reasons : Option (AMap Bytes I64) := if (← getB j "reasons") then some [] else none
    let ignoreLoaded ← getB j "ignore_loaded"
    let stalecheck ← getB j "stalecheck"
    let verify ← getB j "verify"
    let split ← getB j "split"
    return runIn env (stale_cachefile o (staleOps env) modkey build spec file
      ignoreLoaded flags reasons stalecheck verify split) encDecision
  | "findall" =>
    let pkg ← decPkg (← getK j "pkg")
    return runIn env (find_all_in_cache_path o (candidateOps env) pkg)
      fun ps => Json.arr (ps.map encBytes).toArray
  | "freshest" =>
    let pkg ← decPkg (← getK j "pkg")
    let flags ← getK j "flags"
    let fl ← if flags.isNull then pure none else some <$> decFlags flags
    let ignoreLoaded ← getB j "ignore_loaded"
    let verify ← getB j "verify"
    return runIn env (compilecache_freshest_path o (freshestOps env) pkg ignoreLoaded
      none none fl verify none none) encOptBytes
  | "relocatable" =>
    let pkg ← decPkg (← getK j "pkg")
    return runIn env (isrelocatable o { freshest := freshestOps env } pkg) Json.bool
  | other => throw s!"unknown op {other}"

/-! ## Environment lines -/

def decFsEnt (j : Json) : Except String (String × FsEnt) := do
  let xs ← arr j
  let p ← S <$> decBytes (← at! xs 0)
  if let .ok c := (← at! xs 1).getStr? then
    return (p, { isPath := false, isFile := false, isDir := false, readable := false, size := 0,
                 mtime := 0, mode := 0, dev := 0, ino := 0, hash := 0, err := some c })
  return (p, { isPath := ← (← at! xs 1).getBool?, isFile := ← (← at! xs 2).getBool?
               isDir := ← (← at! xs 3).getBool?, readable := ← (← at! xs 4).getBool?
               size := ← (← at! xs 5).getInt?, mtime := ← hexNat (← (← at! xs 6).getStr?)
               mode := ← (← at! xs 7).getNat?, dev := ← hexNat (← (← at! xs 8).getStr?)
               ino := ← hexNat (← (← at! xs 9).getStr?), hash := ← (← at! xs 10).getNat? })

def decMod (j : Json) : Except String DMod := do
  let xs ← arr j
  return ⟨← decPkg (← at! xs 0), ← hexNat (← (← at! xs 1).getStr?),
    ← hexNat (← (← at! xs 2).getStr?)⟩

def decPrefs (j : Json) : Except String (List (Bytes × Json)) := do
  (← arr j).mapM fun p => do
    let xs ← arr p
    return (← decBytes (← at! xs 0), ← at! xs 1)

def pairsOf (j : Json) : Except String (List (Json × Json)) := do
  (← arr j).mapM fun p => do
    let xs ← arr p
    return (← at! xs 0, ← at! xs 1)

def applyEnv (env : Env) (j : Json) : Except String Env := do
  let mut env := env
  if has j "depot_path" then
    env := { env with depotPath := ← (← getA j "depot_path").mapM (·.getStr?) }
  if has j "stdlib" then env := { env with stdlib := ← getS j "stdlib" }
  if has j "dlext" then env := { env with dlext := ← getS j "dlext" }
  if has j "vmajor" then env := { env with vmajor := ← getS j "vmajor", vminor := ← getS j "vminor" }
  if has j "edition" then
    let xs ← getA j "edition"
    env := { env with edition := (← (← at! xs 0).getInt?, ← (← at! xs 1).getInt?) }
  if has j "imageCov" then env := { env with imageCov := ← getN j "imageCov" }
  if has j "sysimageCov" then env := { env with sysimageCov := ← getN j "sysimageCov" }
  if has j "jlCacheFlags" then env := { env with jlCacheFlags := ← getN j "jlCacheFlags" }
  if has j "usePkgimages" then env := { env with usePkgimages := ← getB j "usePkgimages" }
  if has j "debugBuild" then env := { env with debugBuild := ← getB j "debugBuild" }
  if has j "maxSeek" then env := { env with maxSeek := ← getI j "maxSeek" }
  if has j "clones" then
    let mut m : Std.HashMap String Bool := env.clones
    for (k, v) in ← pairsOf (← getK j "clones") do
      m := m.insert (← k.getStr?) (← v.getBool?)
    env := { env with clones := m }
  if has j "fixup" then
    let mut m : Std.HashMap String Bytes := env.fixup
    for (k, v) in ← pairsOf (← getK j "fixup") do
      m := m.insert (S (← decBytes k)) (← decBytes v)
    env := { env with fixup := m }
  if has j "identify" then
    let xs ← (← getA j "identify").mapM fun c => do
      let ys ← arr c
      let r ← at! ys 2
      let res ← if r.isNull then pure none else some <$> decPkg r
      return ((← decPkg (← at! ys 0), ← decBytes (← at! ys 1)), res)
    env := { env with identify := xs }
  if has j "locate" then
    let xs ← (← pairsOf (← getK j "locate")).mapM fun (k, r) => do
      let res ← if r.isNull then pure none else some <$> decSpec r
      return (← decPkg k, res)
    env := { env with locate := xs }
  if has j "identifyErr" then
    let xs ← (← getA j "identifyErr").mapM fun c => do
      let ys ← arr c
      return ((← decPkg (← at! ys 0), ← decBytes (← at! ys 1)), ← (← at! ys 2).getStr?)
    env := { env with identifyErr := xs }
  if has j "locateErr" then
    let xs ← (← pairsOf (← getK j "locateErr")).mapM fun (k, c) => do
      return (← decPkg k, ← c.getStr?)
    env := { env with locateErr := xs }
  if has j "loaded" then
    let xs ← (← getA j "loaded").mapM fun c => do
      let m ← decMod c
      return (m.pkg, m)
    env := { env with loaded := xs }
  if has j "precomp" then
    let xs ← (← pairsOf (← getK j "precomp")).mapM fun (k, ms) => do
      return (← decPkg k, ← (← arr ms).mapM decMod)
    env := { env with precomp := xs }
  if has j "insys" then env := { env with insys := ← (← getA j "insys").mapM decPkg }
  if has j "concrete" then
    let xs ← (← pairsOf (← getK j "concrete")).mapM fun (k, b) => do
      return (← decPkg k, ← hexNat (← b.getStr?))
    env := { env with concrete := xs }
  if has j "prefs" then
    let xs ← (← pairsOf (← getK j "prefs")).mapM fun (u, ps) => do
      return (← hexNat (← u.getStr?), ← decPrefs ps)
    env := { env with prefs := xs }
  if has j "prefsParsed" then
    let mut m := env.prefsParsed
    for c in ← getA j "prefsParsed" do
      let xs ← arr c
      if let .ok cls := (← at! xs 1).getStr? then
        env := { env with prefsBad := env.prefsBad.insert (← (← at! xs 0).getStr?) cls }
        continue
      let observed ← (← pairsOf (← at! xs 1)).mapM fun (u, ps) => do
        return (← decBytes u, ← decPrefs ps)
      let u ← at! xs 2
      let unset ← if u.isNull then pure none else some <$> (← pairsOf u).mapM fun (k, ks) => do
        return (← decBytes k, ← (← arr ks).mapM decBytes)
      m := m.insert (← (← at! xs 0).getStr?) (observed, unset)
    env := { env with prefsParsed := m }
  if has j "core" then env := { env with core := ← decMod (← getK j "core") }
  if has j "uuidcrc" then
    let xs ← (← pairsOf (← getK j "uuidcrc")).mapM fun (u, c) => do
      return (← hexNat (← u.getStr?), ← c.getNat?)
    env := { env with uuidcrc := xs }
  return env

def applyLine (env : Env) (j : Json) : Except String Env := do
  if let .ok f := getK j "F" then
    let xs ← arr (← getK f "verify")
    let reg : FileReg := { bytes := ← hexBytes (← getS f "hex"), status := ← (← at! xs 0).getInt?
                           flags := ← (← at! xs 1).getNat?, checksum := ← (← at! xs 2).getNat?
                           pos := ← (← at! xs 3).getNat?, crcBody := ← getN f "crc" }
    return { env with files := env.files.insert (S (← decBytes (← getK f "p"))) reg }
  if let .ok fs := getK j "FS" then
    let mut m := env.fs
    for e in ← arr fs do
      let (p, ent) ← decFsEnt e
      m := m.insert p ent
    return { env with fs := m }
  if let .ok rd := getK j "RD" then
    let mut m := env.readdirs
    for (d, xs) in ← pairsOf rd do
      m := m.insert (S (← decBytes d)) (← (← arr xs).mapM decBytes)
    return { env with readdirs := m }
  if let .ok t := getK j "MCF" then
    let mut m := env.mcf
    for e in ← arr t do
      let xs ← arr e
      m := m.insert ((← (← at! xs 0).getNat?), (← (← at! xs 1).getNat?)) (← (← at! xs 2).getNat?)
    return { env with mcf := m }
  if let .ok t := getK j "MCC" then
    let mut m := env.mcc
    for e in ← arr t do
      let xs ← arr e
      m := m.insert ((← (← at! xs 0).getNat?), (← (← at! xs 1).getNat?)) (← (← at! xs 2).getBool?)
    return { env with mcc := m }
  if let .ok e := getK j "ENV" then return ← applyEnv env e
  throw "unknown line"

end LoadingDiff

open LoadingDiff in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut env : Env := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if line.all Char.isWhitespace then continue
    match Json.parse line with
    | .error e => stdout.putStrLn (Json.mkObj [("error", Json.str s!"parse: {e}")]).compress
    | .ok j =>
      if has j "op" then
        let id := (j.getObjVal? "id").toOption.getD Json.null
        match runCase env j, getK j "exp" with
        | .ok got, .ok exp =>
          if got == exp then
            stdout.putStrLn (Json.mkObj [("id", id), ("agree", Json.bool true)]).compress
          else
            stdout.putStrLn (Json.mkObj [("id", id), ("agree", Json.bool false),
              ("got", got), ("exp", exp)]).compress
        | .error e, _ | _, .error e =>
          stdout.putStrLn (Json.mkObj [("id", id), ("error", Json.str e)]).compress
      else
        match applyLine env j with
        | .ok env' => env := env'
        | .error e => stdout.putStrLn (Json.mkObj [("error", Json.str s!"line: {e}")]).compress
    stdout.flush
  return 0
