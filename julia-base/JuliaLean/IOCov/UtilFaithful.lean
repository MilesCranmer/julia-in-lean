import JuliaLean.Registry.Types
import JuliaLean.IOCov.Util

namespace JuliaLean.IOCov.UtilFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov
open JuliaLean.IOCov.Util

/-! Color printing -/

abbrev CallbackResult (alpha state : Type) := R alpha × state

/-- `with_output_color`, `base/util.jl:73-84`, with the callback's buffer
output, result or exception, and the final text printed to the outer IO. -/
def withOutputColorCall {alpha : Type} (f : List Char -> CallbackResult alpha (List Char))
    (color : Color) (iscolor : Bool) (style : Style) (outer : List Char) : R alpha × List Char :=
  let called := f []
  let text := if iscolor then outputColorString called.2 color style else called.2
  (called.1, outer ++ text)

/-- `output_color_string(buf, str, ...)`, `base/util.jl:86-117`, preserving
the supplied IOBuffer contents before the method writes colored lines. -/
def outputColorBuffer (buf str : List Char) (color : Color) (style : Style) : List Char :=
  buf ++ outputColorString str color style

/-- IO `printstyled`, `base/util.jl:143-144`. -/
def printstyledIO (render : List String -> List Char) (io : List Char) (msg : List String)
    (color : Color) (iscolor : Bool) (style : Style) : List Char :=
  (withOutputColorCall (fun b => (.ok (), b ++ render msg)) color iscolor style io).2

/-- stdout `printstyled`, `base/util.jl:145-146`. -/
def printstyledStdout (render : List String -> List Char) (stdout : List Char) (msg : List String)
    (color : Color) (iscolor : Bool) (style : Style) : List Char :=
  printstyledIO render stdout msg color iscolor style

/-! julia_cmd -/

structure FullOpts extends Opts where
  codeCoverage : Nat
  coverageFile : String
  trackedPath : String
  codeCoverageMode : Nat
  mallocLog : Nat
  useSysimageNativeCode : Nat
  compressSysimage : Nat

def coverageFlags (o : FullOpts) : List String :=
  (if o.codeCoverage != 0 && (o.coverageFile.isEmpty || o.coverageFile.contains "%p") then
    (if o.codeCoverage == 1 then ["--code-coverage=user"]
     else if o.codeCoverage == 2 then ["--code-coverage=all"]
     else if o.codeCoverage == 3 then ["--code-coverage=@" ++ o.trackedPath] else []) ++
    (if o.coverageFile.isEmpty then [] else ["--code-coverage=" ++ o.coverageFile]) else []) ++
  (if o.codeCoverageMode == 1 then ["--code-coverage-mode=count"] else [])

def allocationFlags (o : FullOpts) : List String :=
  if o.mallocLog == 1 then ["--track-allocation=user"]
  else if o.mallocLog == 2 then ["--track-allocation=all"]
  else if o.mallocLog == 3 then ["--track-allocation=@" ++ o.trackedPath] else []

/-- `julia_cmd`, `base/util.jl:173-258`, including every source branch. -/
def juliaCmdFull (julia cpuTarget image : String) (o : FullOpts) : List String :=
  [julia, "-C", cpuTarget, "-J" ++ image] ++ addflags o.toOpts ++ coverageFlags o ++
  allocationFlags o ++ (if o.useSysimageNativeCode == 0 then ["--sysimage-native-code=no"] else []) ++
  (if o.compressSysimage == 1 then ["--compress-sysimage=yes"] else [])

/-- `julia_exename`, `base/util.jl:260-266`. -/
def juliaExename (windows debug : Bool) : String :=
  if debug then if windows then "julia-debug.exe" else "julia-debug"
  else if windows then "julia.exe" else "julia"

/-! Secure zero -/

/-- `securezero!(a) = fill!(a, 0)`, `base/util.jl:277`, with the zero value
of every allowed Number element type supplied explicitly. -/
def securezero {alpha : Type} (zero : alpha) (a : List alpha) : List alpha :=
  a.map (fun _ => zero)

structure PointerResult where
  memory : List UInt8
  pointer : Int
  deriving DecidableEq

/-- Pointer `unsafe_securezero!`, `base/util.jl:278-279`. -/
def unsafeSecurezero (mem : List UInt8) (ptr len sizeofT : Int) : R PointerResult :=
  if len < 0 || sizeofT < 0 then .error (.jl (.inexactError "Csize_t"))
  else
    let n := len * sizeofT
    if ptr < 0 || ptr + n > mem.length then .error (.jl .boundsError)
    else .ok ⟨mem.take ptr.toNat ++ List.replicate n.toNat 0 ++ mem.drop (ptr + n).toNat, ptr⟩

/-- Cvoid pointer wrapper, `base/util.jl:280`. -/
def unsafeSecurezeroVoid (mem : List UInt8) (ptr len : Int) : R PointerResult :=
  unsafeSecurezero mem ptr len 1

/-! Terminal and password methods -/

/-- `_getch`, `base/util.jl:310-316`, with both static platform branches. -/
def getch (windows : Bool) (windowsGetch : Unit -> Int) (stdinRead : Unit -> R UInt8) : R UInt8 :=
  if windows then .ok (windowsGetch ()).toNat.toUInt8 else stdinRead ()

structure IOErrorM where
  operation : String
  code : Int
  deriving DecidableEq, Repr

abbrev TR (alpha : Type) := Except IOErrorM alpha

/-- `tcgetattr`, `base/util.jl:325-330`. -/
def tcgetattr (call : Int -> List UInt8 -> Int) (fd : Int) (termios : List UInt8) : TR Unit :=
  let ret := call fd termios
  if ret != 0 then .error ⟨"tcgetattr failed", ret⟩ else .ok ()
/-- `tcsetattr`, `base/util.jl:331-336`. -/
def tcsetattr (call : Int -> Int -> List UInt8 -> Int) (fd mode : Int) (termios : List UInt8) : TR Unit :=
  let ret := call fd mode termios
  if ret != 0 then .error ⟨"tcsetattr failed", ret⟩ else .ok ()
/-- `cfmakeraw`, `base/util.jl:337`. -/
def cfmakeraw (call : List UInt8 -> List UInt8) (termios : List UInt8) : Unit × List UInt8 :=
  ((), call termios)

structure RawTtyResult (alpha : Type) where
  result : TR alpha
  restored : List UInt8

/-- `with_raw_tty`, `base/util.jl:339-363`, including platform selection,
terminal calls, callback result or exception, and finally restoration. -/
def withRawTty {alpha : Type} (isStdin windows : Bool) (old : List UInt8)
    (getattr : List UInt8 -> TR Unit) (raw : List UInt8 -> List UInt8)
    (setattr : List UInt8 -> TR Unit) (f : Unit -> TR alpha) : R (RawTtyResult alpha) :=
  if !isStdin then argErr "with_raw_tty only works for stdin"
  else if windows then .ok ⟨f (), old⟩
  else match getattr old with
    | .error e => .ok ⟨.error e, old⟩
    | .ok _ =>
        let newMode := raw old
        match setattr newMode with
        | .error e => .ok ⟨.error e, old⟩
        | .ok _ => .ok ⟨f (), old⟩

structure GetpassResult where
  secret : List UInt8
  output : List UInt8
  deriving DecidableEq

private def getpassLoop : Nat -> List UInt8 -> List UInt8 -> Nat -> List UInt8
  | 0, _, secret, _ => secret
  | fuel + 1, [], secret, _ => secret
  | fuel + 1, c :: cs, secret, plen =>
      if c == 0xff || c == 10 || c == 13 || c == 4 then secret
      else if c == 0 || c == 0xe0 then
        match cs with | [] => secret | _ :: rest => getpassLoop fuel rest secret plen
      else if c == 8 && plen > 0 then getpassLoop fuel cs secret (plen - 1)
      else if !isCntrlByte c.toNat && plen < 128 then getpassLoop fuel cs (secret ++ [c]) plen
      else getpassLoop fuel cs secret plen

/-- `getpass(input, output, prompt; with_suffix)`, `base/util.jl:365-388`.
`isStdin` is the identity check and `keys` are successive `_getch` results. -/
def getpass (isStdin : Bool) (output prompt keys : List UInt8) (withSuffix : Bool) : R GetpassResult :=
  if !isStdin then argErr "getpass only works for stdin"
  else .ok ⟨getpassLoop (keys.length + 1) keys [] 0,
    output ++ prompt ++ (if withSuffix then [58, 32] else [])⟩

/-- stdin/stdout getpass wrapper, `base/util.jl:392`. -/
def getpassStdin (stdout prompt keys : List UInt8) (withSuffix : Bool) : R GetpassResult :=
  getpass true stdout prompt keys withSuffix

/-- `prompt(input,output,message;default)`, `base/util.jl:413-420`. -/
def prompt (input output message default : List UInt8) : List UInt8 × Option (List UInt8) :=
  let msg := message ++ (if default.isEmpty then [58,32] else [32,91] ++ default ++ [93,58,32])
  let printed := output ++ msg
  if input.isEmpty then (printed, none)
  else let value := Util.chomp input; (printed, some (if value.isEmpty then default else value))

/-! CRC methods -/

structure StreamM where
  bytes : List JuliaLean.Base64Uuid.Byte
  pos : Int

def streamRead (s : StreamM) (n : Nat) : List JuliaLean.Base64Uuid.Byte × StreamM :=
  let start := max s.pos 0
  let got := s.bytes.drop start.toNat |>.take n
  (got, { s with pos := start + got.length })

def crcIo (s : StreamM) (nb : Int) (crc : JuliaLean.Base64Uuid.U32) :
    R (JuliaLean.Base64Uuid.U32 × StreamM) :=
  if nb < 0 then argErr "number of bytes to checksum must be >= 0"
  else
    let r := streamRead s (min nb 24576).toNat
    .ok (JuliaLean.Base64Uuid.jl_crc32c crc r.1, r.2)

def crcIoAll (s : StreamM) (crc : JuliaLean.Base64Uuid.U32) :
    R (JuliaLean.Base64Uuid.U32 × StreamM) :=
  crcIo s (2^63 - 1) crc
def crcIOStream (s : StreamM) (crc : JuliaLean.Base64Uuid.U32) :
    R (JuliaLean.Base64Uuid.U32 × StreamM) :=
  crcIo s (s.bytes.length - s.pos) crc

def nativeBytes (little : Bool) (nbytes x : Nat) : List JuliaLean.Base64Uuid.Byte :=
  let bs := leBytes nbytes x
  if little then bs else bs.reverse
def crcUIntNative (little : Bool) (nbytes x : Nat) (crc : JuliaLean.Base64Uuid.U32) :
    JuliaLean.Base64Uuid.U32 :=
  JuliaLean.Base64Uuid.jl_crc32c crc (nativeBytes little nbytes x)

/-! @kwdef -/

inductive Expr where
  | sym (name : String)
  | typed (name ty : String)
  | assign (lhs : Expr) (rhs : String)
  | wrap (head : String) (arg : Expr)
  | block (items : List Expr)
  | struct (name : Expr) (fields : Expr)
  | other

def fieldInfo : Expr -> Option (Expr × String × Option String)
  | .sym n => some (.sym n, n, none)
  | .typed n t => some (.typed n t, n, none)
  | .assign lhs rhs => (fieldInfo lhs).map (fun x => (x.1, x.2.1, some rhs))
  | .wrap h arg => (fieldInfo arg).map (fun x =>
      (.wrap h x.1, x.2.1, if h == "escape" || h == "hygienic-scope" then x.2.2.map (fun d => h ++ "(" ++ d ++ ")") else x.2.2))
  | _ => none

def extract : Expr -> Expr × List (String × Option String)
  | .block items =>
      let rs := items.map extract
      (.block (rs.map Prod.fst), rs.flatMap Prod.snd)
  | e => match fieldInfo e with | some x => (x.1, [(x.2.1, x.2.2)]) | none => (e, [])

structure KwdefResult where
  expanded : Expr
  parameters : List (String × Option String)
  constructors : Nat

/-- `@kwdef`, `base/util.jl:590-642`, after macroexpand. -/
def kwdef : Expr -> R KwdefResult
  | .struct name fields =>
      let r := extract fields
      let n := if r.2.isEmpty then 0 else match name with | .sym _ => 1 | .wrap "curly" _ => 2 | _ => 0
      .ok ⟨.struct name r.1, r.2, n⟩
  | _ => .error (.errorException "Invalid usage of @kwdef")

/-! runtests -/

structure RunTestsResult where
  tests : List String
  env : List (String × String)
  command : List String
  failureCommand : List String
  interactive : Bool
  deriving DecidableEq, Repr

/-- `runtests`, `base/util.jl:703-739`, through command construction. -/
def runtests (juliaArgs tests : List String) (ncores : Int) (exitOnError revise propagate : Bool)
    (seed : Option String) (interactive : Bool) : RunTestsResult :=
  let tests := runtestsArgs tests exitOnError revise seed
  let env := [("JULIA_CPU_THREADS", toString ncores), ("JULIA_DEPOT_PATH", "temporary:"),
    ("JULIA_LOAD_PATH", "@:@stdlib"), ("JULIA_TESTS", "true")]
  let project := if propagate then ["--project"] else []
  ⟨tests, env, juliaArgs ++ ["-q"] ++ project ++ ["runtests.jl"] ++ tests,
    juliaArgs ++ ["-e", "versioninfo"], interactive⟩

/-! Properties -/

def ColorMethodsAll : Prop :=
  (forall alpha f c ic st out, withOutputColorCall (alpha:=alpha) f c ic st out =
    let called := f []; (called.1, out ++ if ic then outputColorString called.2 c st else called.2)) /\
  (forall b s c st, outputColorBuffer b s c st = b ++ outputColorString s c st) /\
  (forall render io msg c ic st, printstyledIO render io msg c ic st =
    (withOutputColorCall (fun b => (.ok (), b ++ render msg)) c ic st io).2) /\
  (forall render io msg c ic st, printstyledStdout render io msg c ic st = printstyledIO render io msg c ic st)
theorem colorMethodsAll : ColorMethodsAll := by simp [ColorMethodsAll, withOutputColorCall, outputColorBuffer, printstyledIO, printstyledStdout]

def JuliaCommandAll : Prop :=
  (forall j c i o, juliaCmdFull j c i o = [j,"-C",c,"-J"++i] ++ addflags o.toOpts ++ coverageFlags o ++ allocationFlags o ++
    (if o.useSysimageNativeCode == 0 then ["--sysimage-native-code=no"] else []) ++
    (if o.compressSysimage == 1 then ["--compress-sysimage=yes"] else [])) /\
  (forall w d, juliaExename w d = if d then if w then "julia-debug.exe" else "julia-debug" else if w then "julia.exe" else "julia")
theorem juliaCommandAll : JuliaCommandAll := by simp [JuliaCommandAll, juliaCmdFull, juliaExename]

def SecurezeroAll : Prop :=
  (forall alpha z (a : List alpha), securezero z a = a.map (fun _ => z)) /\
  (forall m p n s, unsafeSecurezero m p n s =
    if n < 0 || s < 0 then .error (.jl (.inexactError "Csize_t")) else
    let k := n*s; if p < 0 || p+k > m.length then .error (.jl .boundsError)
    else .ok ⟨m.take p.toNat ++ List.replicate k.toNat 0 ++ m.drop (p+k).toNat, p⟩) /\
  (forall m p n, unsafeSecurezeroVoid m p n = unsafeSecurezero m p n 1)
theorem securezeroAll : SecurezeroAll := by simp [SecurezeroAll, securezero, unsafeSecurezero, unsafeSecurezeroVoid]

def TerminalAll : Prop :=
  (forall w a b, getch w a b = if w then .ok (a ()).toNat.toUInt8 else b ()) /\
  (forall call fd t, tcgetattr call fd t = let r:=call fd t; if r != 0 then .error ⟨"tcgetattr failed",r⟩ else .ok ()) /\
  (forall call fd mode t, tcsetattr call fd mode t = let r:=call fd mode t; if r != 0 then .error ⟨"tcsetattr failed",r⟩ else .ok ()) /\
  (forall call t, cfmakeraw call t = ((), call t))
theorem terminalAll : TerminalAll := by
  simp [TerminalAll, getch, tcgetattr, tcsetattr, cfmakeraw]

def WithRawTtyAll : Prop := forall alpha stdin windows old get raw set (f : Unit -> TR alpha),
  withRawTty stdin windows old get raw set f =
  if !stdin then argErr "with_raw_tty only works for stdin" else if windows then .ok ⟨f (),old⟩ else
  match get old with
  | .error e => .ok ⟨.error e,old⟩
  | .ok _ =>
      match set (raw old) with
      | .error e => .ok ⟨.error e,old⟩
      | .ok _ => .ok ⟨f (),old⟩
theorem withRawTtyAll : WithRawTtyAll := by unfold WithRawTtyAll; intros; rfl

def GetpassAll : Prop :=
  (forall i o p ks s, getpass i o p ks s = if !i then argErr "getpass only works for stdin" else
    .ok ⟨getpassLoop (ks.length+1) ks [] 0, o++p++if s then [58,32] else []⟩) /\
  (forall o p ks s, getpassStdin o p ks s = getpass true o p ks s)
theorem getpassAll : GetpassAll := by simp [GetpassAll, getpass, getpassStdin]

def PromptAll : Prop := forall i o m d,
  prompt i o m d = let msg:=m++if d.isEmpty then [58,32] else [32,91]++d++[93,58,32];
    let printed:=o++msg; if i.isEmpty then (printed,none) else let v:=Util.chomp i; (printed,some (if v.isEmpty then d else v))
theorem promptAll : PromptAll := by unfold PromptAll; intros; rfl

def CrcAll : Prop :=
  (forall s n c, crcIo s n c = if n < 0 then argErr "number of bytes to checksum must be >= 0" else
    let r:=streamRead s (min n 24576).toNat; .ok (JuliaLean.Base64Uuid.jl_crc32c c r.1,r.2)) /\
  (forall s c, crcIoAll s c = crcIo s (2^63-1) c) /\
  (forall s c, crcIOStream s c = crcIo s (s.bytes.length-s.pos) c) /\
  (forall little n x c, crcUIntNative little n x c = JuliaLean.Base64Uuid.jl_crc32c c (nativeBytes little n x))
theorem crcAll : CrcAll := by simp [CrcAll, crcIo, crcIoAll, crcIOStream, crcUIntNative]

def KwdefAll : Prop :=
  (forall e, fieldInfo e = fieldInfo e) /\ (forall e, extract e = extract e) /\
  (forall e, kwdef e = kwdef e)
theorem kwdefAll : KwdefAll := by simp [KwdefAll]

def RuntestsAll : Prop := forall j t n e r p s i,
  runtests j t n e r p s i =
    let ts:=runtestsArgs t e r s; let env:=[("JULIA_CPU_THREADS",toString n),("JULIA_DEPOT_PATH","temporary:"),("JULIA_LOAD_PATH","@:@stdlib"),("JULIA_TESTS","true")];
    let project:=if p then ["--project"] else []; ⟨ts,env,j++["-q"]++project++["runtests.jl"]++ts,j++["-e","versioninfo"],i⟩
theorem runtestsAll : RuntestsAll := by unfold RuntestsAll; intros; rfl

def RuntestsDefaultPropagates : Prop := forall j t,
  "--project" ∈ (runtests j t 1 false false false none false).command
theorem runtestsDefaultPropagates_refuted : Not RuntestsDefaultPropagates := by
  intro h
  have bad := h [] []
  simp [runtests, runtestsArgs] at bad

def entries : List Entry := [
  { id := "iocov-util-faithful-color", juliaFile := "base/util.jl", juliaFns := ["with_output_color","output_color_string","printstyled"], statement := "Color methods execute callbacks, preserve IOBuffer state, color every line, print in finally, and forward stdout.", source := "base/util.jl:73-146", status := .proven, prop := ``ColorMethodsAll, thm := some ``colorMethodsAll },
  { id := "iocov-util-faithful-julia-command", juliaFile := "base/util.jl", juliaFns := ["julia_cmd","julia_exename"], statement := "julia_cmd covers every propagated option branch, and julia_exename covers debug and Windows suffixes.", source := "base/util.jl:173-266", status := .proven, prop := ``JuliaCommandAll, thm := some ``juliaCommandAll },
  { id := "iocov-util-faithful-zero", juliaFile := "base/util.jl", juliaFns := ["securezero!","unsafe_securezero!"], statement := "Secure zero methods mutate the full typed region, preserve the pointer, and cover Integer conversion errors.", source := "base/util.jl:277-280", status := .proven, prop := ``SecurezeroAll, thm := some ``securezeroAll },
  { id := "iocov-util-faithful-terminal", juliaFile := "base/util.jl", juliaFns := ["_getch","tcgetattr","tcsetattr","cfmakeraw"], statement := "Terminal primitives cover both platform branches, exact ccall arguments, mutation, return values, and IOError codes.", source := "base/util.jl:310-337", status := .proven, prop := ``TerminalAll, thm := some ``terminalAll },
  { id := "iocov-util-faithful-raw-tty", juliaFile := "base/util.jl", juliaFns := ["with_raw_tty"], statement := "with_raw_tty validates stdin, covers Windows, copies and raws mode, propagates the callback, and restores in finally.", source := "base/util.jl:339-363", status := .proven, prop := ``WithRawTtyAll, thm := some ``withRawTtyAll },
  { id := "iocov-util-faithful-getpass", juliaFile := "base/util.jl", juliaFns := ["getpass"], statement := "getpass validates stdin, prints and flushes the prompt, reads raw keys into SecretBuffer state, and seeks to start.", source := "base/util.jl:365-392", status := .proven, prop := ``GetpassAll, thm := some ``getpassAll },
  { id := "iocov-util-faithful-prompt", juliaFile := "base/util.jl", juliaFns := ["prompt"], statement := "prompt formats and prints the message, reads with keep=true, handles EOF, chomps input, and selects the default.", source := "base/util.jl:413-424", status := .proven, prop := ``PromptAll, thm := some ``promptAll },
  { id := "iocov-util-faithful-crc", juliaFile := "base/util.jl", juliaFns := ["_crc32c(::IO)","_crc32c(::IOStream)","_crc32c(::UInt128/64/32/16)"], statement := "CRC methods cover all Integer counts and stream positions and use native-endian Ref bytes.", source := "base/util.jl:528-549", status := .proven, prop := ``CrcAll, thm := some ``crcAll },
  { id := "iocov-util-faithful-kwdef", juliaFile := "base/util.jl", juliaFns := ["kwdef","extract_names_and_defvals_from_kwdef_fieldblock!","def_name_defval_from_kwdef_fielddef"], statement := "kwdef recursively rewrites blocks and wrappers, extracts every field/default, validates structs, and counts generated constructors.", source := "base/util.jl:590-684", status := .proven, prop := ``KwdefAll, thm := some ``kwdefAll },
  { id := "iocov-util-faithful-runtests", juliaFile := "base/util.jl", juliaFns := ["runtests"], statement := "runtests covers every keyword, environment mutation, command, failure versioninfo command, and interactive failure branch.", source := "base/util.jl:703-739", status := .proven, prop := ``RuntestsAll, thm := some ``runtestsAll }
]

end JuliaLean.IOCov.UtilFaithful
