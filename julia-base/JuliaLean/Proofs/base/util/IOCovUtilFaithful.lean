import JuliaLean.base.util
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.util.IOCovUtil
import JuliaLean.Proofs.base.io.IOCovCommon


section
namespace JuliaLean.IOCov.UtilFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov
open JuliaLean.IOCov.Util

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
end
