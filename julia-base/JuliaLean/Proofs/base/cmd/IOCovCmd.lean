import JuliaLean.Registry.Types
import JuliaLean.base.cmd

/-!
Method-specific models for the remaining definitions in `base/cmd.jl` at Julia
master `bbfa0ce4150`.  The string and `Cmd` primitives are shared with the
`ShellCmd` area; every definition below follows one source method.
-/

namespace JuliaLean.IOCov.Cmd

open JuliaLean JuliaLean.Registry
open JuliaLean.ShellCmd

/-! ## Quantified properties -/

def CmdExecDefaults : Prop := forall exec, cmdExec exec = cmdOf exec
theorem cmdExecDefaults : CmdExecDefaults := by intro; rfl

def CmdCopyFields : Prop := forall c i f e d same cp u g,
  cmdCopy c i f e d same cp u g = do
    let d <- if same then pure d else cstr d
    pure (CmdM.mk c.exec i f e d cp u g)
theorem cmdCopyFields : CmdCopyFields := by
  intro c i f e d same cp u g
  rfl

def CmdKeywordsFields : Prop := forall c i e d same cp u g a v h,
  cmdKeywords c i e d same cp u g a v h = do
    let d <- if same then pure d else cstr d
    pure (CmdM.mk c.exec i (keywordFlags a v h) e d cp u g)
theorem cmdKeywordsFields : CmdKeywordsFields := by
  intro c i e d same cp u g a v h
  rfl

def HasNondefaultCorrect : Prop := forall c, hasNondefault c = hasNondefaultFlags c
theorem hasNondefaultCorrect : HasNondefaultCorrect := by intro; rfl

def BinaryConstructorsCorrect : Prop := forall a b,
  orCmds a b = ⟨a,b⟩ /\ errOrCmds a b = ⟨a,b⟩ /\ andCmds a b = ⟨a,b⟩
theorem binaryConstructorsCorrect : BinaryConstructorsCorrect := by
  simp [BinaryConstructorsCorrect, orCmds, errOrCmds, andCmds]

def AndMethodsCorrect : Prop := forall hashf x y h,
  hashAnd hashf x h = hashf x.a (hashf x.b h) /\
    eqAnd x y = (x.a == y.a && x.b == y.b)
theorem andMethodsCorrect : AndMethodsCorrect := by
  simp [AndMethodsCorrect, hashAnd, eqAnd]

def EscapeForwardingCorrect : Prop := forall c special,
  shellEscapeCmd c special = shellEscape c.exec special /\
  shellEscapePosixlyCmd c = shellEscapePosixly c.exec /\
  shellEscapeCshCmd c = shellEscapeCsh c.exec /\
  escapeMicrosoftCmd c = escapeMicrosoftCArgs c.exec /\
  escapeMicrosoftCmdIO c = escapeMicrosoftCArgs c.exec
theorem escapeForwardingCorrect : EscapeForwardingCorrect := by
  simp [EscapeForwardingCorrect, shellEscapeCmd, shellEscapePosixlyCmd, shellEscapeCshCmd,
    escapeMicrosoftCmd, escapeMicrosoftCmdIO]

def SensitiveNameCorrect : Prop := forall name,
  isSensitiveEnvName name = (sensitiveParts name).any (fun p => sensitivePatterns.contains p)
theorem sensitiveNameCorrect : SensitiveNameCorrect := by intro; rfl

def ShowEnvModeCorrect : Prop :=
  (forall env, getShowEnvMode .wrongType env = .error .typeError) /\
  getShowEnvMode .unset none = .ok .redact /\
  (forall m env, getShowEnvMode (.mode m) env = .ok m)
theorem showEnvModeCorrect : ShowEnvModeCorrect := by simp [ShowEnvModeCorrect, getShowEnvMode]

def CompositeShowCorrect : Prop := forall render kind x,
  showOrCmds render kind x = S "pipeline(" ++ render x.a ++ S ", " ++
    (if kind == .stderr then S "stderr=" else S "stdout=") ++ render x.b ++ S ")" /\
  showAndCmds render x = render x.a ++ S " & " ++ render x.b
theorem compositeShowCorrect : CompositeShowCorrect := by
  simp [CompositeShowCorrect, showOrCmds, showAndCmds]

def FileRedirectCorrect : Prop := forall w f a,
  (fileRedirectAbstract w f a).filename = f /\
  (fileRedirectAbstract w f a).append = a /\
  (fileRedirectAbstract w f a).warned =
    (f.map lowerAscii == if w then S "nul" else S "/dev/null")
theorem fileRedirectCorrect : FileRedirectCorrect := by
  simp [FileRedirectCorrect, fileRedirectAbstract, fileRedirectString]

def RawHandleCorrect : Prop := forall n b,
  rawhandleDevNull = .null /\ rawhandleOS n = .handle n /\ rawhandleFD n = .handle n /\
    setupStdio (.handle n) b = (.handle n, false)
theorem rawHandleCorrect : RawHandleCorrect := by
  simp [RawHandleCorrect, rawhandleDevNull, rawhandleOS, rawhandleFD, setupStdio]

def CmdRedirectCorrect : Prop := forall c h n,
  (cmdRedirect3 c h n).readable = (n == 0) /\
  (cmdRedirect3 c h n).cmd = c /\ (cmdRedirect3 c h n).handle = h
theorem cmdRedirectCorrect : CmdRedirectCorrect := by
  simp [CmdRedirectCorrect, cmdRedirect3]

def ShowCmdRedirectCorrect : Prop := forall rc rh c,
  showCmdRedirect rc rh c =
    let stream := if c.streamNo == 1 then S "stdout" else if c.streamNo == 2 then S "stderr"
      else if c.streamNo == 0 then S "stdin" else S (toString c.streamNo)
    S "pipeline(" ++ rc c.cmd ++ S ", " ++ stream ++
      (if c.readable then S "<" else S ">") ++ rh c.handle ++ S ")"
theorem showCmdRedirectCorrect : ShowCmdRedirectCorrect := by
  simp [ShowCmdRedirectCorrect, showCmdRedirect]

def IgnoreStatusCorrect : Prop := forall c b r,
  (ignoreStatusCmd c).ignorestatus = true /\
  (ignoreStatusBinary b).a.ignorestatus = true /\
  (ignoreStatusBinary b).b.ignorestatus = true /\
  (ignoreStatusRedirect r).cmd.ignorestatus = true
theorem ignoreStatusCorrect : IgnoreStatusCorrect := by
  simp [IgnoreStatusCorrect, ignoreStatusCmd, ignoreStatusBinary, ignoreStatusRedirect]

def DetachCorrect : Prop := forall c,
  (detachCmd c).flags = keywordFlags true (c.flags &&& 4 != 0) (c.flags &&& 16 != 0)
theorem detachCorrect : DetachCorrect := by simp [DetachCorrect, detachCmd]

def ByteenvCorrect : Prop := forall xs kvs,
  byteenvArray xs = xs.mapM cstr /\ byteenvDict kvs = byteenvPairs kvs /\
  byteenvNothing = none /\ byteenvPairList kvs = byteenvPairs kvs
theorem byteenvCorrect : ByteenvCorrect := by
  simp [ByteenvCorrect, byteenvArray, byteenvDict, byteenvNothing, byteenvPairList]

def CstrCorrect : Prop := forall s,
  cstr s = if s.contains (A '\x00') then
    .error (.jl (.argumentError "strings containing NUL cannot be passed to spawned processes"))
  else .ok s
theorem cstrCorrect : CstrCorrect := by simp [CstrCorrect, cstr]

def SetenvCorrect : Prop := forall c e d pairs,
  setenvArray c e d = (do let env <- byteenvArray e
                          cmdKeywords c c.ignorestatus (some env) d (d == c.dir) c.cpus c.uid c.gid
                            (c.flags &&& 8 != 0) (c.flags &&& 4 != 0) (c.flags &&& 16 != 0)) /\
  setenvVarargs c pairs = setenvPairs c pairs /\
  setenvDir c d = cmdKeywords c c.ignorestatus c.env d (d == c.dir) c.cpus c.uid c.gid
    (c.flags &&& 8 != 0) (c.flags &&& 4 != 0) (c.flags &&& 16 != 0)
theorem setenvCorrect : SetenvCorrect := by
  simp [SetenvCorrect, setenvArray, setenvVarargs, setenvDir]

def AddenvMethodsCorrect : Prop := forall parent c env pairs strs inherit,
  addenvDict parent c env inherit = addenv parent inherit c env /\
  addenvPairsMethod parent c pairs inherit = addenv parent inherit c (dictOf pairs) /\
  addenvVector parent c strs inherit = do
    let ps <- strs.mapM splitenv
    addenv parent inherit c ((ps.foldl (fun d kv => dset d kv.1 kv.2) []).map
      (fun kv => (kv.1, some kv.2)))
theorem addenvMethodsCorrect : AddenvMethodsCorrect := by
  simp [AddenvMethodsCorrect, addenvDict, addenvPairsMethod, addenvVector]

def IdSettersCorrect : Prop := forall c cpus,
  (setCpuNothing c).cpus = none /\ (setCpuValues c cpus).cpus = some cpus /\
  (setUidNothing c).uid = none /\ (setGidNothing c).gid = none
theorem idSettersCorrect : IdSettersCorrect := by
  simp [IdSettersCorrect, setCpuNothing, setCpuValues, setUidNothing, setGidNothing]

def BasicRedirectionsCorrect : Prop := forall a b h,
  andNode a b = .and a b /\ redirOutCmd a b = .out a b /\ redirErrCmd a b = .err a b /\
  redirOutFromHandle h a = .redirect a h 0 true /\
  redirOutToHandle a h = .redirect a h 1 false /\
  redirErrToHandle a h = .redirect a h 2 false
theorem basicRedirectionsCorrect : BasicRedirectionsCorrect := by
  simp [BasicRedirectionsCorrect, andNode, redirOutCmd, redirErrCmd,
    redirOutFromHandle, redirOutToHandle, redirErrToHandle]

def FileRedirectionsCorrect : Prop := forall a n,
  redirOutFile a n = .redirect a (.handle n) 1 false /\
  redirInFile n a = .redirect a (.handle n) 0 true /\
  redirErrFile a n = .redirect a (.handle n) 2 false /\
  redirOutAppendFile a n = .redirect a (.handle n) 1 false /\
  redirErrAppendFile a n = .redirect a (.handle n) 2 false
theorem fileRedirectionsCorrect : FileRedirectionsCorrect := by
  simp [FileRedirectionsCorrect, redirOutFile, redirInFile, redirErrFile,
    redirOutAppendFile, redirErrAppendFile]

def PipelineKeywordsCorrect : Prop := forall c i o e a,
  pipelineKeywords c i o e a = do
    if a && o.isNone && e.isNone then
      .error (.jl (.argumentError "append set to true, but no output redirections specified"))
    let c := match i with | none => c | some h => redirOutFromHandle h c
    let c := match o with | none => c | some h => redirOutToHandle c h
    let c := match e with | none => c | some h => redirErrToHandle c h
    pure c
theorem pipelineKeywordsCorrect : PipelineKeywordsCorrect := by
  unfold PipelineKeywordsCorrect
  intros
  rfl

def PipelineOverloadsCorrect : Prop := forall c h fd,
  pipelineTo c h = pipelineKeywords c none (some h) none false /\
  pipelineFrom h c = pipelineKeywords c (some h) none none false /\
  pipelineFd c fd h = .redirect c h fd (fd == 0)
theorem pipelineOverloadsCorrect : PipelineOverloadsCorrect := by
  simp [PipelineOverloadsCorrect, pipelineTo, pipelineFrom, pipelineFd]

def PipelineManyLeft : Prop := forall a b rest,
  pipelineMany a (b :: rest) = pipelineMany (.out a b) rest
theorem pipelineManyLeft : PipelineManyLeft := by simp [PipelineManyLeft, pipelineMany]

def InterpolateMethodsCorrect : Prop := forall x h e,
  cmdInterpolateIdentity x = x /\
  cmdInterpolateNothing = .error (.jl (.argumentError "`nothing` can not be interpolated into commands (`Cmd`)")) /\
  cmdRedirectTargetHandle h = h /\ cmdRedirectTargetValue e = interp1 e
theorem interpolateMethodsCorrect : InterpolateMethodsCorrect := by
  simp [InterpolateMethodsCorrect, cmdInterpolateIdentity, cmdInterpolateNothing,
    cmdRedirectTargetHandle, cmdRedirectTargetValue]

def ArgGenMethodsCorrect : Prop := forall s c p ps,
  argGen0 = [] /\ argGenString s = (do pure [<- cstr s]) /\
  argGenCmd c = argGen1 (.cmd c) /\ argGenHead p = argGen1 p /\
  argGenTail p ps = argGen (p :: ps)
theorem argGenMethodsCorrect : ArgGenMethodsCorrect := by
  simp [ArgGenMethodsCorrect, argGen0, argGenString, argGenCmd, argGenHead, argGenTail]

def CmdGenMethodsCorrect : Prop := forall parsed,
  cmdGenAny parsed = cmdGen parsed /\ cmdGenTuple parsed = cmdGenAny parsed
theorem cmdGenMethodsCorrect : CmdGenMethodsCorrect := by
  simp [CmdGenMethodsCorrect, cmdGenAny, cmdGenTuple]

def CmdMacroCorrect : Prop := forall parsed id,
  cmdMacro (.tuple parsed) = .ok (cmdGen parsed) /\
  cmdMacro (.expression id) = .error id
theorem cmdMacroCorrect : CmdMacroCorrect := by simp [CmdMacroCorrect, cmdMacro]

/-! ## Registry -/

def entries : List Entry := [
  { id := "iocov-cmd-exec", juliaFile := "base/cmd.jl", juliaFns := ["Cmd(exec::Vector{<:AbstractString})"],
    statement := "The vector constructor stores the vector and uses default process settings.", source := "base/cmd.jl:22-23",
    status := .proven, prop := ``CmdExecDefaults, thm := some ``cmdExecDefaults },
  { id := "iocov-cmd-copy", juliaFile := "base/cmd.jl", juliaFns := ["Cmd(cmd::Cmd, ignorestatus, flags, env, dir, cpus, uid, gid)"],
    statement := "The positional copy constructor preserves exec and stores every supplied setting.", source := "base/cmd.jl:24-26",
    status := .proven, prop := ``CmdCopyFields, thm := some ``cmdCopyFields },
  { id := "iocov-cmd-keywords", juliaFile := "base/cmd.jl", juliaFns := ["Cmd(cmd::Cmd; ... )"],
    statement := "The keyword constructor preserves exec and assembles the three documented libuv flags.", source := "base/cmd.jl:27-39",
    status := .proven, prop := ``CmdKeywordsFields, thm := some ``cmdKeywordsFields },
  { id := "iocov-cmd-has-nondefault", juliaFile := "base/cmd.jl", juliaFns := ["has_nondefault_cmd_flags"],
    statement := "A command is nondefault exactly when one tested setting is nondefault.", source := "base/cmd.jl:42-49",
    status := .proven, prop := ``HasNondefaultCorrect, thm := some ``hasNondefaultCorrect },
  { id := "iocov-cmd-binary-constructors", juliaFile := "base/cmd.jl", juliaFns := ["OrCmds", "ErrOrCmds", "AndCmds"],
    statement := "The three binary command constructors store their two operands.", source := "base/cmd.jl:103-119",
    status := .proven, prop := ``BinaryConstructorsCorrect, thm := some ``binaryConstructorsCorrect },
  { id := "iocov-cmd-and-methods", juliaFile := "base/cmd.jl", juliaFns := ["hash(::AndCmds)", "==(::AndCmds,::AndCmds)"],
    statement := "AndCmds hashing nests both operands and equality compares both operands.", source := "base/cmd.jl:121-122",
    status := .proven, prop := ``AndMethodsCorrect, thm := some ``andMethodsCorrect },
  { id := "iocov-cmd-escape-forwarders", juliaFile := "base/cmd.jl", juliaFns := ["shell_escape(::Cmd)", "shell_escape_posixly(::Cmd)", "shell_escape_csh(::Cmd)", "escape_microsoft_c_args(::Cmd)"],
    statement := "Cmd escape overloads forward the command argument vector to their string-list implementation.", source := "base/cmd.jl:124-133",
    status := .proven, prop := ``EscapeForwardingCorrect, thm := some ``escapeForwardingCorrect },
  { id := "iocov-cmd-sensitive-env", juliaFile := "base/cmd.jl", juliaFns := ["is_sensitive_env_name"],
    statement := "Sensitive environment names are detected by uppercasing, splitting on non-alphanumerics, and matching the pattern list.", source := "base/cmd.jl:142-146",
    status := .proven, prop := ``SensitiveNameCorrect, thm := some ``sensitiveNameCorrect },
  { id := "iocov-cmd-show-env-mode", juliaFile := "base/cmd.jl", juliaFns := ["get_show_env_mode"],
    statement := "The IO context takes precedence and the environment default is redact.", source := "base/cmd.jl:148-160",
    status := .proven, prop := ``ShowEnvModeCorrect, thm := some ``showEnvModeCorrect },
  { id := "iocov-cmd-show-composites", juliaFile := "base/cmd.jl", juliaFns := ["show(::IO,::OrCmds)", "show(::IO,::ErrOrCmds)", "show(::IO,::AndCmds)"],
    statement := "Composite command display prints the documented pipeline or ampersand syntax.", source := "base/cmd.jl:227-240",
    status := .proven, prop := ``CompositeShowCorrect, thm := some ``compositeShowCorrect },
  { id := "iocov-cmd-file-redirect", juliaFile := "base/cmd.jl", juliaFns := ["FileRedirect(::AbstractString,::Bool)", "FileRedirect(::String,::Bool)"],
    statement := "FileRedirect stores the name and append bit and warns for the platform null device.", source := "base/cmd.jl:249-255",
    status := .proven, prop := ``FileRedirectCorrect, thm := some ``fileRedirectCorrect },
  { id := "iocov-cmd-rawhandle", juliaFile := "base/cmd.jl", juliaFns := ["rawhandle", "setup_stdio"],
    statement := "Raw handle conversion is identity except for devnull, and setup_stdio returns a non-owning handle.", source := "base/cmd.jl:260-265",
    status := .proven, prop := ``RawHandleCorrect, thm := some ``rawHandleCorrect },
  { id := "iocov-cmd-redirect-constructor", juliaFile := "base/cmd.jl", juliaFns := ["CmdRedirect(cmd,handle,stream_no)"],
    statement := "A redirect is readable exactly for standard input.", source := "base/cmd.jl:276",
    status := .proven, prop := ``CmdRedirectCorrect, thm := some ``cmdRedirectCorrect },
  { id := "iocov-cmd-show-redirect", juliaFile := "base/cmd.jl", juliaFns := ["show(::IO,::CmdRedirect)"],
    statement := "Redirect display names standard streams, selects the direction glyph, and prints the handle.", source := "base/cmd.jl:278-294",
    status := .proven, prop := ``ShowCmdRedirectCorrect, thm := some ``showCmdRedirectCorrect },
  { id := "iocov-cmd-ignorestatus", juliaFile := "base/cmd.jl", juliaFns := ["ignorestatus(::Cmd)", "ignorestatus(::Union{OrCmds,AndCmds})", "ignorestatus(::CmdRedirect)"],
    statement := "ignorestatus marks every leaf command while preserving the composite shape.", source := "base/cmd.jl:301-305",
    status := .proven, prop := ``IgnoreStatusCorrect, thm := some ``ignoreStatusCorrect },
  { id := "iocov-cmd-detach", juliaFile := "base/cmd.jl", juliaFns := ["detach(::Cmd)"],
    statement := "detach sets the detached-process flag.", source := "base/cmd.jl:312",
    status := .proven, prop := ``DetachCorrect, thm := some ``detachCorrect },
  { id := "iocov-cmd-cstr", juliaFile := "base/cmd.jl", juliaFns := ["cstr"],
    statement := "cstr rejects strings containing NUL and otherwise returns their String conversion.", source := "base/cmd.jl:316-321",
    status := .proven, prop := ``CstrCorrect, thm := some ``cstrCorrect },
  { id := "iocov-cmd-byteenv", juliaFile := "base/cmd.jl", juliaFns := ["byteenv"],
    statement := "Every byteenv overload converts its input to checked key-value strings or nothing.", source := "base/cmd.jl:324-330",
    status := .proven, prop := ``ByteenvCorrect, thm := some ``byteenvCorrect },
  { id := "iocov-cmd-setenv", juliaFile := "base/cmd.jl", juliaFns := ["setenv"],
    statement := "The setenv overloads convert the environment and rebuild the command with the requested directory.", source := "base/cmd.jl:358-361",
    status := .proven, prop := ``SetenvCorrect, thm := some ``setenvCorrect },
  { id := "iocov-cmd-addenv-overloads", juliaFile := "base/cmd.jl", juliaFns := ["addenv(::Cmd,::Dict)", "addenv(::Cmd,::Pair...)", "addenv(::Cmd,::Vector)"],
    statement := "All addenv overloads build dictionary semantics and then merge with the inherited or command environment.", source := "base/cmd.jl:385-412",
    status := .proven, prop := ``AddenvMethodsCorrect, thm := some ``addenvMethodsCorrect },
  { id := "iocov-cmd-id-setters", juliaFile := "base/cmd.jl", juliaFns := ["setcpuaffinity", "setuid(::Cmd,::Nothing)", "setgid(::Cmd,::Nothing)"],
    statement := "The setters store or clear their corresponding command field.", source := "base/cmd.jl:444-445,468,492",
    status := .proven, prop := ``IdSettersCorrect, thm := some ``idSettersCorrect },
  { id := "iocov-cmd-basic-redirections", juliaFile := "base/cmd.jl", juliaFns := ["&", "redir_out", "redir_err"],
    statement := "Command and handle redirection overloads construct the correct composite and stream number.", source := "base/cmd.jl:495-502",
    status := .proven, prop := ``BasicRedirectionsCorrect, thm := some ``basicRedirectionsCorrect },
  { id := "iocov-cmd-file-redirections", juliaFile := "base/cmd.jl", juliaFns := ["redir_out(::AbstractString)", "redir_err(::AbstractString)", "redir_out_append", "redir_err_append"],
    statement := "File redirect overloads use the correct stream number, direction, and append constructor.", source := "base/cmd.jl:505-509",
    status := .proven, prop := ``FileRedirectionsCorrect, thm := some ``fileRedirectionsCorrect },
  { id := "iocov-cmd-pipeline-keywords", juliaFile := "base/cmd.jl", juliaFns := ["pipeline(::AbstractCmd;...)"],
    statement := "Keyword pipeline applies stdin, stdout, then stderr redirections and rejects append without output.", source := "base/cmd.jl:527-541",
    status := .proven, prop := ``PipelineKeywordsCorrect, thm := some ``pipelineKeywordsCorrect },
  { id := "iocov-cmd-pipeline-overloads", juliaFile := "base/cmd.jl", juliaFns := ["pipeline(::AbstractCmd,dest)", "pipeline(src,::AbstractCmd)", "pipeline(::AbstractCmd,::Pair)"],
    statement := "Two-argument and file-descriptor pipeline overloads select the documented stream.", source := "base/cmd.jl:543-556",
    status := .proven, prop := ``PipelineOverloadsCorrect, thm := some ``pipelineOverloadsCorrect },
  { id := "iocov-cmd-pipeline-many", juliaFile := "base/cmd.jl", juliaFns := ["pipeline(a,b,c,d...)"],
    statement := "Variadic pipelines associate from the left.", source := "base/cmd.jl:576",
    status := .proven, prop := ``PipelineManyLeft, thm := some ``pipelineManyLeft },
  { id := "iocov-cmd-interpolate-methods", juliaFile := "base/cmd.jl", juliaFns := ["cmd_interpolate1", "cmd_redirect_target"],
    statement := "Interpolation preserves ordinary values, rejects nothing, and converts non-redirectable targets.", source := "base/cmd.jl:582-586",
    status := .proven, prop := ``InterpolateMethodsCorrect, thm := some ``interpolateMethodsCorrect },
  { id := "iocov-cmd-arg-gen-methods", juliaFile := "base/cmd.jl", juliaFns := ["arg_gen"],
    statement := "Each arg_gen overload applies the corresponding checked scalar, command, iterable, or Cartesian-product path.", source := "base/cmd.jl:588-617",
    status := .proven, prop := ``ArgGenMethodsCorrect, thm := some ``argGenMethodsCorrect },
  { id := "iocov-cmd-gen-methods", juliaFile := "base/cmd.jl", juliaFns := ["cmd_gen"],
    statement := "The foldable tuple specialization invokes the generic command generator.", source := "base/cmd.jl:619-641",
    status := .proven, prop := ``CmdGenMethodsCorrect, thm := some ``cmdGenMethodsCorrect },
  { id := "iocov-cmd-macro", juliaFile := "base/cmd.jl", juliaFns := ["@cmd"],
    statement := "The cmd macro calls cmd_gen for tuple parses and returns pipeline expressions directly.", source := "base/cmd.jl:659-668",
    status := .proven, prop := ``CmdMacroCorrect, thm := some ``cmdMacroCorrect }
]

end JuliaLean.IOCov.Cmd
