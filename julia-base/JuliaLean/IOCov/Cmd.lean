import JuliaLean.Registry.Types
import JuliaLean.ShellCmd.Cmd

/-!
Method-specific models for the remaining definitions in `base/cmd.jl` at Julia
master `bbfa0ce4150`.  The string and `Cmd` primitives are shared with the
`ShellCmd` area; every definition below follows one source method.
-/

namespace JuliaLean.IOCov.Cmd

open JuliaLean JuliaLean.Registry
open JuliaLean.ShellCmd

/-! ## Constructors and command flags -/

/-- `Cmd(exec::Vector{<:AbstractString})`, `base/cmd.jl:22-23`. -/
def cmdExec (exec : List JS) : CmdM := cmdOf exec

/-- `Cmd(cmd, ignorestatus, flags, env, dir, cpus, uid, gid)`,
`base/cmd.jl:24-26`.  `sameDir` models the `dir === cmd.dir` identity test. -/
def cmdCopy (cmd : CmdM) (ignorestatus : Bool) (flags : UInt32)
    (env : Option (List JS)) (dir : JS) (sameDir : Bool)
    (cpus : Option (List UInt16)) (uid gid : Option UInt32) : SH CmdM := do
  let dir <- if sameDir then pure dir else cstr dir
  pure (CmdM.mk cmd.exec ignorestatus flags env dir cpus uid gid)

/-- The three libuv flags assembled by the keyword `Cmd` constructor,
`base/cmd.jl:34-36`. -/
def keywordFlags (detach windowsVerbatim windowsHide : Bool) : UInt32 :=
  (if detach then 8 else 0) ||| (if windowsVerbatim then 4 else 0) |||
    (if windowsHide then 16 else 0)

/-- `Cmd(cmd::Cmd; ...)`, `base/cmd.jl:27-39`, after `byteenv` converts `env`.
`sameDir` is the source identity test. -/
def cmdKeywords (cmd : CmdM) (ignorestatus : Bool) (env : Option (List JS))
    (dir : JS) (sameDir : Bool) (cpus : Option (List UInt16)) (uid gid : Option UInt32)
    (detach windowsVerbatim windowsHide : Bool) : SH CmdM := do
  let dir <- if sameDir then pure dir else cstr dir
  pure (CmdM.mk cmd.exec ignorestatus (keywordFlags detach windowsVerbatim windowsHide)
    env dir cpus uid gid)

/-- `has_nondefault_cmd_flags`, `base/cmd.jl:42-49`. -/
def hasNondefault (c : CmdM) : Bool := hasNondefaultFlags c

structure BinaryCmd where
  a : CmdM
  b : CmdM
  deriving DecidableEq, Repr

/-- `OrCmds(a, b)`, `base/cmd.jl:106`. -/
def orCmds (a b : CmdM) : BinaryCmd := ⟨a, b⟩
/-- `ErrOrCmds(a, b)`, `base/cmd.jl:112`. -/
def errOrCmds (a b : CmdM) : BinaryCmd := ⟨a, b⟩
/-- `AndCmds(a, b)`, `base/cmd.jl:118`. -/
def andCmds (a b : CmdM) : BinaryCmd := ⟨a, b⟩

/-- `hash(x::AndCmds, h)`, `base/cmd.jl:121`. -/
def hashAnd (hashCmd : CmdM -> Nat -> Nat) (x : BinaryCmd) (h : Nat) : Nat :=
  hashCmd x.a (hashCmd x.b h)

/-- `==(x::AndCmds, y::AndCmds)`, `base/cmd.jl:122`. -/
def eqAnd (x y : BinaryCmd) : Bool := x.a == y.a && x.b == y.b

/-! ## Escape forwarding -/

/-- `shell_escape(cmd::Cmd; special)`, `base/cmd.jl:124-125`. -/
def shellEscapeCmd (cmd : CmdM) (special : JS) : JS := shellEscape cmd.exec special
/-- `shell_escape_posixly(cmd::Cmd)`, `base/cmd.jl:126-127`. -/
def shellEscapePosixlyCmd (cmd : CmdM) : JS := shellEscapePosixly cmd.exec
/-- `shell_escape_csh(cmd::Cmd)`, `base/cmd.jl:128-129`. -/
def shellEscapeCshCmd (cmd : CmdM) : SH JS := shellEscapeCsh cmd.exec
/-- `escape_microsoft_c_args(cmd::Cmd)`, `base/cmd.jl:130-131`. -/
def escapeMicrosoftCmd (cmd : CmdM) : SH JS := escapeMicrosoftCArgs cmd.exec
/-- `escape_microsoft_c_args(io, cmd::Cmd)`, `base/cmd.jl:132-133`.
The model returns the bytes written to `io`. -/
def escapeMicrosoftCmdIO (cmd : CmdM) : SH JS := escapeMicrosoftCArgs cmd.exec

/-! ## Sensitive environment display -/

def isAsciiAlphaNum (c : JC) : Bool :=
  (A 'A' <= c && c <= A 'Z') || (A 'a' <= c && c <= A 'z') ||
    (A '0' <= c && c <= A '9')

def upperAscii (c : JC) : JC :=
  if A 'a' <= c && c <= A 'z' then c - A 'a' + A 'A' else c

def lowerAscii (c : JC) : JC :=
  if A 'A' <= c && c <= A 'Z' then c - A 'A' + A 'a' else c

private def splitPartsGo : JS -> JS -> List JS
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: cs, cur =>
      if isAsciiAlphaNum c then splitPartsGo cs (c :: cur)
      else (if cur.isEmpty then [] else [cur.reverse]) ++ splitPartsGo cs []

/-- `eachsplit(uppercase(name), r"[^A-Za-z0-9]+")`, `base/cmd.jl:143-144`. -/
def sensitiveParts (name : JS) : List JS := splitPartsGo (name.map upperAscii) []

def sensitivePatterns : List JS :=
  [S "KEY", S "TOKEN", S "SECRET", S "JWT", S "PAT", S "PASSWORD", S "PASSWD",
   S "PASS", S "PWD", S "PW", S "CREDENTIAL", S "CRED", S "AUTH", S "PRIVATE", S "PRIV"]

/-- `is_sensitive_env_name`, `base/cmd.jl:142-146`. -/
def isSensitiveEnvName (name : JS) : Bool :=
  (sensitiveParts name).any (fun part => sensitivePatterns.contains part)

inductive ContextShowEnv where
  | unset
  | mode (m : ShowEnvMode)
  | wrongType
  deriving DecidableEq, Repr

/-- `get_show_env_mode`, `base/cmd.jl:148-160`. -/
def getShowEnvMode (ctx : ContextShowEnv) (envval : Option JS) : SH ShowEnvMode :=
  match ctx with
  | .mode m => .ok m
  | .wrongType => .error .typeError
  | .unset =>
      match envval with
      | none => .ok .redact
      | some value =>
          let value := value.map lowerAscii
          if value == S "all" then .ok .all
          else if value == S "none" then .ok .none
          else if value == S "keys" then .ok .keys
          else .ok .redact

inductive OrKind where | stdout | stderr deriving DecidableEq, Repr

/-- `show(io, ::Union{OrCmds,ErrOrCmds})`, `base/cmd.jl:227-234`, represented
by its printed character sequence. -/
def showOrCmds (render : CmdM -> JS) (kind : OrKind) (cmds : BinaryCmd) : JS :=
  S "pipeline(" ++ render cmds.a ++ S ", " ++
    (if kind == .stderr then S "stderr=" else S "stdout=") ++ render cmds.b ++ S ")"

/-- `show(io, ::AndCmds)`, `base/cmd.jl:236-240`. -/
def showAndCmds (render : CmdM -> JS) (cmds : BinaryCmd) : JS :=
  render cmds.a ++ S " & " ++ render cmds.b

/-! ## Redirect values -/

structure FileRedirectM where
  filename : JS
  append : Bool
  warned : Bool
  deriving DecidableEq, Repr

/-- Inner `FileRedirect(filename::String, append)`, `base/cmd.jl:250-255`.
`isWindows` selects the static platform branch. -/
def fileRedirectString (isWindows : Bool) (filename : JS) (append : Bool) : FileRedirectM :=
  let nullName := if isWindows then S "nul" else S "/dev/null"
  { filename, append, warned := filename.map lowerAscii == nullName }

/-- Outer `FileRedirect(filename::AbstractString, append)`, `base/cmd.jl:249`. -/
def fileRedirectAbstract (isWindows : Bool) (filename : JS) (append : Bool) : FileRedirectM :=
  fileRedirectString isWindows filename append

inductive RawHandle where
  | null
  | handle (n : Int)
  deriving DecidableEq, Repr

/-- `rawhandle(::DevNull)`, `base/cmd.jl:260`. -/
def rawhandleDevNull : RawHandle := .null
/-- `rawhandle(x::OS_HANDLE)`, `base/cmd.jl:261`. -/
def rawhandleOS (x : Int) : RawHandle := .handle x
/-- `rawhandle(x::RawFD)`, `base/cmd.jl:263`, with the Unix `_get_osfhandle`. -/
def rawhandleFD (x : Int) : RawHandle := .handle x
/-- `setup_stdio`, `base/cmd.jl:265`. -/
def setupStdio (stdio : RawHandle) (_readable : Bool) : RawHandle × Bool := (stdio, false)

structure CmdRedirectM where
  cmd : CmdM
  handle : RawHandle
  streamNo : Int
  readable : Bool
  deriving DecidableEq, Repr

/-- Three-argument `CmdRedirect`, `base/cmd.jl:276`. -/
def cmdRedirect3 (cmd : CmdM) (handle : RawHandle) (streamNo : Int) : CmdRedirectM :=
  { cmd, handle, streamNo, readable := streamNo == 0 }

/-- `show(io, cr::CmdRedirect)`, `base/cmd.jl:278-294`. -/
def showCmdRedirect (renderCmd : CmdM -> JS) (renderHandle : RawHandle -> JS)
    (cr : CmdRedirectM) : JS :=
  let stream := if cr.streamNo == 1 then S "stdout"
    else if cr.streamNo == 2 then S "stderr"
    else if cr.streamNo == 0 then S "stdin"
    else S (toString cr.streamNo)
  S "pipeline(" ++ renderCmd cr.cmd ++ S ", " ++ stream ++
    (if cr.readable then S "<" else S ">") ++ renderHandle cr.handle ++ S ")"

/-! ## Command transformations and environments -/

/-- `ignorestatus(cmd::Cmd)`, `base/cmd.jl:301`. -/
def ignoreStatusCmd (cmd : CmdM) : CmdM := { cmd with ignorestatus := true }

/-- `ignorestatus` for `OrCmds` and `AndCmds`, `base/cmd.jl:302-303`. -/
def ignoreStatusBinary (cmd : BinaryCmd) : BinaryCmd :=
  ⟨ignoreStatusCmd cmd.a, ignoreStatusCmd cmd.b⟩

/-- `ignorestatus(cmd::CmdRedirect)`, `base/cmd.jl:304-305`. -/
def ignoreStatusRedirect (cmd : CmdRedirectM) : CmdRedirectM :=
  { cmd with cmd := ignoreStatusCmd cmd.cmd }

/-- `detach(cmd::Cmd)`, `base/cmd.jl:312`. -/
def detachCmd (cmd : CmdM) : CmdM :=
  { cmd with flags := keywordFlags true (cmd.flags &&& 4 != 0) (cmd.flags &&& 16 != 0) }

/-- `byteenv(env::AbstractArray{<:AbstractString})`, `base/cmd.jl:324-325`. -/
def byteenvArray (env : List JS) : SH (List JS) := env.mapM cstr

/-- `byteenv(env::AbstractDict)`, `base/cmd.jl:326-327`. -/
def byteenvDict (env : List (JS × JS)) : SH (List JS) := byteenvPairs env

/-- `byteenv(::Nothing)`, `base/cmd.jl:328`. -/
def byteenvNothing : Option (List JS) := none

/-- `byteenv` for vectors or tuples of pairs, `base/cmd.jl:329-330`. -/
def byteenvPairList (env : List (JS × JS)) : SH (List JS) := byteenvPairs env

/-- `setenv(cmd, env; dir)`, `base/cmd.jl:358`. -/
def setenvArray (cmd : CmdM) (env : List JS) (dir : JS) : SH CmdM := do
  let env <- byteenvArray env
  cmdKeywords cmd cmd.ignorestatus (some env) dir (dir == cmd.dir) cmd.cpus cmd.uid cmd.gid
    (cmd.flags &&& 8 != 0) (cmd.flags &&& 4 != 0) (cmd.flags &&& 16 != 0)

/-- Vararg-pair `setenv`, `base/cmd.jl:359-360`. -/
def setenvVarargs (cmd : CmdM) (env : List (JS × JS)) : SH CmdM := setenvPairs cmd env

/-- `setenv(cmd; dir)`, `base/cmd.jl:361`. -/
def setenvDir (cmd : CmdM) (dir : JS) : SH CmdM :=
  cmdKeywords cmd cmd.ignorestatus cmd.env dir (dir == cmd.dir) cmd.cpus cmd.uid cmd.gid
    (cmd.flags &&& 8 != 0) (cmd.flags &&& 4 != 0) (cmd.flags &&& 16 != 0)

/-- Dictionary `addenv`, `base/cmd.jl:385-404`. -/
def addenvDict (parent : List (JS × JS)) (cmd : CmdM)
    (env : List (JS × Option JS)) (inherit : Bool) : SH CmdM :=
  addenv parent inherit cmd env

/-- Pair-vararg `addenv`, including the `Dict` conversion, `base/cmd.jl:406-408`. -/
def addenvPairsMethod (parent : List (JS × JS)) (cmd : CmdM)
    (pairs : List (JS × Option JS)) (inherit : Bool) : SH CmdM :=
  addenv parent inherit cmd (dictOf pairs)

/-- Vector-string `addenv`, including `splitenv.(env)` and `Dict`,
`base/cmd.jl:410-412`. -/
def addenvVector (parent : List (JS × JS)) (cmd : CmdM)
    (env : List JS) (inherit : Bool) : SH CmdM := do
  let pairs <- env.mapM splitenv
  addenv parent inherit cmd ((pairs.foldl (fun d kv => dset d kv.1 kv.2) []).map
    (fun kv => (kv.1, some kv.2)))

/-- `setcpuaffinity(cmd, nothing)`, `base/cmd.jl:444`. -/
def setCpuNothing (cmd : CmdM) : CmdM := { cmd with cpus := none }
/-- `setcpuaffinity(cmd, cpus)`, `base/cmd.jl:445`, after `collect(UInt16, cpus)`. -/
def setCpuValues (cmd : CmdM) (cpus : List UInt16) : CmdM := { cmd with cpus := some cpus }
/-- `setuid(cmd, nothing)`, `base/cmd.jl:468`. -/
def setUidNothing (cmd : CmdM) : CmdM := { cmd with uid := none }
/-- `setgid(cmd, nothing)`, `base/cmd.jl:492`. -/
def setGidNothing (cmd : CmdM) : CmdM := { cmd with gid := none }

/-! ## Pipelines and interpolation -/

inductive PipeNode where
  | cmd (c : CmdM)
  | and (a b : PipeNode)
  | out (a b : PipeNode)
  | err (a b : PipeNode)
  | redirect (cmd : PipeNode) (handle : RawHandle) (streamNo : Int) (readable : Bool)
  deriving DecidableEq, Repr

/-- `(&)(left, right)`, `base/cmd.jl:495`. -/
def andNode (left right : PipeNode) : PipeNode := .and left right
/-- Command destination `redir_out`, `base/cmd.jl:496`. -/
def redirOutCmd (src dest : PipeNode) : PipeNode := .out src dest
/-- Command destination `redir_err`, `base/cmd.jl:497`. -/
def redirErrCmd (src dest : PipeNode) : PipeNode := .err src dest
/-- Redirectable source `redir_out`, `base/cmd.jl:500`. -/
def redirOutFromHandle (dest : RawHandle) (src : PipeNode) : PipeNode := .redirect src dest 0 true
/-- Redirectable destination `redir_out`, `base/cmd.jl:501`. -/
def redirOutToHandle (src : PipeNode) (dest : RawHandle) : PipeNode := .redirect src dest 1 false
/-- Redirectable destination `redir_err`, `base/cmd.jl:502`. -/
def redirErrToHandle (src : PipeNode) (dest : RawHandle) : PipeNode := .redirect src dest 2 false

/-- File destination `redir_out`, `base/cmd.jl:505`. -/
def redirOutFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 1 false
/-- File source `redir_out`, `base/cmd.jl:506`. -/
def redirInFile (fileId : Int) (dest : PipeNode) : PipeNode := .redirect dest (.handle fileId) 0 true
/-- File destination `redir_err`, `base/cmd.jl:507`. -/
def redirErrFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 2 false
/-- Append file destination `redir_out_append`, `base/cmd.jl:508`. -/
def redirOutAppendFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 1 false
/-- Append file destination `redir_err_append`, `base/cmd.jl:509`. -/
def redirErrAppendFile (src : PipeNode) (fileId : Int) : PipeNode := .redirect src (.handle fileId) 2 false

/-- Keyword `pipeline`, `base/cmd.jl:527-541`. -/
def pipelineKeywords (cmd : PipeNode) (stdin stdout stderr : Option RawHandle)
    (append : Bool) : SH PipeNode := do
  if append && stdout.isNone && stderr.isNone then
    .error (.jl (.argumentError "append set to true, but no output redirections specified"))
  let cmd := match stdin with | none => cmd | some h => redirOutFromHandle h cmd
  let cmd := match stdout with | none => cmd | some h => redirOutToHandle cmd h
  let cmd := match stderr with | none => cmd | some h => redirErrToHandle cmd h
  pure cmd

/-- Two-argument `pipeline(cmd, dest)`, `base/cmd.jl:543`. -/
def pipelineTo (cmd : PipeNode) (dest : RawHandle) : SH PipeNode :=
  pipelineKeywords cmd none (some dest) none false
/-- Two-argument `pipeline(src, cmd)`, `base/cmd.jl:544`. -/
def pipelineFrom (src : RawHandle) (cmd : PipeNode) : SH PipeNode :=
  pipelineKeywords cmd (some src) none none false
/-- File-descriptor-pair `pipeline`, `base/cmd.jl:556`. -/
def pipelineFd (cmd : PipeNode) (fd : Int) (dest : RawHandle) : PipeNode :=
  .redirect cmd dest fd (fd == 0)

/-- Variadic `pipeline(a,b,c,d...)`, `base/cmd.jl:576`, left associated. -/
def pipelineMany : PipeNode -> List PipeNode -> PipeNode
  | a, [] => a
  | a, b :: rest => pipelineMany (.out a b) rest

/-- `cmd_interpolate1(x)`, `base/cmd.jl:582`. -/
def cmdInterpolateIdentity (x : JS) : JS := x
/-- `cmd_interpolate1(::Nothing)`, `base/cmd.jl:583`. -/
def cmdInterpolateNothing : SH JS :=
  .error (.jl (.argumentError "`nothing` can not be interpolated into commands (`Cmd`)"))
/-- `cmd_redirect_target(x::Redirectable)`, `base/cmd.jl:585`. -/
def cmdRedirectTargetHandle (x : RawHandle) : RawHandle := x
/-- Generic `cmd_redirect_target`, `base/cmd.jl:586`. -/
def cmdRedirectTargetValue (x : Elem) : SH JS := interp1 x

/-- `arg_gen()`, `base/cmd.jl:588`. -/
def argGen0 : List JS := []
/-- `arg_gen(x::AbstractString)`, `base/cmd.jl:589`. -/
def argGenString (x : JS) : SH (List JS) := do pure [<- cstr x]
/-- `arg_gen(cmd::Cmd)`, `base/cmd.jl:590-595`. -/
def argGenCmd (cmd : CmdM) : SH (List JS) := argGen1 (.cmd cmd)
/-- Generic one-argument `arg_gen`, `base/cmd.jl:597-607`. -/
def argGenHead (head : Part) : SH (List JS) := argGen1 head
/-- Variadic `arg_gen`, `base/cmd.jl:609-617`. -/
def argGenTail (head : Part) (tail : List Part) : SH (List JS) := argGen (head :: tail)
/-- Generic `cmd_gen`, `base/cmd.jl:619-635`. -/
def cmdGenAny (parsed : List (List Part)) : SH CmdM := cmdGen parsed
/-- Foldable tuple-specialized `cmd_gen`, `base/cmd.jl:637-641`. -/
def cmdGenTuple (parsed : List (List Part)) : SH CmdM := cmdGenAny parsed

inductive CmdMacroResult where
  | tuple (parsed : List (List Part))
  | expression (id : Nat)

/-- `@cmd`, `base/cmd.jl:659-668`, after `shell_parse` returns its expression. -/
def cmdMacro : CmdMacroResult -> Except Nat (SH CmdM)
  | .tuple parsed => .ok (cmdGen parsed)
  | .expression id => .error id

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
