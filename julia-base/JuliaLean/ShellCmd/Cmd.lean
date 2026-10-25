import JuliaLean.ShellCmd.Escape

/-!
# `Cmd` objects, `base/cmd.jl`

Master `bbfa0ce4150`: the `Cmd` struct, `==`, the parts of `show(::IO, ::Cmd)`
that print the arguments, uid/gid, CPU list and environment, `setenv` with
pairs, `splitenv`, `addenv`, and the interpolation functions `arg_gen` and
`cmd_gen` that build argument vectors from a parsed command literal.

`Dict{String,String}` in `addenv` is modelled by an association list with
`Dict` update semantics (setting a present key replaces its value, `delete!`
removes it). Iteration order is not modelled; the properties stated about
`addenv` only look up keys, which does not depend on the order.
-/

namespace JuliaLean.ShellCmd

/-- `struct Cmd`, `base/cmd.jl:13-21`. -/
structure CmdM where
  exec : List JS
  ignorestatus : Bool
  flags : UInt32
  env : Option (List JS)
  dir : JS
  cpus : Option (List UInt16)
  uid : Option UInt32
  gid : Option UInt32
  deriving DecidableEq, Repr

/-- `Cmd(exec::Vector{String})`, `base/cmd.jl:22-23`. -/
def cmdOf (exec : List JS) : CmdM :=
  { exec, ignorestatus := false, flags := 0, env := none, dir := [], cpus := none,
    uid := none, gid := none }

/-- `==(x::Cmd, y::Cmd)`, `base/cmd.jl:100-101`. -/
def cmdEq (x y : CmdM) : Bool :=
  x.exec == y.exec && x.env == y.env && x.ignorestatus == y.ignorestatus &&
    x.dir == y.dir && x.flags == y.flags && x.uid == y.uid && x.gid == y.gid

/-- `has_nondefault_cmd_flags(c)`, `base/cmd.jl:42-49`. -/
def hasNondefaultFlags (c : CmdM) : Bool :=
  c.ignorestatus || c.flags != 0 || c.env.isSome || !c.dir.isEmpty || c.cpus.isSome ||
    c.uid.isSome || c.gid.isSome

/-- `setcpuaffinity(cmd, cpus)` with a list of CPU ids, `base/cmd.jl:445`. -/
def setcpuaffinity (c : CmdM) (cpus : List UInt16) : CmdM := { c with cpus := some cpus }

/-! ### `show(::IO, ::Cmd)`, `base/cmd.jl:185-225` -/

/-- `shell_special`, `base/shell.jl:5`. -/
def shellSpecial : JS := S "#{}()[]<>|&*?;"

/-- One argument as printed by `show(::Cmd)`, `base/cmd.jl:203-208`, before the
backtick escaping: `print_shell_word` with `shell_special`, plus `~` for a
word starting with `~`. -/
def showWordRaw (arg : JS) : JS :=
  printShellWord arg (if arg.head? == some (A '~') then shellSpecial ++ [A '~'] else shellSpecial)

/-- One argument as printed: `replace(..., '`' => "\\`")`. -/
def showWord (arg : JS) : JS := replaceC (showWordRaw arg) (A '`') (S "\\`")

/-- The command literal printed for `exec`, `base/cmd.jl:201-210`. -/
def showExec (exec : List JS) : JS := A '`' :: joinSp (exec.map showWord) ++ [A '`']

/-- The text of the literal before backtick escaping: the shell-quoted words. -/
def showBody (exec : List JS) : JS := joinSp (exec.map showWordRaw)

/-- Decimal digits of a natural number. -/
def decimal (n : Nat) : JS := S (toString n)

/-- `show(io, Int32(x))` for `x::UInt32`: `Int32(x)` throws `InexactError`
unless `x < 2^31`. -/
def showInt32OfU32 (x : UInt32) : SH JS :=
  if x.toNat < 2 ^ 31 then .ok (decimal x.toNat) else .error (.jl (.inexactError "convert"))

/-- `show(io, collect(Int, cpus))`: `[1, 2]`. -/
def showCpus (cpus : List UInt16) : JS :=
  A '[' :: (match cpus.map (fun c => decimal c.toNat) with
    | [] => []
    | d :: ds => d ++ ds.flatMap (fun e => S ", " ++ e)) ++ [A ']']

/-- `show(io, cmd)` for a `Cmd` without environment and directory
(`base/cmd.jl:185-225` with `print_env` and `print_dir` false). -/
def showCmdNoEnv (c : CmdM) : SH JS := do
  let uidT ← match c.uid with
    | some u => do let t ← showInt32OfU32 u; pure (S ", " ++ t ++ S ")")
    | none => pure []
  let gidT ← match c.gid with
    | some g => do let t ← showInt32OfU32 g; pure (S ", " ++ t ++ S ")")
    | none => pure []
  let cpusT := match c.cpus with
    | some cs => S ", " ++ showCpus cs ++ S ")"
    | none => []
  pure ((if c.cpus.isSome then S "setcpuaffinity(" else []) ++
    (if c.gid.isSome then S "setgid(" else []) ++
    (if c.uid.isSome then S "setuid(" else []) ++
    showExec c.exec ++ uidT ++ gidT ++ cpusT)

/-- `findnext('=', e, 2)` for a `String` (`base/strings/search.jl:143-166`):
`nothing` if `2 == ncodeunits(e) + 1`, `BoundsError` if `2 > ncodeunits(e) + 1`,
`StringIndexError` unless `2` is a character index, else the index of the first
`'='` at or after byte 2. -/
def findEq2 (e : JS) : SH (Option Int) :=
  let n : Int := ncu e
  if (2 : Int) = n + 1 then .ok none
  else if (2 : Int) > n + 1 then .error (.jl .boundsError)
  else if !isStart e 2 then .error .stringIndex
  else .ok (((pairsFrom 1 e).find? (fun q => 2 ≤ q.1 && q.2 == A '=')).map (fun q => (q.1 : Int)))

/-- The display mode of `show_env`, `base/cmd.jl:148-160`. -/
inductive ShowEnvMode where
  | all | keys | redact | none
  deriving DecidableEq, Repr

/-- `show_env(io, env)`, `base/cmd.jl:162-183`: the strings it passes to
`show`, in order. `sens` is `is_sensitive_env_name` (`base/cmd.jl:142-146`);
it is only consulted after `findnext`. -/
def showEnv (mode : ShowEnvMode) (sens : JS → Bool) : List JS → SH (List JS)
  | [] => .ok []
  | e :: es => do
    let eqidx ← findEq2 e
    let shown ← match eqidx with
      | none => pure e
      | some i =>
        if mode == .all then pure e
        else do
          let key ← slice e 1 (prevind e i)
          pure (if mode == .keys then key else if sens key then key else e)
    let rest ← showEnv mode sens es
    pure (shown :: rest)

/-- Whether `show(io, cmd)` (`base/cmd.jl:185-225`) completes, for a `Cmd`
without uid, gid and CPU list: in mode `:none` the environment is not shown. -/
def showCmdEnvOk (mode : ShowEnvMode) (sens : JS → Bool) (c : CmdM) : Bool :=
  match c.env with
  | some env => mode == .none || (showEnv mode sens env).toOption.isSome
  | none => true

/-! ### `setenv` and `addenv` -/

/-- `cstr(s)`, `base/cmd.jl:316-321`. -/
def cstr (s : JS) : SH JS :=
  if s.contains (A '\x00') then
    .error (.jl (.argumentError "strings containing NUL cannot be passed to spawned processes"))
  else .ok s

/-- `byteenv` of pairs `k => v` with string values, `base/cmd.jl:329-330`. -/
def byteenvPairs (kvs : List (JS × JS)) : SH (List JS) :=
  kvs.mapM (fun kv => cstr (kv.1 ++ [A '='] ++ kv.2))

/-- `setenv(cmd, pairs...)`, `base/cmd.jl:358-360`. -/
def setenvPairs (c : CmdM) (kvs : List (JS × JS)) : SH CmdM := do
  let env ← byteenvPairs kvs
  pure { c with env := some env }

/-- `splitenv(e)`, `base/cmd.jl:364-370`. -/
def splitenv (e : JS) : SH (JS × JS) := do
  let i ← findEq2 e
  match i with
  | none => .error (.jl (.argumentError "malformed environment entry"))
  | some i => do
    let k ← slice e 1 (prevind e i)
    let v ← slice e (i + 1) (lastindex e)
    pure (k, v)

/-- `d[k] = v` for the association-list model of a `Dict`. -/
def dset (d : List (JS × JS)) (k v : JS) : List (JS × JS) :=
  if d.any (·.1 == k) then d.map (fun kv => if kv.1 == k then (k, v) else kv) else d ++ [(k, v)]

/-- `delete!(d, k)`. -/
def ddel (d : List (JS × JS)) (k : JS) : List (JS × JS) := d.filter (·.1 != k)

/-- `get(d, k, nothing)`. -/
def dget (d : List (JS × JS)) (k : JS) : Option JS := (d.find? (·.1 == k)).map (·.2)

/-- `Dict(k => v for (k, v) in pairs)`: later pairs replace earlier ones. -/
def dictOf (kvs : List (JS × Option JS)) : List (JS × Option JS) :=
  kvs.foldl (fun d kv =>
    if d.any (·.1 == kv.1) then d.map (fun x => if x.1 == kv.1 then kv else x) else d ++ [kv]) []

/-- `addenv(cmd, pairs...; inherit)`, `base/cmd.jl:385-408`; `v = none` is
`nothing`. `ENV` is the parent environment as key/value pairs. -/
def addenv (envENV : List (JS × JS)) (inherit : Bool) (c : CmdM) (kvs : List (JS × Option JS)) :
    SH CmdM := do
  let base ← match c.env with
    | none => pure (if inherit then envENV.foldl (fun d kv => dset d kv.1 kv.2) [] else [])
    | some env => do
      let split ← env.mapM splitenv
      pure (split.foldl (fun d kv => dset d kv.1 kv.2) [])
  let newEnv := (dictOf kvs).foldl (fun d kv =>
    match kv.2 with
    | none => ddel d kv.1
    | some v => dset d kv.1 v) base
  let env ← byteenvPairs newEnv
  pure { c with env := some env }

/-! ### Interpolation, `base/cmd.jl:579-635` -/

/-- An element of an interpolated collection: a value with its `string(x)`, or `nothing`. -/
inductive Elem where
  | val (s : JS)
  | nothing
  deriving DecidableEq, Repr

/-- A part of a word of a parsed command literal: a literal or interpolated
`AbstractString`, an interpolated iterable collection, an interpolated `Cmd`,
or an interpolated non-iterable value (or `nothing`). -/
inductive Part where
  | str (s : JS)
  | iter (xs : List Elem)
  | cmd (c : CmdM)
  | scalar (x : Elem)
  deriving Repr

/-- `cmd_interpolate1` followed by `string`, `base/cmd.jl:581-583`. -/
def interp1 : Elem → SH JS
  | .val s => .ok s
  | .nothing => .error (.jl (.argumentError "`nothing` can not be interpolated into commands (`Cmd`)"))

/-- `arg_gen(head)` for one part, `base/cmd.jl:589-607`. -/
def argGen1 : Part → SH (List JS)
  | .str s => do let s ← cstr s; pure [s]
  | .cmd c =>
    if hasNondefaultFlags c then
      .error (.jl (.argumentError "Non-default environment behavior is only permitted for the first interpolant."))
    else .ok c.exec
  | .iter xs => xs.mapM (fun x => do let s ← interp1 x; cstr s)
  | .scalar x => do let s ← interp1 x; let s ← cstr s; pure [s]

/-- `arg_gen(head, tail...)`, `base/cmd.jl:588-617`: `cmd_interpolate(h, t)` for
every `h` of the head and `t` of the tail, head varying slowest. -/
def argGen : List Part → SH (List JS)
  | [] => .ok []
  | [p] => argGen1 p
  | p :: ps => do
    let head ← argGen1 p
    let tail ← argGen ps
    head.flatMap (fun h => tail.map (fun t => h ++ t)) |>.mapM cstr

/-- `cmd_gen(parsed)`, `base/cmd.jl:619-635`. -/
def cmdGen (parsed : List (List Part)) : SH CmdM :=
  match parsed with
  | [Part.cmd c] :: rest => do
    let more ← rest.mapM argGen
    pure { c with exec := c.exec ++ more.flatten }
  | _ => do
    let args ← parsed.mapM argGen
    pure (cmdOf args.flatten)

end JuliaLean.ShellCmd
