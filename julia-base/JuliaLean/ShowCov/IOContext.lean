import JuliaLean.ShowCov.Basic

/-!
# `IOContext` (`base/show.jl:332-491`)

A property value is compared with `===`; `PV` is a value with decidable
identity. An `IOContext` stores an underlying (non-`IOContext`) stream and an
`ImmutableDict`, a binding list with the newest binding first; iteration,
`in` and `keys` visit every binding, including shadowed ones.
-/

namespace JuliaLean.ShowCov.IOCtx

open JuliaLean.ShowCov

/-- Property values (compared by identity). -/
inductive PV where
  | bool (b : Bool)
  | int (n : Int)
  | dims (rows cols : Int)
  | obj (id : Nat)
  deriving DecidableEq, Repr

/-- A stream that is not an `IOContext`: its identity, what `get(io, :color, false)`
returns for it (`true` only for a colour `TTY`/`TTYTerminal`), and its
`displaysize`. -/
structure BaseIO where
  id : Nat
  color : Bool
  displaysize : Int × Int
  deriving DecidableEq, Repr

/-- `ImmutableDict{Symbol,Any}`: newest binding first. -/
abbrev IDict := List (String × PV)

/-- An `IO`: a plain stream or `IOContext(io, dict)` over a plain stream. -/
inductive JIO where
  | plain (b : BaseIO)
  | ctx (b : BaseIO) (dict : IDict)
  deriving DecidableEq, Repr

/-- `get(dict, key, default)`: the newest binding. -/
def dget (d : IDict) (k : String) (default : PV) : PV :=
  match d.find? (·.1 == k) with
  | some (_, v) => v
  | none => default

def dhas (d : IDict) (k : String) : Bool := d.any (·.1 == k)

/-- Julia `===` on the modeled property values. Object identity is the stored
object id; immutable scalar values are identical exactly when their payloads
and types agree. -/
def sameIdentity (a b : PV) : Bool := a == b

/-- `ImmutableDict(d, k, v)`: push a binding. -/
def dpush (d : IDict) (k : String) (v : PV) : IDict := (k, v) :: d

/-- The inner constructor `IOContext{IO_t}(io, dict)`, `base/show.jl:336-339`:
an `IOContext` argument is unwrapped to its stream. -/
def mkCtx (io : JIO) (dict : IDict) : JIO :=
  match io with
  | .plain b => .ctx b dict
  | .ctx b _ => .ctx b dict

/-- `ioproperties(io::IO)` and `ioproperties(io::IOContext)`, `base/show.jl:343-344`. -/
def ioproperties : JIO → IDict
  | .plain b => if b.color then [("color", .bool true)] else []
  | .ctx _ d => d

/-- `unwrapcontext(io::IO) = (io,)`, `unwrapcontext(io::IOContext) = (io.io,)`,
`base/show.jl:346-347`. -/
def unwrapcontext : JIO → JIO
  | .plain b => .plain b
  | .ctx b _ => .plain b

/-- `IOContext(io::IO, dict)` and `IOContext(io::IOContext, dict)`,
`base/show.jl:349-355`. -/
def ioContextDict (io : JIO) (dict : IDict) : JIO :=
  match io with
  | .plain b => mkCtx (.plain b) dict
  | .ctx b _ => mkCtx (.plain b) dict

/-- The `convert` methods, `base/show.jl:358-361`: an `IOContext` is returned
as is; another stream is wrapped with its `ioproperties`. -/
def convertCtx (io : JIO) : JIO :=
  match io with
  | .ctx b d => .ctx b d
  | .plain b => ioContextDict (.plain b) (ioproperties (.plain b))

/-- `IOContext(io::IO) = convert(IOContext, io)` and `IOContext{IO_t}(io)`,
`base/show.jl:363-364`. -/
def ioContext1 (io : JIO) : JIO := convertCtx io

/-- `IOContext(io::IO, KV::Pair)`, `base/show.jl:366-369`. -/
def ioContextPair (io : JIO) (kv : String × PV) : JIO :=
  ioContextDict io (dpush (ioproperties io) kv.1 kv.2)

/-- `IOContext(io::IO, context::IO) = IOContext(io, ioproperties(context))`,
`base/show.jl:381`. -/
def ioContextIO (io context : JIO) : JIO := ioContextDict io (ioproperties context)

/-- `IOContext(io::IO, KV::Pair, KVs::Pair...)`, `base/show.jl:456`. -/
def ioContextPairs (io : JIO) : List (String × PV) → JIO
  | [] => io
  | kv :: kvs => ioContextPairs (ioContextPair io kv) kvs

/-- `show(io, ctx::IOContext)`, `base/show.jl:458`; `shownInner` is `show(io, ctx.io)`. -/
def showCtx (shownInner : String) : Out := ["IOContext(", shownInner, ")"]

/-- `pipe_reader(io::IOContext) = io.io`, `pipe_writer`, and `lock`/`unlock`
forwarding, `base/show.jl:460-463`: all act on the wrapped stream. -/
def pipeReader : JIO → JIO := unwrapcontext
def pipeWriter : JIO → JIO := unwrapcontext
def lockTarget : JIO → JIO := unwrapcontext

/-- `in(key_value::Pair, io::IOContext) = in(key_value, io.dict, ===)` and
`in(key_value, io::IO) = false`, `base/show.jl:465-466`: any binding matches. -/
def inWith (identity : PV → PV → Bool) (kv : String × PV) : JIO → Bool
  | .plain _ => false
  | .ctx _ d => d.any (fun e => e.1 == kv.1 && identity e.2 kv.2)

def inCtx (kv : String × PV) (io : JIO) : Bool := inWith sameIdentity kv io

/-- `haskey`, `getindex`, `get`, `keys` on `IOContext` and plain `IO`,
`base/show.jl:467-474`. -/
def haskeyCtx (k : String) : JIO → Bool
  | .plain _ => false
  | .ctx _ d => dhas d k
def getindexCtx (k : String) : JIO → R PV
  | .plain _ => .error (.keyError k)
  | .ctx _ d => match d.find? (·.1 == k) with
    | some (_, v) => .ok v
    | none => .error (.keyError k)
def getCtx (k : String) (default : PV) : JIO → PV
  | .plain _ => default
  | .ctx _ d => dget d k default
def keysCtx : JIO → List String
  | .plain _ => []
  | .ctx _ d => d.map (·.1)

/-- `displaysize(io::IOContext)`, `base/show.jl:476`: the `:displaysize`
property if set (a non-tuple value fails the type assertion), else the stream's. -/
def displaysizeCtx : JIO → R (Int × Int)
  | .plain b => .ok b.displaysize
  | .ctx b d =>
    if dhas d "displaysize" then
      match dget d "displaysize" (.int 0) with
      | .dims r c => .ok (r, c)
      | _ => .error .typeError
    else .ok b.displaysize

/-- The loop of `show_circular(io::IOContext, x)`, `base/show.jl:481-489`:
`d` counts the `:SHOWN_SET` bindings seen, starting at 1. -/
def circularScan (x : PV) : Nat → IDict → Option Out
  | _, [] => none
  | d, (k, v) :: rest =>
    if k = "SHOWN_SET" then
      if v = x then some ["#= circular reference @-" ++ toString d ++ " =#"]
      else circularScan x (d + 1) rest
    else circularScan x d rest

/-- `show_circular(io::IO, x) = false` and `show_circular(io::IOContext, x)`,
`base/show.jl:478-491`: scanning the bindings newest first, the `d`-th
`:SHOWN_SET` binding that is `x` prints `#= circular reference @-d =#`. -/
def showCircular (x : PV) : JIO → Option Out
  | .plain _ => none
  | .ctx _ dict => circularScan x 1 dict

end JuliaLean.ShowCov.IOCtx
