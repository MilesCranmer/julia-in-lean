import JuliaLean.base.char
import JuliaLean.base.parse
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.io
import JuliaLean.base.strings.substring

/-!
# Model of `base/shell.jl`

Source-mirrored parsing at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
String, character, Meta.parseatom, Stateful and Core Expr operations are typed
callees. Stateful is loaded later in Base, so no backward iterator import is
introduced. The shared I/O world retains mutations before errors and represents
nontermination by none. Every Julia index and descriptor is JInt .i64.
-/

namespace JuliaLean.base.shell
open JuliaLean
abbrev I := JInt .i64
abbrev M := JuliaLean.base.io.M
abbrev Error := JuliaLean.base.io.Error

def i (n : Int) : I := JInt.wrap .i64 n
def add (a b : I) : I := JuliaLean.base.int.add a b

def raise {W A : Type} (message : String) : M W A :=
  throwThe Error (.errorException message)

inductive Builtin where
  | cmdGen | pipeline | cmdInterpolate | cmdRedirectTarget | expanduser
  deriving DecidableEq
inductive Head where
  | call | tuple | parameters | kw
  deriving DecidableEq

/-- The actual heterogeneous argument categories of the generated Julia AST. -/
inductive Term (S Atom Expr : Type) where
  | string (value : S)
  | atom (value : Atom)
  | expr (value : Expr)
  | symbol (name : String)
  | reference (name : Builtin)
  | boolean (value : Bool)

inductive RedirectMode where
  | none | stdin | stdout | stderr
  deriving DecidableEq

structure Segment (S Atom Expr : Type) where
  arguments : Expr
  stdin : Option (Term S Atom Expr)
  stdout : Option (Term S Atom Expr)
  stdoutAppend : Bool
  stderr : Option (Term S Atom Expr)
  stderrAppend : Bool

/-- Selected methods, with no laws or precomputed parsing result. Expr allocation
stores its head and ordered arguments; pushExpr mutates that expression's args.
The quote primitive constructs the literal tilde let-expression at shell.jl:289,
substituting the supplied parts without evaluating expanduser. -/
structure Ops (W S C Atom Expr Pairs Rev RevState Cursor File : Type) where
  literal : String → S
  atomString : Atom → Option S
  isempty : S → M W Bool
  firstindex : S → M W I
  lastindex : S → M W I
  offset : S → M W I
  substring : S → I → Option I → M W S
  slice : S → I → I → M W S
  lstrip : S → M W S
  nextind : S → I → M W I
  prevind : S → I → M W I
  getindex : S → I → M W C
  startswith : S → S → M W Bool
  string : S → M W S
  concat : S → S → M W S
  render : S → M W String
  writeString : S → M W Unit
  writeChar : C → M W Unit
  sprint : M W Unit → M W S
  escapeRawString : S → M W Unit
  eqAscii : C → Char → M W Bool
  isspace : C → M W Bool
  isdigit : C → M W Bool
  inChars : C → List Char → M W Bool
  inString : C → S → M W Bool
  allDigits : S → M W Bool
  parseInt : S → M W I
  pairs : S → M W Pairs
  reverse : Pairs → M W Rev
  iterateReverse : Rev → Option RevState → M W (Option ((I × C) × RevState))
  stateful : Pairs → M W Cursor
  iterate : Cursor → M W (Option (I × C))
  emptyCursor : Cursor → M W Bool
  peek : Cursor → M W (Option (I × C))
  popfirst : Cursor → M W (I × C)
  reset : Cursor → Pairs → M W Unit
  parseatom : S → I → File → M W (Atom × I)
  expr : Head → List (Term S Atom Expr) → M W Expr
  pushExpr : Expr → Term S Atom Expr → M W Unit
  tildeQuote : List (Term S Atom Expr) → M W Expr

variable {W S C Atom Expr Pairs Rev RevState Cursor File : Type}

def asString (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File) :
    Term S Atom Expr → Option S
  | .string value => some value
  | .atom value => ops.atomString value
  | _ => none

def peekPair (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File) (cursor : Cursor) : M W (I × C) := do
  match ← ops.peek cursor with
  | some pair => pure pair
  | none => throwThe Error (.foreignError "TypeError" "expected a pair")

def nextCursorIndex (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (cursor : Cursor) (s : S) : M W I := do
  let next ← ops.peek cursor
  let last ← ops.lastindex s
  pure (match next with | some pair => pair.1 | none => add last (i 1))

structure ParserState (S Atom Expr Cursor : Type) where
  s : S
  cursor : Cursor
  inSingle : Bool := false
  inDouble : Bool := false
  args : List (List (Term S Atom Expr)) := []
  arg : List (Term S Atom Expr) := []
  index : I
  lastArg : I
  updateLast : Bool := false
  hasSpecial : Bool := false
  parts : List (Segment S Atom Expr) := []
  stdin : Option (Term S Atom Expr) := none
  stdout : Option (Term S Atom Expr) := none
  stdoutAppend : Bool := false
  stderr : Option (Term S Atom Expr) := none
  stderrAppend : Bool := false
  mode : RedirectMode := .none

inductive Parsed (S Atom Expr : Type) where
  | words (arguments : List (List (Term S Atom Expr)))
  | expression (value : Expr)


/--
Julia source: base/shell.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const shell_special = "#{}()[]<>|&*?;"
```
-/
def shellSpecial : String := "#{}()[]<>|&*?;"

/--
Julia source: base/shell.jl:20-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function rstrip_shell(s::AbstractString)
    c_old = nothing
    for (i, c) in Iterators.reverse(pairs(s))
        i::Int; c::AbstractChar
        ((c == '\\') && c_old == ' ') && return SubString(s, 1, i+1)
        isspace(c) || return SubString(s, 1, i)
        c_old = c
    end
    SubString(s, 1, 0)
end)
```
-/
def rstripShell (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File) (s : S) : M W S := do
  let reverse ← ops.reverse (← ops.pairs s)
  JuliaLean.base.io.whileLoop (fun (state : Option RevState × Option C) => do
    match ← ops.iterateReverse reverse state.1 with
    | none => pure (.inl (← ops.substring s (i 1) (some (i 0))))
    | some ((index,c),next) =>
        if ← ops.eqAscii c '\\' then
          match state.2 with
          | some previous =>
              if ← ops.eqAscii previous ' ' then
                return .inl (← ops.substring s (i 1) (some (add index (i 1))))
          | none => pure ()
        if !(← ops.isspace c) then
          pure (.inl (← ops.substring s (i 1) (some index)))
        else pure (.inr (some next,some c))) (none,none)


/--
Julia source: base/shell.jl:63-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function push_nonempty!(list, x)
        if !isa(x,AbstractString) || !isempty(x)
            push!(list, x)
        end
        return nothing
    end
```
-/
def pushNonempty (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (list : List (Term S Atom Expr)) (value : Term S Atom Expr) : M W (List (Term S Atom Expr)) := do
  match asString ops value with
  | none => pure (list ++ [value])
  | some valueString => if ← ops.isempty valueString then pure list else pure (list ++ [value])


/--
Julia source: base/shell.jl:69-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function consume_upto!(list, s, i, j)
        push_nonempty!(list, s[i:prevind(s, j)::Int])
        something(peek(st), lastindex(s)::Int+1 => '\0').first::Int
    end
```
-/
def consumeUpto (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (cursor : Cursor) (list : List (Term S Atom Expr)) (s : S) (first stop : I) :
    M W (List (Term S Atom Expr) × I) := do
  let list ← pushNonempty ops list (.string (← ops.slice s first (← ops.prevind s stop)))
  pure (list,← nextCursorIndex ops cursor s)


/--
Julia source: base/shell.jl:73-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function append_2to1!(list, innerlist)
        if isempty(innerlist); push!(innerlist, ""); end
        push!(list, copy(innerlist))
        empty!(innerlist)
    end
```
-/
def append2to1 (empty : S) (args : List (List (Term S Atom Expr)))
    (arg : List (Term S Atom Expr)) : List (List (Term S Atom Expr)) × List (Term S Atom Expr) :=
  (args ++ [if arg.isEmpty then [.string empty] else arg],[])


/--
Julia source: base/shell.jl:86-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function parse_dollar_interp(st, s)
        isempty(st) && error("\$ right before end of command")
        stpos, c = popfirst!(st)::P
        isspace(c) && error("space not allowed right after \$")
        if startswith(SubString(s, stpos), "var\"")
            # Disallow var"#" syntax in cmd interpolations.
            # TODO: Allow only identifiers after the $ for consistency with
            # string interpolation syntax (see #3150)
            atom, j = :var, stpos+3
        else
            # use parseatom instead of parse to respect filename (#28188)
            atom, j = Meta.parseatom(s, stpos, filename=filename)
        end
        interp_pos = stpos + s.offset
        s = SubString(s, j)
        Iterators.reset!(st, pairs(s))
        return atom, s, interp_pos
    end
```
-/
def parseDollar (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (filename : File) (cursor : Cursor) (s : S) : M W (Term S Atom Expr × S × I) := do
  if ← ops.emptyCursor cursor then raise "$ right before end of command"
  let (position,c) ← ops.popfirst cursor
  if ← ops.isspace c then raise "space not allowed right after $"
  let (atom,next) ← if ← ops.startswith (← ops.substring s position none) (ops.literal "var\"") then
      pure (Term.symbol "var",add position (i 3))
    else do
      let (atom,next) ← ops.parseatom s position filename
      pure (.atom atom,next)
  let absolute := add position (← ops.offset s)
  let s ← ops.substring s next none
  ops.reset cursor (← ops.pairs s)
  pure (atom,s,absolute)


/--
Julia source: base/shell.jl:106-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function redirect_word_expr(word)
        if length(word) == 1 && isa(word[1], AbstractString)
            return String(word[1])
        elseif length(word) == 1
            return Expr(:call, GlobalRef(Base, :cmd_redirect_target), word[1])
        else
            return Expr(:call, GlobalRef(Base, :cmd_interpolate), word...)
        end
    end
```
-/
def redirectWordExpr (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (word : List (Term S Atom Expr)) : M W (Term S Atom Expr) := do
  match word with
  | [value] =>
      match asString ops value with
      | some text => pure (.string (← ops.string text))
      | none => pure (.expr (← ops.expr .call [.reference .cmdRedirectTarget,value]))
  | values => pure (.expr (← ops.expr .call (.reference .cmdInterpolate :: values)))


def setRedirect (state : ParserState S Atom Expr Cursor) (value : Term S Atom Expr) : ParserState S Atom Expr Cursor :=
  match state.mode with
  | .stdin => {state with stdin := some value}
  | .stdout => {state with stdout := some value}
  | _ => {state with stderr := some value}

def tupleOf (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List (List (Term S Atom Expr))) : M W Expr := do
  let tuple ← ops.expr .tuple []
  for arg in args do
    ops.pushExpr tuple (.expr (← ops.expr .tuple arg))
  pure tuple

def finishWord (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (resetMode : Bool) (state : ParserState S Atom Expr Cursor) : M W (ParserState S Atom Expr Cursor) := do
  if state.mode != .none && (!state.arg.isEmpty || state.hasSpecial) then
    let state := setRedirect state (← redirectWordExpr ops state.arg)
    pure {state with arg := [],mode := if resetMode then .none else state.mode}
  else if state.mode = .none && (!state.arg.isEmpty || state.hasSpecial) then
    let (args,arg) := append2to1 (ops.literal "") state.args state.arg
    pure {state with args,arg}
  else pure state

def skipWhitespace (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (state : ParserState S Atom Expr Cursor) : M W (ParserState S Atom Expr Cursor) :=
  JuliaLean.base.io.whileLoop (fun state => do
    if ← ops.emptyCursor state.cursor then return .inl state
    let (index,c) ← peekPair ops state.cursor
    let state := {state with index}
    if !(← ops.isspace c) then return .inl state
    let _ ← ops.popfirst state.cursor
    pure (.inr state)) state

def skipIndent (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (advanceIndex : Bool) (state : ParserState S Atom Expr Cursor) :
    M W (ParserState S Atom Expr Cursor) :=
  JuliaLean.base.io.whileLoop (fun state => do
    if ← ops.emptyCursor state.cursor then return .inl state
    let (_,c) ← peekPair ops state.cursor
    if !(← ops.inChars c [' ','\t']) then return .inl state
    let state ← if advanceIndex then do
        let index ← ops.nextind original state.index
        pure {state with index}
      else pure state
    let _ ← ops.popfirst state.cursor
    pure (.inr state)) state


def tildeStop (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File) (c : C) : M W Bool := do
  if ← ops.eqAscii c '/' then return true
  if ← ops.isspace c then return true
  for stop in ['\'','"','\\','|','<','>'] do
    if ← ops.eqAscii c stop then return true
  pure false

def tildeParts (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (filename : File) (initial : ParserState S Atom Expr Cursor) :
    M W (ParserState S Atom Expr Cursor × List (Term S Atom Expr) × I) :=
  JuliaLean.base.io.whileLoop (fun (current : ParserState S Atom Expr Cursor × List (Term S Atom Expr) × I) => do
    let (state,parts,start) := current
    if ← ops.emptyCursor state.cursor then return .inl current
    let (position,c) ← peekPair ops state.cursor
    let continuation ← if ← ops.eqAscii c '\\' then do
        let next ← ops.nextind state.s position
        let last ← ops.lastindex state.s
        if next.val ≤ last.val then
          ops.inChars (← ops.getindex state.s (← ops.nextind state.s position)) ['\n','\r']
        else pure false
      else pure false
    if continuation then
      let parts ← pushNonempty ops parts (.string (← ops.slice state.s start (← ops.prevind state.s position)))
      let _ ← ops.popfirst state.cursor
      let (_,newline) ← ops.popfirst state.cursor
      if ← ops.eqAscii newline '\r' then
        if !(← ops.emptyCursor state.cursor) then
          if ← ops.eqAscii (← peekPair ops state.cursor).2 '\n' then
            let _ ← ops.popfirst state.cursor
            pure ()
      let state ← skipIndent ops original false state
      let start ← nextCursorIndex ops state.cursor state.s
      return .inr (state,parts,start)
    if ← tildeStop ops c then return .inl current
    if ← ops.eqAscii c '$' then
      let parts ← pushNonempty ops parts (.string (← ops.slice state.s start (← ops.prevind state.s position)))
      let _ ← ops.popfirst state.cursor
      let (atom,s,_) ← parseDollar ops filename state.cursor state.s
      let index ← ops.firstindex s
      pure (.inr ({state with s,index},parts ++ [atom],index))
    else
      let _ ← ops.popfirst state.cursor
      pure (.inr current)) (initial,[],initial.index)

def expandTilde (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (filename : File) (initial : ParserState S Atom Expr Cursor) :
    M W (ParserState S Atom Expr Cursor) := do
  let (state,parts,start) ← tildeParts ops original filename initial
  let stop ← nextCursorIndex ops state.cursor state.s
  let parts ← pushNonempty ops parts (.string (← ops.slice state.s start (← ops.prevind state.s stop)))
  let quoted ← if !(← ops.emptyCursor state.cursor) then
      ops.inChars (← peekPair ops state.cursor).2 ['\'','"','\\']
    else pure false
  let arg ← if quoted then pure (state.arg ++ [.string (ops.literal "~")] ++ parts)
    else if parts.isEmpty then do
      let ex ← ops.expr .call [.reference .expanduser,.string (ops.literal "~")]
      pure (state.arg ++ [.expr ex])
    else
      match parts with
      | [part] =>
          match asString ops part with
          | some text => do
              let name ← ops.concat (ops.literal "~") text
              let ex ← ops.expr .call [.reference .expanduser,.string name]
              pure (state.arg ++ [.expr ex])
          | none => do pure (state.arg ++ [.expr (← ops.tildeQuote parts)])
      | _ => do pure (state.arg ++ [.expr (← ops.tildeQuote parts)])
  pure {state with arg,index := stop}

def descriptorOfWord (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (hasSpecial : Bool) (arg : List (Term S Atom Expr)) : M W (Option I) := do
  if hasSpecial then return none
  match arg with
  | [value] =>
      match asString ops value with
      | some text =>
          if !(← ops.isempty text) then
            if ← ops.allDigits text then
              return some (← ops.parseInt (← ops.string text))
          pure none
      | none => pure none
  | _ => pure none

def redirectStep (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (state : ParserState S Atom Expr Cursor) (position : I) (c : C) :
    M W (ParserState S Atom Expr Cursor) := do
  let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
  let state := {state with arg,index}
  let descriptor ← descriptorOfWord ops state.hasSpecial arg
  let state := if descriptor.isSome then {state with arg := [],hasSpecial := false}
    else if !state.arg.isEmpty then
      let (args,arg) := append2to1 (ops.literal "") state.args state.arg
      {state with args,arg}
    else state
  let state ← if ← ops.eqAscii c '>' then do
      let append ← if !(← ops.emptyCursor state.cursor) then
          ops.eqAscii (← peekPair ops state.cursor).2 '>'
        else pure false
      let state ← if append then do
          let _ ← ops.popfirst state.cursor
          pure {state with index := ← nextCursorIndex ops state.cursor state.s}
        else pure state
      match descriptor with
      | none => pure {state with mode := .stdout,stdoutAppend := append}
      | some descriptor =>
          if descriptor.val = 1 then pure {state with mode := .stdout,stdoutAppend := append}
          else if descriptor.val = 2 then pure {state with mode := .stderr,stderrAppend := append}
          else raise ("parsing command `" ++ (← ops.render original) ++ "`: unsupported fd " ++ toString descriptor.val ++ " in redirection")
    else do
      match descriptor with
      | none => pure {state with mode := .stdin}
      | some descriptor =>
          if descriptor.val = 0 then pure {state with mode := .stdin}
          else raise ("parsing command `" ++ (← ops.render original) ++ "`: unsupported fd " ++ toString descriptor.val ++ " in redirection")
  pure {state with updateLast := true}

def parserStep (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (interpolate : Bool) (special : S) (filename : File)
    (initial : ParserState S Atom Expr Cursor) (position : I) (c : C) :
    M W (ParserState S Atom Expr Cursor) := do
  if !initial.inSingle && !initial.inDouble then
    if ← ops.isspace c then
      let (arg,index) ← consumeUpto ops initial.cursor initial.arg initial.s initial.index position
      let state ← finishWord ops true {initial with arg,index,updateLast := true}
      return ← skipWhitespace ops {state with hasSpecial := false}
  if interpolate && !initial.inSingle then
    if ← ops.eqAscii c '$' then
      let (arg,_) ← consumeUpto ops initial.cursor initial.arg initial.s initial.index position
      let (atom,s,absolute) ← parseDollar ops filename initial.cursor initial.s
      let index ← ops.firstindex s
      return {initial with s,index,arg := arg ++ [atom],lastArg := absolute,updateLast := true}
  if interpolate && !initial.inSingle && !initial.inDouble then
    if ← ops.eqAscii c '|' then
      let (arg,index) ← consumeUpto ops initial.cursor initial.arg initial.s initial.index position
      let state ← finishWord ops false {initial with arg,index}
      let segment ← tupleOf ops state.args
      let part : Segment S Atom Expr := ⟨segment,state.stdin,state.stdout,state.stdoutAppend,state.stderr,state.stderrAppend⟩
      return {state with args := [],parts := state.parts ++ [part],stdin := none,stdout := none,stdoutAppend := false,stderr := none,stderrAppend := false,mode := .none,hasSpecial := false,updateLast := true}
    let redirect ← if ← ops.eqAscii c '<' then pure true else ops.eqAscii c '>'
    if redirect then return ← redirectStep ops original initial position c
  let state ← if initial.updateLast then do
      pure {initial with lastArg := add initial.index (← ops.offset initial.s),updateLast := false}
    else pure initial
  if !state.inDouble then
    if ← ops.eqAscii c '\'' then
      let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
      return {state with inSingle := !state.inSingle,hasSpecial := true,arg,index}
  if !state.inSingle then
    if ← ops.eqAscii c '"' then
      let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
      return {state with inDouble := !state.inDouble,hasSpecial := true,arg,index}
    if ← ops.eqAscii c '\\' then
      let state := {state with hasSpecial := true}
      let continuation ← if !(← ops.emptyCursor state.cursor) then
          ops.inChars (← peekPair ops state.cursor).2 ['\n','\r']
        else pure false
      if continuation then
        let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
        let state := {state with arg,index := add index (i 1)}
        let (_,newline) ← ops.popfirst state.cursor
        let state ← if ← ops.eqAscii newline '\r' then do
            if ← ops.eqAscii (← peekPair ops state.cursor).2 '\n' then
              let _ ← ops.popfirst state.cursor
              pure {state with index := add state.index (i 1)}
            else pure state
          else pure state
        return ← skipIndent ops original true state
      else if state.inDouble then
        if ← ops.emptyCursor state.cursor then raise "unterminated double quote"
        let (_,next) ← peekPair ops state.cursor
        if ← ops.inChars next ['"','$','\\'] then
          let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
          let _ ← ops.popfirst state.cursor
          return {state with arg,index}
        return state
      else
        if ← ops.emptyCursor state.cursor then raise "dangling backslash"
        let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
        let _ ← ops.popfirst state.cursor
        return {state with arg,index}
  if interpolate && !state.inSingle && !state.inDouble then
    if ← ops.eqAscii c '~' then
      if state.index = position && state.arg.isEmpty then
        let (arg,index) ← consumeUpto ops state.cursor state.arg state.s state.index position
        return ← expandTilde ops original filename {state with arg,index}
  if !state.inSingle && !state.inDouble then
    if ← ops.inString c special then
      raise ("parsing command `" ++ (← ops.render original) ++ "`: special characters \"" ++ (← ops.render special) ++ "\" must be quoted in commands")
  pure state


/--
Julia source: base/shell.jl:328-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function build_seg_expr(seg_tuple, s_in, s_out, s_out_app, s_err, s_err_app)
        cmd_ex = Expr(:call, GlobalRef(Base, :cmd_gen), seg_tuple)
        if s_in !== nothing || s_out !== nothing
            kwargs = Any[]
            s_in !== nothing && push!(kwargs, Expr(:kw, :stdin, s_in))
            s_out !== nothing && push!(kwargs, Expr(:kw, :stdout, s_out))
            s_out_app && push!(kwargs, Expr(:kw, :append, true))
            cmd_ex = Expr(:call, GlobalRef(Base, :pipeline), Expr(:parameters, kwargs...), cmd_ex)
        end
        if s_err !== nothing
            kwargs = Any[Expr(:kw, :stderr, s_err)]
            s_err_app && push!(kwargs, Expr(:kw, :append, true))
            cmd_ex = Expr(:call, GlobalRef(Base, :pipeline), Expr(:parameters, kwargs...), cmd_ex)
        end
        return cmd_ex
    end
```
-/
def buildSegment (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (segment : Segment S Atom Expr) : M W Expr := do
  let command ← ops.expr .call [.reference .cmdGen,.expr segment.arguments]
  let command ← if segment.stdin.isSome || segment.stdout.isSome then do
      let kwargs ← match segment.stdin with
        | none => pure []
        | some input => do pure [.expr (← ops.expr .kw [.symbol "stdin",input])]
      let kwargs ← match segment.stdout with
        | none => pure kwargs
        | some output => do pure (kwargs ++ [.expr (← ops.expr .kw [.symbol "stdout",output])])
      let kwargs ← if segment.stdoutAppend then do
          pure (kwargs ++ [.expr (← ops.expr .kw [.symbol "append",.boolean true])])
        else pure kwargs
      let parameters ← ops.expr .parameters kwargs
      ops.expr .call [.reference .pipeline,.expr parameters,.expr command]
    else pure command
  match segment.stderr with
  | none => pure command
  | some output =>
      let kwargs := [.expr (← ops.expr .kw [.symbol "stderr",output])]
      let kwargs ← if segment.stderrAppend then do
          pure (kwargs ++ [.expr (← ops.expr .kw [.symbol "append",.boolean true])])
        else pure kwargs
      let parameters ← ops.expr .parameters kwargs
      ops.expr .call [.reference .pipeline,.expr parameters,.expr command]


/--
Julia source: base/shell.jl:36-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __repl_entry_shell_parse(str::AbstractString, interpolate::Bool, special::AbstractString, filename)
    last_arg = firstindex(str) # N.B.: This is used by REPLCompletions
    s = SubString(str, last_arg)
    s = rstrip_shell(lstrip(s))

    isempty(s) && return interpolate ? (Expr(:tuple,:()), last_arg) : ([], last_arg)

    in_single_quotes = false
    in_double_quotes = false

    args = []
    arg = []
    i = firstindex(s)
    st = Iterators.Stateful(pairs(s))
    update_last_arg = false # true after spaces or interpolate
    word_has_special = false # true if current word contains any quoted/escaped content

    # Pipeline/redirection state (used only when interpolate=true).
    # pipeline_parts accumulates completed segments as (seg_tuple, stdin, stdout, stdout_append, stderr, stderr_append).
    pipeline_parts = []
    seg_stdin = nothing        # stdin redirect expression for current segment
    seg_stdout = nothing       # stdout redirect expression for current segment
    seg_stdout_append = false  # true if stdout redirect is >> (append mode)
    seg_stderr = nothing       # stderr redirect expression for current segment
    seg_stderr_append = false  # true if stderr redirect is >> (append mode)
    redirect_mode = :none      # :none | :stdin | :stdout | :stderr

    function push_nonempty!(list, x)
        if !isa(x,AbstractString) || !isempty(x)
            push!(list, x)
        end
        return nothing
    end
    function consume_upto!(list, s, i, j)
        push_nonempty!(list, s[i:prevind(s, j)::Int])
        something(peek(st), lastindex(s)::Int+1 => '\0').first::Int
    end
    function append_2to1!(list, innerlist)
        if isempty(innerlist); push!(innerlist, ""); end
        push!(list, copy(innerlist))
        empty!(innerlist)
    end

    C = eltype(str)
    P = Pair{Int,C}

    # Parse the expression following a `$` interpolation marker.
    # Pops the first char of the expression from `st`, parses the atom, advances
    # `s` past it, and resets `st`. Returns `(expr, new_s, interp_pos)` where
    # `interp_pos` is the absolute position in `str` (for REPLCompletions).
    function parse_dollar_interp(st, s)
        isempty(st) && error("\$ right before end of command")
        stpos, c = popfirst!(st)::P
        isspace(c) && error("space not allowed right after \$")
        if startswith(SubString(s, stpos), "var\"")
            # Disallow var"#" syntax in cmd interpolations.
            # TODO: Allow only identifiers after the $ for consistency with
            # string interpolation syntax (see #3150)
            atom, j = :var, stpos+3
        else
            # use parseatom instead of parse to respect filename (#28188)
            atom, j = Meta.parseatom(s, stpos, filename=filename)
        end
        interp_pos = stpos + s.offset
        s = SubString(s, j)
        Iterators.reset!(st, pairs(s))
        return atom, s, interp_pos
    end

    # Convert a word (list of string/expr parts) to a redirect filename expression.
    function redirect_word_expr(word)
        if length(word) == 1 && isa(word[1], AbstractString)
            return String(word[1])
        elseif length(word) == 1
            return Expr(:call, GlobalRef(Base, :cmd_redirect_target), word[1])
        else
            return Expr(:call, GlobalRef(Base, :cmd_interpolate), word...)
        end
    end

    for (j, c) in st
        j, c = j::Int, c::C
        if !in_single_quotes && !in_double_quotes && isspace(c)
            update_last_arg = true
            i = consume_upto!(arg, s, i, j)
            if redirect_mode != :none && (!isempty(arg) || word_has_special)
                # This word is the redirect filename.
                re = redirect_word_expr(arg)
                if redirect_mode === :stdin; seg_stdin = re
                elseif redirect_mode === :stdout; seg_stdout = re
                else; seg_stderr = re; end
                empty!(arg)
                redirect_mode = :none
            elseif redirect_mode == :none && (!isempty(arg) || word_has_special)
                append_2to1!(args, arg)
            end
            word_has_special = false
            # else: in redirect_mode but arg empty — still waiting for the filename.
            while !isempty(st)
                # We've made sure above that we don't end in whitespace,
                # so updating `i` here is ok
                (i, c) = peek(st)::P
                isspace(c) || break
                popfirst!(st)
            end
        elseif interpolate && !in_single_quotes && c == '$'
            consume_upto!(arg, s, i, j)
            result = parse_dollar_interp(st, s)
            s = result[2]
            last_arg = result[3]
            update_last_arg = true
            push!(arg, result[1])
            i = firstindex(s)
        elseif interpolate && !in_single_quotes && !in_double_quotes && c == '|'
            # Pipeline operator: finalize current word/redirect, then save segment.
            i = consume_upto!(arg, s, i, j)
            if redirect_mode != :none && (!isempty(arg) || word_has_special)
                re = redirect_word_expr(arg)
                if redirect_mode === :stdin; seg_stdin = re
                elseif redirect_mode === :stdout; seg_stdout = re
                else; seg_stderr = re; end
                empty!(arg)
            elseif redirect_mode == :none && (!isempty(arg) || word_has_special)
                append_2to1!(args, arg)
            end
            seg_tuple = Expr(:tuple)
            for a in args; push!(seg_tuple.args, Expr(:tuple, a...)); end
            push!(pipeline_parts, (seg_tuple, seg_stdin, seg_stdout, seg_stdout_append,
                                   seg_stderr, seg_stderr_append))
            empty!(args)
            seg_stdin = nothing; seg_stdout = nothing; seg_stdout_append = false
            seg_stderr = nothing; seg_stderr_append = false; redirect_mode = :none
            word_has_special = false
            update_last_arg = true
        elseif interpolate && !in_single_quotes && !in_double_quotes && (c == '<' || c == '>')
            # Redirection operator: finalize any pending word, then set redirect mode.
            # A pure-integer word immediately before the operator is an fd number (e.g. 2>).
            i = consume_upto!(arg, s, i, j)
            fd = nothing
            if !word_has_special && length(arg) == 1 && isa(arg[1], AbstractString) &&
                    !isempty(arg[1]::AbstractString) && all(isdigit, arg[1]::AbstractString)
                fd = parse(Int, String(arg[1]::AbstractString)::String)
                empty!(arg)
                word_has_special = false
            elseif !isempty(arg)
                append_2to1!(args, arg)
            end
            if c == '>'
                append = false
                if !isempty(st) && (peek(st)::P).second == '>'
                    popfirst!(st)  # consume second >
                    append = true
                    i = something(peek(st), lastindex(s)::Int+1 => '\0').first::Int
                end
                if fd === nothing || fd == 1
                    redirect_mode = :stdout; seg_stdout_append = append
                elseif fd == 2
                    redirect_mode = :stderr; seg_stderr_append = append
                else
                    error("parsing command `$str`: unsupported fd $fd in redirection")
                end
            else  # '<'
                (fd === nothing || fd == 0) ||
                    error("parsing command `$str`: unsupported fd $fd in redirection")
                redirect_mode = :stdin
            end
            update_last_arg = true
        else
            if update_last_arg
                last_arg = i + s.offset
                update_last_arg = false
            end
            if !in_double_quotes && c == '\''
                in_single_quotes = !in_single_quotes
                word_has_special = true
                i = consume_upto!(arg, s, i, j)
            elseif !in_single_quotes && c == '"'
                in_double_quotes = !in_double_quotes
                word_has_special = true
                i = consume_upto!(arg, s, i, j)
            elseif !in_single_quotes && c == '\\'
                word_has_special = true
                if !isempty(st) && (peek(st)::P)[2] in ('\n', '\r')
                    i = consume_upto!(arg, s, i, j) + 1
                    if popfirst!(st)[2] == '\r' && (peek(st)::P)[2] == '\n'
                        i += 1
                        popfirst!(st)
                    end
                    while !isempty(st) && (peek(st)::P)[2] in (' ', '\t')
                        i = nextind(str, i)
                        _ = popfirst!(st)
                    end
                elseif in_double_quotes
                    isempty(st) && error("unterminated double quote")
                    _, c′ = peek(st)::P
                    if c′ == '"' || c′ == '$' || c′ == '\\'
                        i = consume_upto!(arg, s, i, j)
                        _ = popfirst!(st)
                    end
                else
                    isempty(st) && error("dangling backslash")
                    i = consume_upto!(arg, s, i, j)
                    _ = popfirst!(st)
                end
            elseif interpolate && !in_single_quotes && !in_double_quotes &&
                    c == '~' && i == j && isempty(arg)
                # Tilde expansion: `~` or `~username` at start of a word.
                # Collect the username, which may include $interpolations (e.g. `~$user`).
                # Stop at /, whitespace, uninterpolable chars (quotes, backslash), or operators.
                i = consume_upto!(arg, s, i, j)  # i now points past the ~
                user_parts = []
                user_lit_start = i
                while !isempty(st)
                    nxt = peek(st)::P
                    nc = nxt[2]
                    if nc == '\\' && nextind(s, nxt[1]) <= lastindex(s) && s[nextind(s, nxt[1])] in ('\n', '\r')
                        # A line continuation joins the lines without ending the user name.
                        push_nonempty!(user_parts, s[user_lit_start:prevind(s, nxt[1])])
                        popfirst!(st)
                        if popfirst!(st)[2] == '\r' && !isempty(st) && (peek(st)::P)[2] == '\n'
                            popfirst!(st)
                        end
                        while !isempty(st) && (peek(st)::P)[2] in (' ', '\t')
                            popfirst!(st)
                        end
                        user_lit_start = something(peek(st), (lastindex(s) + 1) => '\0').first
                        continue
                    end
                    (nc == '/' || isspace(nc) || nc == '\'' || nc == '"' || nc == '\\' ||
                     nc == '|' || nc == '<' || nc == '>') && break
                    if nc == '$'
                        push_nonempty!(user_parts, s[user_lit_start:prevind(s, nxt[1])])
                        popfirst!(st)  # consume $
                        result = parse_dollar_interp(st, s)
                        push!(user_parts, result[1])
                        s = result[2]
                        i = firstindex(s)
                        user_lit_start = i
                    else
                        popfirst!(st)
                    end
                end
                user_end = something(peek(st), (lastindex(s) + 1) => '\0').first
                push_nonempty!(user_parts, s[user_lit_start:prevind(s, user_end)])
                if !isempty(st) && (peek(st)::P)[2] in ('\'', '"', '\\')
                    # As in POSIX shells, a quoted character before the first `/` disables expansion.
                    push!(arg, "~")
                    append!(arg, user_parts)
                elseif isempty(user_parts)
                    push!(arg, :(expanduser("~")))
                elseif length(user_parts) == 1 && (u = user_parts[1]; u isa AbstractString)
                    push!(arg, :(expanduser($("~" * u))))
                else
                    push!(arg, :(let _u = string($(user_parts...)); isempty(_u) ? "~" : expanduser(string('~', _u)) end))
                end
                i = user_end
            elseif !in_single_quotes && !in_double_quotes && c in special
                error("parsing command `$str`: special characters \"$special\" must be quoted in commands")
            end
        end
    end

    if in_single_quotes; error("unterminated single quote"); end
    if in_double_quotes; error("unterminated double quote"); end

    push_nonempty!(arg, s[i:end])
    if interpolate && redirect_mode != :none
        isempty(arg) && error("parsing command `$str`: redirect operator without filename")
        re = redirect_word_expr(arg)
        if redirect_mode === :stdin; seg_stdin = re
        elseif redirect_mode === :stdout; seg_stdout = re
        else; seg_stderr = re; end
        empty!(arg)
    elseif !isempty(arg) || word_has_special
        append_2to1!(args, arg)
    end

    interpolate || return args, last_arg

    # If no pipeline operators and no redirects: return existing tuple format (backward compat).
    if isempty(pipeline_parts) && seg_stdin === nothing && seg_stdout === nothing &&
            seg_stderr === nothing
        ex = Expr(:tuple)
        for arg in args
            push!(ex.args, Expr(:tuple, arg...))
        end
        return ex, last_arg
    end

    # Build a cmd_gen(seg_tuple) expression, wrapped in pipeline() calls for each redirect.
    # stdin and stdout (with its append flag) are combined into one call; stderr is separate
    # so that different append modes can be handled independently.
    function build_seg_expr(seg_tuple, s_in, s_out, s_out_app, s_err, s_err_app)
        cmd_ex = Expr(:call, GlobalRef(Base, :cmd_gen), seg_tuple)
        if s_in !== nothing || s_out !== nothing
            kwargs = Any[]
            s_in !== nothing && push!(kwargs, Expr(:kw, :stdin, s_in))
            s_out !== nothing && push!(kwargs, Expr(:kw, :stdout, s_out))
            s_out_app && push!(kwargs, Expr(:kw, :append, true))
            cmd_ex = Expr(:call, GlobalRef(Base, :pipeline), Expr(:parameters, kwargs...), cmd_ex)
        end
        if s_err !== nothing
            kwargs = Any[Expr(:kw, :stderr, s_err)]
            s_err_app && push!(kwargs, Expr(:kw, :append, true))
            cmd_ex = Expr(:call, GlobalRef(Base, :pipeline), Expr(:parameters, kwargs...), cmd_ex)
        end
        return cmd_ex
    end

    # Build the final segment's tuple.
    final_seg_tuple = Expr(:tuple)
    for a in args; push!(final_seg_tuple.args, Expr(:tuple, a...)); end

    if isempty(pipeline_parts)
        # Only redirects, no pipes.
        return build_seg_expr(final_seg_tuple, seg_stdin, seg_stdout, seg_stdout_append,
                              seg_stderr, seg_stderr_append), last_arg
    end

    # Chain pipeline segments left-to-right: pipeline(seg1, pipeline(seg2, seg3, ...)).
    (s0_args, s0_in, s0_out, s0_out_app, s0_err, s0_err_app) = pipeline_parts[1]
    result = build_seg_expr(s0_args, s0_in, s0_out, s0_out_app, s0_err, s0_err_app)
    for k in 2:length(pipeline_parts)
        (sk_args, sk_in, sk_out, sk_out_app, sk_err, sk_err_app) = pipeline_parts[k]
        result = Expr(:call, GlobalRef(Base, :pipeline), result,
                      build_seg_expr(sk_args, sk_in, sk_out, sk_out_app, sk_err, sk_err_app))
    end
    result = Expr(:call, GlobalRef(Base, :pipeline), result,
                  build_seg_expr(final_seg_tuple, seg_stdin, seg_stdout, seg_stdout_append,
                                 seg_stderr, seg_stderr_append))

    return result, last_arg
end
```
-/
def replEntryShellParse (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (interpolate : Bool) (special : S) (filename : File) :
    M W (Parsed S Atom Expr × I) := do
  let lastArg ← ops.firstindex original
  let s ← rstripShell ops (← ops.lstrip (← ops.substring original lastArg none))
  if ← ops.isempty s then
    if interpolate then
      let inner ← ops.expr .tuple []
      return (.expression (← ops.expr .tuple [.expr inner]),lastArg)
    else return (.words [],lastArg)
  let index ← ops.firstindex s
  let cursor ← ops.stateful (← ops.pairs s)
  let initial : ParserState S Atom Expr Cursor := {s,cursor,index,lastArg}
  let state ← JuliaLean.base.io.whileLoop (fun state => do
    match ← ops.iterate state.cursor with
    | none => pure (.inl state)
    | some (position,c) => pure (.inr (← parserStep ops original interpolate special filename state position c))) initial
  if state.inSingle then raise "unterminated single quote"
  if state.inDouble then raise "unterminated double quote"
  let arg ← pushNonempty ops state.arg (.string (← ops.slice state.s state.index (← ops.lastindex state.s)))
  let state := {state with arg}
  let state ← if interpolate && state.mode != .none then do
      if state.arg.isEmpty then
        raise ("parsing command `" ++ (← ops.render original) ++ "`: redirect operator without filename")
      let state := setRedirect state (← redirectWordExpr ops state.arg)
      pure {state with arg := []}
    else if !state.arg.isEmpty || state.hasSpecial then
      let (args,arg) := append2to1 (ops.literal "") state.args state.arg
      pure {state with args,arg}
    else pure state
  if !interpolate then return (.words state.args,state.lastArg)
  if state.parts.isEmpty && state.stdin.isNone && state.stdout.isNone && state.stderr.isNone then
    return (.expression (← tupleOf ops state.args),state.lastArg)
  let finalArgs ← tupleOf ops state.args
  let finalSegment : Segment S Atom Expr := ⟨finalArgs,state.stdin,state.stdout,state.stdoutAppend,state.stderr,state.stderrAppend⟩
  match state.parts with
  | [] => pure (.expression (← buildSegment ops finalSegment),state.lastArg)
  | first :: rest =>
      let initial ← buildSegment ops first
      let command ← rest.foldlM (fun command segment => do
        let next ← buildSegment ops segment
        ops.expr .call [.reference .pipeline,.expr command,.expr next]) initial
      let final ← buildSegment ops finalSegment
      pure (.expression (← ops.expr .call [.reference .pipeline,.expr command,.expr final]),state.lastArg)


/--
Julia source: base/shell.jl:31-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_parse(str::AbstractString, interpolate::Bool=true;
            special::AbstractString="", filename="none") =
    __repl_entry_shell_parse(str, interpolate, special, filename)
```
-/
def shellParse (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (original : S) (filename : File) (interpolate : Bool := true) (special : S := ops.literal "") :
    M W (Parsed S Atom Expr × I) :=
  replEntryShellParse ops original interpolate special filename


/--
Julia source: base/shell.jl:385-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function shell_split(s::AbstractString)
    parsed = shell_parse(s, false)[1]
    args = String[]
    for arg in parsed
        push!(args, string(arg...)::String)
    end
    args
end
```
-/
def shellSplit (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (stringParts : List (Term S Atom Expr) → M W S) (original : S) (filename : File) : M W (List S) := do
  let (parsed,_) ← shellParse ops original filename false
  match parsed with
  | .expression _ => throwThe Error (.foreignError "TypeError" "expected parsed words")
  | .words words => words.mapM stringParts
/--
Julia source: base/shell.jl:394-422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_shell_word(io::IO, word::AbstractString, special::AbstractString = "")
    has_single = false
    has_special = false
    for c in word
        if isspace(c) || c=='\\' || c=='\'' || c=='"' || c=='$' || c in special
            has_special = true
            if c == '\''
                has_single = true
            end
        end
    end
    if isempty(word)
        print(io, "''")
    elseif !has_special
        print(io, word)
    elseif !has_single
        print(io, '\'', word, '\'')
    else
        print(io, '"')
        for c in word
            if c == '"' || c == '$' || c == '\\'
                print(io, '\\')
            end
            print(io, c)
        end
        print(io, '"')
    end
    nothing
end
```
-/
def printShellWord (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (word special : S) : M W Unit := do
  if ← ops.isempty word then ops.writeString (ops.literal "''")
  else
    let cursor ← ops.stateful (← ops.pairs word)
    let (hasSingle,hasSpecial) ← JuliaLean.base.io.whileLoop
      (fun (flags : Bool × Bool) => do
        match ← ops.iterate cursor with
        | none => pure (.inl flags)
        | some (_,c) =>
            let whitespace ← ops.isspace c
            let backslash ← ops.eqAscii c '\\'
            let single ← ops.eqAscii c '\''
            let double ← ops.eqAscii c '"'
            let dollar ← ops.eqAscii c '$'
            let inSpecial ← ops.inString c special
            pure (.inr (flags.1 || single,
              flags.2 || whitespace || backslash || single || double || dollar || inSpecial)))
      (false,false)
    if !hasSpecial then ops.writeString word
    else if !hasSingle then do
      ops.writeString (ops.literal "'")
      ops.writeString word
      ops.writeString (ops.literal "'")
    else do
      ops.writeString (ops.literal "\"")
      let cursor ← ops.stateful (← ops.pairs word)
      let _ ← JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
        match ← ops.iterate cursor with
        | none => pure (.inl ())
        | some (_,c) =>
            if (← ops.eqAscii c '"') || (← ops.eqAscii c '$') || (← ops.eqAscii c '\\') then
              ops.writeString (ops.literal "\\")
            ops.writeChar c
            pure (.inr ())) ()
      ops.writeString (ops.literal "\"")


/--
Julia source: base/shell.jl:424-431 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_shell_escaped(io::IO, cmd::AbstractString, args::AbstractString...;
                             special::AbstractString="")
    print_shell_word(io, cmd, special)
    for arg in args
        print(io, ' ')
        print_shell_word(io, arg, special)
    end
end
```
-/
def printShellEscaped (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (cmd : S) (args : List S) (special : S) : M W Unit := do
  printShellWord ops cmd special
  for arg in args do
    ops.writeString (ops.literal " ")
    printShellWord ops arg special


/--
Julia source: base/shell.jl:432-432 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_shell_escaped(io::IO; special::String="") = nothing
```
-/
def printShellEscapedEmpty : M W Unit := pure ()


/--
Julia source: base/shell.jl:452-453 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape(args::AbstractString...; special::AbstractString="") =
    sprint((io, args...) -> print_shell_escaped(io, args..., special=special), args...)
```
-/
def shellEscape (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) (special : S) : M W S :=
  match args with
  | [] => ops.sprint printShellEscapedEmpty
  | cmd :: rest => ops.sprint (printShellEscaped ops cmd rest special)

def asciiShellAlphaNum : List Char :=
  (List.range 10).map (fun n => Char.ofNat (48 + n)) ++
    (List.range 26).map (fun n => Char.ofNat (65 + n)) ++
    (List.range 26).map (fun n => Char.ofNat (97 + n))

def posixWordFlags (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (first : Bool) (arg : S) : M W (Bool × Bool × Bool) := do
  let cursor ← ops.stateful (← ops.pairs arg)
  JuliaLean.base.io.whileLoop (fun (flags : Bool × Bool × Bool) => do
    if !flags.1 then return .inl flags
    match ← ops.iterate cursor with
    | none => pure (.inl flags)
    | some (_,c) =>
        if ← ops.inChars c asciiShellAlphaNum then pure (.inr flags)
        else if ← ops.inChars c ['_','/','+','-','.'] then pure (.inr flags)
        else if ← ops.eqAscii c '\'' then pure (.inr (true,true,flags.2.2))
        else if ← ops.eqAscii c '"' then
          if flags.2.2 then pure (.inl (false,flags.2.1,flags.2.2))
          else pure (.inr (true,flags.2.1,true))
        else if !first && (← ops.eqAscii c '=') then pure (.inr flags)
        else pure (.inl (false,flags.2.1,flags.2.2))) (true,false,false)

def writePosixReplacement (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (word : S) (escapeSingle escapeDouble : Bool) : M W Unit := do
  let cursor ← ops.stateful (← ops.pairs word)
  let _ ← JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
    match ← ops.iterate cursor with
    | none => pure (.inl ())
    | some (_,c) =>
        if escapeSingle && (← ops.eqAscii c '\'') then ops.writeString (ops.literal "\\'")
        else if escapeDouble && (← ops.eqAscii c '"') then ops.writeString (ops.literal "\\\"")
        else ops.writeChar c
        pure (.inr ())) ()

def printPosixWord (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (first : Bool) (arg : S) : M W Unit := do
  if ← ops.isempty arg then ops.writeString (ops.literal "''")
  else
    let (isWord,hasSingle,hasDouble) ← posixWordFlags ops first arg
    if isWord then
      writePosixReplacement ops arg hasSingle hasDouble
    else do
      ops.writeString (ops.literal "'")
      let cursor ← ops.stateful (← ops.pairs arg)
      let _ ← JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
        match ← ops.iterate cursor with
        | none => pure (.inl ())
        | some (_,c) =>
            if ← ops.eqAscii c '\'' then ops.writeString (ops.literal "'\\''")
            else ops.writeChar c
            pure (.inr ())) ()
      ops.writeString (ops.literal "'")


/--
Julia source: base/shell.jl:456-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_shell_escaped_posixly(io::IO, args::AbstractString...)
    first = true
    for arg in args
        first || print(io, ' ')
        # avoid printing quotes around simple enough strings
        # that any (reasonable) shell will definitely never consider them to be special
        if isempty(arg)
            print(io, "''")
        else
            have_single = false
            have_double = false
            isword = true
            for c in arg
                if '0' <= c <= '9' || 'a' <= c <= 'z' || 'A' <= c <= 'Z'
                    # word characters
                elseif c == '_' || c == '/' || c == '+' || c == '-' || c == '.'
                    # other common characters
                elseif c == '\''
                    have_single = true
                elseif c == '"'
                    if have_double
                        isword = false
                        break # switch to single quoting
                    end
                    have_double = true
                elseif !first && c == '='
                    # equals is special if it is first (e.g. `env=val ./cmd`)
                else
                    # anything else
                    isword = false
                    break
                end
            end
            if isword
                have_single && (arg = replace(arg, '\'' => "\\'"))
                have_double && (arg = replace(arg, '"' => "\\\""))
                print(io, arg)
            else
                print(io, '\'', replace(arg, '\'' => "'\\''"), '\'')
            end
        end
        first = false
    end
end
```
-/
def printShellEscapedPosixly (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W Unit := do
  let mut first := true
  for arg in args do
    if !first then ops.writeString (ops.literal " ")
    printPosixWord ops first arg
    first := false


/--
Julia source: base/shell.jl:519-520 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape_posixly(args::AbstractString...) =
    sprint(print_shell_escaped_posixly, args...)
```
-/
def shellEscapePosixly (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W S :=
  ops.sprint (printShellEscapedPosixly ops args)

def cshPlain (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File) (c : C) : M W Bool := do
  if ← ops.inChars c asciiShellAlphaNum then return true
  ops.inChars c ['/','.', '_','-']

def cshDoubleSafe (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File) (c : C) : M W Bool :=
  do pure !(← ops.inChars c ['$','`','"'])

def scanShellPrefix (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) (start : I) (predicate : C → M W Bool) : M W (Bool × I) := do
  let last ← ops.lastindex s
  JuliaLean.base.io.whileLoop (fun (state : Bool × I) => do
    let (active,index) := state
    if !active || index.val > last.val then pure (.inl state)
    else
      let c ← ops.getindex s index
      if ← predicate c then pure (.inr (true,← ops.nextind s index))
      else pure (.inl (false,index))) (true,start)

def writeCshSegment (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) (start stop : I) : M W Unit := do
  let _ ← JuliaLean.base.io.whileLoop (fun (index : I) => do
    if index.val ≥ stop.val then pure (.inl ())
    else
      let c ← ops.getindex s index
      if ← ops.eqAscii c '\n' then ops.writeString (ops.literal "\\\n")
      else ops.writeChar c
      pure (.inr (← ops.nextind s index))) start
  pure ()

def writeCshQuote (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) (start stop : I) (quote : String) : M W Unit := do
  ops.writeString (ops.literal quote)
  writeCshSegment ops s start stop
  ops.writeString (ops.literal quote)

def printShellCshWord (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (arg : S) : M W Unit := do
  let firstIndex ← ops.firstindex arg
  let lastIndex ← ops.lastindex arg
  let endIndex ← if lastIndex.val < firstIndex.val then pure firstIndex else ops.nextind arg lastIndex
  let _ ← JuliaLean.base.io.whileLoop (fun (index : I) => do
    if index.val ≥ endIndex.val then pure (.inl ())
    else
      let (plain,afterPlain) ← scanShellPrefix ops arg index (cshPlain ops)
      if plain then
        writeCshSegment ops arg index afterPlain
        pure (.inr afterPlain)
      else
        let notSingle : C → M W Bool := fun c => do pure !(← ops.eqAscii c '\'')
        let (noSingle,_) ← scanShellPrefix ops arg index notSingle
        if noSingle then
          writeCshQuote ops arg index endIndex "'"
          pure (.inl ())
        else
          let (doubleSafe,_) ← scanShellPrefix ops arg index (cshDoubleSafe ops)
          if doubleSafe then
            writeCshQuote ops arg index endIndex "\""
            pure (.inl ())
          else
            let (_,afterSingle) ← scanShellPrefix ops arg index notSingle
            if afterSingle.val > index.val then
              writeCshQuote ops arg index afterSingle "'"
              pure (.inr afterSingle)
            else
              let (_,afterDouble) ← scanShellPrefix ops arg index (cshDoubleSafe ops)
              writeCshQuote ops arg index afterDouble "\""
              pure (.inr afterDouble)) firstIndex

def printShellEscapedCsh (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W Unit := do
  let mut first := true
  for arg in args do
    if first then first := false else ops.writeString (ops.literal " ")
    if ← ops.isempty arg then ops.writeString (ops.literal "''")
    else printShellCshWord ops arg
    pure ()


/--
Julia source: base/shell.jl:544-565 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function shell_escape_csh(io::IO, args::AbstractString...)
    first = true
    for arg in args
        first || write(io, ' ')
        first = false
        i = 1
        while true
            for (r,e) = (r"^[A-Za-z0-9/\._-]+\z"sa => "",
                         r"^[^']*\z"sa => "'", r"^[^\$\`\"]*\z"sa => "\"",
                         r"^[^']+"sa  => "'", r"^[^\$\`\"]+"sa  => "\"")
                if ((m = match(r, SubString(arg, i))) !== nothing)
                    write(io, e)
                    write(io, replace(m.match, '\n' => "\\\n"))
                    write(io, e)
                    i += ncodeunits(m.match)
                    break
                end
            end
            i <= lastindex(arg) || break
        end
    end
end
```
-/
def shellEscapeCshIO (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W Unit :=
  printShellEscapedCsh ops args


/--
Julia source: base/shell.jl:566-568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape_csh(args::AbstractString...) =
    sprint(shell_escape_csh, args...;
           sizehint = sum(sizeof, args) + length(args) * 3)
```
-/
def shellEscapeCsh (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W S :=
  ops.sprint (shellEscapeCshIO ops args)

def cmdControl (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) : M W Bool := do
  let cursor ← ops.stateful (← ops.pairs s)
  JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
    match ← ops.iterate cursor with
    | none => pure (.inl false)
    | some (_,c) =>
        if ← ops.inChars c ['\r','\n',Char.ofNat 0] then pure (.inl true)
        else pure (.inr ())) ()

def findShellQuote (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) (start : I) : M W (Option I) := do
  let last ← ops.lastindex s
  JuliaLean.base.io.whileLoop (fun (index : I) => do
    if index.val > last.val then pure (.inl none)
    else
      let c ← ops.getindex s index
      if ← ops.eqAscii c '"' then pure (.inl (some index))
      else pure (.inr (← ops.nextind s index))) start


/--
Julia source: base/shell.jl:648-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function shell_escape_wincmd(io::IO, s::AbstractString)
    # https://stackoverflow.com/a/4095133/1990689
    occursin(r"[\r\n\0]"sa, s) &&
        throw(ArgumentError("control character unsupported by CMD.EXE"))
    i = 1
    len = ncodeunits(s)
    if len > 0 && s[1] == '@'
        write(io, '^')
    end
    while i <= len
        c = s[i]
        if c == '"' && (j = findnext('"', s, nextind(s,i))) !== nothing
            write(io, SubString(s,i,j))
            i = j
        else
            if c in ('"', '(', ')', '!', '^', '<', '>', '&', '|')
                write(io, '^', c)
            else
                write(io, c)
            end
        end
        i = nextind(s,i)
    end
end
```
-/
def shellEscapeWincmdIO (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) : M W Unit := do
  if ← cmdControl ops s then
    throwThe Error (.foreignError "ArgumentError" "control character unsupported by CMD.EXE")
  let first ← ops.firstindex s
  let last ← ops.lastindex s
  if first.val ≤ last.val then
    if ← ops.eqAscii (← ops.getindex s first) '@' then
      ops.writeString (ops.literal "^")
  let _ ← JuliaLean.base.io.whileLoop (fun (index : I) => do
    if index.val > last.val then pure (.inl ())
    else
      let c ← ops.getindex s index
      if ← ops.eqAscii c '"' then
        let next ← ops.nextind s index
        match ← findShellQuote ops s next with
        | some closing =>
            ops.writeString (← ops.substring s index (some closing))
            pure (.inr (← ops.nextind s closing))
        | none =>
            if ← ops.inChars c ['"','(',')','!','^','<','>','&','|'] then
              ops.writeString (ops.literal "^")
            ops.writeChar c
            pure (.inr (← ops.nextind s index))
      else if ← ops.inChars c ['"','(',')','!','^','<','>','&','|'] then
        ops.writeString (ops.literal "^")
        ops.writeChar c
        pure (.inr (← ops.nextind s index))
      else
        ops.writeChar c
        pure (.inr (← ops.nextind s index))) first


/--
Julia source: base/shell.jl:672-673 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shell_escape_wincmd(s::AbstractString) = sprint(shell_escape_wincmd, s;
                                                sizehint = 2*sizeof(s))
```
-/
def shellEscapeWincmd (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (s : S) : M W S :=
  ops.sprint (shellEscapeWincmdIO ops s)

def microsoftNeedsQuotes (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (arg : S) : M W Bool := do
  if ← ops.isempty arg then return true
  let cursor ← ops.stateful (← ops.pairs arg)
  JuliaLean.base.io.whileLoop (fun (_ : Unit) => do
    match ← ops.iterate cursor with
    | none => pure (.inl false)
    | some (_,c) =>
        if ← ops.inChars c [' ','\t','"'] then pure (.inl true)
        else pure (.inr ())) ()


/--
Julia source: base/shell.jl:696-715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function escape_microsoft_c_args(io::IO, args::AbstractString...)
    # http://daviddeley.com/autohotkey/parameters/parameters.htm#WINCRULES
    first = true
    for arg in args
        if first
            first = false
        else
            write(io, ' ')  # separator
        end
        if isempty(arg) || occursin(r"[ \t\"]"sa, arg)
            # Julia raw strings happen to use the same escaping convention
            # as the argv[] parser in Microsoft's C runtime library.
            write(io, '"')
            escape_raw_string(io, arg)
            write(io, '"')
        else
            write(io, arg)
        end
    end
end
```
-/
def escapeMicrosoftCArgsIO (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W Unit := do
  let mut first := true
  for arg in args do
    if first then first := false else ops.writeString (ops.literal " ")
    if ← microsoftNeedsQuotes ops arg then
      ops.writeString (ops.literal "\"")
      ops.escapeRawString arg
      ops.writeString (ops.literal "\"")
    else ops.writeString arg


/--
Julia source: base/shell.jl:716-718 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_microsoft_c_args(args::AbstractString...) =
    sprint(escape_microsoft_c_args, args...;
           sizehint = (sum(sizeof, args) + 3*length(args)))
```
-/
def escapeMicrosoftCArgs (ops : Ops W S C Atom Expr Pairs Rev RevState Cursor File)
    (args : List S) : M W S :=
  ops.sprint (escapeMicrosoftCArgsIO ops args)






/- Untranslated: Documentation and module scaffolding. -/
-- UNTRANSLATED
-- Source: base/shell.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## shell-like command parsing ##
-- 
-- /Source

/- Untranslated: Documentation and module scaffolding. -/
-- UNTRANSLATED
-- Source: base/shell.jl:6-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- (@doc raw"""
--     rstrip_shell(s::AbstractString)
-- 
-- Strip trailing whitespace from a shell command string, while respecting a trailing backslash followed by a space ("\\ ").
-- 
-- ```jldoctest
-- julia> Base.rstrip_shell("echo 'Hello World' \\ ")
-- "echo 'Hello World' \\ "
-- 
-- julia> Base.rstrip_shell("echo 'Hello World'    ")
-- "echo 'Hello World'"
-- ```
-- """
-- /Source

/- Untranslated: Documentation and module scaffolding. -/
-- UNTRANSLATED
-- Source: base/shell.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/- Untranslated: Documentation and module scaffolding. -/
-- UNTRANSLATED
-- Source: base/shell.jl:34-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # N.B.: Any functions starting with __repl_entry cut off backtraces when printing in the REPL.
-- /Source

/- Untranslated: Documentation and module scaffolding. -/
-- UNTRANSLATED
-- Source: base/shell.jl:369-384 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     shell_split(command::AbstractString)
-- 
-- Split a shell command string into its individual components.
-- 
-- # Examples
-- ```jldoctest
-- julia> Base.shell_split("git commit -m 'Initial commit'")
-- 4-element Vector{String}:
--  "git"
--  "commit"
--  "-m"
--  "Initial commit"
-- ```
-- """
-- /Source


end JuliaLean.base.shell

/-!
# Strings and characters for `base/shell.jl` and `base/cmd.jl`

Master `bbfa0ce4150`.

* A `Char` is its raw `UInt32` bit pattern, as in `JuliaLean.Strings`
  (`'a'` is `0x61000000`, `'é'` is `0xc3a90000`, the invalid byte `'\xff'` is
  `0xff000000`).
* A Julia string is modelled by the sequence of `Char`s that iterating it
  yields (`JS`). Every function modelled here iterates its input character by
  character and builds its output by concatenating input characters and ASCII
  characters. For a string produced by Julia, the concatenation of the bytes of
  its characters is the string, and inserting ASCII bytes between characters
  never changes how the neighbouring bytes decode (an ASCII byte is neither a
  lead nor a continuation byte). So iterating Julia's output yields exactly the
  modelled character list, including for invalid UTF-8.
* Byte indices are needed where Julia does index arithmetic. `pairsFrom` gives
  each character its byte index (`pairs(s)`), using `ncodeunits(c::Char)` from
  `JuliaLean.Strings.ncodeunitsChar`. Indices stay below `ncodeunits(s) + 2 < 2^62`,
  so `Int` arithmetic on them is `Int64` arithmetic.
-/

namespace JuliaLean.ShellCmd

open JuliaLean


/-- The `Char` literal of an ASCII character: its code in the top byte. -/
def A (c : Char) : JC := c.toNat.toUInt32 <<< 24

/-- An ASCII string literal. -/
def S (s : String) : JS := s.toList.map A

/-- `isspace(c::Char)`, `base/strings/unicode.jl:624-626`, on the raw bits. -/
def isspace (c : JC) : Bool := ParsePrint.IntParse.isspaceChar c.toNat

/-- `prevind(s, j)` for `1 ≤ j ≤ ncodeunits(s) + 1` (`base/strings/basic.jl:540-548`):
the largest character index below `j`, or `0`. -/
def prevind (s : JS) (j : Int) : Int :=
  ((pairsFrom 1 s).filter (fun q => (q.1 : Int) < j)).foldl (fun _ q => (q.1 : Int)) 0

/-- The bytes of a string: the bytes of its characters. -/
def bytesOf (s : JS) : List UInt8 := s.flatMap Strings.charBytes

/-- `nextind(str::String, i)` (`base/strings/string.jl:273-306`) on the bytes of
`str`, via `JuliaLean.Strings.nextind`. -/
def nextindStr (str : JS) (i : Int) : SH Int :=
  match Strings.stringOfChars str with
  | .error _ => .error .outOfMemory
  | .ok js =>
    match Strings.nextind js (Strings.ix i) with
    | .ok r => .ok r.val
    | .error (.jl e) => .error (.jl e)
    | .error _ => .error .stringIndex

/-- `c ∈ s` for a character and a string. -/
def cin (c : JC) (s : JS) : Bool := s.contains c

end JuliaLean.ShellCmd

/-!
# The shell escaping functions of `base/shell.jl`

Master `bbfa0ce4150`: `print_shell_word`, `shell_escape`,
`shell_escape_posixly`, `shell_escape_csh`, `shell_escape_wincmd`,
`escape_microsoft_c_args`, and `escape_raw_string` from `base/strings/io.jl`.

`Char` comparisons such as `'0' <= c <= '9'` compare raw bits, as in Julia.
The regular expressions of `shell_escape_csh` and `shell_escape_wincmd` use the
`a` flag, so they match bytes; their character classes contain only ASCII
bytes, so on the characters of a string they select the same characters as the
character-level tests used here (a non-ASCII character consists of bytes
`≥ 0x80`, none of which is in or equal to an ASCII class member).
-/

namespace JuliaLean.ShellCmd

/-- `replace(s, c => r)` for a character `c`. -/
def replaceC (s : JS) (c : JC) (r : JS) : JS := s.flatMap (fun x => if x == c then r else [x])

/-- `join(words, ' ')`. -/
def joinSp : List JS → JS
  | [] => []
  | w :: ws => w ++ ws.flatMap (fun a => A ' ' :: a)

/-- The special-character test of `print_shell_word`, `base/shell.jl:398`. -/
def wordSpecial (special : JS) (c : JC) : Bool :=
  isspace c || c == A '\\' || c == A '\'' || c == A '"' || c == A '$' || cin c special

/-- `print_shell_word(io, word, special)`, `base/shell.jl:394-422`. -/
def printShellWord (word special : JS) : JS :=
  let hasSingle := word.any (fun c => wordSpecial special c && c == A '\'')
  let hasSpecial := word.any (wordSpecial special)
  if word.isEmpty then S "''"
  else if !hasSpecial then word
  else if !hasSingle then A '\'' :: word ++ [A '\'']
  else
    A '"' :: word.flatMap (fun c =>
      if c == A '"' || c == A '$' || c == A '\\' then [A '\\', c] else [c]) ++ [A '"']

/-- `shell_escape(args...; special)`, `base/shell.jl:424-453`: the words printed
by `print_shell_word`, separated by spaces (`""` for no arguments). -/
def shellEscape (xs : List JS) (special : JS) : JS := joinSp (xs.map (printShellWord · special))

/-! ### `shell_escape_posixly`, `base/shell.jl:456-520` -/

/-- `'0' <= c <= '9' || 'a' <= c <= 'z' || 'A' <= c <= 'Z'`. -/
def isAlnum (c : JC) : Bool :=
  (A '0' ≤ c && c ≤ A '9') || (A 'a' ≤ c && c ≤ A 'z') || (A 'A' ≤ c && c ≤ A 'Z')

/-- `c == '_' || c == '/' || c == '+' || c == '-' || c == '.'`. -/
def isCommon (c : JC) : Bool :=
  c == A '_' || c == A '/' || c == A '+' || c == A '-' || c == A '.'

/-- The scan `for c in arg`, `base/shell.jl:468-488`: returns
`(have_single, have_double, isword)`. -/
def posixScan (first : Bool) : JS → Bool → Bool → Bool × Bool × Bool
  | [], hs, hd => (hs, hd, true)
  | c :: cs, hs, hd =>
    if isAlnum c then posixScan first cs hs hd
    else if isCommon c then posixScan first cs hs hd
    else if c == A '\'' then posixScan first cs true hd
    else if c == A '"' then
      if hd then (hs, hd, false) else posixScan first cs hs true
    else if !first && c == A '=' then posixScan first cs hs hd
    else (hs, hd, false)

/-- One argument of `print_shell_escaped_posixly`, `base/shell.jl:462-496`. -/
def posixWord (first : Bool) (arg : JS) : JS :=
  if arg.isEmpty then S "''"
  else
    let (hs, hd, isword) := posixScan first arg false false
    if isword then
      let a := if hs then replaceC arg (A '\'') (S "\\'") else arg
      if hd then replaceC a (A '"') (S "\\\"") else a
    else A '\'' :: replaceC arg (A '\'') (S "'\\''") ++ [A '\'']

/-- `shell_escape_posixly(args...)`, `base/shell.jl:456-520`. -/
def shellEscapePosixly : List JS → JS
  | [] => []
  | x :: xs => posixWord true x ++ xs.flatMap (fun a => A ' ' :: posixWord false a)

/-! ### `shell_escape_csh`, `base/shell.jl:544-568` -/

/-- `[A-Za-z0-9/\._-]`. -/
def cshPlain (c : JC) : Bool :=
  isAlnum c || c == A '/' || c == A '.' || c == A '_' || c == A '-'

/-- `[^\$\`\"]`. -/
def notDqSpecial (c : JC) : Bool := c != A '$' && c != A '`' && c != A '"'

/-- The `while true` loop for one argument, `base/shell.jl:549-563`, on the
remaining text `SubString(arg, i)`. The five patterns are tried in order; for a
nonempty remainder one of the last two always matches, and every match of a
non-final pattern is nonempty, so the bound `length(arg) + 1` is never
exhausted. -/
def cshLoop : Nat → JS → JS
  | 0, _ => []
  | n + 1, rest =>
    let (seg, e, rest') :=
      if !rest.isEmpty && rest.all cshPlain then (rest, ([] : JS), ([] : JS))
      else if !rest.contains (A '\'') then (rest, [A '\''], [])
      else if rest.all notDqSpecial then (rest, [A '"'], [])
      else
        let p := rest.takeWhile (· != A '\'')
        if !p.isEmpty then (p, [A '\''], rest.drop p.length)
        else
          let q := rest.takeWhile notDqSpecial
          (q, [A '"'], rest.drop q.length)
    e ++ replaceC seg (A '\n') [A '\\', A '\n'] ++ e ++
      (if rest'.isEmpty then [] else cshLoop n rest')

/-- `shell_escape_csh(io, args...)`, `base/shell.jl:544-565`. -/
def cshIO (xs : List JS) : JS := joinSp (xs.map (fun a => cshLoop (a.length + 1) a))

/-- The `ArgumentError` of `sum(sizeof, ())`: `mapreduce` over an empty tuple
without `init` (`base/reduce.jl`). -/
def emptyReduceErr : ShErr :=
  .jl (.argumentError "reducing over an empty collection is not allowed; consider supplying `init` to the reducer")

/-- `shell_escape_csh(args...)`, `base/shell.jl:566-568`: the `sizehint` computes
`sum(sizeof, args)` before anything is printed. -/
def shellEscapeCsh (xs : List JS) : SH JS :=
  if xs.isEmpty then .error emptyReduceErr else .ok (cshIO xs)

/-! ### `shell_escape_wincmd`, `base/shell.jl:648-673` -/

/-- `c in ('"', '(', ')', '!', '^', '<', '>', '&', '|')`. -/
def wincmdSpecial (c : JC) : Bool := cin c (S "\"()!^<>&|")

/-- The `while i <= len` loop, `base/shell.jl:657-670`, on the remaining characters:
a `"` with a later `"` is copied with everything up to that `"`. -/
def wincmdLoop : Nat → JS → JS
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, c :: cs =>
    if c == A '"' && cs.contains (A '"') then
      let inner := cs.takeWhile (· != A '"')
      (c :: inner ++ [A '"']) ++ wincmdLoop n (cs.drop (inner.length + 1))
    else (if wincmdSpecial c then [A '^', c] else [c]) ++ wincmdLoop n cs

/-- `shell_escape_wincmd(s)`, `base/shell.jl:648-673`. -/
def shellEscapeWincmd (s : JS) : SH JS :=
  if s.any (fun c => c == A '\r' || c == A '\n' || c == A '\x00') then
    .error (.jl (.argumentError "control character unsupported by CMD.EXE"))
  else .ok ((if s.head? == some (A '@') then [A '^'] else []) ++ wincmdLoop (s.length + 1) s)

/-! ### `escape_microsoft_c_args`, `base/shell.jl:696-718` -/

/-- `escape_raw_string(io, str, delim)`, `base/strings/io.jl:663-693`; `esc` is
the number of backslashes since the last other character. -/
def escapeRawString (delim : JC) : JS → Nat → JS
  | [], esc => List.replicate esc (A '\\')
  | c :: cs, esc =>
    if c == A '\\' then c :: escapeRawString delim cs (esc + 1)
    else if c == delim then List.replicate (esc + 1) (A '\\') ++ c :: escapeRawString delim cs 0
    else c :: escapeRawString delim cs 0

/-- One argument of `escape_microsoft_c_args(io, args...)`, `base/shell.jl:705-713`. -/
def msArg (arg : JS) : JS :=
  if arg.isEmpty || arg.any (fun c => c == A ' ' || c == A '\t' || c == A '"') then
    A '"' :: escapeRawString (A '"') arg 0 ++ [A '"']
  else arg

/-- `escape_microsoft_c_args(io, args...)`, `base/shell.jl:696-715`. -/
def msIO (xs : List JS) : JS := joinSp (xs.map msArg)

/-- `escape_microsoft_c_args(args...)`, `base/shell.jl:716-718` (with `sizehint`). -/
def escapeMicrosoftCArgs (xs : List JS) : SH JS :=
  if xs.isEmpty then .error emptyReduceErr else .ok (msIO xs)

end JuliaLean.ShellCmd

/-!
# `shell_parse(str, false)` and `shell_split`, `base/shell.jl:20-392`

Master `bbfa0ce4150`. With `interpolate = false` (the `shell_split` path) the
`$`, pipeline, redirection and tilde branches of the loop are never taken, so
they are not modelled. `last_arg` only feeds REPL completion and is not part
of the result, so it is omitted too.

The input is `str`; the parsed text is the SubString `s` of `str` left after
`lstrip` and `rstrip_shell`. `s` keeps its own one-based byte indices, which
is what `pairs(s)`, `s[i:j]` and `prevind(s, j)` use; the index arithmetic of
the loop is done on these indices exactly as in Julia, including the call
`nextind(str, i)` at `base/shell.jl:225`, which uses the indices of `str`.

`Iterators.Stateful(pairs(s))` is the list `st` of remaining (index, char)
pairs; `peek(st)` is its head and `popfirst!(st)` drops it. The `for` loop is
recursion on a bound on the number of remaining iterations: every iteration
pops at least one pair, so the bound `length(st) + 1` is never exhausted.
-/

namespace JuliaLean.ShellCmd

/-- `lstrip(s)` (`base/strings/util.jl:416-423`): the characters left after the
leading `isspace` ones, and the byte offset of the result in `s`. -/
def lstripOff (s : JS) : Nat × JS :=
  let pre := s.takeWhile isspace
  (ncu pre, s.drop pre.length)

/-- The loop of `rstrip_shell(s)`, `base/shell.jl:20-29`, over the characters of
`s` from the end (`r` is the reversed prefix still to scan, `cOld` the
previously scanned character). Returns the number of characters kept:
`SubString(s, 1, i+1)` keeps the backslash and the space after it;
`SubString(s, 1, i)` keeps everything up to the non-space character. -/
def rstripKeep : Option JC → List JC → Nat
  | _, [] => 0
  | cOld, c :: rest =>
    if c == A '\\' && cOld == some (A ' ') then rest.length + 2
    else if !isspace c then rest.length + 1
    else rstripKeep (some c) rest

/-- `rstrip_shell(s)`, `base/shell.jl:20-29`. -/
def rstripShell (s : JS) : JS := s.take (rstripKeep none s.reverse)

/-- `push_nonempty!(list, x)` for a string `x`, `base/shell.jl:63-68`. -/
def pushNonempty (l : List JS) (x : JS) : List JS := if x.isEmpty then l else l ++ [x]

/-- `something(peek(st), lastindex(s)+1 => '\0').first`. -/
def peekIdx (s : JS) : List (Nat × JC) → Int
  | (p, _) :: _ => p
  | [] => lastindex s + 1

/-- `consume_upto!(list, s, i, j)`, `base/shell.jl:69-72`: push `s[i:prevind(s, j)]`
if nonempty, return the index of the next pair (`st` is the iterator state at
the call). -/
def consumeUpto (s : JS) (st : List (Nat × JC)) (arg : List JS) (i j : Int) :
    SH (List JS × Int) := do
  let x ← slice s i (prevind s j)
  pure (pushNonempty arg x, peekIdx s st)

/-- `append_2to1!(list, innerlist)`, `base/shell.jl:73-77`: an empty word is `[""]`. -/
def append2to1 (args : List (List JS)) (arg : List JS) : List (List JS) :=
  args ++ [if arg.isEmpty then [[]] else arg]

/-- The whitespace-skipping loop of `base/shell.jl:134-140`: `i` becomes the
index of each peeked pair, and spaces are popped. -/
def skipSpaces (i : Int) : List (Nat × JC) → Int × List (Nat × JC)
  | [] => (i, [])
  | (p, c) :: rest => if isspace c then skipSpaces p rest else (p, (p, c) :: rest)

/-- The indentation-skipping loop after a line continuation,
`base/shell.jl:224-227`: `i = nextind(str, i)` for each popped space or tab. -/
def skipIndent (str : JS) (i : Int) : List (Nat × JC) → SH (Int × List (Nat × JC))
  | [] => .ok (i, [])
  | (p, c) :: rest =>
    if c == A ' ' || c == A '\t' then do
      let i' ← nextindStr str i
      skipIndent str i' rest
    else .ok (i, (p, c) :: rest)

/-- The parser state: `in_single_quotes`, `in_double_quotes`, `args`, `arg`,
`i`, `word_has_special`. -/
structure PState where
  inSQ : Bool
  inDQ : Bool
  args : List (List JS)
  arg : List JS
  i : Int
  whs : Bool
  deriving Repr, DecidableEq

/-- The main loop `for (j, c) in st`, `base/shell.jl:116-296`, with
`interpolate = false`. -/
def parseLoop (str s special : JS) : Nat → List (Nat × JC) → PState → SH PState
  | _, [], σ => .ok σ
  | 0, _ :: _, _ => .error .fuel
  | n + 1, (j, c) :: st, σ =>
    if !σ.inSQ && !σ.inDQ && isspace c then do
      -- `base/shell.jl:118-140`; `redirect_mode` is always `:none`
      let (arg, i) ← consumeUpto s st σ.arg σ.i j
      let (args, arg) :=
        if !arg.isEmpty || σ.whs then (append2to1 σ.args arg, []) else (σ.args, arg)
      let (i, st) := skipSpaces i st
      parseLoop str s special n st { σ with args := args, arg := arg, i := i, whs := false }
    else if !σ.inDQ && c == A '\'' then do
      -- `base/shell.jl:208-211`
      let (arg, i) ← consumeUpto s st σ.arg σ.i j
      parseLoop str s special n st { σ with inSQ := !σ.inSQ, whs := true, arg := arg, i := i }
    else if !σ.inSQ && c == A '"' then do
      -- `base/shell.jl:212-215`
      let (arg, i) ← consumeUpto s st σ.arg σ.i j
      parseLoop str s special n st { σ with inDQ := !σ.inDQ, whs := true, arg := arg, i := i }
    else if !σ.inSQ && c == A '\\' then
      -- `base/shell.jl:216-239`
      match st with
      | (_, c') :: st' =>
        if c' == A '\n' || c' == A '\r' then do
          let (arg, i) ← consumeUpto s st σ.arg σ.i j
          let i := i + 1
          -- `if popfirst!(st)[2] == '\r' && (peek(st)::P)[2] == '\n'`
          let (i, st'') ←
            if c' == A '\r' then
              match st' with
              | (_, c'') :: st'' =>
                if c'' == A '\n' then (pure (i + 1, st'') : SH _) else pure (i, st')
              | [] => .error .typeError
            else pure (i, st')
          let (i, st''') ← skipIndent str i st''
          parseLoop str s special n st''' { σ with whs := true, arg := arg, i := i }
        else if σ.inDQ then
          if c' == A '"' || c' == A '$' || c' == A '\\' then do
            let (arg, i) ← consumeUpto s st σ.arg σ.i j
            parseLoop str s special n st' { σ with whs := true, arg := arg, i := i }
          else parseLoop str s special n st { σ with whs := true }
        else do
          let (arg, i) ← consumeUpto s st σ.arg σ.i j
          parseLoop str s special n st' { σ with whs := true, arg := arg, i := i }
      | [] =>
        if σ.inDQ then .error (.error "unterminated double quote")
        else .error (.error "dangling backslash")
    else if !σ.inSQ && !σ.inDQ && cin c special then
      -- `base/shell.jl:292-293`
      .error (.error "special characters must be quoted in commands")
    else parseLoop str s special n st σ

/-- `shell_parse(str, false; special)[1]`, `base/shell.jl:31-41,116-313`: the
words, each a list of string parts. -/
def shellParse (str special : JS) : SH (List (List JS)) :=
  let s := rstripShell (lstripOff str).2
  if s.isEmpty then .ok []
  else do
    let st := pairsFrom 1 s
    let σ ← parseLoop str s special (st.length + 1) st
      { inSQ := false, inDQ := false, args := [], arg := [], i := 1, whs := false }
    if σ.inSQ then .error (.error "unterminated single quote")
    else if σ.inDQ then .error (.error "unterminated double quote")
    else do
      let x ← slice s σ.i (lastindex s)
      let arg := pushNonempty σ.arg x
      pure (if !arg.isEmpty || σ.whs then append2to1 σ.args arg else σ.args)

/-- `shell_split(s)`, `base/shell.jl:385-392`: `string(arg...)` of each word. -/
def shellSplit (s : JS) : SH (List JS) := do
  let words ← shellParse s []
  pure (words.map List.flatten)

end JuliaLean.ShellCmd

namespace JuliaLean.ShellCmd

/-- `shell_special`, `base/shell.jl:5`. -/
def shellSpecial : JS := S "#{}()[]<>|&*?;"

end JuliaLean.ShellCmd

namespace JuliaLean.MiscCov.Shell

open JuliaLean JuliaLean.ShellCmd

/-- The values `shell_parse` puts into its result: `String`s, atoms returned by
`Meta.parseatom`, the symbol `:var`, and `Expr`s. `call f args` is
`Expr(:call, f, args...)` with `f` a `GlobalRef` or function name; `tildeLet parts`
is the `let _u = string(parts...); isempty(_u) ? "~" : expanduser(string('~', _u)) end`
expression of `base/shell.jl:282`. -/
inductive SEx where
  | lit (s : JS)
  | atom (a : Nat)
  | varSym
  | call (f : String) (args : List SEx)
  | tuple (args : List SEx)
  | params (args : List SEx)
  | kw (k : String) (v : SEx)
  | btrue
  | tildeLet (parts : List SEx)
  deriving Repr, Inhabited, BEq

/-- `Meta.parseatom(s, i; filename)`: the atom and the index after it. -/
abbrev ParseAtom := JS → Int → SH (SEx × Int)

/-- `push_nonempty!(list, x)`, `base/shell.jl:63-68`: push unless `x` is an empty string. -/
def pushNonempty (l : List SEx) (x : SEx) : List SEx :=
  match x with
  | .lit v => if v.isEmpty then l else l ++ [x]
  | _ => l ++ [x]

/-- `consume_upto!(list, s, i, j)`, `base/shell.jl:69-72`: push `s[i:prevind(s, j)]`,
return the index of the next pair of the iterator `st` (or `lastindex(s) + 1`). -/
def consumeUpto (s : JS) (st : List (Nat × JC)) (arg : List SEx) (i j : Int) : SH (List SEx × Int) := do
  let x ← slice s i (prevind s j)
  pure (pushNonempty arg (.lit x), peekIdx s st)

/-- `append_2to1!(list, innerlist)`, `base/shell.jl:73-77`: an empty word becomes `[""]`. -/
def append2to1 (args : List (List SEx)) (arg : List SEx) : List (List SEx) :=
  args ++ [if arg.isEmpty then [.lit []] else arg]

/-- `startswith(SubString(s, p), "var\"")` for a character index `p`. -/
def startsWithVar (s : JS) (p : Nat) : Bool :=
  (((pairsFrom 1 s).filter (fun q => p ≤ q.1)).map (·.2)).take 4 == S "var\""

/-- `parse_dollar_interp(st, s)`, `base/shell.jl:86-103`: the atom, the new `s` (with its
offset), `interp_pos`, and the reset iterator `pairs(s)`. -/
def parseDollar (pa : ParseAtom) (st : List (Nat × JC)) (s : JS) (off : Nat) :
    SH (SEx × (JS × Nat) × Int × List (Nat × JC)) :=
  match st with
  | [] => .error (.error "$ right before end of command")
  | (stpos, c) :: _ =>
    if isspace c then .error (.error "space not allowed right after $")
    else do
      let (atom, j) ← if startsWithVar s stpos then pure (SEx.varSym, (stpos : Int) + 3) else pa s stpos
      let interpPos : Int := stpos + off
      let (s', off') ← subFrom s off j
      pure (atom, (s', off'), interpPos, pairsFrom 1 s')

/-- `redirect_word_expr(word)`, `base/shell.jl:106-114`. -/
def redirectWordExpr (word : List SEx) : SEx :=
  match word with
  | [.lit w] => .lit w
  | [w] => .call "Base.cmd_redirect_target" [w]
  | ws => .call "Base.cmd_interpolate" ws

/-- `redirect_mode`. -/
inductive RMode where
  | none | stdin | stdout | stderr
  deriving DecidableEq, Repr

/-- A finished pipeline segment: `(seg_tuple, stdin, stdout, stdout_append, stderr,
stderr_append)`. -/
abbrev Seg := SEx × Option SEx × Option SEx × Bool × Option SEx × Bool

/-- The local variables of the parser. -/
structure PS where
  inSQ : Bool
  inDQ : Bool
  args : List (List SEx)
  arg : List SEx
  i : Int
  s : JS
  off : Nat
  lastArg : Int
  upd : Bool
  whs : Bool
  parts : List Seg
  sin : Option SEx
  sout : Option SEx
  soutApp : Bool
  serr : Option SEx
  serrApp : Bool
  mode : RMode

/-- `if redirect_mode === :stdin; seg_stdin = re elseif ... :stdout ... else seg_stderr = re`. -/
def setRedirect (σ : PS) (re : SEx) : PS :=
  if σ.mode = .stdin then { σ with sin := some re }
  else if σ.mode = .stdout then { σ with sout := some re }
  else { σ with serr := some re }

/-- `isdigit(c)`: `'0' <= c <= '9'` on the raw bits. -/
def isdigitC (c : JC) : Bool := A '0' ≤ c && c ≤ A '9'

/-- `parse(Int, String(w)::String)` for a nonempty word of ASCII digits:
`OverflowError` above `typemax(Int)`. The list representation abstracts the
copy to a concrete String and does not represent custom conversion failures. -/
def parseFd (w : JS) : SH Int :=
  let v : Nat := w.foldl (fun a c => a * 10 + (c.toNat / 2 ^ 24 - 48)) 0
  if v > 2 ^ 63 - 1 then .error (.jl (.overflowError "")) else .ok v

/-- `Expr(:tuple, (Expr(:tuple, a...) for a in args)...)`. -/
def tupleOf (args : List (List SEx)) : SEx := .tuple (args.map .tuple)

/-- The redirect-or-word step shared by whitespace and `|` (`base/shell.jl:121-129,
152-159`): the pending word becomes the redirect target (and, after whitespace,
`redirect_mode = :none`), or a new argument. -/
def finishWord (resetMode : Bool) (σ : PS) : PS :=
  if σ.mode ≠ .none && (!σ.arg.isEmpty || σ.whs) then
    { setRedirect σ (redirectWordExpr σ.arg) with arg := [], mode := if resetMode then .none else σ.mode }
  else if σ.mode = .none && (!σ.arg.isEmpty || σ.whs) then { σ with args := append2to1 σ.args σ.arg, arg := [] }
  else σ

/-- The `while !isempty(st)` loop of the tilde branch, `base/shell.jl:247-276`: returns
the user-name parts, `s` with its offset, `i`, `user_lit_start` and the iterator. -/
def tildeLoop (pa : ParseAtom) : Nat → List SEx → JS → Nat → Int → Int → List (Nat × JC) →
    SH (List SEx × (JS × Nat) × Int × Int × List (Nat × JC))
  | _, parts, s, off, i, uls, [] => .ok (parts, (s, off), i, uls, [])
  | 0, _, _, _, _, _, _ :: _ => .error .fuel
  | n + 1, parts, s, off, i, uls, (p, nc) :: st =>
    let nextIsNl : Bool := match st with
      | (_, c2) :: _ => c2 == A '\n' || c2 == A '\r'
      | [] => false
    if nc == A '\\' && nextIsNl then do
      -- `nextind(s, nxt[1]) <= lastindex(s) && s[nextind(s, nxt[1])] in ('\n', '\r')`
      let lit ← slice s uls (prevind s p)
      let parts := pushNonempty parts (.lit lit)
      match st with
      | (_, c2) :: st2 =>
        let st3 := if c2 == A '\r' then
            (match st2 with
             | (_, c3) :: st4 => if c3 == A '\n' then st4 else st2
             | [] => st2)
          else st2
        let st5 := st3.dropWhile (fun q => q.2 == A ' ' || q.2 == A '\t')
        tildeLoop pa n parts s off i (peekIdx s st5) st5
      | [] => .error .fuel
    else if nc == A '/' || isspace nc || nc == A '\'' || nc == A '"' || nc == A '\\' ||
        nc == A '|' || nc == A '<' || nc == A '>' then
      .ok (parts, (s, off), i, uls, (p, nc) :: st)
    else if nc == A '$' then do
      let lit ← slice s uls (prevind s p)
      let parts := pushNonempty parts (.lit lit)
      let (atom, (s', off'), _, st') ← parseDollar pa st s off
      tildeLoop pa n (parts ++ [atom]) s' off' 1 1 st'
    else tildeLoop pa n parts s off i uls st

/-- The loop `for (j, c) in st`, `base/shell.jl:116-296`. -/
def parseLoop (pa : ParseAtom) (interp : Bool) (str special : JS) : Nat → List (Nat × JC) → PS → SH PS
  | _, [], σ => .ok σ
  | 0, _ :: _, _ => .error .fuel
  | n + 1, (j, c) :: st, σ =>
    if !σ.inSQ && !σ.inDQ && isspace c then do
      -- `base/shell.jl:118-140`
      let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
      let σ := finishWord true { σ with upd := true, arg := arg, i := i }
      let σ := { σ with whs := false }
      let (i, st) := skipSpaces σ.i st
      parseLoop pa interp str special n st { σ with i := i }
    else if interp && !σ.inSQ && c == A '$' then do
      -- `base/shell.jl:141-148`
      let (arg, _) ← consumeUpto σ.s st σ.arg σ.i j
      let (atom, (s, off), pos, st) ← parseDollar pa st σ.s σ.off
      parseLoop pa interp str special n st
        { σ with arg := arg ++ [atom], s := s, off := off, lastArg := pos, upd := true, i := 1 }
    else if interp && !σ.inSQ && !σ.inDQ && c == A '|' then do
      -- `base/shell.jl:149-169`
      let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
      let σ := finishWord false { σ with arg := arg, i := i }
      let seg : Seg := (tupleOf σ.args, σ.sin, σ.sout, σ.soutApp, σ.serr, σ.serrApp)
      parseLoop pa interp str special n st
        { σ with parts := σ.parts ++ [seg], args := [], sin := none, sout := none, soutApp := false,
                 serr := none, serrApp := false, mode := .none, whs := false, upd := true }
    else if interp && !σ.inSQ && !σ.inDQ && (c == A '<' || c == A '>') then do
      -- `base/shell.jl:170-201`
      let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
      let (fd, σ) ← (match arg with
        | [.lit w] =>
          if !σ.whs && !w.isEmpty && w.all isdigitC then do
            let v ← parseFd w
            pure (some v, { σ with arg := [], i := i, whs := false })
          else pure (none, { σ with args := append2to1 σ.args arg, arg := [], i := i })
        | [] => pure (none, { σ with arg := [], i := i })
        | _ => pure (none, { σ with args := append2to1 σ.args arg, arg := [], i := i }) : SH (Option Int × PS))
      if c == A '>' then do
        let (append, i, st) := match st with
          | (_, c2) :: st2 => if c2 == A '>' then (true, peekIdx σ.s st2, st2) else (false, σ.i, st)
          | [] => (false, σ.i, st)
        let σ := { σ with i := i }
        let σ ← (if fd = none || fd = some 1 then pure { σ with mode := .stdout, soutApp := append }
          else if fd = some 2 then pure { σ with mode := .stderr, serrApp := append }
          else .error (.error "unsupported fd in redirection") : SH PS)
        parseLoop pa interp str special n st { σ with upd := true }
      else do
        if fd = none || fd = some 0 then
          parseLoop pa interp str special n st { σ with mode := .stdin, upd := true }
        else .error (.error "unsupported fd in redirection")
    else do
      -- `base/shell.jl:202-294`
      let σ := if σ.upd then { σ with lastArg := σ.i + σ.off, upd := false } else σ
      if !σ.inDQ && c == A '\'' then do
        let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
        parseLoop pa interp str special n st { σ with inSQ := !σ.inSQ, whs := true, arg := arg, i := i }
      else if !σ.inSQ && c == A '"' then do
        let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
        parseLoop pa interp str special n st { σ with inDQ := !σ.inDQ, whs := true, arg := arg, i := i }
      else if !σ.inSQ && c == A '\\' then
        let σ := { σ with whs := true }
        match st with
        | (_, c') :: st' =>
          if c' == A '\n' || c' == A '\r' then do
            let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
            let i := i + 1
            let (i, st'') ←
              if c' == A '\r' then
                match st' with
                | (_, c'') :: st'' => if c'' == A '\n' then (pure (i + 1, st'') : SH _) else pure (i, st')
                | [] => .error .typeError
              else pure (i, st')
            let (i, st''') ← skipIndent str i st''
            parseLoop pa interp str special n st''' { σ with arg := arg, i := i }
          else if σ.inDQ then
            if c' == A '"' || c' == A '$' || c' == A '\\' then do
              let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
              parseLoop pa interp str special n st' { σ with arg := arg, i := i }
            else parseLoop pa interp str special n st σ
          else do
            let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
            parseLoop pa interp str special n st' { σ with arg := arg, i := i }
        | [] =>
          if σ.inDQ then .error (.error "unterminated double quote")
          else .error (.error "dangling backslash")
      else if interp && !σ.inSQ && !σ.inDQ && c == A '~' && σ.i == j && σ.arg.isEmpty then do
        -- `base/shell.jl:240-290`
        let (arg, i) ← consumeUpto σ.s st σ.arg σ.i j
        let (parts, (s, off), i, uls, st) ← tildeLoop pa (st.length + 1) [] σ.s σ.off i i st
        let userEnd := peekIdx s st
        let lit ← slice s uls (prevind s userEnd)
        let parts := pushNonempty parts (.lit lit)
        let quoted : Bool := match st with
          | (_, c2) :: _ => c2 == A '\'' || c2 == A '"' || c2 == A '\\'
          | [] => false
        let arg :=
          if quoted then arg ++ [.lit (S "~")] ++ parts
          else match parts with
            | [] => arg ++ [.call "expanduser" [.lit (S "~")]]
            | [.lit u] => arg ++ [.call "expanduser" [.lit (S "~" ++ u)]]
            | ps => arg ++ [.tildeLet ps]
        let _ := i
        parseLoop pa interp str special n st { σ with arg := arg, s := s, off := off, i := userEnd }
      else if !σ.inSQ && !σ.inDQ && cin c special then
        .error (.error "special characters must be quoted in commands")
      else parseLoop pa interp str special n st σ

/-- `build_seg_expr(seg_tuple, s_in, s_out, s_out_app, s_err, s_err_app)`,
`base/shell.jl:328-343`. -/
def buildSeg (seg : SEx) (sIn sOut : Option SEx) (sOutApp : Bool) (sErr : Option SEx) (sErrApp : Bool) : SEx :=
  let cmd := SEx.call "Base.cmd_gen" [seg]
  let cmd :=
    if sIn.isSome || sOut.isSome then
      let kwargs := (match sIn with | some x => [SEx.kw "stdin" x] | none => []) ++
        (match sOut with | some x => [SEx.kw "stdout" x] | none => []) ++
        (if sOutApp then [SEx.kw "append" .btrue] else [])
      SEx.call "Base.pipeline" [.params kwargs, cmd]
    else cmd
  match sErr with
  | some e =>
    let kwargs := [SEx.kw "stderr" e] ++ (if sErrApp then [SEx.kw "append" .btrue] else [])
    SEx.call "Base.pipeline" [.params kwargs, cmd]
  | none => cmd

/-- The value of `shell_parse`: the words (`interpolate = false`) or the expression
(`interpolate = true`), with `last_arg`. -/
inductive Out where
  | words (w : List (List SEx)) (lastArg : Int)
  | expr (e : SEx) (lastArg : Int)
  deriving Repr, Inhabited

/-- `__repl_entry_shell_parse(str, interpolate, special, filename)`, `base/shell.jl:36-368`. -/
def shellParse (pa : ParseAtom) (str : JS) (interp : Bool) (special : JS) : SH Out :=
  let (off, s0) := lstripOff str
  let s := rstripShell s0
  if s.isEmpty then .ok (if interp then .expr (.tuple [.tuple []]) 1 else .words [] 1)
  else do
    let st := pairsFrom 1 s
    let σ ← parseLoop pa interp str special (st.length + 1) st
      { inSQ := false, inDQ := false, args := [], arg := [], i := 1, s := s, off := off, lastArg := 1,
        upd := false, whs := false, parts := [], sin := none, sout := none, soutApp := false,
        serr := none, serrApp := false, mode := .none }
    if σ.inSQ then .error (.error "unterminated single quote")
    else if σ.inDQ then .error (.error "unterminated double quote")
    else do
      let x ← slice σ.s σ.i (lastindex σ.s)
      let σ := { σ with arg := pushNonempty σ.arg (.lit x) }
      let σ ← (if interp && σ.mode ≠ .none then
          if σ.arg.isEmpty then .error (.error "redirect operator without filename")
          else pure { setRedirect σ (redirectWordExpr σ.arg) with arg := [] }
        else if !σ.arg.isEmpty || σ.whs then pure { σ with args := append2to1 σ.args σ.arg, arg := [] }
        else pure σ : SH PS)
      if !interp then .ok (.words σ.args σ.lastArg)
      else if σ.parts.isEmpty && σ.sin.isNone && σ.sout.isNone && σ.serr.isNone then
        .ok (.expr (tupleOf σ.args) σ.lastArg)
      else
        let final := buildSeg (tupleOf σ.args) σ.sin σ.sout σ.soutApp σ.serr σ.serrApp
        match σ.parts with
        | [] => .ok (.expr final σ.lastArg)
        | (a, i, o, oa, e, ea) :: rest =>
          let r := rest.foldl (fun r (p : Seg) =>
            SEx.call "Base.pipeline" [r, buildSeg p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2])
            (buildSeg a i o oa e ea)
          .ok (.expr (.call "Base.pipeline" [r, final]) σ.lastArg)

end JuliaLean.MiscCov.Shell
