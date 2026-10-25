import JuliaLean.RegexUnicode.SubstPattern

/-!
# Properties of regex substitution and the regex builders

Each property is a closed `Prop`; `SubstProofs.lean` settles them.
-/

namespace JuliaLean.RegexUnicode.Subst

open JuliaLean JuliaLean.IOBuffers

/-! ## `replace(io, s, r => sub)` on an `IOBuffer` -/

/-- Calls made on a buffer before `replace`. -/
inductive Pre where
  /-- `write(io, bytes)`. -/
  | write (bs : List UInt8)
  /-- `read(io, UInt8)`. -/
  | readByte

def runPre : List Pre → M Unit
  | [] => pure ()
  | .write bs :: t => do let _ ← unsafeWrite bs; runPre t
  | .readByte :: t => do let _ ← IOBuffers.readByte; runPre t

/-- Constructors of append-mode buffers: `PipeBuffer(data; maxsize)` and
`IOBuffer(; read, write, append=true, truncate, maxsize, sizehint)`. -/
inductive AppendCtor where
  | pipe (d : DataArg) (maxsize : Int)
  | buffer (rd wr tr : Option Bool) (maxsize : Int) (sizehint : Option Int)

def AppendCtor.build : AppendCtor → Except IOErr IOBuf
  | .pipe d mx => pipeBuffer d .i64 mx
  | .buffer rd wr tr mx sh => iobufferEmpty rd wr (some true) tr mx sh

/-- After `replace(io, s, r => sub)` the unread bytes are the old unread bytes followed by
`replace(s, r => sub)`, and `position(io)` is unchanged. -/
def appendOk (io : IOBuf) (p : Pat) (s repl : List UInt8) : Bool :=
  match replaceStr p s repl with
  | .error _ => true
  | .ok out =>
    match replaceIO p s repl (.buf io) with
    | .ok _ (.buf io') =>
      match pending io, pending io' with
      | .ok a, .ok b => decide (b = a ++ out) && decide (position io' = position io)
      | _, _ => false
    | _ => false

/-- Build the buffer, run the calls `pre`; if the result is in append mode with unbounded
`maxsize`, check `appendOk`. -/
def appendCase (c : AppendCtor) (pre : List Pre) (p : Pat) (s repl : List UInt8) : Bool :=
  match c.build with
  | .ok io0 =>
    match runPre pre io0 with
    | .ok _ io => !(io.append && decide (io.maxsize = imaxval)) || appendOk io p s repl
    | .error _ _ => true
  | .error _ => true

/-- `regexunicode-replace-capture-append`: on an append-mode `IOBuffer` (made by
`PipeBuffer` or `IOBuffer(; append=true)`, after any writes and reads, `maxsize`
unbounded), `replace(io, s, r => sub)` appends exactly the bytes of `replace(s, r => sub)`
after the existing content and leaves the read position. -/
def ReplaceCaptureAppend : Prop :=
  ∀ (c : AppendCtor) (pre : List Pre) (p : Pat) (s repl : List UInt8),
    isAscii s = true → isAscii repl = true → appendCase c pre p s repl = true

/-- The `io` arguments considered: a fresh `IOBuffer()`, or any other `IO`. -/
def GoodIO (snk : Sink) : Prop := (∃ out, snk = .other out) ∨ (∃ io, iobuffer = .ok io ∧ snk = .buf io)

def resOk {α} : EStateM.Result IOErr Sink α → Bool
  | .ok _ _ => true
  | .error _ _ => false

def exOk {α} : Except IOErr α → Bool
  | .ok _ => true
  | .error _ => false

/-- `regexunicode-replace-capture-generic-io`: for every IO kind, `replace(io, s, r =>
sub)` succeeds whenever `replace(s, r => sub)` does. -/
def ReplaceCaptureGenericIO : Prop :=
  ∀ snk, GoodIO snk → ∀ (p : Pat) (s repl : List UInt8), isAscii s = true → isAscii repl = true →
    exOk (replaceStr p s repl) = true → resOk (replaceIO p s repl snk) = true

/-! ## The substitution step -/

/-- The documented substitution syntax (`SubstitutionString`, `base/regex.jl:585-604`;
`replace`, `base/strings/util.jl`): `\\` (a backslash), `\n` with decimal digits `n`, and
`\g<name>` with a non-empty name, in the text after `unescape_string`; any other
backslash is malformed. -/
def wfAux : Nat → List UInt8 → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | f + 1, c :: t =>
    if c ≠ SUB then wfAux f t
    else
      match t with
      | [] => false
      | d :: t' =>
        if d = SUB then wfAux f t'
        else if isDigitB d then wfAux f (t'.dropWhile isDigitB)
        else if d = GRP then
          match t' with
          | c2 :: t'' =>
            if c2 = LB then
              let name := t''.takeWhile (· ≠ RB)
              let rest := t''.dropWhile (· ≠ RB)
              !name.isEmpty && !rest.isEmpty && wfAux f rest.tail
            else false
          | [] => false
        else false

def wfRepl (repl : List UInt8) : Bool := wfAux (repl.length + 1) repl

def badRepl {α} : EStateM.Result IOErr Sink α → Bool
  | .error (.errorException msg) _ => "Bad replacement string".isPrefixOf msg
  | _ => false

/-- `regexunicode-subst-empty-group-name`: for every match, a malformed substitution
string makes the substitution throw `ErrorException("Bad replacement string: ...")`
(`replace_err`, `base/regex.jl:652`). -/
def SubstEmptyGroupName : Prop :=
  ∀ (p : Pat) (s : List UInt8) (off : Nat) (md : Ovec), exec p s off = some md →
    ∀ (snk : Sink) (repl : List UInt8), isAscii repl = true → wfRepl repl = false →
      badRepl (substStep ⟨s, md, []⟩ repl snk) = true

/-- The substitution `\N` succeeded only if group `N` exists, and it wrote that group. -/
def refOk (md : Ovec) (n : Nat) : EStateM.Result IOErr Sink I → Bool
  | .ok nb _ =>
    decide (n < md.length) &&
      decide (nb.val = match md.getD n none with
        | some (a, b) => ((b - a : Nat) : Int)
        | none => 0)
  | .error _ _ => true

/-- For the match of `p` on `s` at `off` (if any), the substitution `\` ++ `ds` into a fresh
`IOBuffer()` satisfies `refOk`. -/
def groupRefCase (p : Pat) (s : List UInt8) (off : Nat) (ds : List UInt8) : Bool :=
  match exec p s off, iobuffer with
  | some md, .ok io => refOk md (digitsValue ds) (substStep ⟨s, md, []⟩ (SUB :: ds) (.buf io))
  | _, _ => true

/-- `regexunicode-subst-group-overflow`: for every match, a reference `\N` (`N` the decimal
number written) either throws or writes capture group `N`. -/
def SubstGroupRef : Prop :=
  ∀ (p : Pat) (s : List UInt8) (off : Nat) (ds : List UInt8), ds ≠ [] → ds.all isDigitB = true →
    groupRefCase p s off ds = true

/-- `regexunicode-subst-literal`: for every match and every `io`, a substitution string
without a backslash writes exactly its characters, one `write(io, c)` each; on an `IO`
that is not an `IOBuffer` the bytes written are the bytes of the string, as for the plain
`String` replacement `write(io, repl)`. -/
def SubstLiteral : Prop :=
  ∀ (ctx : Ctx) (repl : List UInt8), SUB ∉ repl →
    (∀ snk, substStep ctx repl snk = writeChars repl (i 0) snk) ∧
    (∀ out, ∃ nb, substStep ctx repl (.other out) = .ok nb (.other (out ++ repl)))

/-! ## Regex builders -/

/-- `r^n` either throws or is the pattern of `r` in a group followed by the quantifier
`{n}`. -/
def powOk (r : Regex) (n : Int) : Bool :=
  match pow r n with
  | .error _ => true
  | .ok r' =>
    match lex r.pattern r.flags.x, lex r'.pattern r'.flags.x with
    | .ok toks, .ok toks' =>
      decide (0 ≤ n) && decide (toks' = [.openNC] ++ toks ++ [.close, .quant n.toNat (some n.toNat)])
    | _, _ => false

/-- `regexunicode-regex-pow-negative`: for every compiling regex `r` and every `n`, `r^n`
either throws or produces a pattern that PCRE reads as the pattern of `r` followed by the
repetition quantifier `{n}` (docstring `base/regex.jl:910-928`: "Repeat a regex `n`
times"). -/
def RegexPowQuant : Prop := ∀ (r : Regex) (n : Int), compiles r = true → powOk r n = true

def noCompileErr : Except RErr Regex → Bool
  | .error (.compile _) => false
  | _ => true

/-- `regexunicode-regex-concat-comment`: for every regex `r` that compiles and every string
`s`, `r * s` compiles. -/
def RegexConcatCompiles : Prop :=
  ∀ (r : Regex) (s : List Char), compiles r = true → noCompileErr (mul [.rx r, .str s]) = true

/-- `regexunicode-concat-quote`: for every string `s`, `wrap_string(s)` lexes to exactly the
literal characters of `s`, and lexing `wrap_string(s)` followed by any text consumes the
whole quoted part and returns to the ordinary state (in either `x` setting). -/
def ConcatQuote : Prop :=
  ∀ (s : List Char) (ext : Bool),
    lex (wrapString s) ext = .ok (s.map Tok.lit) ∧
    ∃ g, ∀ (rest : List Char) (stk : List Bool) (acc : List Tok) (f : Nat),
      lexAux (f + g) (wrapString s ++ rest) false ext stk acc =
        lexAux f rest false ext stk ((s.map Tok.lit).reverse ++ acc)

/-! ## Capture names -/

/-- A PCRE2 name table for a regex with `ncap` groups: group numbers in `1:ncap`, names
non-empty and NUL-free. -/
def tableOk (ncap : Nat) (tbl : NameTable) : Bool :=
  tbl.all fun e => 1 ≤ e.1 && e.1 ≤ ncap && !e.2.isEmpty && !e.2.contains 0

/-- `regexunicode-dupnames-haskey`: every key `k` in `keys(m)` satisfies `haskey(m, k)`
(`keys` docstring, `base/regex.jl:238-259`). -/
def DupnamesHaskey : Prop :=
  ∀ (ncap : Nat) (tbl : NameTable), tableOk ncap tbl = true →
    ∀ k ∈ keys ncap tbl, haskey ncap tbl k = .ok true

end JuliaLean.RegexUnicode.Subst
