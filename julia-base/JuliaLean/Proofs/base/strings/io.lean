import JuliaLean.base.strings.io
import JuliaLean.Proofs.base.intfuncs
import JuliaLean.Registry.Types

/-!
# Properties of `base/strings/io.jl`

These statements specify observable text, byte writes, string transformations, and stream views.
Streams are the installed `show.jl` interface; `RecM` below is a stream that records its writes
and its lock depth, and `IOBuffer` results are read back through the installed buffer model.
A string type is any `basic.StringOps`; `IterYields` states what its own `iterate` methods
return.
-/

namespace JuliaLean.Proofs.base.strings.io

open JuliaLean JuliaLean.base JuliaLean.base.show JuliaLean.base.strings.io JuliaLean.Registry

/-! ## A recording stream -/

/-- The observable state of a stream: the bytes written so far and the lock depth. -/
structure Rec where
  bytes : List UInt8 := []
  depth : Int := 0

abbrev RecM (E : Type) := EStateM (Error (StrIOError E)) Rec

instance {E : Type} : MonadExceptOf ShowError (RecM E) where
  throw error := fun state => .error (.display error) state
  tryCatch action handler := fun state =>
    match action state with
    | .error (.display error) state => handler error state
    | r => r

instance {E : Type} : MonadExceptOf (StrIOError E) (RecM E) where
  throw error := fun state => .error (.callback error) state
  tryCatch action handler := fun state =>
    match action state with
    | .error (.callback error) state => handler error state
    | r => r

/-- A stream type whose `write` appends the bytes, whose `lock`/`unlock` count the lock depth,
with no properties of its own. -/
def recPrims {E V : Type} (displaySize : JInt64 × JInt64) : IOPrims (RecM E) Unit V where
  write := fun _ bytes => modify fun r => { r with bytes := r.bytes ++ bytes }
  lock := fun _ => modify fun r => { r with depth := r.depth + 1 }
  unlock := fun _ => modify fun r => { r with depth := r.depth - 1 }
  get := fun _ _ => none
  displaysize := fun _ => pure displaySize

/-- The same stream with `write(io, ::UInt8)` appending the byte and returning `1`. -/
def recCharIO {E V : Type} (displaySize : JInt64 × JInt64) : CharIO (RecM E) Unit V :=
  ⟨recPrims displaySize, fun _ b => do
    modify fun r => { r with bytes := r.bytes ++ [b] }
    pure (JuliaLean.base.int.lit .i64 1)⟩

/-- The same stream with `unsafe_write(io, p, n)` appending the first `n` bytes at `p` and returning
`n` (no `cancel` keyword; the pointer is the byte list it designates, as in the `IOBuffer` world). -/
def recUnsafeWrite {E : Type} : UnsafeWrite (RecM E) Unit (List UInt8) Empty JInt64 where
  plain _ p n := do
    modify fun r => { r with bytes := r.bytes ++ p.take n.val.toNat }
    pure (JInt.wrap .i64 n.val)
  explicit _ p n token := match token with
    | none => do
      modify fun r => { r with bytes := r.bytes ++ p.take n.val.toNat }
      pure (JInt.wrap .i64 n.val)
    | some token => nomatch token
  toInt := JuliaLean.base.int.remT .i64

/-- `act` appends exactly `bytes` and changes nothing else. -/
def Appends {E : Type} (act : RecM E Unit) (bytes : List UInt8) : Prop :=
  ∀ r : Rec, act r = .ok () { r with bytes := r.bytes ++ bytes }

/-- `act` throws `e` without writing. -/
def ThrowsAt {E : Type} (act : RecM E Unit) (e : Error (StrIOError E)) : Prop :=
  ∀ r : Rec, act r = .error e r

/-! ## Iteration of a string with its own methods -/

/-- `iterate(s, i)` from index `i` yields `cs` and then `nothing`. -/
def IterFrom {S R C CU CT E : Type} (ops : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (s : S) : JuliaLean.base.strings.basic.Index → List C → Prop
  | i, [] => ops.iterateAt s i = .ok none
  | i, c :: cs => ∃ k, ops.iterateAt s i = .ok (some (c, k)) ∧ IterFrom ops s k cs

/-- `for c in s` yields `cs`, within the string's iteration bound. -/
def IterYields {S R C CU CT E : Type} (ops : JuliaLean.base.strings.basic.StringOps S R C CU CT E)
    (s : S) (cs : List C) : Prop :=
  cs.length ≤ ops.iterationBound s ∧
  match cs with
  | [] => ops.iterateFirst s = .ok none
  | c :: rest => ∃ k, ops.iterateFirst s = .ok (some (c, k)) ∧ IterFrom ops s k rest

/-- An iterator `itr` with `iterate` methods `it` yields `items` and then `nothing`. -/
def IterOpsFrom {I X St : Type} (it : IterOps I X St) (itr : I) : St → List X → Prop
  | st, [] => it.iterateFrom itr st = none
  | st, x :: xs => ∃ st', it.iterateFrom itr st = some (x, st') ∧ IterOpsFrom it itr st' xs

def IterOpsYields {I X St : Type} (it : IterOps I X St) (itr : I) : List X → Prop
  | [] => it.iterate itr = none
  | x :: xs => ∃ st, it.iterate itr = some (x, st) ∧ IterOpsFrom it itr st xs

/-- `R` relates the two lists element by element. -/
def Forall2 {α β : Type} (R : α → β → Prop) (xs : List α) (ys : List β) : Prop :=
  xs.length = ys.length ∧ ∀ p ∈ xs.zip ys, R p.1 p.2

/-! ## Expected outputs -/

def joinBytes (delim : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | first :: rest => rest.foldl (fun out item => out ++ delim ++ item) first

def joinBytesLast (delim last : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [x] => x
  | x :: y :: [] => x ++ last ++ y
  | x :: y :: rest => x ++ delim ++ joinBytesLast delim last (y :: rest)

/-- The UTF-8 code units of a character (installed `charUtf8Bytes`). -/
def charBytes (cs : List JChar) : List UInt8 := (cs.map charUtf8Bytes).flatten

/-- The ASCII character with code `n`. -/
def ascii (n : Nat) : JChar := asciiLit n.toUInt32

/-- `string(n, base = 16, pad = width)`: lowercase hexadecimal digits, zero-padded. -/
def hexPad (n width : Nat) : List UInt8 :=
  let digits := (Nat.toDigits 16 n).map fun ch => ch.toNat.toUInt8
  List.replicate (width - digits.length) 0x30 ++ digits

/-- The code point of a well-formed character (installed `codepoint(::Char)`). -/
def codepointOf (c : JChar) : Option Nat :=
  match JuliaLean.base.char.codepointChar c with
  | .ok u => some u.toNat
  | .error _ => none

def isPrint (P : JuliaLean.base.strings.unicode.Utf8proc) (c : JChar) : Prop :=
  JuliaLean.base.strings.unicode.isprint JuliaLean.base.strings.unicode.charOps P c = .ok true

def wellFormed (c : JChar) : Prop :=
  JuliaLean.base.char.isoverlong_Char c = false ∧ JuliaLean.base.char.ismalformedChar c = false

/-- The installed `IOBuffer` of `sprint` with `context = nothing` and a size hint of `0`. -/
def bufferRun {E V Ty R : Type} (displaySize : JInt64 × JInt64) (a : AnyOps V Ty)
    (f : JIO Unit V → Unit → BufferShowM E R) : Except (Error E) JuliaString :=
  sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a .none
    (JuliaLean.base.iobuffer.i 0) f ()

/-- `print(io, bytes)` on the installed `IOBuffer`. -/
def bufferBytes {E V : Type} (displaySize : JInt64 × JInt64) (bytes : List UInt8) :
    JIO Unit V → BufferShowM E Unit :=
  fun io => printBytes (bufferPrims displaySize) io bytes

/-! ## 1. `print`, `println` -/

/-- `print(io, x)` and `print(io, xs...)` write the shown values in order and leave the lock as
they found it, including when a `show` throws; `println` adds `"\n"`. -/
def PrintLocking : Prop :=
  (∀ {E V X : Type} (ds : JInt64 × JInt64) (showX : JIO Unit V → X → RecM E Unit) (x : X)
      (r r' : Rec),
    showX (.plain ()) x { r with depth := r.depth + 1 } = .ok () r' →
      printValue (recPrims ds) showX (.plain ()) x r = .ok () { r' with depth := r'.depth - 1 }) ∧
  (∀ {E V X : Type} (ds : JInt64 × JInt64) (showX : JIO Unit V → X → RecM E Unit) (x : X)
      (r r' : Rec) (e : Error (StrIOError E)),
    showX (.plain ()) x { r with depth := r.depth + 1 } = .error e r' →
      printValue (recPrims ds) showX (.plain ()) x r = .error e { r' with depth := r'.depth - 1 }) ∧
  (∀ {E V : Type} (ds : JInt64 × JInt64) (xs : List (RecM E Unit)) (bytes : List (List UInt8))
      (r : Rec),
    Forall2 Appends xs bytes →
      printValues (recPrims (V := V) ds) (.plain ()) xs r = .ok () { r with bytes := r.bytes ++ bytes.flatten } ∧
      printlnValues (recPrims (V := V) ds) (.plain ()) xs r =
        .ok () { r with bytes := r.bytes ++ bytes.flatten ++ [10] }) ∧
  (∀ {E V : Type} (ds : JInt64 × JInt64) (pre post : List (RecM E Unit))
      (bytes : List (List UInt8)) (bad : RecM E Unit) (e : Error (StrIOError E)) (r : Rec),
    Forall2 Appends pre bytes → ThrowsAt bad e →
      printValues (recPrims (V := V) ds) (.plain ()) (pre ++ bad :: post) r =
        .error e { r with bytes := r.bytes ++ bytes.flatten })

/-! ## 2. `sprint`, `repr`, `limitrepr` -/

/-- `sprint(f, args...; context, sizehint)` returns exactly what `f` wrote to its `IOBuffer` and
propagates `f`'s exception; `repr` is `sprint(show, x)`; `limitrepr` shows `x` on a stream
whose `:limit` property is `true`. -/
def SprintCapture : Prop :=
  (∀ {E V Ty : Type} (ds : JInt64 × JInt64) (a : AnyOps V Ty) (bytes : List UInt8)
      (hint : JInt64), 0 ≤ hint.val →
    ∃ out, sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) ds a .none hint
        (fun io (_ : Unit) => bufferBytes (E := E) ds bytes io) () = .ok out ∧ out.bytes = bytes) ∧
  (∀ {E V Ty R : Type} (ds : JInt64 × JInt64) (a : AnyOps V Ty) (e : E) (hint : JInt64),
    0 ≤ hint.val →
    sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) ds a .none hint
        (fun (_ : JIO Unit V) (_ : Unit) => (throwCallback e : BufferShowM E R)) () =
      .error (.callback e)) ∧
  (∀ {E V Ty X : Type} (ds : JInt64 × JInt64) (a : AnyOps V Ty) (showBytes : X → List UInt8)
      (x : X),
    ∃ out, reprIOBuffer (E := E) ds a .none (fun io x => bufferBytes ds (showBytes x) io) x =
      .ok out ∧ out.bytes = showBytes x) ∧
  (∀ {E V Ty X : Type} (ds : JInt64 × JInt64) (a : AnyOps V Ty) (showBytes : X → List UInt8)
      (x : X),
    a.asBool (a.ofBool true) = some true →
    ∃ out, limitrepr (E := E) ds a
        (fun io x => match getIO (bufferPrims (E := E) ds) io "limit" false with
          | .inl v => if a.asBool v = some true then bufferBytes ds (showBytes x) io else pure ()
          | .inr _ => pure ()) x = .ok out ∧ out.bytes = showBytes x)

/-! ## 3. Size hints and string building -/

/-- `string`/`print_to_string` arguments whose `print` method is the given bytes. -/
def PrintsBytes {E V : Type} (ds : JInt64 × JInt64) : StrArg E V → Prop
  | .other print => ∃ bytes, ∀ io, print io = bufferBytes ds bytes io
  | _ => True

/-- The size hint of `sprint` and `print_to_string` changes no output: `sprint` returns the same
for any two non-negative hints, and `print_to_string(xs...)` returns what a `sprint` printing the
same arguments with hint `0` returns. -/
def SizeHintSpec : Prop :=
  (∀ {E V Ty Args R : Type} (ds : JInt64 × JInt64) (a : AnyOps V Ty)
      (f : JIO Unit V → Args → BufferShowM E R) (args : Args) (h₁ h₂ : JInt64),
    0 ≤ h₁.val → 0 ≤ h₂.val →
    sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) ds a .none h₁ f args =
      sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) ds a .none h₂ f args) ∧
  (∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
      (a : AnyOps V Ty) (xs : List (StrArg E V)) (hints : List JInt64),
    xs ≠ [] →
    Forall2 (fun x h => strSizehint c x = .ok h) xs hints →
    0 ≤ (hints.foldl JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 0)).val →
    printToString c ds a xs =
      bufferRun ds a (fun io (_ : Unit) => do for x in xs do printArg c ds a io x))

/-- `string(xs...)` and `string_with_env(env, xs...)` concatenate the printed forms of their
arguments in order and propagate an argument's `print` exception; `string(::Symbol)` is the
symbol's name. -/
def StringBuilding : Prop :=
  ∀ {E V Ty : Type} (c : JuliaLean.base.intfuncs.DigitCallees) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (xs : List (StrArg E V)) (env : SprintContext E V) (symbol : JuliaSymbol),
    (∀ x ∈ xs, PrintsBytes ds x) →
    (∀ out, printToString c ds a xs = .ok out →
      ∃ outs, xs.mapM (fun x => printToString c ds a [x]) = .ok outs ∧
        out.bytes = (outs.map (·.bytes)).flatten) ∧
    stringWithEnv c ds a env ([] : List (StrArg E V)) = .ok ⟨[]⟩ ∧
    stringSymbol symbol = ⟨symbol.name⟩ ∧
    (∀ (e : E), printToString c ds a [StrArg.other (fun _ => throwCallback e)] =
      .error (.callback e)) ∧
    stringWithEnv c ds a .none xs = printToString c ds a xs

/-! ## 4. Character and string output -/

/-- `print(io, s::AbstractString)` writes the UTF-8 bytes of each character of `s` in order and
`write(io, s::AbstractString)` returns their count; `print` of a `String` or `SubString{String}`
writes its bytes. -/
def StringWrites : Prop :=
  ∀ {S R CU CT E V : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (ds : JInt64 × JInt64) (s : S) (cs : List JChar) (r : Rec),
    IterYields ops s cs →
    printAbstractString ops (recCharIO (E := E) (V := V) ds) (.plain ()) s r =
      .ok () { r with bytes := r.bytes ++ charBytes cs } ∧
    writeAbstractString ops (recCharIO (E := E) (V := V) ds) (.plain ()) s r =
      .ok (JInt.wrap .i64 (charBytes cs).length) { r with bytes := r.bytes ++ charBytes cs } ∧
    (∀ str : JString,
      printConcreteString (recUnsafeWrite (E := E)) pointerStringPure sizeofJString () str r =
        .ok () { r with bytes := r.bytes ++ str.bytes }) ∧
    (∀ sub : JuliaLean.base.strings.substring.SubString JString,
      0 ≤ sub.offset.val → 0 ≤ sub.ncodeunits.val →
      printConcreteString (recUnsafeWrite (E := E)) pointerSubStringPure sizeofJSubString () sub r =
        .ok () { r with bytes := r.bytes ++
          (sub.string.bytes.drop sub.offset.val.toNat).take sub.ncodeunits.val.toNat })

/-- `show(io, s::AbstractString)` writes `"`, the output of `escape_string(io, s, "\"\$")`, and
`"`; a quote or `$` is written as a backslash and the character. -/
def QuotedString : Prop :=
  (∀ {S R CU CT E V : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (P : JuliaLean.base.strings.unicode.Utf8proc)
      (digits : JuliaLean.base.intfuncs.DigitCallees) (s : S) (r r' : Rec),
    escapeStringIO ops (recCharIO (E := E) (V := V) ds) P digits (.plain ()) s
        [ascii 0x22, ascii 0x24] [] false false { r with bytes := [] } = .ok () r' →
      printQuoted ops (recCharIO (E := E) (V := V) ds) P digits (.plain ()) s r =
        .ok () { r' with bytes := r.bytes ++ [0x22] ++ r'.bytes ++ [0x22] }) ∧
  (∀ {S R CU CT E V : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (P : JuliaLean.base.strings.unicode.Utf8proc) (s : S) (q : Nat)
      (r : Rec),
    (q = 0x22 ∨ q = 0x24) → IterYields ops s [ascii q] →
    printQuoted ops (recCharIO (E := E) (V := V) ds) P
        JuliaLean.Proofs.base.intfuncs.exactDigitCallees (.plain ()) s r =
      .ok () { r with bytes := r.bytes ++ [0x22, 0x5c, q.toUInt8, 0x22] })

/-! ## 5. Limited `text/plain` show -/

/-- The columns of a `String`'s characters (installed `textwidth`). -/
def displayCols (P : JuliaLean.base.strings.unicode.Utf8proc) (bytes : List UInt8) : Int :=
  if h : bytes.length < 2 ^ 62 then
    (stringChars ⟨bytes, h⟩).foldl (fun w c => w + JuliaLean.base.strings.unicode.textwidthChar P c) 0
  else 0

/-- `printstyled` that prints its arguments without styling. -/
def plainStyled {E V : Type} : PrintStyled (RecM E) Unit V :=
  fun io xs _ _ => do for x in xs do x io

/-- `show(io, MIME"text/plain", str; limit)` with an `Int` limit: a string whose text width fits
`limit - 2` columns is shown as `show(io, str)`; otherwise it is either shown in full or written
as the shown head, the elision marker and the shown tail, and the elided output fits the limit. -/
def LimitedShow : Prop :=
  ∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (liftJ : JlError → E) (stringify : S → Except E S) (stringifyRepl : JString → Except E S)
    (concat : List (JuliaLean.base.strings.util.TruncPiece S (List JChar)) → Except E S)
    (s : S) (limit : JInt64) (r r' : Rec),
    let cio := recCharIO (E := E) (V := V) ds
    let digits := JuliaLean.Proofs.base.intfuncs.exactDigitCallees
    let clipped := if limit.val - 2 < 0 then 0 else limit.val - 2
    let tops := truncOps ops P liftJ stringify stringifyRepl concat
    let shown := printQuoted ops cio P digits (.plain ()) s
    2 ≤ limit.val →
    showTextPlain ops cio a plainStyled P digits liftJ stringify stringifyRepl concat (.plain ()) s
      (some limit) r = .ok () r' →
    (JuliaLean.base.strings.util.checkTextwidth tops s clipped = some (.ok true) →
      shown r = .ok () r') ∧
    (shown r ≠ .ok () r' →
      ∃ (head tail last : JuliaLean.base.strings.basic.Index) (h t : Rec),
        ops.lastindex s = .ok last ∧
        printQuotedView ops cio P digits (.plain ()) s (JuliaLean.base.int.lit .i64 1) head
          { r with bytes := [] } = .ok () h ∧
        printQuotedView ops cio P digits (.plain ()) s tail last { h with bytes := [] } = .ok () t ∧
        let units := if ops.codeunitSize (ops.codeunitType s) == JuliaLean.base.int.lit .i64 1 then
          "bytes" else "code units"
        let skipText := fun (skip : Int) => " ⋯ " ++ toString skip ++ " " ++ units ++ " ⋯ "
        ∃ (maxReplacement : JString) (afterhead : JuliaLean.base.strings.basic.Index),
          maxReplacement.bytes = (skipText (JuliaLean.base.int.mul (ops.ncodeunits s)
            (JuliaLean.base.int.lit .i64 100)).val).toUTF8.toList ∧
          JuliaLean.base.strings.util.stringTruncateBoundaries tops
            JuliaLean.base.strings.util.truncModeOps s clipped maxReplacement
            ⟨JuliaLean.base.strings.util.TruncMode.center⟩ = some (.ok (some (head, tail))) ∧
          JuliaLean.base.strings.basic.nextindOne ops s head = .ok afterhead ∧
          let marker := (skipText (tail.val - afterhead.val)).toUTF8.toList
          r'.bytes = r.bytes ++ h.bytes ++ marker ++ t.bytes ∧
          displayCols P (h.bytes ++ marker ++ t.bytes) ≤ limit.val)

/-! ## 6. `join` -/

/-- `join(io, iterator, delim[, last])` and `join(iterator[, delim[, last]])` print the items in
iteration order with `delim` between consecutive items and `last` (when given) between the final
two, for an iterator of non-annotated items (named gap `join-annotated`). -/
def JoinSpec : Prop :=
  (∀ {E V I X D St : Type} (ds : JInt64 × JInt64) (it : IterOps I X St) (itr : I)
      (items : List X) (showX : X → List UInt8) (showD : D → List UInt8) (delim last : D),
    IterOpsYields it itr items →
    let printX := fun (io : JIO Unit V) (x : X) =>
      liftShow (E := E) (bufferBytes ds (showX x) io)
    let printD := fun (io : JIO Unit V) (d : D) =>
      liftShow (E := E) (bufferBytes ds (showD d) io)
    (∃ out, joinString ds it printX printD itr (none, none) = some (.ok out) ∧
      out.bytes = joinBytes [] (items.map showX)) ∧
    (∃ out, joinString ds it printX printD itr (some delim, none) = some (.ok out) ∧
      out.bytes = joinBytes (showD delim) (items.map showX)) ∧
    (∃ out, joinString ds it printX printD itr (some delim, some last) = some (.ok out) ∧
      out.bytes = joinBytesLast (showD delim) (showD last) (items.map showX))) ∧
  (∀ {E V I X D St : Type} (ds : JInt64 × JInt64) (it : IterOps I X St) (itr : I)
      (items : List X) (showX : X → List UInt8) (showD : D → List UInt8) (delim last : D)
      (initial : JuliaLean.base.iobuffer.BufferState),
    IterOpsYields it itr items →
    newBufferState (JuliaLean.base.iobuffer.bitsConversions .i64)
      (some (JuliaLean.base.iobuffer.i 0)) = .ok initial →
    let p := liftPrims (E := E) (bufferPrims (V := V) ds)
    let printX := fun (io : JIO Unit V) (x : X) => printBytes p io (showX x)
    let printD := fun (io : JIO Unit V) (d : D) => printBytes p io (showD d)
    (∃ final rest, join3 it printX printD (.plain ()) itr delim initial = some (.ok ((), final)) ∧
      JuliaLean.base.iobuffer.takestring final =
        .ok (joinBytes (showD delim) (items.map showX)) rest) ∧
    (∃ final rest, join4 p it printX printD (.plain ()) itr delim last initial =
        some (.ok ((), final)) ∧
      JuliaLean.base.iobuffer.takestring final =
        .ok (joinBytesLast (showD delim) (showD last) (items.map showX)) rest))

/-! ## 7. `escape_string`, `unescape_string` -/

/-- `escape_string(s)` of a `String` (installed `String` methods, `esc = ('"',)`). -/
def escapeDefault {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime)
    (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (s : JString) :=
  escapeString (JuliaLean.base.strings.search.stringBasic rt) ds a P
    JuliaLean.Proofs.base.intfuncs.exactDigitCallees s [ascii 0x22] [] false false

/-- `unescape_string(s)` of a `String`. -/
def unescapeDefault {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime)
    (ds : JInt64 × JInt64) (a : AnyOps V Ty) (s : JString) :=
  unescapeString (JuliaLean.base.strings.search.stringBasic rt) ds a s []

/-- `unescape_string(escape_string(s)) == s`. -/
def RoundTrips {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime)
    (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (s : JString) : Prop :=
  ∃ (out : JuliaString) (t : JString), escapeDefault rt ds a P s = .ok out ∧ t.bytes = out.bytes ∧
    ∃ back, unescapeDefault rt ds a t = .ok back ∧ back.bytes = s.bytes

/-- Default escape and unescape round-trip every `String` whose characters are malformed,
overlong, or have a code point at most `U+10FFFF`. -/
def EscapeRoundTripInRange : Prop :=
  ∀ {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc) (s : JString),
    (∀ c ∈ stringChars s, ¬ wellFormed c ∨ ∃ u, codepointOf c = some u ∧ u ≤ 0x10ffff) →
    RoundTrips rt ds a P s

/-- Default escaping and unescaping round-trip valid strings within Unicode's code-point range. -/
def EscapeRoundTripValid : Prop :=
  ∀ {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc) (s : JString),
    (∀ c ∈ stringChars s, wellFormed c ∧ ∃ u, codepointOf c = some u ∧ u ≤ 0x10ffff) →
    RoundTrips rt ds a P s

/-- Default escaping and unescaping round-trip every `String`, including invalid UTF-8. -/
def EscapeRoundTripAll : Prop :=
  ∀ {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc) (s : JString),
    RoundTrips rt ds a P s

/-- `escape_string(s, esc; keep, ascii, fullhex)` of a string type with its own `iterate`. -/
def escapeOf {S R CU CT E V Ty : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc) (s : S)
    (esc keep : List JChar) (asciiOnly fullhex : Bool) :=
  escapeString ops ds a P JuliaLean.Proofs.base.intfuncs.exactDigitCallees s esc keep asciiOnly
    fullhex

/-- `escape_string` returned `bytes`. -/
def Escapes {S R CU CT E V Ty : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc) (s : S)
    (esc keep : List JChar) (asciiOnly fullhex : Bool) (bytes : List UInt8) : Prop :=
  ∃ out, escapeOf ops ds a P s esc keep asciiOnly fullhex = .ok out ∧ out.bytes = bytes

/-- `escape_string` options: with ASCII `esc`/`keep`, `ascii = true` writes only ASCII; a kept
character stays literal; an `esc` character gets a backslash; a non-ASCII character that is not
printable (or with `ascii = true`) is `\u` with 4 hex digits up to `U+FFFF` and `\U` with 8 above
under `fullhex`, and 2 or 4 digits otherwise unless the next character is a hex digit; printable
non-ASCII characters stay literal; `need_full_hex` and `escape_nul` as in the source. -/
def EscapeOptions : Prop :=
  (∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
      (s : S) (esc keep : List JChar) (fullhex : Bool) (out : JuliaString),
    (∀ c ∈ esc ++ keep, JuliaLean.base.strings.basic.isasciiChar c = true) →
    escapeOf ops ds a P s esc keep true fullhex = .ok out → ∀ b ∈ out.bytes, b.toNat < 0x80) ∧
  (∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
      (s : S) (c : JChar) (asciiOnly fullhex : Bool) (h : JuliaLean.base.strings.basic.Index),
    IterYields ops s [c] → ops.lastindex s = .ok h → 0 ≤ h.val →
    Escapes ops ds a P s [] [c] asciiOnly fullhex (charUtf8Bytes c) ∧
    Escapes ops ds a P s [c] [] asciiOnly fullhex (0x5c :: charUtf8Bytes c)) ∧
  (∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
      (s : S) (c : JChar) (u : Nat) (asciiOnly : Bool) (h : JuliaLean.base.strings.basic.Index),
    IterYields ops s [c] → ops.lastindex s = .ok h → 0 ≤ h.val →
    JuliaLean.base.strings.basic.isasciiChar c = false → wellFormed c → codepointOf c = some u →
    (asciiOnly = true ∨ ¬ isPrint P c) →
    (u ≤ 0xffff → Escapes ops ds a P s [] [] asciiOnly true ([0x5c, 0x75] ++ hexPad u 4)) ∧
    (0xffff < u → Escapes ops ds a P s [] [] asciiOnly true ([0x5c, 0x55] ++ hexPad u 8))) ∧
  (∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
      (s : S) (c next : JChar) (u : Nat) (h : JuliaLean.base.strings.basic.Index) (out : JuliaString),
    IterYields ops s [c, next] → ops.lastindex s = .ok h → 0 ≤ h.val →
    JuliaLean.base.strings.basic.isasciiChar c = false → wellFormed c → codepointOf c = some u →
    0x80 ≤ u →
    escapeOf ops ds a P s [] [] true false = .ok out →
    let full := needFullHex (some next)
    (u ≤ 0xffff → ∃ rest, out.bytes = [0x5c, 0x75] ++ hexPad u (if full then 4 else 2) ++ rest) ∧
    (0xffff < u → ∃ rest, out.bytes = [0x5c, 0x55] ++ hexPad u (if full then 8 else 4) ++ rest)) ∧
  (∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (a : AnyOps V Ty) (P : JuliaLean.base.strings.unicode.Utf8proc)
      (s : S) (c : JChar) (h : JuliaLean.base.strings.basic.Index),
    IterYields ops s [c] → ops.lastindex s = .ok h → 0 ≤ h.val →
    JuliaLean.base.strings.basic.isasciiChar c = false → wellFormed c → isPrint P c →
    Escapes ops ds a P s [] [] false false (charUtf8Bytes c)) ∧
  (∀ c : Option JChar,
    needFullHex c = c.elim false
      (JuliaLean.base.strings.unicode.isxdigit JuliaLean.base.strings.unicode.charOps) ∧
    escapeNul c = if c.elim false (fun x => ascii 0x30 ≤ x ∧ x ≤ ascii 0x37) then "\\x00" else "\\0")

/-- `unescape_string` returned `bytes`. -/
def Unescapes {S R CU CT E V Ty : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (s : S) (keep : List JChar) (bytes : List UInt8) : Prop :=
  ∃ out, unescapeString ops ds a s keep = .ok out ∧ out.bytes = bytes

def hexDigitChar (d : Nat) : JChar := ascii (if d < 10 then 0x30 + d else 0x57 + d)

/-- `unescape_string` keeps a backslash pair whose character is in `keep`, and decodes the
standard C escapes, `\x` hex bytes, `\u`/`\U` characters, and octal bytes. -/
def UnescapeOptions : Prop :=
  ∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (ds : JInt64 × JInt64) (a : AnyOps V Ty) (s : S) (h : JuliaLean.base.strings.basic.Index),
    ops.lastindex s = .ok h → 0 ≤ h.val →
    (∀ c : JChar, IterYields ops s [ascii 0x5c, c] →
      Unescapes ops ds a s [c] (0x5c :: charUtf8Bytes c)) ∧
    (∀ code value : Nat,
      (code, value) ∈ [(0x61, 7), (0x62, 8), (0x74, 9), (0x6e, 10), (0x76, 11), (0x66, 12),
        (0x72, 13), (0x65, 27), (0x5c, 0x5c), (0x22, 0x22)] →
      IterYields ops s [ascii 0x5c, ascii code] → Unescapes ops ds a s [] [value.toUInt8]) ∧
    (∀ d : Nat, d < 16 → IterYields ops s [ascii 0x5c, ascii 0x78, hexDigitChar d] →
      Unescapes ops ds a s [] [d.toUInt8]) ∧
    (∀ d : Nat, d < 8 → IterYields ops s [ascii 0x5c, ascii (0x30 + d)] →
      Unescapes ops ds a s [] [d.toUInt8]) ∧
    (∀ d : Nat, d < 16 → IterYields ops s [ascii 0x5c, ascii 0x75, hexDigitChar d] →
      Unescapes ops ds a s [] (charUtf8Bytes (ascii d))) ∧
    (∀ d : Nat, d < 16 → IterYields ops s [ascii 0x5c, ascii 0x55, hexDigitChar d] →
      Unescapes ops ds a s [] (charUtf8Bytes (ascii d)))

/-- `b"..."` is `codeunits(unescape_string(s))` of the `String` literal. -/
def ByteStringMacro : Prop :=
  ∀ {V Ty : Type} (rt : JuliaLean.base.strings.search.StringRuntime) (ds : JInt64 × JInt64)
    (a : AnyOps V Ty) (s : JString),
    (∀ out, unescapeString (JuliaLean.base.strings.search.stringBasic rt) ds a s [] = .ok out →
      bStr rt ds a s = .ok ⟨⟨out.bytes⟩⟩) ∧
    (∀ e, unescapeString (JuliaLean.base.strings.search.stringBasic rt) ds a s [] = .error e →
      bStr rt ds a s = .error e)

/-! ## 8. Raw strings -/

/-- The characters `escape_raw_string` writes: backslashes before a delimiter and at the end of
the string are doubled, and the delimiter gets one backslash. -/
def rawEscapeChars (delim : JChar) : Nat → List JChar → List JChar
  | escapes, [] => List.replicate escapes (ascii 0x5c)
  | escapes, c :: rest =>
    if c = ascii 0x5c then ascii 0x5c :: rawEscapeChars delim (escapes + 1) rest
    else List.replicate (if c = delim then escapes + 1 else 0) (ascii 0x5c) ++
      c :: rawEscapeChars delim 0 rest

/-- `escape_raw_string(io, s, delim)` writes the doubled form and returns the number of inserted
backslashes; `escape_raw_string(s, delim)` returns `s` itself when none are inserted; `raw"..."`
returns its input. -/
def RawStringSpec : Prop :=
  ∀ {S R CU CT E V Ty : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (ds : JInt64 × JInt64) (a : AnyOps V Ty) (s : S) (cs : List JChar) (delim : JChar) (r : Rec),
    IterYields ops s cs →
    let expected := rawEscapeChars delim 0 cs
    let added := expected.length - cs.length
    escapeRawStringIO ops (recCharIO (E := E) (V := V) ds) (.plain ()) s delim r =
      .ok (JInt.wrap .i64 added) { r with bytes := r.bytes ++ charBytes expected } ∧
    (added = 0 → escapeRawString ops ds a s delim = .ok (RawStringResult.original s)) ∧
    (0 < added → 0 ≤ (JuliaLean.base.strings.basic.sizeofString ops s).val →
      escapeRawString ops ds a s delim = .ok (RawStringResult.copied (charBytes expected))) ∧
    rawStr s = s

/-! ## 9. Multiline strings -/

/-- `indentation(str; tabwidth)`: spaces count one column, a tab moves to the next multiple of
`tabwidth`; the count stops at the first other character. -/
def indentationSpecValue (tabwidth : Int) : Int → List JChar → Int × Bool
  | count, [] => (count, true)
  | count, c :: rest =>
    if c = ascii 0x20 then indentationSpecValue tabwidth (count + 1) rest
    else if c = ascii 0x09 then
      indentationSpecValue tabwidth ((count + tabwidth).tdiv tabwidth * tabwidth) rest
    else (count, false)

def spaces (n : Int) : List UInt8 := List.replicate n.toNat 0x20

/-- The text of `unindent(str, indent; tabwidth)`: leading whitespace of each line is replaced by
spaces up to the column, less `indent`. -/
def unindentSpecLoop (indent tabwidth : Int) : Bool → Int → List JChar → List UInt8
  | cutting, column, [] => if cutting then spaces (column - indent) else []
  | true, column, c :: rest =>
    if c = ascii 0x20 then unindentSpecLoop indent tabwidth true (column + 1) rest
    else if c = ascii 0x09 then
      unindentSpecLoop indent tabwidth true ((column + tabwidth).tdiv tabwidth * tabwidth) rest
    else if c = ascii 0x0a then
      spaces (column - indent) ++ charUtf8Bytes c ++ unindentSpecLoop indent tabwidth true 0 rest
    else
      spaces (column - indent) ++ charUtf8Bytes c ++
        unindentSpecLoop indent tabwidth false (column + 1) rest
  | false, column, c :: rest =>
    if c = ascii 0x09 then
      let updated := (column + tabwidth).tdiv tabwidth * tabwidth
      spaces (updated - column) ++ unindentSpecLoop indent tabwidth false updated rest
    else if c = ascii 0x0a then
      charUtf8Bytes c ++ unindentSpecLoop indent tabwidth true 0 rest
    else charUtf8Bytes c ++ unindentSpecLoop indent tabwidth false (column + 1) rest

/-- `indentation` and `unindent` with a positive `tabwidth` and no `Int` overflow compute the
columns above; `tabwidth == 0` throws `DivideError` at the first tab. -/
def IndentationSpec : Prop :=
  (∀ {S R CU CT E : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (s : S) (cs : List JChar) (tabwidth : JInt64),
    IterYields ops s cs → 0 < tabwidth.val → (cs.length + 1) * tabwidth.val < 2 ^ 62 →
    let v := indentationSpecValue tabwidth.val 0 cs
    indentation ops s tabwidth = .ok (JInt.wrap .i64 v.1, v.2)) ∧
  (∀ {S R CU CT E : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (s : S) (cs : List JChar) (indent tabwidth : JInt64),
    IterYields ops s cs → 0 < tabwidth.val → (cs.length + 1) * tabwidth.val < 2 ^ 62 →
    0 < indent.val → indent.val < 2 ^ 62 →
    0 ≤ (JuliaLean.base.strings.basic.sizeofString ops s).val →
    unindent ops ds s indent tabwidth =
      .ok (.built (unindentSpecLoop indent.val tabwidth.val true 0 cs))) ∧
  (∀ {S R CU CT E : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (ds : JInt64 × JInt64) (s : S) (tabwidth : JInt64),
    unindent ops ds s (JuliaLean.base.int.lit .i64 0) tabwidth = .ok (.original s)) ∧
  (∀ {S R CU CT E : Type} (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
      (s : S) (pre rest : List JChar),
    IterYields ops s (pre ++ ascii 0x09 :: rest) → (∀ c ∈ pre, c = ascii 0x20) →
    indentation ops s (JuliaLean.base.int.lit .i64 0) = .error (.jl .divideError))

/-! ## 10. `String` and `AnnotatedString` from characters -/

/-- The regions of `AnnotatedString(chars)`: each annotation of the character at code-unit
position `point` covers `point:point`. -/
def expectedAnnotations : Nat → List AnnotatedChar → List RegionAnnotation
  | _, [] => []
  | point, c :: rest =>
    c.annotations.map (fun annotation => ⟨point, point, annotation⟩) ++
      expectedAnnotations (point + (charUtf8Bytes c.char).length) rest

/-- `String(v::AbstractVector{Char})` is the concatenation of the characters' code units;
`String(v::AbstractVector{<:AbstractChar})` prints each character converted to `Char`;
`AnnotatedString(v)` keeps the characters in order with each annotation at its byte position. -/
def CharacterVectors : Prop :=
  (∀ cs : List JChar, ∃ out, stringOfChars cs = .ok out ∧ out.bytes = charBytes cs) ∧
  (∀ {C E V Ty : Type} (cops : JuliaLean.base.strings.unicode.CharOps C) (ds : JInt64 × JInt64)
      (a : AnyOps V Ty) (chars : List C) (cs : List JChar),
    Forall2 (fun c ch => cops.toChar c = .ok ch) chars cs →
    ∃ out, stringOfAbstractChars (E := E) cops ds a chars = .ok out ∧ out.bytes = charBytes cs) ∧
  (∀ chars : List AnnotatedChar, ∃ out, annotatedStringOfChars chars = .ok out ∧
    out.bytes = charBytes (chars.map (·.char)) ∧ out.annotations = expectedAnnotations 1 chars)

/-! ## 11. `IOBuffer` views of strings -/

/-- `IOBuffer(s::String)` and `IOBuffer(s::SubString{String})` are read-only buffers over the
string's bytes, the latter over the `sizeof(s)` bytes after its stored offset. -/
def StringIOViews : Prop :=
  (∀ s : JuliaString, s.bytes.length < 2 ^ 62 →
    ∃ st, ioBufferString s = .ok st ∧ st.data = s.bytes ∧ st.readable = true ∧
      st.writable = false ∧ st.ptr.val = 1 ∧ st.size.val = s.bytes.length) ∧
  (∀ sub : JuliaSubString, sub.offset + sub.byteCount ≤ sub.string.bytes.length →
    sub.string.bytes.length < 2 ^ 62 →
    ∃ st, ioBufferSubString sub = .ok st ∧
      st.data = (sub.string.bytes.drop sub.offset).take sub.byteCount ∧ st.readable = true ∧
      st.writable = false ∧ st.ptr.val = 1 ∧ st.size.val = sub.byteCount)

/-! ## Registry entries -/

end JuliaLean.Proofs.base.strings.io

namespace JuliaLean.ChatGPT.Batch4.Group19

open JuliaLean JuliaLean.base.show JuliaLean.base.strings.io

theorem ShowcovStringsBStringCodeunits_proven :
    JuliaLean.Proofs.base.strings.io.ByteStringMacro := by
  intro V Ty rt ds a s
  constructor
  · intro out h
    change Except.bind
      (unescapeString (JuliaLean.base.strings.search.stringBasic rt) ds a s [])
      (fun str => Except.ok (⟨⟨str.bytes⟩⟩ : JuliaLean.base.strings.io.QuoteNode)) = _
    rw [h]
    rfl
  · intro e h
    change Except.bind
      (unescapeString (JuliaLean.base.strings.search.stringBasic rt) ds a s [])
      (fun str => Except.ok (⟨⟨str.bytes⟩⟩ : JuliaLean.base.strings.io.QuoteNode)) = _
    rw [h]
    rfl

end JuliaLean.ChatGPT.Batch4.Group19

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace JuliaLean.ChatGPT.Batch8.Group8
open JuliaLean JuliaLean.base JuliaLean.base.show JuliaLean.base.strings.io
open JuliaLean.Proofs.base.strings.io

theorem g8IoCoreFinallyOk {ε σ : Type} (enter leave : σ → σ)
    (body : EStateM ε σ Unit) (initial after : σ)
    (h : body (enter initial) = .ok () after) :
    (do
      modify enter
      tryFinally body (modify leave) : EStateM ε σ Unit) initial =
      .ok () (leave after) := by
  simp only [tryFinally, Bind.bind, EStateM.bind,
    modify, MonadState.modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    MonadFinally.tryFinally', EStateM.instMonadFinally, Functor.map, EStateM.map, h] <;> rfl

theorem g8IoCoreFinallyError {ε σ : Type} (enter leave : σ → σ)
    (body : EStateM ε σ Unit) (initial after : σ) (error : ε)
    (h : body (enter initial) = .error error after) :
    (do
      modify enter
      tryFinally body (modify leave) : EStateM ε σ Unit) initial =
      .error error (leave after) := by
  simp only [tryFinally, Bind.bind, EStateM.bind,
    modify, MonadState.modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    MonadFinally.tryFinally', EStateM.instMonadFinally, Functor.map, EStateM.map, h] <;> rfl

def g8IoCoreForall2 {α β : Type} (R : α → β → Prop)
    (xs : List α) (ys : List β) : Prop :=
  xs.length = ys.length ∧ ∀ p ∈ xs.zip ys, R p.1 p.2

theorem g8IoCoreForall2Cons {α β : Type} (R : α → β → Prop)
    (x : α) (xs : List α) (b : β) (bs : List β)
    (h : g8IoCoreForall2 R (x :: xs) (b :: bs)) :
    R x b ∧ g8IoCoreForall2 R xs bs := by
  constructor
  · exact h.2 (x, b) (by
      change (x, b) ∈ (x, b) :: xs.zip bs
      exact List.mem_cons_self)
  · refine ⟨?_, ?_⟩
    · have he : xs.length + 1 = bs.length + 1 := by
        simpa only [List.length_cons] using h.1
      exact Nat.succ.inj he
    intro p hp
    exact h.2 p (by
      change p ∈ (x, b) :: xs.zip bs
      exact List.mem_cons_of_mem (x, b) hp)

theorem g8IoCoreForLoopCons {ε σ : Type} (action : EStateM ε σ Unit)
    (rest : List (EStateM ε σ Unit)) (initial : σ) :
    (do for next in action :: rest do next : EStateM ε σ Unit) initial =
      (match action initial with
      | .ok _ state => (do for next in rest do next : EStateM ε σ Unit) state
      | .error error state => .error error state) := by
  simp only [List.forIn_cons, bind_assoc, pure_bind]
  simp only [Bind.bind, EStateM.bind]
  cases action initial <;> rfl

theorem g8IoCoreForLoopAppends {ε σ α : Type}
    (put : σ → List α → σ)
    (put_nil : ∀ state, put state [] = state)
    (put_append : ∀ state left right, put (put state left) right = put state (left ++ right))
    (actions : List (EStateM ε σ Unit)) (chunks : List (List α))
    (h : g8IoCoreForall2 (fun action bytes =>
      ∀ state, action state = .ok () (put state bytes)) actions chunks) (initial : σ) :
    (do for action in actions do action : EStateM ε σ Unit) initial =
      .ok () (put initial chunks.flatten) := by
  induction actions generalizing chunks initial with
  | nil =>
    have hc : chunks = [] := List.eq_nil_of_length_eq_zero h.1.symm
    subst chunks
    simp only [List.forIn_nil, List.flatten_nil, put_nil] <;> rfl
  | cons action rest ih =>
    cases chunks with
    | nil =>
      have hbad : Nat.succ rest.length = 0 := by
        simpa only [List.length_cons, List.length_nil, Nat.succ_eq_add_one] using h.1
      exact False.elim (Nat.noConfusion hbad)
    | cons bytes chunks =>
      obtain ⟨hx, ht⟩ := g8IoCoreForall2Cons _ action rest bytes chunks h
      rw [g8IoCoreForLoopCons, hx initial]
      simpa only [List.flatten_cons, put_append] using
        ih chunks ht (put initial bytes)

theorem g8IoCoreForLoopThrows {ε σ α : Type}
    (put : σ → List α → σ)
    (put_nil : ∀ state, put state [] = state)
    (put_append : ∀ state left right, put (put state left) right = put state (left ++ right))
    (before after : List (EStateM ε σ Unit)) (chunks : List (List α))
    (bad : EStateM ε σ Unit) (error : ε)
    (h : g8IoCoreForall2 (fun action bytes =>
      ∀ state, action state = .ok () (put state bytes)) before chunks)
    (hb : ∀ state, bad state = .error error state) (initial : σ) :
    (do for action in before ++ bad :: after do action : EStateM ε σ Unit) initial =
      .error error (put initial chunks.flatten) := by
  induction before generalizing chunks initial with
  | nil =>
    have hc : chunks = [] := List.eq_nil_of_length_eq_zero h.1.symm
    subst chunks
    simp only [List.nil_append, List.flatten_nil, put_nil]
    rw [g8IoCoreForLoopCons, hb initial]
  | cons action before ih =>
    cases chunks with
    | nil =>
      have hbad : Nat.succ before.length = 0 := by
        simpa only [List.length_cons, List.length_nil, Nat.succ_eq_add_one] using h.1
      exact False.elim (Nat.noConfusion hbad)
    | cons bytes chunks =>
      obtain ⟨hx, ht⟩ := g8IoCoreForall2Cons _ action before bytes chunks h
      simp only [List.cons_append]
      rw [g8IoCoreForLoopCons, hx initial]
      simpa only [List.flatten_cons, put_append] using
        ih chunks ht (put initial bytes)

theorem g8IoCoreForall2Append {α β : Type} (R : α → β → Prop)
    (xs xs' : List α) (ys ys' : List β)
    (h : g8IoCoreForall2 R xs ys) (h' : g8IoCoreForall2 R xs' ys') :
    g8IoCoreForall2 R (xs ++ xs') (ys ++ ys') := by
  refine ⟨by simpa only [List.length_append, h.1, h'.1], ?_⟩
  rw [List.zip_append h.1]
  intro p hp
  cases List.mem_append.mp hp with
  | inl hp => exact h.2 p hp
  | inr hp => exact h'.2 p hp

theorem recLockedOk {E V : Type} (ds : JInt64 × JInt64)
    (body : RecM E Unit) (r r' : Rec)
    (h : body { r with depth := r.depth + 1 } = .ok () r') :
    lockedAll (recPrims (V := V) ds) (.plain ()) body r =
      .ok () { r' with depth := r'.depth - 1 } := by
  simpa only [lockedAll, lockIO, unlockIO, recPrims] using
    g8IoCoreFinallyOk
      (fun state : Rec => { state with depth := state.depth + 1 })
      (fun state : Rec => { state with depth := state.depth - 1 })
      body r r' h

theorem recLockedError {E V : Type} (ds : JInt64 × JInt64)
    (body : RecM E Unit) (r r' : Rec) (e : Error (StrIOError E))
    (h : body { r with depth := r.depth + 1 } = .error e r') :
    lockedAll (recPrims (V := V) ds) (.plain ()) body r =
      .error e { r' with depth := r'.depth - 1 } := by
  simpa only [lockedAll, lockIO, unlockIO, recPrims] using
    g8IoCoreFinallyError
      (fun state : Rec => { state with depth := state.depth + 1 })
      (fun state : Rec => { state with depth := state.depth - 1 })
      body r r' e h

theorem recForLoopAppends {E : Type} (xs : List (RecM E Unit))
    (bs : List (List UInt8)) (h : Forall2 Appends xs bs) (r : Rec) :
    (do for x in xs do x : RecM E Unit) r =
      .ok () { r with bytes := r.bytes ++ bs.flatten } := by
  exact g8IoCoreForLoopAppends
    (fun state : Rec => fun bytes => { state with bytes := state.bytes ++ bytes })
    (by intro state; cases state; simp only [List.append_nil])
    (by intro state left right; simp only [List.append_assoc])
    xs bs h r

theorem recForLoopThrows {E : Type} (pre post : List (RecM E Unit))
    (bs : List (List UInt8)) (bad : RecM E Unit) (e : Error (StrIOError E))
    (h : Forall2 Appends pre bs) (hb : ThrowsAt bad e) (r : Rec) :
    (do for x in pre ++ bad :: post do x : RecM E Unit) r =
      .error e { r with bytes := r.bytes ++ bs.flatten } := by
  exact g8IoCoreForLoopThrows
    (fun state : Rec => fun bytes => { state with bytes := state.bytes ++ bytes })
    (by intro state; cases state; simp only [List.append_nil])
    (by intro state left right; simp only [List.append_assoc])
    pre post bs bad e h hb r

theorem recPrintValuesAppends {E V : Type} (ds : JInt64 × JInt64)
    (xs : List (RecM E Unit)) (bs : List (List UInt8))
    (h : Forall2 Appends xs bs) (r : Rec) :
    printValues (recPrims (V := V) ds) (.plain ()) xs r =
      .ok () { r with bytes := r.bytes ++ bs.flatten } := by
  have hloop := recForLoopAppends xs bs h { r with depth := r.depth + 1 }
  have hlocked := recLockedOk (V := V) ds _ r _ hloop
  simpa only [printValues, Int.add_sub_cancel] using hlocked

theorem recForall2Append {α β : Type} (R : α → β → Prop)
    (xs xs' : List α) (ys ys' : List β)
    (h : Forall2 R xs ys) (h' : Forall2 R xs' ys') :
    Forall2 R (xs ++ xs') (ys ++ ys') := by
  exact g8IoCoreForall2Append R xs xs' ys ys' h h'


end JuliaLean.ChatGPT.Batch8.Group8

namespace JuliaLean.ChatGPT.Batch8.Group8
open JuliaLean JuliaLean.base JuliaLean.base.show JuliaLean.base.strings.io
open JuliaLean.Proofs.base.strings.io

 theorem g8IoByteList (bs : ByteArray) : bs.toList = bs.data.toList := by
  have loop : ∀ (i : Nat) (acc : List UInt8),
      ByteArray.toList.loop bs i acc = acc.reverse ++ bs.data.toList.drop i := by
    intro i acc
    fun_induction ByteArray.toList.loop bs i acc with
    | case1 i acc h ih =>
      rw [ih, List.reverse_cons, List.append_assoc]
      have hsize : i < bs.data.toList.length := h
      rw [List.drop_eq_getElem_cons hsize]
      simp only [List.singleton_append, Array.getElem_toList]
      congr 2
      cases bs with
      | mk data => exact getElem!_pos data i h
    | case2 i acc h =>
      have hsize : bs.data.toList.length ≤ i := Nat.le_of_not_gt h
      rw [List.drop_eq_nil_of_le hsize, List.append_nil]
  unfold ByteArray.toList
  rw [loop]
  rfl

 theorem g8IoLitSingleton (c : Char) :
    JuliaLean.base.show.lit (String.singleton c) = String.utf8EncodeChar c := by
  simp only [JuliaLean.base.show.lit, String.toUTF8_eq_toByteArray, g8IoByteList,
    String.toByteArray_singleton, List.utf8Encode_singleton, List.toList_data_toByteArray]

 theorem recNewlineAppends {E V : Type} (ds : JInt64 × JInt64) :
    Appends (printStr (recPrims (E := E) (V := V) ds) (.plain ()) "\n") [10] := by
  intro r
  have hnl : JuliaLean.base.show.lit "\n" = ([10] : List UInt8) := by
    change JuliaLean.base.show.lit (String.singleton '\n') = [10]
    rw [g8IoLitSingleton]
    rfl
  simp only [printStr, write, recPrims, modify, MonadState.modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, hnl]

 theorem ShowcovStringsPrintLocking_proven : JuliaLean.Proofs.base.strings.io.PrintLocking := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E V X ds showX x r r' h
    exact recLockedOk ds (showX (.plain ()) x) r r' h
  · intro E V X ds showX x r r' e h
    exact recLockedError ds (showX (.plain ()) x) r r' e h
  · intro E V ds xs bs r h
    refine ⟨recPrintValuesAppends (E := E) (V := V) ds xs bs h r, ?_⟩
    have hn : Forall2 Appends [printStr (recPrims (E := E) (V := V) ds) (.plain ()) "\n"] [[10]] := by
      refine ⟨rfl, ?_⟩
      intro p hp
      simp only [List.zip_cons_cons, List.zip_nil_left, List.mem_singleton] at hp
      subst p
      exact recNewlineAppends (E := E) (V := V) ds
    have ha := recForall2Append Appends xs _ bs _ h hn
    have hout := recPrintValuesAppends (E := E) (V := V) ds _ _ ha r
    simpa only [printlnValues, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc] using hout
  · intro E V ds pre post bs bad e r h hb
    have hloop := recForLoopThrows pre post bs bad e h hb { r with depth := r.depth + 1 }
    have hlocked := recLockedError (V := V) ds _ r _ e hloop
    simpa only [printValues, Int.add_sub_cancel] using hlocked

end JuliaLean.ChatGPT.Batch8.Group8

namespace JuliaLean.Proofs.base.strings.io
open JuliaLean.Registry
def entries : List Entry :=
  [ { id := "showcov-strings-print-locking", juliaFile := "base/strings/io.jl"
      juliaFns := ["print(::IO, x)", "print(::IO, xs...)", "println(::IO, xs...)"]
      statement := "Print writes shown values in order, returns nothing, propagates show failures, and restores the stream lock."
      source := "base/strings/io.jl:32-77", status := .proven, prop := ``PrintLocking, thm := some ``JuliaLean.ChatGPT.Batch8.Group8.ShowcovStringsPrintLocking_proven }
  , { id := "showcov-strings-sprint", juliaFile := "base/strings/io.jl"
      juliaFns := ["sprint(::Function, args...)", "repr(x)", "limitrepr(x)"]
      statement := "sprint captures the callback's stream writes and propagates its errors; repr uses show and limitrepr adds the limit context."
      source := "base/strings/io.jl:104-114,284-286", status := .todo, prop := ``SprintCapture, notes := "Prop permits byte lists beyond the native write-count domain; requires realizable length bound." }
  , { id := "showcov-strings-sizehint-output", juliaFile := "base/strings/io.jl"
      juliaFns := ["sprint(::Function, args...)", "_str_sizehint(x)", "print_to_string(xs...)"]
      statement := "Size hints are lower bounds for allocation; changing a hint leaves sprint and print_to_string output unchanged."
      source := "base/strings/io.jl:104-148", status := .todo, prop := ``SizeHintSpec, notes := "Prop permits callbacks that observe allocation, contradicting sizehint-independent output prose." }
  , { id := "showcov-strings-building", juliaFile := "base/strings/io.jl"
      juliaFns := ["string_with_env(env, xs...)", "string(xs...)", "string(::Symbol)"]
      statement := "String builders concatenate printed forms in order and propagate user show errors."
      source := "base/strings/io.jl:150-188", status := .todo, prop := ``StringBuilding, notes := "Prop quantifies over byte counts beyond the native string domain; requires realizable length bound." }
  , { id := "showcov-strings-writes", juliaFile := "base/strings/io.jl"
      juliaFns := ["print(::IO, ::AbstractString)", "write(::IO, ::AbstractString)", "write(::IO, ::Union{String,SubString{String}})", "print(::IO, ::Union{String,SubString{String}})"]
      statement := "Abstract strings print each character; writes append the complete bytes and return their byte count."
      source := "base/strings/io.jl:192-193,242-246", status := .todo, prop := ``StringWrites
      notes := "Prop covers recording-stream abstract writes and concrete prints only; prose also promises concrete write bytes and counts." }
  , { id := "showcov-strings-quoted", juliaFile := "base/strings/io.jl"
      juliaFns := ["show(::IO, ::AbstractString)", "print_quoted(::IO, ::AbstractString)"]
      statement := "String show encloses escaped content in double quotes and escapes quotes and interpolation markers."
      source := "base/strings/io.jl:194,491-495", status := .todo, prop := ``QuotedString, notes := "Needs escapeStringIO prefix invariance on Rec.bytes and lock-depth preservation, then composition with both quote writes; also needs the single quote/dollar IterYields calculation." }
  , { id := "showcov-strings-limited", juliaFile := "base/strings/io.jl"
      juliaFns := ["show(::IO, MIME\"text/plain\", ::AbstractString)", "skip_text(skip)"]
      statement := "Elided output appends the shown head, marker, and shown tail to any stream, within the display width."
      source := "base/strings/io.jl:197-236", status := .todo, prop := ``LimitedShow 
      notes := "Prop demands a strict rendered display-width bound beyond the source promise." }
  , { id := "showcov-strings-join", juliaFile := "base/strings/io.jl"
      juliaFns := ["join(::IO, iterator, delim, last)", "join(::IO, iterator, delim)", "_join_preserve_annotations(iterator, args...)", "_join_preserve_annotations(::Tuple, args...)", "join(iterator)", "join(iterator, delim)", "join(iterator, delim, last)"]
      statement := "join preserves iteration order, places delimiters between items, and uses last only for the final pair."
      source := "base/strings/io.jl:330-391", status := .todo, prop := ``JoinSpec
      notes := "Prop omits the annotation-preserving branch and permits outputs beyond the native string-size domain." }
  , { id := "show-escape-roundtrip-in-range", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "Default escape and unescape round-trip strings whose Unicode escapes stay within U+10FFFF, without a byte-length restriction."
      source := "base/strings/io.jl:400-457", status := .todo, prop := ``EscapeRoundTripInRange, notes := "Prop permits an escaped intermediate beyond the bounded JString carrier." }
  , { id := "show-escape-above-unicode", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "Default escape_string and unescape_string round-trip every String, including invalid UTF-8."
      source := "base/strings/io.jl:400-457 (escape_string docstring; invalid UTF-8 example)"
      status := .todo, prop := ``EscapeRoundTripAll
      notes := "The existing reproducer is not a Lean negation of EscapeRoundTripAll. A closed escapeDefault calculation on the out-of-Unicode witness still exceeds maxRecDepth 65536 with real dependencies; needs staged native IOBuffer write/takestring lemmas, then the unescape failure calculation." }
  , { id := "show-escape-valid-roundtrip", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "Default escaping and unescaping round-trip valid strings whose characters are within Unicode's code-point range."
      source := "base/strings/io.jl:400-457", status := .todo, prop := ``EscapeRoundTripValid, notes := "Prop permits an escaped intermediate beyond the bounded JString carrier." }
  , { id := "show-escape-ascii-output", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString; ascii=true)"]
      statement := "With ASCII esc and keep sets, ascii=true emits only ASCII bytes for either fullhex value."
      source := "base/strings/io.jl:418-419", status := .todo, prop := ``EscapeOptions, notes := "Registry prose promises ASCII output; Prop additionally requires the full composite EscapeOptions contract." }
  , { id := "showcov-strings-escape-helpers", juliaFile := "base/strings/io.jl"
      juliaFns := ["need_full_hex(::Union{Nothing,AbstractChar})", "escape_nul(::Union{Nothing,AbstractChar})", "escape_string(::IO, ::AbstractString)"]
      statement := "Non-printable non-ASCII characters are escaped; printable ones stay literal unless ascii=true, while esc, keep, and fullhex follow source order."
      source := "base/strings/io.jl:395-397,459-486", status := .todo, prop := ``EscapeOptions, notes := "Composite Prop requires u0041 for packed custom character 0x41800000; source selects x-escape." }
  , { id := "showcov-strings-unescape-spec", juliaFile := "base/strings/io.jl"
      juliaFns := ["unescape_string(::IO, ::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "unescape_string decodes kept pairs, standard escapes, hex bytes, Unicode escapes, and octal bytes."
      source := "base/strings/io.jl:500-593", status := .todo, prop := ``UnescapeOptions, notes := "Needs scanner proofs from IterYields for kept, standard, hex, Unicode and octal branches, composed with the installed IOBuffer's write and takestring results; no complete branch-to-buffer proof is present." }
  , { id := "showcov-strings-b-string-codeunits", juliaFile := "base/strings/io.jl"
      juliaFns := ["b_str(::String)"]
      statement := "The String-only byte-string macro returns a CodeUnits vector containing exactly the unescaped bytes."
      source := "base/strings/io.jl:613-616", status := .proven, prop := ``ByteStringMacro, thm := some ``JuliaLean.ChatGPT.Batch4.Group19.ShowcovStringsBStringCodeunits_proven }
  , { id := "showcov-strings-raw-escape", juliaFile := "base/strings/io.jl"
      juliaFns := ["raw_str(s)", "escape_raw_string(::IO, ::AbstractString, ::Char)", "escape_raw_string(::AbstractString, ::Char)"]
      statement := "Raw-string escaping doubles backslashes before delimiters and at the end, while raw_str returns its input."
      source := "base/strings/io.jl:643-697", status := .todo, prop := ``RawStringSpec, notes := "Prop uses a positive mathematical inserted count where source branches on an Int64-wrapped count." }
  , { id := "showcov-strings-char-vectors", juliaFile := "base/strings/io.jl"
      juliaFns := ["String(::AbstractVector{Char})", "String(::AbstractVector{<:AbstractChar})", "AnnotatedString(::AbstractVector{<:AbstractChar})"]
      statement := "Character-vector constructors preserve character order and byte-counted annotation regions."
      source := "base/strings/io.jl:805-847", status := .todo, prop := ``CharacterVectors, notes := "Prop omits native byte-count bounds for finite character lists." }
  , { id := "memsafety-strings-io-wrap", juliaFile := "base/strings/io.jl"
      juliaFns := ["IOBuffer(::String)", "IOBuffer(::SubString{String})"]
      statement := "String IOBuffer views wrap the parent bytes as read-only; SubString views use their stored byte offset and length."
      source := "base/strings/io.jl:288-307", status := .todo, prop := ``StringIOViews, notes := "Prop requires constructor offset one; installed adapter passes zero for one-based memory-reference semantics." }
  ]

end JuliaLean.Proofs.base.strings.io
