import JuliaLean.base.strings.io
import JuliaLean.Registry.Types

/-!
# Properties of `base/strings/io.jl`

These statements specify observable text, byte writes, string transformations, and stream views.
`IOOps` holds typed operations from other Base files and their documented buffer laws.
-/

namespace JuliaLean.Proofs.base.strings.io

open JuliaLean.base.strings.io JuliaLean.Registry

def printForm {C E X : Type} (ops : IOOps C E) (context : List (String × String)) :
    PrintArg C X → List UInt8
  | .char c => ops.printCharBytes c
  | .string bytes => bytes
  | .value x => ops.showBytes context x

def printForms {C E X : Type} (ops : IOOps C E) (context : List (String × String))
    (args : List (PrintArg C X)) : List UInt8 :=
  (args.map (printForm ops context)).flatten

def joinBytes (delim : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | first :: rest => rest.foldl (fun out item => out ++ delim ++ item) first

def joinBytesLast (delim last : List UInt8) : List (List UInt8) → List UInt8
  | [] => []
  | [x] => x
  | x :: y :: [] => x ++ last ++ y
  | x :: y :: rest => x ++ delim ++ joinBytesLast delim last (y :: rest)

def contextBuffer {C E : Type} (ops : IOOps C E) (io : IOBuffer) : Context → IOBuffer
  | .none => io
  | .pair key value => ops.contextPair io key value
  | .tuple pairs => ops.contextTuple io pairs
  | .io parent => ops.contextIO io parent

def expectedJoin3 {C E X : Type} (ops : IOOps C E) (context : List (String × String))
    (items : List X) (delim : X) : List UInt8 :=
  joinBytes (ops.showBytes context delim) (items.map (ops.showBytes context))

def expectedJoin4 {C E X : Type} (ops : IOOps C E) (context : List (String × String))
    (items : List X) (delim last : X) : List UInt8 :=
  joinBytesLast (ops.showBytes context delim) (ops.showBytes context last)
    (items.map (ops.showBytes context))

def expectedJoinParams {C E X : Type} (ops : IOOps C E)
    (context : List (String × String)) (items : List X) :
    JoinParams X → List UInt8
  | .none => joinBytes [] (items.map (ops.showBytes context))
  | .delim delim => expectedJoin3 ops context items delim
  | .delimLast delim last => expectedJoin4 ops context items delim last

def expectedAnnotations {C E : Type} (ops : IOOps C E) : Nat → List C → List RegionAnnotation
  | _, [] => []
  | point, c :: rest =>
      let current := if ops.isAnnotatedChar c then
        (ops.charAnnotations c).map (fun annotation => ⟨point, point, annotation⟩)
        else []
      current ++ expectedAnnotations ops (point + ops.utf8Size c) rest

def indentationSpecValue {C E : Type} (ops : IOOps C E) (tabwidth : Int) :
    Int → List C → Except E (Int × Bool)
  | count, [] => .ok (count, true)
  | count, c :: rest =>
      if ops.charCode c = 32 then
        indentationSpecValue ops tabwidth (count + 1) rest
      else if ops.charCode c = 9 then do
        let quotient ← ops.integerDiv (count + tabwidth) tabwidth
        indentationSpecValue ops tabwidth (quotient * tabwidth) rest
      else
        .ok (count, false)

def indentationSpaces {C E : Type} (ops : IOOps C E) (columns : Int) : List UInt8 :=
  (List.replicate columns.toNat (ops.printCharBytes (ops.fromAscii 32))).flatten

def unindentSpecLoop {C E : Type} (ops : IOOps C E) (indent tabwidth : Int)
    (cutting : Bool) (column : Int) : List C → Except E (List UInt8)
  | [] => .ok (if cutting then indentationSpaces ops (column - indent) else [])
  | c :: rest => do
      if cutting then
        if ops.charCode c = 32 then
          unindentSpecLoop ops indent tabwidth true (column + 1) rest
        else if ops.charCode c = 9 then
          let quotient ← ops.integerDiv (column + tabwidth) tabwidth
          unindentSpecLoop ops indent tabwidth true (quotient * tabwidth) rest
        else if ops.charCode c = 10 then
          let tail ← unindentSpecLoop ops indent tabwidth true 0 rest
          pure (indentationSpaces ops (column - indent) ++ ops.printCharBytes c ++ tail)
        else
          let tail ← unindentSpecLoop ops indent tabwidth false (column + 1) rest
          pure (indentationSpaces ops (column - indent) ++ ops.printCharBytes c ++ tail)
      else if ops.charCode c = 9 then
        let quotient ← ops.integerDiv (column + tabwidth) tabwidth
        let updated := quotient * tabwidth
        let tail ← unindentSpecLoop ops indent tabwidth false updated rest
        pure (indentationSpaces ops (updated - column) ++ tail)
      else if ops.charCode c = 10 then
        let tail ← unindentSpecLoop ops indent tabwidth true 0 rest
        pure (ops.printCharBytes c ++ tail)
      else
        let tail ← unindentSpecLoop ops indent tabwidth false (column + 1) rest
        pure (ops.printCharBytes c ++ tail)

def unindentSpec {C E S : Type} (ops : IOOps C E) (s : S) (indent tabwidth : Int) :
    Except E (Unindented S) := do
  if indent = 0 then return .original s
  return .built (← unindentSpecLoop ops indent tabwidth true 0 (ops.chars s))
/-- Print keeps stream order and propagates user show errors while restoring the lock. -/
def PrintLocking : Prop :=
  (∀ {C E X : Type} (ops : IOOps C E) (io : IOBuffer) (x : X)
      (written : IOBuffer) (result : Except E Unit),
    printOne ops io x = (written, result) →
      written.lockDepth = io.lockDepth ∧
      (result = .ok () → written.bytes = io.bytes ++ ops.showBytes io.context x) ∧
      (∀ e shown, ops.showOne (ops.lock io) x = (shown, .error e) →
        printOne ops io x = (ops.unlock shown, .error e))) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (io out : IOBuffer)
      (args : List (PrintArg C X)) (res : Except E Unit),
    printArgs ops io args = (out, res) →
      out.lockDepth = io.lockDepth ∧
      (res = .ok () → out.bytes = io.bytes ++ printForms ops io.context args)) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (io : IOBuffer) (x : X)
      (shown : IOBuffer) (e : E),
    ops.showOne (ops.lock io) x = (shown, .error e) →
      (printArgs ops io [.value x]).2 = .error e ∧
      (printArgs ops io [.value x]).1.lockDepth = io.lockDepth) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (io out : IOBuffer)
      (args : List (PrintArg C X)) (res : Except E Unit),
    println ops io args = (out, res) →
      out.lockDepth = io.lockDepth ∧
      (res = .ok () → out.bytes = io.bytes ++ printForms ops io.context args ++ [10]))

/-- `sprint` captures callback writes; its size hint does not change output bytes. -/
def SprintCapture : Prop :=
  (∀ {C E X I R : Type} (ops : IOOps C E)
      (f : IOBuffer → List X → Except E (IOBuffer × R)) (args : List X)
      (ctx : Context) (hint : I) (out : List UInt8) (written : IOBuffer) (result : R),
    f (contextBuffer ops (ops.newBuffer hint) ctx) args = .ok (written, result) →
      sprint ops f args ctx hint = .ok out → out = written.bytes) ∧
  (∀ {C E X I R : Type} (ops : IOOps C E)
      (f : IOBuffer → List X → Except E (IOBuffer × R)) (args : List X)
      (ctx : Context) (hint : I) (e : E),
    f (contextBuffer ops (ops.newBuffer hint) ctx) args = .error e →
      sprint ops f args ctx hint = .error e) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (x : X) (ctx : Context) out,
    repr ops x ctx = .ok out →
      out = ops.showBytes (contextBuffer ops (ops.newBuffer (0 : Nat)) ctx).context x) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (x : X) (ctx : Context)
      (shown : IOBuffer) (e : E),
    ops.showOne (contextBuffer ops (ops.newBuffer (0 : Nat)) ctx) x =
        (shown, .error e) →
      repr ops x ctx = .error e) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (x : X) out,
    limitrepr ops x = .ok out →
      out = ops.showBytes (ops.contextPair (ops.newBuffer (0 : Nat))
        "limit" "true").context x) ∧
  (∀ {C E X : Type} (ops : IOOps C E) (x : X) (shown : IOBuffer) (e : E),
    ops.showOne (ops.contextPair (ops.newBuffer (0 : Nat)) "limit" "true") x =
        (shown, .error e) →
      limitrepr ops x = .error e)

/-- String builders concatenate shown arguments and propagate show failures. -/
def StringBuilding : Prop :=
  ∀ {C E X Env : Type} (ops : IOOps C E) (args : List (PrintArg C X))
    (env : Env) (symbol : JuliaSymbol),
    (∀ out, string ops args = .ok out → out = printForms ops [] args) ∧
    (∀ out, stringWithEnv ops env args = .ok out →
      out = printForms ops (ops.environmentProperties env) args) ∧
    (∀ e, printToString ops args = .error e → string ops args = .error e) ∧
    (∀ e, string ops args = .error e → printToString ops args = .error e) ∧
    stringWithEnv (X := Unit) ops env [] = .ok [] ∧
    stringSymbol ops symbol = symbol.name ∧
    (∀ (x : X) shown e, ops.showOne
        (ops.lock (ops.newBuffer (printArgSizehint ops (.value x)))) x =
          (shown, .error e) →
        printToString ops [.value x] = .error e ∧ string ops [.value x] = .error e) ∧
    (∀ (x : X) shown e, ops.showOne
        (ops.lock (ops.contextEnv
          (ops.newBuffer (printArgSizehint ops (.value x))) env)) x =
          (shown, .error e) →
        stringWithEnv ops env [.value x] = .error e)

/-- String size hints affect allocation only; the resulting printed bytes are unchanged. -/
def SizeHintSpec : Prop :=
  (∀ {C E X : Type} (ops : IOOps C E) (args : List (PrintArg C X)) out,
    printToString ops args = .ok out → out = printForms ops [] args) ∧
  (∀ {C E X I J R : Type} (ops : IOOps C E)
      (f : IOBuffer → List X → Except E (IOBuffer × R)) (args : List X)
      (ctx : Context) (hint₁ : I) (hint₂ : J) (out₁ out₂ : List UInt8),
    sprint ops f args ctx hint₁ = .ok out₁ →
    sprint ops f args ctx hint₂ = .ok out₂ → out₁ = out₂)


/-- Abstract strings print each character; writes append bytes and return their total byte count. -/
def StringWrites : Prop :=
  ∀ {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S)
    (printed written : IOBuffer) (count : Int),
    printAbstractString ops io s = .ok printed →
      printed.bytes = io.bytes ++ (ops.chars s).flatMap ops.printCharBytes ∧
    writeAbstractString ops io s = .ok (written, count) →
      written.bytes = io.bytes ++ (ops.chars s).flatMap ops.charBytes ∧
      count = Int.ofNat ((ops.chars s).flatMap ops.charBytes).length ∧
    (∀ {T : Type} (str : T) (out : IOBuffer) (n : Int),
      writeConcreteString ops io str .default = .ok (out, n) →
        out.bytes = io.bytes ++ ops.stringBytes str ∧ n = Int.ofNat (ops.sizeof str)) ∧
    (∀ bytes out, printString ops io bytes = .ok out → out.bytes = io.bytes ++ bytes)

/-- String show encloses the escaped content in quotes. -/
def QuotedString : Prop :=
  ∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (escaped : List UInt8),
    escapeString ops s [ops.fromAscii 34, ops.fromAscii 36] ([] : List C) false false =
      .ok escaped →
    showAbstractString ops io s = .ok out →
      out.bytes = io.bytes ++ ops.printCharBytes (ops.fromAscii 34) ++ escaped ++
        ops.printCharBytes (ops.fromAscii 34)

structure ElisionData where
  head : Nat
  tail : Nat
  afterHead : Nat
  skipped : Int
  replacement : List UInt8

def elisionData {C E S : Type} (ops : IOOps C E) (s : S) (limit : Int) : ElisionData :=
  let clippedLimit := max 0 (limit - 2)
  let units := if ops.codeunitIsUInt8 s then [98, 121, 116, 101, 115]
    else [99, 111, 100, 101, 32, 117, 110, 105, 116, 115]
  let maxReplacement := skipText ops units (Int.ofNat (ops.ncodeunits s * 100))
  let (head, tail) := ops.truncateBoundaries s clippedLimit.toNat maxReplacement
  let afterHead := ops.nextind s head
  let skipped := Int.ofNat tail - Int.ofNat afterHead
  ⟨head, tail, afterHead, skipped, skipText ops units skipped⟩

def elisionWorthwhile {C E S : Type} (ops : IOOps C E) (s : S) (d : ElisionData) : Prop :=
  let t := Int.ofNat d.replacement.length
  4 * t ≤ d.skipped ∨
    t ≤ d.skipped ∧
      t ≤ Int.ofNat (ops.textwidth s d.afterHead (ops.prevind s d.tail))


def LimitedShow : Prop :=
  (∀ {C E : Type} (ops : IOOps C E) (units : List UInt8) (skip : Int),
    skipText ops units skip =
      [32, 0xe2, 0x8b, 0xaf, 32] ++ ops.decimalBytes skip ++ [32] ++ units ++
        [32, 0xe2, 0x8b, 0xaf, 32]) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S) (limit : Int)
      (out : IOBuffer),
    showTextPlain ops io s (some limit) = .ok out →
      let appended := out.bytes.drop io.bytes.length
      out.bytes = io.bytes ++ appended ∧
      (ops.checkTextWidth s (max 0 (limit - 2)).toNat = true →
        ∀ full, showAbstractString ops io s = .ok full → out = full) ∧
      (ops.checkTextWidth s (max 0 (limit - 2)).toNat = false →
        elisionWorthwhile ops s (elisionData ops s limit) →
          ∀ headOut tailOut,
            showAbstractString ops {io with bytes := []}
              (ops.slice s 1 (elisionData ops s limit).head) = .ok headOut →
            showAbstractString ops {io with bytes := []}
              (ops.slice s (elisionData ops s limit).tail (ops.lastindex s)) = .ok tailOut →
            ∃ before after,
              appended = headOut.bytes ++ before ++
                (elisionData ops s limit).replacement ++ after ++ tailOut.bytes ∧
              ops.displayCols {out with bytes := appended} ≤ (max 2 limit).toNat) ∧
      (ops.checkTextWidth s (max 0 (limit - 2)).toNat = true →
        ∀ e, showAbstractString ops io s = .error e →
          showTextPlain ops io s (some limit) = .error e))

/-- `join` preserves order, writes each requested separator, and keeps its output bytes. -/
def JoinSpec : Prop :=
  ∀ {C E I X : Type} (ops : IOOps C E) (io out : IOBuffer) (it : I)
    (items : List X) (delim last : X) (params : JoinParams X),
    ops.iteratorItems it = items →
    (joinIO3 ops io it delim = .ok out →
      out.bytes = io.bytes ++ expectedJoin3 ops io.context items delim) ∧
    (joinIO4 ops io it delim last = .ok out →
      out.bytes = io.bytes ++ expectedJoin4 ops io.context items delim last) ∧
    (∀ result, joinWithDelim ops it delim = .ok result →
      result.bytes = expectedJoin3 ops io.context items delim) ∧
    (∀ result, joinWithLast ops it delim last = .ok result →
      result.bytes = expectedJoin4 ops io.context items delim last) ∧
    (∀ result, joinPreserve ops it params = .ok result →
      result.bytes = expectedJoinParams ops io.context items params) ∧
    (∀ result, join (X := X) ops it = .ok result →
      result.bytes = expectedJoinParams ops io.context items .none)
/-- Default escape/unescape round-trips when every Unicode escape is in its documented range. -/
def EscapeRoundTripInRange : Prop :=
  ∀ {C E S : Type} (ops : IOOps C E) (s : S),
    (∀ c ∈ ops.chars s,
      ops.isOverlong c = true ∨ ops.isMalformed c = true ∨ ops.charCode c ≤ 0x10ffff) →
    ∃ escaped, escapeStringDefault ops s = .ok escaped ∧
      unescapeStringDefault ops (⟨escaped⟩ : JuliaString) = .ok (ops.stringBytes s)

/-- Default escaping and unescaping round-trip valid strings within Unicode's code-point range. -/
def EscapeRoundTripValid : Prop :=
  ∀ {C E S : Type} (ops : IOOps C E) (s : S),
    ops.stringValid s = true →
    (∀ c ∈ ops.chars s,
      ops.isOverlong c = true ∨ ops.isMalformed c = true ∨ ops.charCode c ≤ 0x10ffff) →
    ∃ escaped, escapeStringDefault ops s = .ok escaped ∧
      unescapeStringDefault ops (⟨escaped⟩ : JuliaString) = .ok (ops.stringBytes s)

/-- Default escaping and unescaping round-trip every string, including invalid UTF-8. -/
def EscapeRoundTripAll : Prop :=
  ∀ {C E : Type} (ops : IOOps C E) (s : JuliaString),
    ∃ escaped, escapeStringDefault ops s = .ok escaped ∧
      unescapeStringDefault ops (⟨escaped⟩ : JuliaString) = .ok s.bytes

/-- Printable non-ASCII characters stay literal; ASCII, keep, esc, and fullhex follow source order. -/
def EscapeOptions : Prop :=
  (∀ {C E S Q K : Type} (ops : IOOps C E) (s : S) (esc : Q) (keep : K)
      (fullhex : Bool) (r : List UInt8),
    (∀ c, ops.contains esc c = true → ops.isAscii c = true) →
    (∀ c, ops.contains keep c = true → ops.isAscii c = true) →
    escapeString ops s esc keep true fullhex = .ok r →
      ∀ b ∈ r, b.toNat < 0x80) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c : C) (fullhex : Bool)
      (r : List UInt8),
    ops.chars s = [c] → ops.contains ([] : List C) c = false →
    ops.contains [c] c = true →
    escapeString ops s ([] : List C) [c] true fullhex = .ok r →
      r = ops.printCharBytes c) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c : C) (r : List UInt8),
    ops.chars s = [c] → ops.contains [c] c = true →
    escapeString ops s [c] [c] false false = .ok r →
      r = ops.printCharBytes (ops.fromAscii 92) ++ ops.printCharBytes c) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c : C) (ascii : Bool)
      (r : List UInt8),
    ops.chars s = [c] → ops.contains ([] : List C) c = false →
    ops.isAscii c = false → ops.isOverlong c = false →
    ops.isMalformed c = false → ops.charCode c ≤ 0xffff →
    (ascii = true ∨ ops.isPrint c = false) →
    escapeString ops s ([] : List C) ([] : List C) ascii true = .ok r →
      r = [92, 117] ++ ops.hexString (ops.charCode c) 4) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c : C) (ascii : Bool)
      (r : List UInt8),
    ops.chars s = [c] → ops.contains ([] : List C) c = false →
    ops.isAscii c = false → ops.isOverlong c = false →
    ops.isMalformed c = false → 0x10000 ≤ ops.charCode c →
    ops.charCode c ≤ 0x10ffff →
    (ascii = true ∨ ops.isPrint c = false) →
    escapeString ops s ([] : List C) ([] : List C) ascii true = .ok r →
      r = [92, 85] ++ ops.hexString (ops.charCode c) 8) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c next : C) (r : List UInt8),
    ops.chars s = [c, next] → ops.contains ([] : List C) c = false →
    ops.isAscii c = false → ops.isOverlong c = false →
    ops.isMalformed c = false → 0x80 ≤ ops.charCode c →
    ops.charCode c ≤ 0xffff →
    escapeString ops s ([] : List C) ([] : List C) true false = .ok r →
    ∃ rest, r = [92, 117] ++
      ops.hexString (ops.charCode c) (if ops.isHexDigit next then 4 else 2) ++ rest) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c next : C) (r : List UInt8),
    ops.chars s = [c, next] → ops.contains ([] : List C) c = false →
    ops.isAscii c = false → ops.isOverlong c = false →
    ops.isMalformed c = false → 0x10000 ≤ ops.charCode c →
    ops.charCode c ≤ 0x10ffff →
    escapeString ops s ([] : List C) ([] : List C) true false = .ok r →
    ∃ rest, r = [92, 85] ++
      ops.hexString (ops.charCode c) (if ops.isHexDigit next then 8 else 4) ++ rest) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (s : S) (c : C) (r : List UInt8),
    ops.chars s = [c] → ops.isAscii c = false →
    ops.isOverlong c = false → ops.isMalformed c = false →
    ops.isPrint c = true →
    escapeString ops s ([] : List C) ([] : List C) false false = .ok r →
      r = ops.printCharBytes c) ∧
  (∀ {C E : Type} (ops : IOOps C E) (c : Option C),
    needFullHex ops c = c.elim false ops.isHexDigit ∧
    escapeNul ops c = if c.elim false (fun x => 48 ≤ ops.charCode x && ops.charCode x ≤ 55)
      then [92, 120, 48, 48] else [92, 48])

def simpleEscapeValue (code : Nat) : Option Nat :=
  if code = 97 then some 7 else if code = 98 then some 8 else
  if code = 116 then some 9 else if code = 110 then some 10 else
  if code = 118 then some 11 else if code = 102 then some 12 else
  if code = 114 then some 13 else if code = 101 then some 27 else
  if code = 92 || code = 34 then some code else none

/-- Kept pairs remain literal; C, hex, Unicode, and octal escapes decode as documented. -/
def UnescapeOptions : Prop :=
  (∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (c : C),
    ops.chars s = [ops.fromAscii 92, c] → ops.contains [c] c = true →
    unescapeStringIO ops io s [c] = .ok out →
      out.bytes = io.bytes ++ ops.printCharBytes (ops.fromAscii 92) ++ ops.printCharBytes c) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (digit : Nat),
    digit < 16 → ops.chars s = [ops.fromAscii 92, ops.fromAscii 120,
      ops.fromAscii (if digit < 10 then 48 + digit else 87 + digit)] →
    unescapeStringIO ops io s ([] : List C) = .ok out →
      out.bytes = io.bytes ++ [digit.toUInt8]) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (code : Nat),
    simpleEscapeValue code = some (if code = 92 || code = 34 then code else
      if code = 97 then 7 else if code = 98 then 8 else if code = 116 then 9 else
      if code = 110 then 10 else if code = 118 then 11 else if code = 102 then 12 else
      if code = 114 then 13 else 27) →
    ops.chars s = [ops.fromAscii 92, ops.fromAscii code] →
    unescapeStringIO ops io s ([] : List C) = .ok out →
      out.bytes = io.bytes ++ ops.printCharBytes
        (ops.fromAscii (if code = 92 || code = 34 then code else
          if code = 97 then 7 else if code = 98 then 8 else if code = 116 then 9 else
          if code = 110 then 10 else if code = 118 then 11 else if code = 102 then 12 else
          if code = 114 then 13 else 27))) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (digit : Nat),
    digit < 8 → ops.chars s = [ops.fromAscii 92, ops.fromAscii (48 + digit)] →
    unescapeStringIO ops io s ([] : List C) = .ok out →
      out.bytes = io.bytes ++ [digit.toUInt8]) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (digit : Nat),
    digit < 16 → ops.chars s = [ops.fromAscii 92, ops.fromAscii 117,
      ops.fromAscii (if digit < 10 then 48 + digit else 87 + digit)] →
    unescapeStringIO ops io s ([] : List C) = .ok out →
      out.bytes = io.bytes ++ ops.printCharBytes (ops.fromAscii digit)) ∧
  (∀ {C E S : Type} (ops : IOOps C E) (io out : IOBuffer) (s : S) (digit : Nat),
    digit < 16 → ops.chars s = [ops.fromAscii 92, ops.fromAscii 85,
      ops.fromAscii (if digit < 10 then 48 + digit else 87 + digit)] →
    unescapeStringIO ops io s ([] : List C) = .ok out →
      out.bytes = io.bytes ++ ops.printCharBytes (ops.fromAscii digit))

def rawEscapeChars {C E : Type} (ops : IOOps C E) (delim : C) :
    Nat → List C → List C
  | escapes, [] => List.replicate escapes (ops.fromAscii 92)
  | escapes, c :: rest =>
      if ops.charCode c = 92 then rawEscapeChars ops delim (escapes + 1) rest
      else
        List.replicate (escapes + if ops.equalChar c delim then 1 else 0)
          (ops.fromAscii 92) ++ [c] ++ rawEscapeChars ops delim 0 rest

def RawStringSpec : Prop :=
  ∀ {C E S : Type} (ops : IOOps C E) (s : S) (delim : C),
    let expected := rawEscapeChars ops delim 0 (ops.chars s)
    let added := expected.length - (ops.chars s).length
    (∀ io out n, escapeRawStringIO ops io s delim = .ok (out, n) →
      out.bytes = io.bytes ++ expected.flatMap ops.charBytes ∧ n = added) ∧
    (added = 0 → escapeRawString ops s delim =
      .ok (RawStringResult.original s)) ∧
    (0 < added → escapeRawString ops s delim =
      .ok (RawStringResult.copied (expected.flatMap ops.charBytes))) ∧
    rawStr s = s

def IndentationSpec : Prop :=
  (∀ {C E S I : Type} (ops : IOOps C E) (s : S) (tabwidth : I),
    indentation ops s tabwidth =
      indentationSpecValue ops (ops.integerValue tabwidth) 0 (ops.chars s)) ∧
  (∀ {C E S I : Type} (ops : IOOps C E) (s : S) (indent : Int) (tabwidth : I),
    (∀ result, unindent ops s indent tabwidth = .ok result →
      unindentSpec ops s indent (ops.integerValue tabwidth) = .ok result) ∧
    (∀ e, unindentSpec ops s indent (ops.integerValue tabwidth) = .error e →
      unindent ops s indent tabwidth = .error e))

/-- Character-vector constructors preserve order, byte lengths, and annotation positions. -/
def CharacterVectors : Prop :=
  ∀ {C E V : Type} (ops : IOOps C E) (v : V),
    stringCharArray ops v = (ops.arrayChars v).flatMap ops.charBytes ∧
    (∀ out, stringAbstractCharArray ops v = .ok out →
      out = (ops.arrayChars v).flatMap ops.printCharBytes) ∧
    (∀ out, annotatedString ops v = .ok out →
      out.annotations = expectedAnnotations ops 1 (ops.arrayChars v) ∧
      out.bytes = if ops.annotatedType then
        (ops.arrayChars (ops.unwrappedChars v)).flatMap ops.charBytes
      else (ops.arrayChars v).flatMap ops.printCharBytes)

/-- String IO views expose their byte spans as read-only. -/
def StringIOViews : Prop :=
  ∀ {C E : Type} (ops : IOOps C E) (s : JuliaString) (sub : JuliaSubString),
    let full := ioBufferString ops s
    full.parent = s.bytes ∧ full.first = 1 ∧ full.length = s.bytes.length ∧
    full.writable = false ∧
    (sub.offset + sub.byteCount ≤ sub.string.bytes.length →
      let view := ioBufferSubString ops sub
      view.parent = sub.string.bytes ∧ view.first = sub.offset + 1 ∧
        view.length = sub.byteCount ∧ view.writable = false)

def ByteStringMacro : Prop :=
  ∀ {C E : Type} (ops : IOOps C E) (s : JuliaString),
    (∀ bytes, unescapeStringDefault ops s = .ok bytes →
      bStr ops s = .ok ⟨⟨bytes⟩⟩) ∧
    (∀ e, unescapeStringDefault ops s = .error e → bStr ops s = .error e)

/-! ## Registry entries -/

def entries : List Entry :=
  [ { id := "showcov-strings-print-locking", juliaFile := "base/strings/io.jl"
      juliaFns := ["print(::IO, x)", "print(::IO, xs...)", "println(::IO, xs...)"]
      statement := "Print writes shown values in order, returns nothing, propagates show failures, and restores the stream lock."
      source := "base/strings/io.jl:32-77", status := .todo, prop := ``PrintLocking }
  , { id := "showcov-strings-sprint", juliaFile := "base/strings/io.jl"
      juliaFns := ["sprint(::Function, args...)", "repr(x)", "limitrepr(x)"]
      statement := "sprint captures the callback's stream writes and propagates its errors; repr uses show and limitrepr adds the limit context."
      source := "base/strings/io.jl:104-114,284-286", status := .todo, prop := ``SprintCapture }
  , { id := "showcov-strings-sizehint-output", juliaFile := "base/strings/io.jl"
      juliaFns := ["sprint(::Function, args...)", "_str_sizehint(x)", "print_to_string(xs...)"]
      statement := "Size hints are lower bounds for allocation; changing a hint leaves sprint and print_to_string output unchanged."
      source := "base/strings/io.jl:104-148", status := .todo, prop := ``SizeHintSpec }
  , { id := "showcov-strings-building", juliaFile := "base/strings/io.jl"
      juliaFns := ["string_with_env(env, xs...)", "string(xs...)", "string(::Symbol)"]
      statement := "String builders concatenate printed forms in order and propagate user show errors."
      source := "base/strings/io.jl:150-188", status := .todo, prop := ``StringBuilding }
  , { id := "showcov-strings-writes", juliaFile := "base/strings/io.jl"
      juliaFns := ["print(::IO, ::AbstractString)", "write(::IO, ::AbstractString)", "write(::IO, ::Union{String,SubString{String}})", "print(::IO, ::Union{String,SubString{String}})"]
      statement := "Abstract strings print each character; writes append the complete bytes and return their byte count."
      source := "base/strings/io.jl:192-193,242-246", status := .todo, prop := ``StringWrites }
  , { id := "showcov-strings-quoted", juliaFile := "base/strings/io.jl"
      juliaFns := ["show(::IO, ::AbstractString)", "print_quoted(::IO, ::AbstractString)"]
      statement := "String show encloses escaped content in double quotes and escapes quotes and interpolation markers."
      source := "base/strings/io.jl:194,491-495", status := .todo, prop := ``QuotedString }
  , { id := "showcov-strings-limited", juliaFile := "base/strings/io.jl"
      juliaFns := ["show(::IO, MIME\"text/plain\", ::AbstractString)", "skip_text(skip)"]
      statement := "Elided output appends the shown head, marker, and shown tail to any stream, within the display width."
      source := "base/strings/io.jl:197-236", status := .todo, prop := ``LimitedShow }
  , { id := "showcov-strings-join", juliaFile := "base/strings/io.jl"
      juliaFns := ["join(::IO, iterator, delim, last)", "join(::IO, iterator, delim)", "_join_preserve_annotations(iterator, args...)", "_join_preserve_annotations(::Tuple, args...)", "join(iterator)", "join(iterator, delim)", "join(iterator, delim, last)"]
      statement := "join preserves iteration order, places delimiters between items, and uses last only for the final pair."
      source := "base/strings/io.jl:330-391", status := .todo, prop := ``JoinSpec }
  , { id := "show-escape-roundtrip-in-range", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "Default escape and unescape round-trip strings whose Unicode escapes stay within U+10FFFF, without a byte-length restriction."
      source := "base/strings/io.jl:400-457", status := .todo, prop := ``EscapeRoundTripInRange }
  , { id := "show-escape-above-unicode", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "Default escape_string and unescape_string round-trip every String, including invalid UTF-8."
      source := "base/strings/io.jl:400-457 (escape_string docstring; invalid UTF-8 example)"
      status := .todo, prop := ``EscapeRoundTripAll
      notes := "repro/show-escape-above-unicode.jl prints REPRODUCED on target Julia." }
  , { id := "show-escape-valid-roundtrip", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "Default escaping and unescaping round-trip valid strings whose characters are within Unicode's code-point range."
      source := "base/strings/io.jl:400-457", status := .todo, prop := ``EscapeRoundTripValid }
  , { id := "show-escape-ascii-output", juliaFile := "base/strings/io.jl"
      juliaFns := ["escape_string(::AbstractString; ascii=true)"]
      statement := "With ASCII esc and keep sets, ascii=true emits only ASCII bytes for either fullhex value."
      source := "base/strings/io.jl:418-419", status := .todo, prop := ``EscapeOptions }
  , { id := "showcov-strings-escape-helpers", juliaFile := "base/strings/io.jl"
      juliaFns := ["need_full_hex(::Union{Nothing,AbstractChar})", "escape_nul(::Union{Nothing,AbstractChar})", "escape_string(::IO, ::AbstractString)"]
      statement := "Non-printable non-ASCII characters are escaped; printable ones stay literal unless ascii=true, while esc, keep, and fullhex follow source order."
      source := "base/strings/io.jl:395-397,459-486", status := .todo, prop := ``EscapeOptions }
  , { id := "showcov-strings-unescape-spec", juliaFile := "base/strings/io.jl"
      juliaFns := ["unescape_string(::IO, ::AbstractString)", "unescape_string(::AbstractString)"]
      statement := "unescape_string decodes kept pairs, standard escapes, hex bytes, Unicode escapes, and octal bytes."
      source := "base/strings/io.jl:500-593", status := .todo, prop := ``UnescapeOptions }
  , { id := "showcov-strings-b-string-codeunits", juliaFile := "base/strings/io.jl"
      juliaFns := ["b_str(::String)"]
      statement := "The String-only byte-string macro returns a CodeUnits vector containing exactly the unescaped bytes."
      source := "base/strings/io.jl:613-616", status := .todo, prop := ``ByteStringMacro }
  , { id := "showcov-strings-raw-escape", juliaFile := "base/strings/io.jl"
      juliaFns := ["raw_str(s)", "escape_raw_string(::IO, ::AbstractString, ::Char)", "escape_raw_string(::AbstractString, ::Char)"]
      statement := "Raw-string escaping doubles backslashes before delimiters and at the end, while raw_str returns its input."
      source := "base/strings/io.jl:643-697", status := .todo, prop := ``RawStringSpec }
  , { id := "showcov-strings-indent", juliaFile := "base/strings/io.jl"
      juliaFns := ["indentation(::AbstractString)", "unindent(::AbstractString, ::Int)"]
      statement := "For every string, tabwidth, and indent, tab stops use div(column + tabwidth, tabwidth) * tabwidth and division errors propagate."
      source := "base/strings/io.jl:719-803", status := .todo, prop := ``IndentationSpec }
  , { id := "showcov-strings-char-vectors", juliaFile := "base/strings/io.jl"
      juliaFns := ["String(::AbstractVector{Char})", "String(::AbstractVector{<:AbstractChar})", "AnnotatedString(::AbstractVector{<:AbstractChar})"]
      statement := "Character-vector constructors preserve character order and byte-counted annotation regions."
      source := "base/strings/io.jl:805-847", status := .todo, prop := ``CharacterVectors }
  , { id := "memsafety-strings-io-wrap", juliaFile := "base/strings/io.jl"
      juliaFns := ["IOBuffer(::String)", "IOBuffer(::SubString{String})"]
      statement := "String IOBuffer views wrap the parent bytes as read-only; SubString views use their stored byte offset and length."
      source := "base/strings/io.jl:288-307", status := .todo, prop := ``StringIOViews }
  ]

end JuliaLean.Proofs.base.strings.io
