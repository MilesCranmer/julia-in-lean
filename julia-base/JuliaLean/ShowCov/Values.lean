import JuliaLean.ShowCov.Basic

/-!
# `show` for scalars, pairs, modules, and small wrappers (`base/show.jl`)

Values printed by methods in other files enter as the text those methods
print. Type names enter as their printed form.
-/

namespace JuliaLean.ShowCov.Values

open JuliaLean.ShowCov

/-! ## `Bool`, `Nothing`, integers -/

/-- `show(io, b::Bool)`, `base/show.jl:1423`; `tiIsBool` is
`nonnothing_nonmissing_typeinfo(io) === Bool` (`base/show.jl:1422`). -/
def showBool (tiIsBool : Bool) (b : Bool) : String :=
  if tiIsBool then (if b then "1" else "0") else (if b then "true" else "false")

/-- `nonnothing_nonmissing_typeinfo(io) = nonmissingtype(nonnothingtype(get(io, :typeinfo, Any)))`,
`base/show.jl:1422`, on a type given as its union components: `Nothing` and
`Missing` are dropped; an empty remainder is `Union{}`. -/
def nonnothingNonmissing (components : List String) : List String :=
  components.filter (fun c => c ≠ "Nothing" ∧ c ≠ "Missing")

/-- `show(io, ::Nothing) = print(io, "nothing")`, `base/show.jl:1424`. -/
def showNothing : String := "nothing"

/-- `show(io, n::Signed) = (write(io, string(n)); nothing)`, `base/show.jl:1425`. -/
def showSigned (n : Int) : String := toString n

/-- Hexadecimal digits of `n`, at least `pad` of them (`string(n, base=16, pad=pad)`). -/
def hexPad (n pad : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (pad - ds.length) '0' ++ ds)

/-- The unsigned integer types by bit size. -/
def uintName (bits : Nat) : String := "UInt" ++ toString bits

/-- `show(io, n::Unsigned)`, `base/show.jl:1426-1436`. `hex` is
`get(io, :hexunsigned, true)`; `tiSame` is `get(io, :typeinfo, Nothing) == typeof(n)`. -/
def showUnsigned (hex tiSame : Bool) (bits n : Nat) : String :=
  if hex then "0x" ++ hexPad n ((bits + 3) / 4)
  else if tiSame then toString n
  else uintName bits ++ "(" ++ toString n ++ ")"

/-- `print(io, n::Unsigned) = print(io, string(n))`, `base/show.jl:1437`. -/
def printUnsigned (n : Nat) : String := toString n

/-- Julia's type for an unsigned hexadecimal literal with `k` digits: the
smallest of `UInt8`..`UInt128` with at least `4k` bits (`BigInt` beyond 32 digits). -/
def hexLiteralBits (k : Nat) : Nat :=
  if k ≤ 2 then 8 else if k ≤ 4 then 16 else if k ≤ 8 then 32 else if k ≤ 16 then 64
  else if k ≤ 32 then 128 else 0

/-- Value of one lowercase hexadecimal digit. -/
def hexDigitVal (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87

/-- Value of a hexadecimal digit string. -/
def hexValue (s : List Char) : Nat :=
  s.foldl (fun acc c => 16 * acc + hexDigitVal c) 0

/-! ## `Pair` -/

/-- What `show(io, p::Pair)` needs about a pair: whether its type is tight
(`has_tight_type`), whether `get(io, :typeinfo, Any) == typeof(p)`, whether
`:compact` is set, and, for each element under its typeinfo, whether it is
delimited and its printed text. -/
structure PairInfo where
  firstTight : Bool
  secondTight : Bool
  tiIsPairType : Bool
  compact : Bool
  firstDelimited : Bool
  secondDelimited : Bool
  firstText : String
  secondText : String
  /-- `show(io, typeof(p))` and `show(io, (p.first, p.second))`. -/
  typeText : String
  tupleText : String

/-- `has_tight_type(p)`, `base/show.jl:1439-1441`. -/
def hasTightType (p : PairInfo) : Bool := p.firstTight && p.secondTight

/-- `isdelimited(io, x) = true`, `isdelimited(io, x::Function) = !isoperator(Symbol(x))`,
`isdelimited(io, p::Pair) = !(has_tight_type(p) || get(io, :typeinfo, Any) == typeof(p))`,
`base/show.jl:1443-1448`. -/
def isdelimitedAny : Bool := true
def isdelimitedFunction (isOperator : Bool) : Bool := !isOperator
def isdelimitedPair (p : PairInfo) : Bool := !(hasTightType p || p.tiIsPairType)

/-- `gettypeinfos(io, p)`, `base/show.jl:1450-1455`: the field types of the
`:typeinfo` when `p isa typeinfo <: Pair`, else `Any => Any`. -/
def gettypeinfos (pIsaTi tiSubPair : Bool) (fieldTypes : String × String) : String × String :=
  if pIsaTi && tiSubPair then fieldTypes else ("Any", "Any")

/-- `show_pairtyped(io, p)`, `base/show.jl:1469-1472`. -/
def showPairtyped (p : PairInfo) : Out := [p.typeText, p.tupleText]

/-- `show(io, p::Pair)`, `base/show.jl:1457-1467`. -/
def showPair (p : PairInfo) : Out :=
  if isdelimitedPair p then showPairtyped p else
  let elt (delim : Bool) (t : String) : Out := (if delim then [] else ["("]) ++ [t] ++ (if delim then [] else [")"])
  elt p.firstDelimited p.firstText ++ [if p.compact then "=>" else " => "] ++ elt p.secondDelimited p.secondText

/-! ## Modules -/

/-- A module: its name, whether its name is a valid identifier (`show_sym`
prints it bare) and its parent; `none` marks `Main`, `Base`, `Core` or a
module that is its own parent. -/
inductive Mod where
  | top (name : String)
  | sub (name : String) (parent : Mod)
  deriving DecidableEq, Repr

/-- `show_sym(io, nameof(m))` for a module name; `symText` renders names. -/
def printFullname (symText : String → String) : Mod → Out
  | .top n => [symText n]
  | .sub n p => printFullname symText p ++ [".", symText n]

/-- `show(io, m::Module)`, `base/show.jl:1474-1480`: a root module prints its
name, others their full dotted path (`print_fullname`, `base/show.jl:1484-1493`). -/
def showModule (symText : String → String) (isRoot : Bool) (m : Mod) : Out :=
  if isRoot then [match m with | .top n => n | .sub n _ => n] else printFullname symText m

/-- `fullname(m)`, joined with `"."`. -/
def fullnameJoin : Mod → String
  | .top n => n
  | .sub n p => fullnameJoin p ++ "." ++ n

/-! ## Small wrappers -/

/-- `show(io, ::UndefInitializer) = print(io, "UndefInitializer()")`, `base/show.jl:3228`. -/
def showUndef : String := "UndefInitializer()"

/-- `show(io, ::MIME"text/plain", u::UndefInitializer)`, `base/show.jl:6-10`. -/
def showUndefPlain (compact : Bool) : Out :=
  [showUndef] ++ (if compact then [] else [": array initializer with undefined values"])

/-- `show(io, ::MIME"text/plain", r::AbstractRange) = show(io, r)`, and the
`UnitRange` method that appends `" (empty range)"`, `base/show.jl:14-21`. -/
def showRangePlain (shown : String) : Out := [shown]
def showUnitRangePlain (shown : String) (compact isEmpty : Bool) : Out :=
  [shown] ++ (if !compact && isEmpty then [" (empty range)"] else [])

/-- `show(io, ::MIME"text/plain", r::LinRange)` and `LogRange`, `base/show.jl:23-39`:
an empty range shows compactly; otherwise the summary, `":\n"`, and the
`print_range` output. -/
def showLinLogPlain (isEmpty : Bool) (shown summary printed : String) : Out :=
  if isEmpty then [shown] else [summary, ":", "\n", printed]

/-- `show(io, ::MIME"text/plain", c::ComposedFunction) = show(io, c)`, also for
`Returns`, `Splat`, `OpaqueClosure` (`base/show.jl:75-77, 3450-3452`). -/
def showPlainForward (shown : String) : Out := [shown]

/-- `show(io, ::MIME"text/plain", t::Task)`, `base/show.jl:294-300`. -/
def showTaskPlain (shown : String) (failed : Bool) (exceptionText : String) : Out :=
  [shown] ++ (if failed then ["\n", exceptionText] else [])

/-- `show(io, src::Core.CancellationTokenSource)`, `base/show.jl:304-319`;
`sev` is `cancel_severity(src)` (`none` for `nothing`), `reprR` is `repr(r)`. -/
def showCTS (sev : Option UInt8) (reprR : String) (nparents : Int) : Out :=
  ["CancellationTokenSource("] ++
  [match sev with
   | none => "active"
   | some r => if r = 1 then "cancelled" else if r = 3 then "cancelled, abandon external"
       else if r = 4 then "cancelled, abandon all" else "cancelled, severity " ++ reprR] ++
  (if nparents > 0 then [", ", toString nparents, if nparents = 1 then " parent" else " parents"] else []) ++
  [")"]

/-- `print(io::IO, s::Symbol) = (write(io,s); nothing)`, `base/show.jl:322`: the
name's bytes. -/
def printSymbol (name : String) : String := name

/-- `show(io, ::MIME"text/plain", ::Core.TypeofBottom) = print(io, "Union{}")`,
`base/show.jl:615`. -/
def showBottomPlain : String := "Union{}"

/-- `show(io, ii::IncludeInto)` and `show(io, ei::Core.EvalInto)`,
`base/show.jl:3539-3555`: `M.include` / `M.eval` when the object is the
module's own binding, else `show_default`. -/
def showInto (isOwn : Bool) (modText field defaultText : String) : Out :=
  if isOwn then [modText, "." ++ field] else [defaultText]

/-- `show(io, ::MIME"text/plain", opt::JLOptions)`, `base/show.jl:278-292`: one
line per field, `repr(value)` after `" = "`, commas between. Pointer fields
are shown as their strings (`""` for `C_NULL`). -/
def showJLOptions (fields : List (String × String)) : Out :=
  let n := fields.length
  ["JLOptions(", "\n"] ++
  ((fields.zipIdx).flatMap (fun ((f, v), i) =>
    ["  ", f, " = ", v, if i + 1 < n then "," else "", "\n"])) ++ [")"]

/-- `show(io, ::MIME"text/plain", ti::TermInfo)` lives in `TermInfo`; the
`summary(io, t::AbstractSet)` header, `base/show.jl:235-239`. -/
def summarySet (typeArg : String) (n : Nat) : Out :=
  [typeArg, " with ", toString n, if n = 1 then " element" else " elements"]

/-- `show(io, x) = show_default(io, x)`, `show(x) = show(stdout, x)`,
`show_default(io, x) = _show_default(io, inferencebarrier(x))`,
`base/show.jl:520-525`: all print what `_show_default` prints. -/
def showFallback (defaultText : String) : String := defaultText

/-- A field of a struct shown by `_show_default`: undefined, or its shown text. -/
inductive Field where
  | undef
  | val (shown : String)

/-- `_show_default(io, x)`, `base/show.jl:527-568`. `fields` are the fields
when `nf != 0 || nb == 0`; `bits` is `none` in that case, else the object's
bytes (little-endian) and `Core.bitsizeof`. `circular` is what `show_circular(io, x)`
printed (`some marker` when it returned `true`). -/
def showDefault (typeText : String) (circular : Option String) (fields : List Field)
    (bits : Option (List UInt8 × Nat)) : Out :=
  [typeText, "("] ++
  (match bits with
   | none =>
     if let some marker := circular then [marker] else
     let shown := fields.map (fun f => match f with | .undef => "#undef" | .val s => s)
     (shown.zipIdx.flatMap (fun (s, i) => [s] ++ (if i + 1 < fields.length then [", "] else [])))
   | some (bytes, nbits) =>
     let nbytes := (nbits + 7) / 8
     ["0x"] ++ ((List.range nbytes).reverse.map (fun i =>
       let byte := (bytes.getD i 0).toNat
       if i = nbytes - 1 ∧ nbits % 8 ≠ 0 then
         hexPad (byte % 2 ^ (nbits % 8)) ((nbits % 8 + 3) / 4)
       else hexPad byte 2))) ++ [")"]

end JuliaLean.ShowCov.Values
