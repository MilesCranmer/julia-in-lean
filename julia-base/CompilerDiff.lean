import Lean.Data.Json
import JuliaLean.Compiler.src.typelattice
import JuliaLean.Compiler.src.typelimits
import JuliaLean.Compiler.src.effects
import JuliaLean.Compiler.src.tfuncs
import JuliaLean.Compiler.src.reinfer
import Std.Data.HashMap
import JuliaLean.Compiler.src.ssair.domtree
import JuliaLean.Compiler.src.ssair.slot2ssa
import JuliaLean.Compiler.src.typeutils.lattice
import JuliaLean.Compiler.src.ssair.EscapeAnalysis
import JuliaLean.Compiler.src.inferenceresult
import JuliaLean.Compiler.src.typeinfer
import JuliaLean.Compiler.src.ssair.inlining

/-!
`compilerdiff`: differential-testing driver for the `Compiler/src` models.

Reads JSON lines on stdin and prints one JSON line per case on stdout.

* `{"U": {...}}` extends the type universe (type names, layouts and the `CEnv` side tables).
* `{"TF": {"tns": [...]}}` extends the per-type-name facts `TEnv.tns` that `tfuncs.lean` reads.
* `{"id": k, "dt": "<op>", ...}` and `{"id": k, "s2s": "<op>", ...}` run a dominator-tree or
  `slot2ssa.jl` case and compare its JSON result with `exp` (see the sections at the end).
* `{"id": k, "op": "...", "L": "...", "a": [...], "next": N, "exp": {...}}` runs one operation
  with fresh `TypeVar`/object ids starting at `N`, compares the result with the expected one
  (`exp`, computed by the pinned Julia), and prints `{"id": k, "agree": true}` or the two results.

The serialization format is the one `difftest/compiler/common.jl` writes. Results are compared
structurally: `TypeVar`s up to a consistent renaming, `IdSet`s as sets, and the identities of
mutable `Vector`s and `IdSet`s ignored.
-/

open Lean (Json)
open JuliaLean.C JuliaLean.Compiler

namespace CompilerDiff

/-- Recursion budget given to every model call. -/
def fuel : Nat := 4000

def getK (j : Json) (k : String) : Except String Json := j.getObjVal? k
def hasK (j : Json) (k : String) : Bool := (j.getObjVal? k).toOption.isSome

partial def decodeVal (j : Json) : Except String Val := do
  if let .ok s := j.getStr? then
    if s == "bot" then return .bottom
    throw s!"bad Val string {s}"
  if let .ok name := (getK j "dt" >>= Json.getStr?) then
    let ps ← (← getK j "p").getArr?
    return .datatype name (← ps.toList.mapM decodeVal)
  if hasK j "u" then
    let ab ← (← getK j "u").getArr?
    return .union (← decodeVal ab[0]!) (← decodeVal ab[1]!)
  if hasK j "ua" then
    return .unionall (← (← getK j "ua").getNat?) (← (← getK j "n").getStr?)
      (← decodeVal (← getK j "lb")) (← decodeVal (← getK j "ub")) (← decodeVal (← getK j "body"))
  if hasK j "tv" then
    return .typevar (← (← getK j "tv").getNat?) (← (← getK j "n").getStr?)
      (← decodeVal (← getK j "lb")) (← decodeVal (← getK j "ub"))
  if hasK j "va" then
    let T ← if hasK j "T" then pure (some (← decodeVal (← getK j "T"))) else pure none
    let N ← if hasK j "N" then pure (some (← decodeVal (← getK j "N"))) else pure none
    return .vararg T N
  if hasK j "teq" then return .typeeq (← decodeVal (← getK j "teq"))
  if hasK j "tegal" then return .typeegal (← decodeVal (← getK j "tegal"))
  if hasK j "long" then return .long (← (← getK j "long").getInt?)
  if hasK j "sym" then return .symbol (← (← getK j "sym").getStr?)
  if hasK j "bits" then return .bits (← decodeVal (← getK j "bits")) (← (← getK j "v").getInt?)
  if hasK j "imm" then
    let fs ← (← getK j "f").getArr?
    return .imm (← decodeVal (← getK j "imm")) (← fs.toList.mapM decodeVal)
  if hasK j "mut" then
    return .mutableRef (← decodeVal (← getK j "mut")) (UInt64.ofNat (← (← getK j "a").getNat?))
  if hasK j "mod" then return .module (← (← getK j "mod").getStr?)
  throw s!"bad Val {j.compress}"

def getBool (j : Json) (k : String) : Except String Bool := do (← getK j k).getBool?
def getInt (j : Json) (k : String) : Except String Int := do (← getK j k).getInt?
def getNat (j : Json) (k : String) : Except String Nat := do (← getK j k).getNat?

partial def decodeElt (j : Json) : Except String LElt := do
  if hasK j "T" then return .ty (← decodeVal (← getK j "T"))
  if hasK j "C" then return .const (← decodeVal (← getK j "C"))
  if hasK j "PS" then
    let us ← (← getK j "u").getArr?
    let us ← us.toList.mapM fun u => match u with
      | .null => pure none
      | .bool b => pure (some b)
      | _ => throw "bad undefs"
    let fs ← (← getK j "f").getArr?
    return .partialStruct (← decodeVal (← getK j "PS")) us (← fs.toList.mapM decodeElt)
      (← getNat j "uid") (← getNat j "fid")
  if hasK j "Cond" then
    let sd ← (← getK j "Cond").getArr?
    return .conditional (← sd[0]!.getInt?) (← sd[1]!.getInt?) (← decodeElt (← getK j "t"))
      (← decodeElt (← getK j "e")) (← getBool j "d")
  if hasK j "ICond" then
    return .interConditional (← getInt j "ICond") (← decodeElt (← getK j "t"))
      (← decodeElt (← getK j "e"))
  if hasK j "MA" then
    let sd ← (← getK j "MA").getArr?
    return .mustAlias (← sd[0]!.getInt?) (← sd[1]!.getInt?) (← decodeElt (← getK j "v"))
      (← getInt j "i") (← decodeElt (← getK j "f"))
  if hasK j "IMA" then
    return .interMustAlias (← getInt j "IMA") (← decodeElt (← getK j "v")) (← getInt j "i")
      (← decodeElt (← getK j "f"))
  if hasK j "PTV" then
    return .partialTypeVar (← decodeVal (← getK j "PTV")) (← getBool j "l") (← getBool j "u")
  if hasK j "LA" then
    let cs ← (← getK j "c").getArr?
    return .limitedAccuracy (← decodeElt (← getK j "LA")) (← cs.toList.mapM Json.getNat?)
      (← getNat j "cid")
  if hasK j "PO" then
    return .partialOpaque (← decodeVal (← getK j "PO")) (← decodeElt (← getK j "env"))
      (← getNat j "par") (← getNat j "src")
  if hasK j "PT" then return .partialTask (← decodeElt (← getK j "PT"))
  throw s!"bad lattice element {j.compress}"

partial def encodeVal : Val → Json
  | .datatype n ps => Json.mkObj [("dt", n), ("p", Json.arr (ps.map encodeVal).toArray)]
  | .union a b => Json.mkObj [("u", Json.arr #[encodeVal a, encodeVal b])]
  | .intersect a b => Json.mkObj [("intersect", Json.arr #[encodeVal a, encodeVal b])]
  | .typeeq T => Json.mkObj [("teq", encodeVal T)]
  | .typeegal T => Json.mkObj [("tegal", encodeVal T)]
  | .unionall id n lb ub body => Json.mkObj [("ua", id), ("n", n), ("lb", encodeVal lb),
      ("ub", encodeVal ub), ("body", encodeVal body)]
  | .typevar id n lb ub => Json.mkObj [("tv", id), ("n", n), ("lb", encodeVal lb), ("ub", encodeVal ub)]
  | .vararg T N => Json.mkObj ([("va", Json.bool true)] ++ (T.map fun t => ("T", encodeVal t)).toList ++
      (N.map fun t => ("N", encodeVal t)).toList)
  | .bottom => "bot"
  | .typeapp a b => Json.mkObj [("typeapp", Json.arr #[encodeVal a, encodeVal b])]
  | .long n => Json.mkObj [("long", n)]
  | .symbol s => Json.mkObj [("sym", s)]
  | .bits ty v => Json.mkObj [("bits", encodeVal ty), ("v", v)]
  | .imm ty fs => Json.mkObj [("imm", encodeVal ty), ("f", Json.arr (fs.map encodeVal).toArray)]
  | .mutableRef ty a => Json.mkObj [("mut", encodeVal ty), ("a", a.toNat)]
  | .module m => Json.mkObj [("mod", m)]

partial def encodeElt : LElt → Json
  | .ty t => Json.mkObj [("T", encodeVal t)]
  | .const v => Json.mkObj [("C", encodeVal v)]
  | .partialStruct typ us fs uid fid => Json.mkObj [("PS", encodeVal typ),
      ("u", Json.arr (us.map fun | none => Json.null | some b => Json.bool b).toArray),
      ("f", Json.arr (fs.map encodeElt).toArray), ("uid", uid), ("fid", fid)]
  | .conditional s d t e i => Json.mkObj [("Cond", Json.arr #[Lean.toJson s, Lean.toJson d]), ("t", encodeElt t),
      ("e", encodeElt e), ("d", i)]
  | .interConditional s t e => Json.mkObj [("ICond", s), ("t", encodeElt t), ("e", encodeElt e)]
  | .mustAlias s d v i f => Json.mkObj [("MA", Json.arr #[Lean.toJson s, Lean.toJson d]), ("v", encodeElt v), ("i", i),
      ("f", encodeElt f)]
  | .interMustAlias s v i f => Json.mkObj [("IMA", s), ("v", encodeElt v), ("i", i), ("f", encodeElt f)]
  | .partialTypeVar tv l u => Json.mkObj [("PTV", encodeVal tv), ("l", l), ("u", u)]
  | .limitedAccuracy t cs cid => Json.mkObj [("LA", encodeElt t),
      ("c", Json.arr (cs.map Lean.toJson).toArray), ("cid", cid)]
  | .partialOpaque typ env p s => Json.mkObj [("PO", encodeVal typ), ("env", encodeElt env),
      ("par", p), ("src", s)]
  | .partialTask f => Json.mkObj [("PT", encodeElt f)]

/-- Structural equality up to a consistent renaming of `TypeVar` ids (`ren` pairs left and right
ids). -/
partial def alphaEq (ren : List (Nat × Nat)) (a b : Val) : Option (List (Nat × Nat)) := do
  let list (ren : List (Nat × Nat)) (xs ys : List Val) : Option (List (Nat × Nat)) :=
    if xs.length != ys.length then none
    else (xs.zip ys).foldlM (fun r (x, y) => alphaEq r x y) ren
  let opt (ren : List (Nat × Nat)) : Option Val → Option Val → Option (List (Nat × Nat))
    | none, none => some ren
    | some x, some y => alphaEq ren x y
    | _, _ => none
  match a, b with
  | .datatype n ps, .datatype m qs => if n == m then list ren ps qs else none
  | .union a1 a2, .union b1 b2 | .intersect a1 a2, .intersect b1 b2
  | .typeapp a1 a2, .typeapp b1 b2 => list ren [a1, a2] [b1, b2]
  | .typeeq x, .typeeq y | .typeegal x, .typeegal y => alphaEq ren x y
  | .unionall i n lb ub body, .unionall j m lb' ub' body' =>
    -- A binder scopes its variable: two `UnionAll`s may bind one `TypeVar` object on one side and
    -- two different ones on the other (Julia's type caches share them), which `===` and `==` do
    -- not see.
    if n != m then none else
    let ren ← list ren [lb, ub] [lb', ub']
    let ren' ← alphaEq ((i, j) :: ren) body body'
    some (ren'.erase (i, j))
  | .typevar i n lb ub, .typevar j m lb' ub' =>
    if n != m then none else
    match ren.lookup i, (ren.map (fun (x, y) => (y, x))).lookup j with
    | some j', _ => if j' == j then some ren else none
    | none, some _ => none
    | none, none => list ((i, j) :: ren) [lb, ub] [lb', ub']
  | .vararg t n, .vararg u m => do opt (← opt ren t u) n m
  | .bottom, .bottom => some ren
  | .long x, .long y => if x == y then some ren else none
  | .symbol x, .symbol y => if x == y then some ren else none
  | .bits t x, .bits u y => if x == y then alphaEq ren t u else none
  | .imm t xs, .imm u ys => list ren (t :: xs) (u :: ys)
  | .mutableRef _ x, .mutableRef _ y => if x == y then some ren else none
  | .module x, .module y => if x == y then some ren else none
  | _, _ => none

partial def eltAlphaEq (ren : List (Nat × Nat)) (a b : LElt) : Option (List (Nat × Nat)) := do
  let list (ren : List (Nat × Nat)) (xs ys : List LElt) : Option (List (Nat × Nat)) :=
    if xs.length != ys.length then none
    else (xs.zip ys).foldlM (fun r (x, y) => eltAlphaEq r x y) ren
  let guardB (c : Bool) : Option Unit := if c then some () else none
  match a, b with
  | .ty x, .ty y | .const x, .const y => alphaEq ren x y
  | .partialStruct t1 u1 f1 _ _, .partialStruct t2 u2 f2 _ _ => do
    guardB (u1 == u2); list (← alphaEq ren t1 t2) f1 f2
  | .conditional s1 d1 t1 e1 i1, .conditional s2 d2 t2 e2 i2 => do
    guardB (s1 == s2 && d1 == d2 && i1 == i2); list ren [t1, e1] [t2, e2]
  | .interConditional s1 t1 e1, .interConditional s2 t2 e2 => do
    guardB (s1 == s2); list ren [t1, e1] [t2, e2]
  | .mustAlias s1 d1 v1 i1 f1, .mustAlias s2 d2 v2 i2 f2 => do
    guardB (s1 == s2 && d1 == d2 && i1 == i2); list ren [v1, f1] [v2, f2]
  | .interMustAlias s1 v1 i1 f1, .interMustAlias s2 v2 i2 f2 => do
    guardB (s1 == s2 && i1 == i2); list ren [v1, f1] [v2, f2]
  | .partialTypeVar t1 l1 u1, .partialTypeVar t2 l2 u2 => do
    guardB (l1 == l2 && u1 == u2); alphaEq ren t1 t2
  | .limitedAccuracy t1 c1 _, .limitedAccuracy t2 c2 _ => do
    guardB (c1.all c2.contains && c2.all c1.contains); eltAlphaEq ren t1 t2
  | .partialOpaque t1 e1 p1 s1, .partialOpaque t2 e2 p2 s2 => do
    guardB (p1 == p2 && s1 == s2); eltAlphaEq (← alphaEq ren t1 t2) e1 e2
  | .partialTask f1, .partialTask f2 => eltAlphaEq ren f1 f2
  | _, _ => none

/-- `alphaEq` with the variables bound by each `UnionAll` scoped to its body, so separate binders
may use different variables on the two sides (the runtime sometimes renames the variable of a
`UnionAll` it copies, for example `Type` in a `Union` built in compiled code). Free `TypeVar`s
still need one consistent renaming. -/
partial def alphaEqS (ren : List (Nat × Nat)) (a b : Val) : Option (List (Nat × Nat)) := do
  let list (ren : List (Nat × Nat)) (xs ys : List Val) : Option (List (Nat × Nat)) :=
    if xs.length != ys.length then none
    else (xs.zip ys).foldlM (fun r (x, y) => alphaEqS r x y) ren
  let opt (ren : List (Nat × Nat)) : Option Val → Option Val → Option (List (Nat × Nat))
    | none, none => some ren
    | some x, some y => alphaEqS ren x y
    | _, _ => none
  match a, b with
  | .datatype n ps, .datatype m qs => if n == m then list ren ps qs else none
  | .union a1 a2, .union b1 b2 | .intersect a1 a2, .intersect b1 b2
  | .typeapp a1 a2, .typeapp b1 b2 => list ren [a1, a2] [b1, b2]
  | .typeeq x, .typeeq y | .typeegal x, .typeegal y => alphaEqS ren x y
  | .unionall i n lb ub body, .unionall j m lb' ub' body' =>
    if n != m then none else
    let ren ← list ren [lb, ub] [lb', ub']
    let ren ← list ((i, j) :: ren) [body] [body']
    ren.erase (i, j)
  | .typevar i n lb ub, .typevar j m lb' ub' =>
    if n != m then none else
    match ren.lookup i, (ren.map (fun (x, y) => (y, x))).lookup j with
    | some j', _ => if j' == j then some ren else none
    | none, some _ => none
    | none, none => list ((i, j) :: ren) [lb, ub] [lb', ub']
  | .vararg t n, .vararg u m => do opt (← opt ren t u) n m
  | .bottom, .bottom => some ren
  | .long x, .long y => if x == y then some ren else none
  | .symbol x, .symbol y => if x == y then some ren else none
  | .bits t x, .bits u y => if x == y then alphaEqS ren t u else none
  | .imm t xs, .imm u ys => list ren (t :: xs) (u :: ys)
  | .mutableRef _ x, .mutableRef _ y => if x == y then some ren else none
  | .module x, .module y => if x == y then some ren else none
  | _, _ => none

partial def eltAlphaEqS (ren : List (Nat × Nat)) (a b : LElt) : Option (List (Nat × Nat)) := do
  let list (ren : List (Nat × Nat)) (xs ys : List LElt) : Option (List (Nat × Nat)) :=
    if xs.length != ys.length then none
    else (xs.zip ys).foldlM (fun r (x, y) => eltAlphaEqS r x y) ren
  let guardB (c : Bool) : Option Unit := if c then some () else none
  match a, b with
  | .ty x, .ty y | .const x, .const y => alphaEqS ren x y
  | .partialStruct t1 u1 f1 _ _, .partialStruct t2 u2 f2 _ _ => do
    guardB (u1 == u2); list (← alphaEqS ren t1 t2) f1 f2
  | .conditional s1 d1 t1 e1 i1, .conditional s2 d2 t2 e2 i2 => do
    guardB (s1 == s2 && d1 == d2 && i1 == i2); list ren [t1, e1] [t2, e2]
  | .interConditional s1 t1 e1, .interConditional s2 t2 e2 => do
    guardB (s1 == s2); list ren [t1, e1] [t2, e2]
  | .mustAlias s1 d1 v1 i1 f1, .mustAlias s2 d2 v2 i2 f2 => do
    guardB (s1 == s2 && d1 == d2 && i1 == i2); list ren [v1, f1] [v2, f2]
  | .interMustAlias s1 v1 i1 f1, .interMustAlias s2 v2 i2 f2 => do
    guardB (s1 == s2 && i1 == i2); list ren [v1, f1] [v2, f2]
  | .partialTypeVar t1 l1 u1, .partialTypeVar t2 l2 u2 => do
    guardB (l1 == l2 && u1 == u2); alphaEqS ren t1 t2
  | .limitedAccuracy t1 c1 _, .limitedAccuracy t2 c2 _ => do
    guardB (c1.all c2.contains && c2.all c1.contains); eltAlphaEqS ren t1 t2
  | .partialOpaque t1 e1 p1 s1, .partialOpaque t2 e2 p2 s2 => do
    guardB (p1 == p2 && s1 == s2); eltAlphaEqS (← alphaEqS ren t1 t2) e1 e2
  | .partialTask f1, .partialTask f2 => eltAlphaEqS ren f1 f2
  | _, _ => none

/-- A model result: a Julia value, a Julia exception, or a model failure. -/
inductive Outcome where
  | bool (b : Bool)
  | optBool (b : Option Bool)
  | val (v : Val)
  | elt (e : LElt)
  | none_
  | jlErr (exc : String)
  | fail (msg : String)
  /-- A record of integers (`Effects` fields, `EffectsOverride` fields) or one word. -/
  | nums (xs : List Nat)
  /-- A structured result compared as compressed JSON (the reinfer cases). -/
  | json (j : Json)
  /-- A Julia `Vector` of results, e.g. the tuples of `switchtupleunion`. -/
  | list (xs : List Outcome)

partial def Outcome.toJson : Outcome → Json
  | .nums xs => Json.mkObj [("nums", Json.arr (xs.map Lean.toJson).toArray)]
  | .bool b => Json.mkObj [("bool", b)]
  | .optBool b => Json.mkObj [("optbool", match b with | none => Json.null | some b => Json.bool b)]
  | .val v => Json.mkObj [("val", encodeVal v)]
  | .elt e => Json.mkObj [("elt", encodeElt e)]
  | .none_ => Json.mkObj [("nothing", true)]
  | .jlErr e => Json.mkObj [("err", e)]
  | .fail m => Json.mkObj [("fail", m)]
  | .json j => Json.mkObj [("json", j)]
  | .list xs => Json.mkObj [("list", Json.arr (xs.map Outcome.toJson).toArray)]

/-- The exception type of a thrown `julia:<Exc>: <msg>` string. -/
def classify (msg : String) : Outcome :=
  match msg.splitOn ":" with
  | "julia" :: exc :: _ => .jlErr exc
  | _ => .fail msg

partial def decodeExpected (j : Json) : Except String Outcome := do
  if hasK j "list" then
    return .list (← (← (← getK j "list").getArr?).toList.mapM decodeExpected)
  if hasK j "bool" then return .bool (← getBool j "bool")
  if hasK j "optbool" then
    return .optBool (match (← getK j "optbool") with | .bool b => some b | _ => none)
  if hasK j "val" then return .val (← decodeVal (← getK j "val"))
  if hasK j "elt" then return .elt (← decodeElt (← getK j "elt"))
  if hasK j "nothing" then return .none_
  if hasK j "err" then return .jlErr (← (← getK j "err").getStr?)
  if hasK j "nums" then return .nums (← (← (← getK j "nums").getArr?).toList.mapM Json.getNat?)
  if hasK j "json" then return .json (← getK j "json")
  throw s!"bad expected {j.compress}"

partial def agree : Outcome → Outcome → Bool
  | .list xs, .list ys => xs.length == ys.length && (xs.zip ys).all fun (x, y) => agree x y
  | .bool a, .bool b => a == b
  | .optBool a, .optBool b => a == b
  | .val a, .val b => (alphaEq [] a b).isSome
  | .elt a, .elt b => (eltAlphaEq [] a b).isSome
  | .none_, .none_ => true
  | .jlErr a, .jlErr b => a == b
  | .nums a, .nums b => a == b
  | .json a, .json b => a.compress == b.compress
  | _, _ => false

/-- `agree` with `alphaEqS`: the comparison of the `tf.*` cases. -/
def agreeScoped : Outcome → Outcome → Bool
  | .val a, .val b => (alphaEqS [] a b).isSome
  | .elt a, .elt b => (eltAlphaEqS [] a b).isSome
  | a, b => agree a b

def decodeLattice : String → Except String Lattice
  | "typeinf" => pure typeinfLattice
  | "ipo" => pure ipoLattice
  | "opt" => pure optimizerLattice
  | "jltype" => pure .jlType
  | "consts" => pure .consts
  | "partials" => pure (.partials .consts)
  | "conditionals" => pure (.conditionals simpleInferenceLattice)
  | "mustaliases" => pure baseInferenceLattice
  | s => throw s!"unknown lattice {s}"

def run (E : CEnv) (next : Nat) (m : CM Outcome) : Outcome :=
  match m.run next with
  | .ok (o, _) => o
  | .error e => classify e

def optElt : Option LElt → Outcome
  | some e => .elt e
  | none => .none_

/-- `fargs`: `null` for `nothing`, else a list of `{"slot": k}`, `{"ssa": k}` or `{"other": true}`. -/
def decodeFargs (j : Json) : Except String (Option (List FArg)) := do
  if j.isNull then return none
  let xs ← j.getArr?
  return some (← xs.toList.mapM fun x => do
    if hasK x "slot" then return FArg.slot (← getInt x "slot")
    if hasK x "ssa" then return FArg.ssa (← getInt x "ssa")
    return FArg.other)

def longOut (k : Int) : Outcome := .val (.long k)

/-- The cases of `Compiler/src/typeutils.jl` (`difftest/compiler/typeutils.jl`). -/
def typeutilsCase (E : CEnv) (n : Nat) (L : Lattice) (op : String) (args : Array Json)
    (next : Nat) : Except String Outcome := do
  let elt (i : Nat) : Except String LElt := decodeElt args[i]!
  let val (i : Nat) : Except String Val := decodeVal args[i]!
  let int (i : Nat) : Except String Int := args[i]!.getInt?
  let elts (i : Nat) : Except String (List LElt) := do (← args[i]!.getArr?).toList.mapM decodeElt
  let vals (i : Nat) : Except String (List Val) := do (← args[i]!.getArr?).toList.mapM decodeVal
  match op with
  | "unionsplitcost" => do
    let a ← elts 0; let fa ← decodeFargs args[1]!
    pure (run E next (longOut <$> unionsplitcost n E L a true fa))
  | "unionsplitcostSvec" => do
    let a ← vals 0
    pure (run E next (longOut <$> unionsplitcost n E L (a.map LElt.ty) false))
  | "isUnionSplitEligible" => do
    let a ← elts 0; let m ← int 1; let fa ← decodeFargs args[2]!
    pure (run E next (.bool <$> isUnionSplitEligible n E L a m fa))
  | "switchtupleunion" => do
    let t ← val 0
    pure (run E next ((fun r => .list (r.map Outcome.val)) <$> switchtupleunion n E t))
  | "switchtupleunionL" => do
    let a ← elts 0; let fa ← decodeFargs args[1]!
    pure (run E next ((fun r => .list (r.map fun xs => .list (xs.map Outcome.elt))) <$>
      switchtupleunionL n E L a fa))
  | "computeAliasGroups" => do
    let na ← int 0; let fa ← decodeFargs args[1]!
    let at? ← if args[2]!.isNull then pure none else some <$> elts 2
    pure (run E next ((fun
      | none => .none_
      | some g => .list (g.toList.map fun k => longOut (Int.ofNat k))) <$> computeAliasGroups na.toNat fa at?))
  | "argtypesToType" => do
    let a ← elts 0; pure (run E next (.val <$> argtypesToType n E a))
  | "typesubtract" => do
    let a ← val 0; let b ← val 1; let m ← int 2
    pure (run E next (.val <$> typesubtract n E a b m))
  | "isnotbrokensubtype" => do
    let a ← val 0; let b ← val 1; pure (run E next (.bool <$> isnotbrokensubtype n E a b))
  | "compatibleVatuple" => do
    let a ← val 0; let b ← val 1; pure (run E next (.bool <$> compatibleVatuple n E a b))
  | "isknownlength" => do let t ← val 0; pure (run E next (.bool <$> isknownlength t))
  | "isTypeDataType" => do let t ← val 0; pure (run E next (pure (.bool (isTypeDataType t))))
  | "hasExtendedInfo" => do let x ← elt 0; pure (run E next (pure (.bool (hasExtendedInfo x))))
  | "validTypeofTparam" => do
    let t ← val 0; pure (run E next (.bool <$> validTypeofTparam n E t))
  | "validTparam" => do let x ← val 0; pure (run E next (.bool <$> validTparam n E x))
  | "unionallDepth" => do
    let t ← val 0; pure (run E next (pure (longOut (unionallDepth t))))
  | "unwraptvUb" => do let t ← val 0; pure (run E next (.val <$> unwraptv n t))
  | "unwraptvLb" => do let t ← val 0; pure (run E next (pure (.val (unwraptvLb t))))
  | "typename" => do
    let t ← val 0
    pure (run E next (pure (.val (.symbol (match typenameT t with
      | .bottom => "bottom"
      | .typeName => "typename"
      | .const nm => nm)))))
  | "isImmutableArgtype" => do
    let x ← elt 0; pure (run E next (.bool <$> isImmutableArgtype n E x))
  | "hasConcreteSubtype" => do
    let t ← val 0; pure (run E next (.bool <$> hasConcreteSubtypeDT n E t))
  | op => throw s!"unknown op {op}"

/-- The cases of `Compiler/src/typelimits.jl` (`difftest/compiler/typelimits.jl`). -/
def typelimitsCase (E : CEnv) (n : Nat) (L : Lattice) (op : String) (args : Array Json)
    (next : Nat) : Except String Outcome := do
  let elt (i : Nat) : Except String LElt := decodeElt args[i]!
  let val (i : Nat) : Except String Val := decodeVal args[i]!
  let int (i : Nat) : Except String Int := args[i]!.getInt?
  let vals (i : Nat) : Except String (List Val) := do (← args[i]!.getArr?).toList.mapM decodeVal
  let tm := tmergeFallback n E
  match op with
  | "tmerge" => do let a ← elt 0; let b ← elt 1; pure (run E next (.elt <$> tmerge n E L a b))
  | "tmergeFastPath" => do
    let a ← elt 0; let b ← elt 1; pure (run E next (optElt <$> tmergeFastPath n E L a b))
  | "issimplertype" => do
    let a ← elt 0; let b ← elt 1; pure (run E next (.bool <$> issimplertype n E L a b))
  | "tmergePartialStruct" => do
    let a ← elt 0; let b ← elt 1; pure (run E next (optElt <$> tmergePartialStruct n E L a b))
  | "tmergeTypesSlow" => do
    let a ← val 0; let b ← val 1; pure (run E next (.val <$> tmergeTypesSlow n E a b))
  | "tuplemerge" => do
    let a ← val 0; let b ← val 1; pure (run E next (.val <$> tuplemerge n E a b))
  | "issimpleenoughtype" => do
    let t ← val 0; pure (run E next (.bool <$> issimpleenoughtype n E t))
  | "unioncomplexity" => do
    let t ← val 0; pure (run E next ((fun k => .val (.long k)) <$> unioncomplexity n t))
  | "unionCountAbstract" => do
    let t ← val 0; pure (run E next ((fun k => .val (.long k)) <$> unionCountAbstract E t))
  | "limitTypeSize" => do
    let t ← val 0; let c ← val 1; let s ← val 2; let d ← int 3; let l ← int 4
    pure (run E next (.val <$> limitTypeSize n E tm t c s d l))
  | "limitTypeSize_" => do
    let t ← val 0; let c ← val 1; let ss ← vals 2; let d ← int 3; let l ← int 4
    pure (run E next (.val <$> limitTypeSize_ n E tm t c ss d l))
  | "typeMoreComplex" => do
    let t ← val 0; let c ← val 1; let ss ← vals 2; let d ← int 3; let td ← int 4; let l ← int 5
    pure (run E next (.bool <$> typeMoreComplex n E t c ss d td l))
  | "isDerivedType" => do
    let t ← val 0; let c ← val 1; let d ← int 2
    pure (run E next (.bool <$> isDerivedType n E t c d))
  | "tnameIntersect" => do
    let a ← val 0; let b ← val 1
    pure (run E next (do
      let some an := a.unwrapUnionall.name? | throw "tnameIntersect: not a wrapper"
      let some bn := b.unwrapUnionall.name? | throw "tnameIntersect: not a wrapper"
      match ← tnameIntersect n E an bn with
      | some r => return .val (← E.types.typename r).wrapper
      | none => return .val (.symbol "none")))
  | "tupleTailElem" => do
    let i ← elt 0; let ct ← vals 1
    pure (run E next (.val <$> tupleTailElem n E tm i ct))
  | op => typeutilsCase E n L op args next

/-- An `Effects` as the list of its ten fields in declaration order (`Bool`s as `0`/`1`). -/
def effectsNums (e : Effects) : List Nat :=
  let b (x : Bool) : Nat := if x then 1 else 0
  [e.consistent.toNat, e.effect_free.toNat, e.reset_safe.toNat, b e.nothrow, b e.terminates,
    b e.notaskstate, e.inaccessiblememonly.toNat, e.noub.toNat, e.nonoverlayed.toNat, b e.nortcall]

def decodeEffectsJson (j : Json) : Except String Effects := do
  let xs ← (← j.getArr?).toList.mapM Json.getNat?
  let some [c, ef, rs, nt, t, s, m, u, o, r] := some xs | throw s!"bad Effects {j.compress}"
  return ⟨c.toUInt8, ef.toUInt8, rs.toUInt8, nt != 0, t != 0, s != 0, m.toUInt8, u.toUInt8,
    o.toUInt8, r != 0⟩

def overrideNums (o : EffectsOverride) : List Nat :=
  [o.consistent, o.effect_free, o.nothrow, o.terminates_globally, o.terminates_locally,
    o.notaskstate, o.inaccessiblememonly, o.noub, o.noub_if_noinbounds, o.consistent_overlay,
    o.nortcall].map fun x => if x then 1 else 0

def decodeOverrideJson (j : Json) : Except String EffectsOverride := do
  let xs ← (← j.getArr?).toList.mapM fun x => (· != 0) <$> x.getNat?
  let some [a, b, c, d, e, f, g, h, i, k, l] := some xs | throw s!"bad EffectsOverride {j.compress}"
  return ⟨a, b, c, d, e, f, g, h, i, k, l⟩

/-- The cases of `Compiler/src/effects.jl` (`difftest/compiler/effects.jl`). -/
def effectsCase (op : String) (args : Array Json) : Except String Outcome := do
  let eff (i : Nat) := decodeEffectsJson args[i]!
  let ovr (i : Nat) := decodeOverrideJson args[i]!
  let nat (i : Nat) : Except String Nat := args[i]!.getNat?
  let exprs (i : Nat) : Except String (List (List Bool)) := do
    (← args[i]!.getArr?).toList.mapM fun a => do
      (← a.getArr?).toList.mapM fun x => (· != 0) <$> x.getNat?
  match op with
  | "eff.kw" => do
    let e ← eff 0
    let given ← (← args[1]!.getArr?).toList.mapM fun x => (· != 0) <$> x.getNat?
    let v ← decodeEffectsJson args[2]!
    let g (k : Nat) : Bool := given.getD k false
    pure (.nums (effectsNums (Effects.kw e
      (consistent := if g 0 then v.consistent else e.consistent)
      (effect_free := if g 1 then v.effect_free else e.effect_free)
      (reset_safe := if g 2 then v.reset_safe else e.reset_safe)
      (nothrow := if g 3 then v.nothrow else e.nothrow)
      (terminates := if g 4 then v.terminates else e.terminates)
      (notaskstate := if g 5 then v.notaskstate else e.notaskstate)
      (inaccessiblememonly := if g 6 then v.inaccessiblememonly else e.inaccessiblememonly)
      (noub := if g 7 then v.noub else e.noub)
      (nonoverlayed := if g 8 then v.nonoverlayed else e.nonoverlayed)
      (nortcall := if g 9 then v.nortcall else e.nortcall))))
  | "eff.isBetter" => do pure (.bool (isBetterEffects (← eff 0) (← eff 1)))
  | "eff.merge" => do pure (.nums (effectsNums (mergeEffects (← eff 0) (← eff 1))))
  | "eff.mergebits" => do
    pure (.nums [(mergeEffectbits (← nat 0).toUInt8 (← nat 1).toUInt8).toNat])
  | "eff.mergebitsBool" => do pure (.bool (mergeEffectbitsBool ((← nat 0) != 0) ((← nat 1) != 0)))
  | "eff.query" => do
    let q ← args[0]!.getStr?
    let e ← eff 1
    let check := (args[2]?.bind fun j => j.getNat?.toOption).getD 0 != 0
    let r ← match q with
      | "is_consistent" => pure (isConsistent e)
      | "is_effect_free" => pure (isEffectFree e)
      | "is_reset_safe" => pure (isResetSafe e)
      | "is_nothrow" => pure (isNothrow e)
      | "is_terminates" => pure (isTerminates e)
      | "is_notaskstate" => pure (isNotaskstate e)
      | "is_inaccessiblememonly" => pure (isInaccessiblememonly e)
      | "is_noub" => pure (isNoub e)
      | "is_noub_if_noinbounds" => pure (isNoubIfNoinbounds e)
      | "is_nonoverlayed" => pure (isNonoverlayed e)
      | "is_nortcall" => pure (isNortcall e)
      | "is_foldable" => pure (isFoldable e check)
      | "is_foldable_nothrow" => pure (isFoldableNothrow e check)
      | "is_removable_if_unused" => pure (isRemovableIfUnused e)
      | "is_finalizer_inlineable" => pure (isFinalizerInlineable e)
      | "is_consistent_if_notreturned" => pure (isConsistentIfNotreturned e)
      | "is_consistent_if_inaccessiblememonly" => pure (isConsistentIfInaccessiblememonly e)
      | "is_effect_free_if_inaccessiblememonly" => pure (isEffectFreeIfInaccessiblememonly e)
      | "is_reset_safe_if_inaccessiblememonly" => pure (isResetSafeIfInaccessiblememonly e)
      | "is_inaccessiblemem_or_argmemonly" => pure (isInaccessiblememOrArgmemonly e)
      | "is_consistent_overlay" => pure (isConsistentOverlay e)
      | q => throw s!"unknown query {q}"
    pure (.bool r)
  | "eff.encode" => do pure (.nums [(encodeEffects (← eff 0)).toNat])
  | "eff.decode" => do pure (.nums (effectsNums (decodeEffects (← nat 0).toUInt32)))
  | "eff.encodeOverride" => do pure (.nums [(encodeEffectsOverride (← ovr 0)).toNat])
  | "eff.decodeOverride" => do pure (.nums (overrideNums (decodeEffectsOverride (← nat 0).toUInt16)))
  | "eff.decodeStmtOverride" => do
    pure (.nums (overrideNums (decodeStatementEffectsOverride (← nat 0).toUInt32)))
  | "eff.override" => do pure (.nums (effectsNums (overrideEffects (← eff 0) (← ovr 1))))
  | "eff.adjustMethod" => do
    pure (.nums (effectsNums (adjustEffectsMethod (← eff 0) (← nat 1).toUInt16)))
  | "eff.methodPurity" => do pure (.nums [(methodPurityBits (← exprs 0)).toNat])
  | "eff.stmtPurity" => do pure (.nums [(statementPurityFlag (← exprs 0)).toNat])
  | op => throw s!"unknown op {op}"
/-! ## Inlining cases (`difftest/compiler/inlining.jl`): ops `inl.*` -/

namespace InlDiff

open JuliaLean.Compiler.Optimize JuliaLean.Compiler.Inlining

def gB (j : Json) (k : String) : Except String Bool := do (← getK j k).getBool?
def gI (j : Json) (k : String) : Except String Int := do (← getK j k).getInt?
def gN (j : Json) (k : String) : Except String Nat := do (← getK j k).getNat?
def gS (j : Json) (k : String) : Except String String := do (← getK j k).getStr?
def toJI (x : Int) : JI := ji x

def decodeBuiltinKind : String → Except String BuiltinKind
  | "getfield" => pure .getfield | "tuple" => pure .tuple | "getglobal" => pure .getglobal
  | "memoryrefget" => pure .memoryrefget | "const_memoryrefget" => pure .constMemoryrefget
  | "memoryref_isassigned" => pure .memoryrefIsassigned | "memoryrefset!" => pure .memoryrefset
  | "memoryrefunset!" => pure .memoryrefunset | "typeassert" => pure .typeassert
  | "invoke" => pure .invoke | "other" => pure .other
  | s => throw s!"bad builtin kind {s}"

def decodeCallee (j : Json) : Except String Callee := do
  match ← gS j "t" with
  | "i" => return .intrinsic (← gB j "as") (toJI (← gI j "mn")) (toJI (← gI j "mx")) (toJI (← gI j "c")) (← gB j "ll")
  | "b" =>
    let tc ← match ← getK j "tc" with
      | .null => pure none
      | x => pure (some (toJI (← x.getInt?)))
    return .builtin (← decodeBuiltinKind (← gS j "k")) tc
  | "o" => return .other
  | s => throw s!"bad callee {s}"

def decodeArgFacts (j : Json) : Except String (Option ArgFacts) := do
  match j with
  | .null => return none
  | _ =>
    let xs ← (← j.getArr?).toList.mapM Json.getBool?
    let some [a, b, c, d] := some xs | throw s!"bad arg facts {j.compress}"
    return some ⟨a, b, c, d⟩

partial def decodeSExpr (j : Json) : Except String SExpr := do
  match ← gS j "h" with
  | "meta" => return .metaHead
  | "call" =>
    let c ← getK j "c"
    let args ← (← (← getK c "a").getArr?).toList.mapM decodeArgFacts
    return .call {
      c0 := (← decodeCallee (← getK c "c0")), ftypIntrinsic := (← gB c "fi"),
      fargSSA := (← gB c "fs"), defRecoverable := (← gB c "dr"), c1 := (← decodeCallee (← getK c "c1")),
      nargs := (← gN c "n"), args, retBottom := (← gB c "rb") }
  | "fc" => return .foreigncall (← gB j "sp")
  | "fg" => return .foreignglobal
  | "inv" => return .invoke (← gB j "rb")
  | "=" => return .assign (← gB j "g")
  | "=e" => return .assignExpr (← gB j "g") (← decodeSExpr (← getK j "r"))
  | "copyast" => return .copyast
  | "o" => return .other
  | s => throw s!"bad expr head {s}"

def decodeStmt (j : Json) : Except String Stmt := do
  match ← gS j "k" with
  | "e" => return .expr (← decodeSExpr (← getK j "e"))
  | "g" => return .goto (← gI j "l")
  | "gi" => return .gotoifnot (← gI j "l")
  | "enter" => return .enter
  | "o" => return .other
  | s => throw s!"bad stmt {s}"

def decodeSrc (j : Json) : Except String Src := do
  match ← gS j "s" with
  | "ci" => return .codeInfo (← gN j "c").toUInt16 (← gN j "i").toUInt8
  | "str" => return compressCodeInfo (← gN j "c").toUInt16 (← gN j "i").toUInt8
  | "u8" => return .uint8 (← gN j "b").toUInt8
  | "ir" => return .irCode
  | "opt" => return .optState (← gN j "c").toUInt16 (← gN j "i").toUInt8
  | "other" => return .other
  | s => throw s!"bad src {s}"

def decodeSpecial : String → Except String Special
  | "compilerbarrier" => pure .compilerbarrier | "ifelse" => pure .ifelse
  | "task_result_type" => pure .taskResultType | "none" => pure .none
  | s => throw s!"bad special {s}"

def decodeTerm : String → Except String Terminator
  | "rv" => pure .returnVal | "ru" => pure .returnUndef | "o" => pure .other
  | s => throw s!"bad terminator {s}"

def jiJson (x : JI) : Json := Lean.toJson x.val

/-- A model `Jl` result as an outcome: Julia exceptions by type name, a missing fact as a model
failure. -/
def ofJl {α : Type} (f : α → Outcome) : JuliaLean.Jl α → Outcome
  | .ok a => f a
  | .error .boundsError => .jlErr "BoundsError"
  | .error (.methodError _) => .jlErr "MethodError"
  | .error (.argumentError "fact") => .fail "missing fact"
  | .error e => .fail s!"model error {repr e}"

def u32 (j : Json) : Except String UInt32 := do return (← j.getNat?).toUInt32

def inliningCase (op : String) (args : Array Json) : Except String Outcome := do
  let a (i : Nat) : Except String Json := match args[i]? with
    | some x => pure x | none => throw s!"missing argument {i}"
  let nat (i : Nat) : Except String Nat := do (← a i).getNat?
  let int (i : Nat) : Except String Int := do (← a i).getInt?
  let bool (i : Nat) : Except String Bool := do (← a i).getBool?
  let stmts (i : Nat) : Except String (List Stmt) := do (← (← a i).getArr?).toList.mapM decodeStmt
  let ints (i : Nat) : Except String (List Int) := do (← (← a i).getArr?).toList.mapM Json.getInt?
  match op with
  | "inl.consts" =>
    pure (.nums ([IR_FLAG_NULL, IR_FLAG_INBOUNDS, IR_FLAG_INLINE, IR_FLAG_NOINLINE, IR_FLAG_CONSISTENT,
      IR_FLAG_EFFECT_FREE, IR_FLAG_NOTHROW, IR_FLAG_TERMINATES, IR_FLAG_NOUB, IR_FLAG_NORTCALL,
      IR_FLAG_RESET_SAFE, IR_FLAG_REFINED, IR_FLAG_UNUSED, IR_FLAG_EFIIMO,
      IR_FLAG_INACCESSIBLEMEM_OR_ARGMEM, IR_FLAG_RSIIMO, IR_FLAGS_EFFECTS, IR_FLAGS_REMOVABLE,
      IR_FLAGS_NEEDS_EA].map UInt32.toNat ++
      [JuliaLean.Compiler.NUM_IR_FLAGS, SLOT_STATICUNDEF.toNat, SLOT_ASSIGNEDONCE.toNat,
       SLOT_USEDUNDEF.toNat, MAX_INLINE_COST.toNat, MIN_INLINE_COST.toNat,
       SRC_FLAG_DECLARED_INLINE.toNat, SRC_FLAG_DECLARED_NOINLINE.toNat]))
  | "inl.hasFlag" => pure (.bool (hasFlag (← u32 (← a 0)) (← u32 (← a 1))))
  | "inl.isStmtInline" => pure (.bool (isStmtInline (← u32 (← a 0))))
  | "inl.isStmtNoinline" => pure (.bool (isStmtNoinline (← u32 (← a 0))))
  | "inl.iscallstmt" =>
    let h ← match ← a 0 with | .null => pure none | x => pure (some (← x.getStr?))
    pure (.bool (iscallstmt h))
  | "inl.flagsForEffects" => pure (.nums [(flagsForEffects (← decodeEffectsJson (← a 0))).toNat])
  | "inl.plusSaturate" => pure (.json (jiJson (plusSaturate (toJI (← int 0)) (toJI (← int 1)))))
  | "inl.clamp" => pure (.nums [(inlineCostClamp (toJI (← int 0))).toNat])
  | "inl.encode" => pure (.nums [(jlEncodeInliningCost (← nat 0).toUInt16).toNat])
  | "inl.decode" => pure (.nums [(jlDecodeInliningCost (← nat 0).toUInt8).toNat])
  | "inl.inliningCost" => pure (.nums [(inliningCost (← decodeSrc (← a 0))).toNat])
  | "inl.isInlineable" => pure (.bool (isInlineable (← decodeSrc (← a 0))))
  | "inl.isDeclaredInline" => pure (ofJl .bool (isDeclaredInline (← decodeSrc (← a 0))))
  | "inl.isDeclaredNoinline" => pure (ofJl .bool (isDeclaredNoinline (← decodeSrc (← a 0))))
  | "inl.setInlineable" => pure (.nums [(setInlineable (← bool 0)).toNat])
  | "inl.srcPolicy" => pure (.bool (srcInliningPolicy (← decodeSrc (← a 0)) (← u32 (← a 1))))
  | "inl.srcPolicyMI" =>
    pure (.bool (srcInliningPolicyMI (← bool 0) (← bool 1) (← bool 2) (← decodeSrc (← a 3))
      (← u32 (← a 4))))
  | "inl.stmtCost" =>
    let s ← decodeStmt (← a 0)
    pure (ofJl (fun x => .json (jiJson x))
      (statementOrBranchCost (← bool 2) (← ints 3) (toJI (← int 4)) s (← int 1)))
  | "inl.stmtCosts" =>
    pure (ofJl (fun (cs, m) => .json (Json.mkObj [("c", Json.arr (cs.map jiJson).toArray), ("m", jiJson m)]))
      (statementCosts (← bool 1) (← ints 2) (toJI (← int 3)) (← stmts 0)))
  | "inl.bodyCost" =>
    pure (ofJl (fun c => .nums [c.toNat])
      (inlineCostModel (← ints 1) (toJI (← int 2)) (toJI (← int 3)) (← stmts 0)))
  | "inl.threshold" =>
    let p ← (← (← a 0).getArr?).toList.mapM Json.getInt?
    let some [th, pen, bonus] := some p | throw "bad params"
    let f ← a 1
    let r : ResultFacts := {
      defIsMethod := (← gB f "dm"), sigIsTuple := (← gB f "st"),
      rtIsBottom := (← gB f "rb"), isDispatchTuple := (← gB f "dt"), tupleRet := (← gB f "tr"),
      moduleIsTop := (← gB f "mt"), name := (← gS f "nm") }
    let params : CostParams := ⟨toJI th, toJI pen, toJI bonus⟩
    pure (ofJl (fun c => .nums [c.toNat])
      (inlineCostModelResult params r (← nat 2).toUInt8 (← ints 3) (← stmts 4)))
  | "inl.constabi" =>
    pure (.bool (isResultConstabiEligible (← bool 0) (← decodeEffectsJson (← a 1)) (← bool 2)))
  | "inl.early" =>
    let f ← a 0
    let x : EarlyFacts := {
      inlining := (← gB f "inl"), typeConst := (← gB f "tc"),
      valInlineable := (← gB f "vi"), fIntrinsic := (← gB f "fi"), pureIntrinsic := (← gB f "pi"),
      inPure := (← gB f "ip"), inEffectFree := (← gB f "ie"), special := (← decodeSpecial (← gS f "sp")),
      nargtypes := (← gN f "na"), arg2Const := (← gB f "a2c"), arg2Symbol := (← gB f "a2s"),
      arg2Conditional := (← gB f "a2cd"), arg2True := (← gB f "a2t"), arg2False := (← gB f "a2f"),
      arg2Bool := (← gB f "a2b"), arg2Task := (← gB f "a2k"), args34Egal := (← gB f "e34") }
    -- Harness normalization: Julia's result object is the same in each pair (see the driver).
    let ieq ← bool 2
    let r := match earlyInlineSpecialCase x (← u32 (← a 1)) with
      | .none_ => "none" | .quotedVal => "quoted" | .arg3 => "arg3"
      | .arg4 => if x.args34Egal then "arg3" else "arg4"
      | .instanceof => if ieq then "quoted" else "instanceof"
    pure (.json (Json.str r))
  | "inl.handleCases" =>
    let sigs ← (← (← a 4).getArr?).toList.mapM Json.getBool?
    let flag ← u32 (← a 6)
    let r := handleCases (← bool 0) (← bool 1) (← nat 2) (← bool 3) sigs
      (← decodeEffectsJson (← a 5)) flag
    -- Harness normalization: a flag update that adds no bit is not observable.
    let r := match r with | .flags f => if f == flag then HandleCasesResult.none_ else r | _ => r
    pure (.json (match r with
      | .single => Json.str "single"
      | .unionSplit h f => Json.arr #[Json.str "us", Json.bool h, Json.bool f]
      | .none_ => Json.str "none"
      | .flags f => Json.arr #[Json.str "flags", Lean.toJson f.toNat]))
  | "inl.inlineConst" =>
    let (b, f) := inlineConstIfInlineable (← bool 0) (← bool 1) (← u32 (← a 2))
    pure (.json (Json.arr #[Json.bool b, Lean.toJson f.toNat]))
  | "inl.linear" => pure (.bool (linearInlineEligible (← nat 0) (← decodeTerm (← gS (← a 1) "t"))))
  | op => throw s!"unknown op {op}"

end InlDiff

/-- The cases of `Compiler/src/tfuncs.jl` (`difftest/compiler/tfuncs.jl`): ops `tf.*`. -/
def tfuncsCase (T : TEnv) (j : Json) : Except String (Outcome × Outcome) := do
  let E := T.E
  let op ← (← getK j "op").getStr?
  let L ← decodeLattice ((getK j "L" >>= Json.getStr?).toOption.getD "typeinf")
  let args ← (← getK j "a").getArr?
  let next ← getNat j "next"
  let exp ← decodeExpected (← getK j "exp")
  let elts (i : Nat) : Except String (List LElt) := do (← args[i]!.getArr?).toList.mapM decodeElt
  let n := fuel
  let got ← match op with
    | "tf.builtin" => do
      let f ← args[0]!.getStr?; let as ← elts 1
      pure (run E next (.elt <$> builtinTfunction n T L f as))
    | "tf.nothrow" => do
      let f ← args[0]!.getStr?; let as ← elts 1; let rt ← decodeElt args[2]!
      pure (run E next (.bool <$> builtinNothrow n T L f as rt))
    | "tf.instanceof" => do
      let t ← decodeElt args[0]!; let astag ← args[1]!.getBool?
      pure (run E next (do
        let (r, a, b, c) ← instanceofTfunc n E t astag
        return .val (← tupleRT n E [r, boolVal a, boolVal b, boolVal c])))
    | op => throw s!"unknown op {op}"
  return (got, exp)

def decodeTns (u : Json) : Except String (List (String × TnInfo)) := do
  let rows ← (← getK u "tns").getArr?
  rows.toList.mapM fun r => do
    let r ← r.getArr?
    let names ← (← r[1]!.getArr?).toList.mapM Json.getStr?
    let const ← (← r[2]!.getArr?).toList.mapM Json.getBool?
    let atomic ← (← r[3]!.getArr?).toList.mapM Json.getBool?
    pure (← r[0]!.getStr?, { names, const, atomic, nUninit := ← r[4]!.getNat? })

/-- The `count_const_size` tables (`ConstLayout`): `dts` rows
`[type, sizeof, isbits, pointerfree, [isptr...], [isconst...]]` and `heap` rows
`[object id, [field or null...]]`. -/
def decodeConstLayout (j : Json) : Except String ConstLayout := do
  let dts ← (← getK j "dts").getArr?
  let dts ← dts.toList.mapM fun r => do
    let r ← r.getArr?
    let bools (k : Nat) : Except String (List Bool) := do (← r[k]!.getArr?).toList.mapM Json.getBool?
    let dt ← decodeVal r[0]!
    let size ← r[1]!.getNat?
    let isbits ← r[2]!.getBool?
    let pointerfree ← r[3]!.getBool?
    let isptr ← bools 4
    let isconst ← bools 5
    pure (dt, ({ size, isbits, pointerfree, isptr, isconst } : DTFacts))
  let heap ← (← getK j "heap").getArr?
  let heap ← heap.toList.mapM fun r => do
    let r ← r.getArr?
    let fs ← (← r[1]!.getArr?).toList.mapM fun f =>
      if f.isNull then pure none else some <$> decodeVal f
    pure (← r[0]!.getNat?, fs)
  return { dts, heap }

def decodeWorlds (j : Json) : Except String Worlds := do
  let a ← j.getArr?
  return (← a[0]!.getNat?, ← a[1]!.getNat?)

/-- One `InferenceCache` entry: `{"mi", "loc", "pw", "cw", "rw", "at", "ov", "tomb"}`. -/
def decodeConstpropEntry (j : Json) : Except String ConstpropEntry := do
  let ov ← match ← getK j "ov" with
    | .null => pure none
    | a => some <$> (← a.getArr?).toList.mapM Json.getBool?
  return { mi := (← getNat j "mi"), isLocal := (← getBool j "loc"),
           proofWorlds := (← decodeWorlds (← getK j "pw")), cacheWorld := (← getNat j "cw"),
           validWorlds := (← decodeWorlds (← getK j "rw")),
           argtypes := (← (← (← getK j "at").getArr?).toList.mapM decodeElt),
           overriddenByConst := ov, tombstone := (← getBool j "tomb") }

/-- `cr.rehit`: the key `const_prop_call` builds from `given` and `cache_argtypes`, its
`overridden_by_const` flags, and the lookup of that key in a cache holding only its own entry, as
`found + 2 * missing + 3 * (found at another position) + 4 * (flags as bits)`. -/
def rehitCode (ops : TmeetOps) (n : Nat) (E : CEnv) (L : Lattice) (given cacheArgtypes : List LElt)
    (w : Nat) : CM Int := do
  let key ← matchingCacheArgtypesSimple ops n E L given cacheArgtypes
  let ov ← overriddenByConstFlags n E key cacheArgtypes
  let entry : ConstpropEntry :=
    { mi := 1, isLocal := false, proofWorlds := (0, 0), cacheWorld := w, validWorlds := (w, w),
      argtypes := key, overriddenByConst := some ov, tombstone := false }
  let code : Int := match ← constpropCacheLookup n E L 1 true key [entry] w with
    | .found 1 => 1
    | .found _ => 3
    | .nothing_ => 0
    | .missing_ => 2
  let bits : Int := (ov.zipIdx.map fun (b, i) => if b then (2 : Int) ^ i else 0).sum
  return code + 4 * bits

/-- The cases of `Compiler/src/inferenceresult.jl`, the result-caching decisions of
`Compiler/src/typeinfer.jl` and `count_const_size` (`difftest/compiler/cacheresult.jl`). -/
def cacheresultCase (T : TEnv) (j : Json) : Except String (Outcome × Outcome) := do
  let E := T.E
  let op ← (← getK j "op").getStr?
  let L ← decodeLattice ((getK j "L" >>= Json.getStr?).toOption.getD "typeinf")
  let args ← (← getK j "a").getArr?
  let next ← getNat j "next"
  let exp ← decodeExpected (← getK j "exp")
  let elts (i : Nat) : Except String (List LElt) := do (← args[i]!.getArr?).toList.mapM decodeElt
  let bool (i : Nat) : Except String Bool := args[i]!.getBool?
  let nat (i : Nat) : Except String Nat := args[i]!.getNat?
  let n := fuel
  let ops := tfuncTmeetOps n T
  let eltList (xs : List LElt) : Outcome := .list (xs.map Outcome.elt)
  let got ← match op with
    | "cr.mostGeneral" => do
      let nargs ← if args[0]!.isNull then pure none else some <$> nat 0
      let spec ← decodeVal args[1]!
      pure (run E next (eltList <$> mostGeneralArgtypes n E nargs spec))
    | "cr.nospecInfer" => do
      let flag ← bool 0; let mask ← nat 1; let nargs ← nat 2
      let a ← elts 3; let c ← elts 4
      pure (run E next (eltList <$> getNospecializeinferArgtypes flag mask nargs a c))
    | "cr.matchSimple" => do
      let a ← elts 0; let c ← elts 1
      pure (run E next (eltList <$> matchingCacheArgtypesSimple ops n E L a c))
    | "cr.rehit" => do
      let a ← elts 0; let c ← elts 1; let w ← nat 2
      pure (run E next (longOut <$> rehitCode ops n E L a c w))
    | "cr.isArgtypeMatch" => do
      let a ← decodeElt args[0]!; let c ← decodeElt args[1]!; let o ← bool 2
      pure (run E next (.bool <$> isArgtypeMatch n E L a c o))
    | "cr.vaProcess" => do
      let a ← elts 0; let nargs ← nat 1; let isva ← bool 2
      pure (run E next (eltList <$> vaProcessArgtypes n E L a nargs isva))
    | "cr.lookup" => do
      let mi ← nat 0; let miVa ← bool 1; let given ← elts 2
      let cache ← (← args[3]!.getArr?).toList.mapM decodeConstpropEntry
      let world ← nat 4
      pure (run E next ((fun
        | .found k => longOut k
        | .nothing_ => longOut 0
        | .missing_ => longOut (-1)) <$> constpropCacheLookup n E L mi miVa given cache world))
    | "cr.countConstSize" => do
      let x ← decodeVal args[0]!; let cs ← bool 1; let C ← decodeConstLayout args[2]!
      pure (run E next ((fun k => longOut k) <$> countConstSize n E C x cs))
    | "cr.isInlineableConstant" => do
      let x ← decodeVal args[0]!; let C ← decodeConstLayout args[1]!
      pure (run E next (.bool <$> isInlineableConstant n E C x))
    | "cr.constabi" => do
      let r ← decodeElt args[0]!; let eff := decodeEffects (← nat 1).toUInt32
      let C ← decodeConstLayout args[2]!
      let md ← if args[3]!.isNull then pure none else some <$> bool 3
      pure (run E next (.bool <$> match md with
        | none => isResultConstabiEligible n E C r eff
        | some d => resultIsConstabi n E C d r eff))
    | "cr.discard" => do
      let d ← bool 0; let k ← bool 1; let g ← bool 2; let cs ← bool 3; let cost ← nat 4
      pure (.bool (discardOptimizedResult d k g (fun _ => cs) cost))
    | "cr.compress" => do
      let isM ← bool 0; let d ← bool 1; let inl ← bool 2; let k ← bool 3; let g ← bool 4
      let c ← bool 5; let cs ← bool 6
      pure (longOut (match maybeCompressCodeinfo isM d inl k g c (fun _ => cs) with
        | .nothing_ => 0 | .codeinfo => 1 | .compressed => 2))
    | op => throw s!"unknown op {op}"
  return (got, exp)

/-- Run one case. -/
def runCase (E : CEnv) (j : Json) : Except String (Outcome × Outcome) := do
  let op ← (← getK j "op").getStr?
  let L ← decodeLattice ((getK j "L" >>= Json.getStr?).toOption.getD "typeinf")
  let args ← (← getK j "a").getArr?
  let next ← getNat j "next"
  let exp ← decodeExpected (← getK j "exp")
  let elt (i : Nat) : Except String LElt := decodeElt args[i]!
  let val (i : Nat) : Except String Val := decodeVal args[i]!
  let n := fuel
  let got ← match op with
    | "sqsub" => do let a ← elt 0; let b ← elt 1; pure (run E next (.bool <$> sqsub n E L a b))
    | "sqsubStrict" => do
      let a ← elt 0; let b ← elt 1; pure (run E next (.bool <$> sqsubStrict n E L a b))
    | "sqsubStrictNe" => do
      let a ← elt 0; let b ← elt 1; pure (run E next (.bool <$> sqsubStrictNe n E L a b))
    | "isLatticeEqual" => do
      let a ← elt 0; let b ← elt 1; pure (run E next (.bool <$> isLatticeEqual n E L a b))
    | "tmeet" => do
      let a ← elt 0; let t ← val 1
      pure (run E next (.elt <$> tmeet tmeetOpsUnmodelled n E L a t))
    | "widenconst" => do let a ← elt 0; pure (run E next (.val <$> widenconst n E a))
    | "widenconstSplit" => do let a ← elt 0; pure (run E next (.val <$> widenconstSplit n E a))
    | "widenconditional" => do let a ← elt 0; pure (run E next (.elt <$> widenconditional a))
    | "widenwrappedconditional" => do
      let a ← elt 0; pure (run E next (.elt <$> widenwrappedconditional a))
    | "widenslotwrapper" => do let a ← elt 0; pure (run E next (.elt <$> widenslotwrapper a))
    | "widenmustalias" => do let a ← elt 0; pure (run E next (.elt <$> widenmustalias a))
    | "widenwrappedmustalias" => do
      let a ← elt 0; pure (run E next (.elt <$> widenwrappedmustalias a))
    | "hasNontrivialExtendedInfo" => do
      let a ← elt 0; pure (run E next (.bool <$> hasNontrivialExtendedInfo n E L a))
    | "isConstPropProfitableArg" => do
      let a ← elt 0; pure (run E next (.bool <$> isConstPropProfitableArg E L a))
    | "isForwardableArgtype" => do
      let a ← elt 0; pure (run E next (pure (.bool (isForwardableArgtype L a))))
    | "isValidLattice" => do let a ← elt 0; pure (run E next (pure (.bool (isValidLattice L a))))
    | "isLatticeBool" => do let a ← elt 0; pure (run E next (.bool <$> isLatticeBool n E L a))
    | "maybeExtractConstBool" => do
      let a ← elt 0; pure (run E next (pure (.optBool (maybeExtractConstBool a))))
    | "isalreadyconst" => do let a ← elt 0; pure (run E next (.bool <$> isalreadyconst n E a))
    | "widenlattice" => do let a ← elt 0; pure (run E next (.elt <$> widenlatticeElt n E L a))
    | "narrowMustalias" => do
      let a ← elt 0; let b ← elt 1; pure (run E next (.elt <$> narrowMustalias n E L a b))
    | "narrowLimitedTyp" => do
      let a ← elt 0; let b ← elt 1; pure (run E next (.elt <$> narrowLimitedTyp a b))
    | "validAsLattice" => do
      let t ← val 0; let astag ← args[1]!.getBool?
      pure (run E next (.bool <$> validAsLattice n E t astag))
    | "isconstType" => do let t ← val 0; pure (run E next (pure (.bool (isconstType t))))
    | op =>
      if op.startsWith "eff." then effectsCase op args
      else if op.startsWith "inl." then InlDiff.inliningCase op args
      else typelimitsCase E n L op args next
  return (got, exp)

def decodeUniverse (E : CEnv) (u : Json) : Except String CEnv := do
  let names ← (← getK u "names").getArr?
  let names ← names.toList.mapM fun t => do
    let super ← if hasK t "super" then pure (some (← decodeVal (← getK t "super"))) else pure none
    let name ← (← getK t "name").getStr?
    let abstract ← getBool t "abstract"
    let mutable ← getBool t "mutable"
    let wrapper ← decodeVal (← getK t "wrapper")
    pure ({ name, abstract, mutable, wrapper, super } : TypeName)
  let layouts ← (← getK u "layouts").getArr?
  let layouts ← layouts.toList.mapM fun l => do
    let dt ← decodeVal (← getK l "dt")
    let isbits ← getBool l "isbits"
    let singleton ← getBool l "singleton"
    let concreteSubtype ← getBool l "cs"
    pure ({ dt, isbits, singleton, concreteSubtype } : Layout)
  let nfields ← (← getK u "nfields").getArr?
  let nfields ← nfields.toList.mapM fun p => do
    let p ← p.getArr?
    pure (← decodeVal p[0]!, ← p[1]!.getNat?)
  let instances ← (← getK u "instances").getArr?
  let instances ← instances.toList.mapM fun p => do
    let p ← p.getArr?
    pure (← decodeVal p[0]!, ← decodeVal p[1]!)
  let strs (k : String) : Except String (List String) := do
    let a ← (← getK u k).getArr?
    a.toList.mapM Json.getStr?
  -- `structs` (field types and `datatype_min_ninitialized`) is optional.
  let structs ← match u.getObjVal? "structs" with
    | .ok a => do
      let a ← a.getArr?
      a.toList.mapM fun p => do
        let p ← p.getArr?
        let fts ← p[1]!.getArr?
        pure (← decodeVal p[0]!, ← fts.toList.mapM decodeVal, ← p[2]!.getNat?)
    | .error _ => pure []
  return { E with
    structs := E.structs ++ structs
    types := { names := E.types.names ++ names, layouts := E.types.layouts ++ layouts }
    nfields := E.nfields ++ nfields
    instances := E.instances ++ instances
    constfields := E.constfields ++ (← strs "constfields")
    primitives := E.primitives ++ (← strs "primitives") }


/-! ## Cases of `Compiler/src/reinfer.jl`, `bindinginvalidations.jl` and `cicache.jl`

Their operations start with `r.` (`difftest/compiler/reinfer.jl`). `{"R": {...}}` lines add
answers to the oracle tables, which persist for the run: the pinned Julia's method table and
bindings do not change while the cases run, so an answer for a signature and world is fixed. Each
case carries the objects it reads (`heap`) and its expected result as JSON, compared after
`compress`. -/

namespace ReinferDiff

open JuliaLean.Compiler.Reinfer JuliaLean.Compiler.CICache

/-- Oracle tables, keyed by the compressed JSON of the re-encoded arguments. -/
structure Tables where
  sub : Std.HashMap String Bool := {}
  isect : Std.HashMap String Val := {}
  egal : Std.HashMap String Bool := {}
  mm : Std.HashMap String (Option (List Nat) × Nat × Nat × Int) := {}
  fs : Std.HashMap String (Option Nat × Nat × Nat) := {}
  bar : Std.HashMap String WorldRange := {}
  scw : Std.HashMap String Nat := {}
  bdw : Std.HashMap String Nat := {}
  deriving Inhabited

def vkey (v : Val) : String := (encodeVal v).compress

def arrAt (a : Array Json) (i : Nat) : Except String Json :=
  if h : i < a.size then pure a[i] else throw s!"short array {i}"

def natOrNull (j : Json) : Except String (Option Nat) :=
  match j with | .null => pure none | j => some <$> j.getNat?

def addTables (T : Tables) (r : Json) : Except String Tables := do
  let rows (k : String) : Except String (Array Json) :=
    match r.getObjVal? k with | .ok a => a.getArr? | .error _ => pure #[]
  let v (a : Array Json) (i : Nat) : Except String String := do
    let x ← arrAt a i
    return vkey (← decodeVal x)
  let n (a : Array Json) (i : Nat) : Except String Nat := do (← arrAt a i).getNat?
  let mut T := T
  for row in ← rows "sub" do
    let a ← row.getArr?
    let k := (← v a 0) ++ "|" ++ (← v a 1)
    let x ← (← arrAt a 2).getBool?
    T := { T with sub := T.sub.insert k x }
  for row in ← rows "isect" do
    let a ← row.getArr?
    let k := (← v a 0) ++ "|" ++ (← v a 1)
    let x ← decodeVal (← arrAt a 2)
    T := { T with isect := T.isect.insert k x }
  for row in ← rows "egal" do
    let a ← row.getArr?
    let k := (← v a 0) ++ "|" ++ (← v a 1)
    let x ← (← arrAt a 2).getBool?
    T := { T with egal := T.egal.insert k x }
  for row in ← rows "mm" do
    let a ← row.getArr?
    let res ← match ← arrAt a 3 with
      | .null => pure none
      | j => do
        let xs ← j.getArr?
        let ns ← xs.toList.mapM Json.getNat?
        pure (some ns)
    let lim ← (← arrAt a 1).getInt?
    let k := (← v a 0) ++ "|" ++ toString lim ++ "|" ++ toString (← n a 2)
    let amb ← (← arrAt a 6).getInt?
    let x := (res, (← n a 4), (← n a 5), amb)
    T := { T with mm := T.mm.insert k x }
  for row in ← rows "fs" do
    let a ← row.getArr?
    let k := (← v a 0) ++ "|" ++ toString (← n a 1)
    let m ← natOrNull (← arrAt a 2)
    let x := (m, (← n a 3), (← n a 4))
    T := { T with fs := T.fs.insert k x }
  for row in ← rows "bar" do
    let a ← row.getArr?
    let k := toString (← n a 0) ++ "|" ++ toString (← n a 1)
    let x : WorldRange := ⟨(← n a 2), (← n a 3)⟩
    T := { T with bar := T.bar.insert k x }
  for row in ← rows "scw" do
    let a ← row.getArr?
    let k := (← v a 0) ++ "|" ++ toString (← n a 1)
    let x ← n a 2
    T := { T with scw := T.scw.insert k x }
  for row in ← rows "bdw" do
    let a ← row.getArr?
    let k := toString (← n a 0) ++ "|" ++ toString (← n a 1)
    let x ← n a 2
    T := { T with bdw := T.bdw.insert k x }
  return T

def need {α : Type} (what key : String) : Option α → Except String α
  | some x => pure x
  | none => throw s!"model: oracle has no {what} for {key}"

def oracle (T : Tables) : Oracle where
  sub a b := let k := vkey a ++ "|" ++ vkey b; need "sub" k (T.sub.get? k)
  isect a b := let k := vkey a ++ "|" ++ vkey b; need "isect" k (T.isect.get? k)
  egal a b := let k := vkey a ++ "|" ++ vkey b; need "egal" k (T.egal.get? k)
  matchingMethods s lim w :=
    let k := vkey s ++ "|" ++ toString lim ++ "|" ++ toString w; need "mm" k (T.mm.get? k)
  findsup s w := let k := vkey s ++ "|" ++ toString w; need "fs" k (T.fs.get? k)
  sigContributorsWorld sig image :=
    let k := vkey sig ++ "|" ++ toString image; need "scw" k (T.scw.get? k)
  linkageBlobDepWorld image blob :=
    let k := toString image ++ "|" ++ toString blob; need "bdw" k (T.bdw.get? k)
  bindingAccessRange b w := let k := toString b ++ "|" ++ toString w; need "bar" k (T.bar.get? k)

def decSig (j : Json) : Except String Sig := do
  let oid ← getNat j "oid"
  let t ← decodeVal (← getK j "t")
  return ⟨oid, t⟩

def decEdge (j : Json) : Except String Edge := do
  if hasK j "ci" then return .ci (← getNat j "ci")
  if hasK j "mi" then return .mi (← getNat j "mi")
  if hasK j "m" then return .method (← getNat j "m")
  if hasK j "int" then return .int (← getInt j "int")
  if hasK j "ty" then return .ty (← decSig (← getK j "ty"))
  if hasK j "b" then return .binding (← getNat j "b")
  if hasK j "pa" then return .possiblyAmbiguous
  if hasK j "mt" then return .methodTable
  throw s!"bad edge {j.compress}"

def nats (j : Json) : Except String (List Nat) := do (← j.getArr?).toList.mapM Json.getNat?

def decMethod (j : Json) : Except String MethodR := do
  let src ← match ← getK j "src" with
    | .null => pure none
    | a => do
      let sts ← (← a.getArr?).toList.mapM fun st => do
        let p ← st.getArr?
        let g ← natOrNull (← arrAt p 0)
        let uses ← (← (← arrAt p 1).getArr?).toList.mapM natOrNull
        pure ({ gr := g, uses } : Stmt)
      pure (some sts)
  let uid ← getNat j "uid"
  let sig ← decodeVal (← getK j "sig")
  let primaryWorld ← getNat j "pw"
  let dispatchStatus ← getNat j "ds"
  let interferences ← nats (← getK j "intf")
  let m : JuliaLean.C.Method := { uid, sig, primaryWorld, dispatchStatus, interferences }
  let interferencesLen ← getNat j "ilen"
  let didScanSource ← getNat j "dss"
  let blob ← getNat j "blob"
  let hasMethodTable ← getBool j "mt"
  let hasImageGlobalref ← getBool j "igr"
  let specializations ← nats (← getK j "specs")
  let module_ ← getNat j "mod"
  return { m, interferencesLen, didScanSource, blob, hasMethodTable, source := src,
           hasImageGlobalref, specializations, module_ }

def decMI (j : Json) : Except String MIR := do
  let id ← getNat j "id"
  let def_ ← getNat j "def"
  let specTypes ← decSig (← getK j "st")
  let dispatchStatus ← getNat j "ds"
  let cache ← nats (← getK j "cache")
  return { id, def_, specTypes, dispatchStatus, cache }

def decCI (j : Json) : Except String CIR := do
  let edges ← match ← getK j "edges" with
    | .null => pure none
    | a => do
      let es ← (← a.getArr?).toList.mapM decEdge
      pure (some es.toArray)
  let id ← getNat j "id"
  let mi ← getNat j "mi"
  let ownerNothing ← getBool j "on"
  let minWorld ← getNat j "min"
  let maxWorld ← getNat j "max"
  let flags ← getNat j "flags"
  let blob ← getNat j "blob"
  return { id, mi, ownerNothing, minWorld, maxWorld, flags, edges, blob }

def decPartition (j : Json) : Except String Partition := do
  let pid ← getNat j "pid"
  let minWorld ← getNat j "min"
  let maxWorld ← getNat j "max"
  let kind ← getNat j "kind"
  let restriction ← natOrNull (← getK j "r")
  return { pid, minWorld, maxWorld, kind, restriction }

def decBinding (j : Json) : Except String BindingR := do
  let id ← getNat j "id"
  let partitions ← (← (← getK j "parts").getArr?).toList.mapM decPartition
  let flags ← getNat j "flags"
  let module_ ← getNat j "mod"
  return { id, partitions, flags, module_ }

def decHeap (j : Json) : Except String Heap := do
  let arr (k : String) : Except String (List Json) := do
    let a ← (← getK j k).getArr?
    return a.toList
  let worldCounter ← getNat j "wc"
  let requireWorld ← getNat j "rw"
  let firstImageReplacementWorld ← getNat j "firw"
  let methods := (← (← arr "methods").mapM decMethod).toArray
  let mis := (← (← arr "mis").mapM decMI).toArray
  let cis := (← (← arr "cis").mapM decCI).toArray
  let bindings := (← (← arr "bindings").mapM decBinding).toArray
  return { worldCounter, requireWorld, firstImageReplacementWorld, methods, mis, cis, bindings }

def encodeState (H : Heap) : List (String × Json) :=
  [("cis", Json.arr (H.cis.map fun c => Json.arr #[c.id, c.minWorld, c.maxWorld])),
   ("mis", Json.arr (H.mis.map fun m => Json.arr #[m.id, m.dispatchStatus])),
   ("dss", Json.arr (H.methods.map fun m => Json.arr #[m.uid, m.didScanSource])),
   ("bf", Json.arr (H.bindings.map fun b => Json.arr #[b.id, b.flags]))]

def decItem (j : Json) : Except String InternalItem := do
  if hasK j "ci" then return .ci (← getNat j "ci")
  if hasK j "m" then return .method (← getNat j "m")
  return .other

def decWR (j : Json) : Except String WorldRange := do
  let a ← j.getArr?
  return ⟨← (← arrAt a 0).getNat?, (← (← arrAt a 1).getNat?)⟩

def encWR (w : WorldRange) : Json := Json.arr #[w.minWorld, w.maxWorld]

def decEntry (j : Json) : Except String CacheEntry := do
  let a ← j.getArr?
  let ci ← (← arrAt a 0).getNat?
  let mn ← (← arrAt a 1).getNat?
  let mx ← (← arrAt a 2).getNat?
  let ow ← (← arrAt a 3).getNat?
  let inf ← (← arrAt a 4).getBool?
  let inv ← if a.size > 5 then (← arrAt a 5).getBool? else pure false
  return ⟨ci, mn, mx, ow, inf, inv⟩

/-- Budget for the `while true` loops of the verifier. -/
def vfuel : Nat := 100000

def outE (r : Except String Json) : Outcome :=
  match r with
  | .ok j => .json j
  | .error e => classify e

/-- The branch markers the run passed, for the driver's path coverage. -/
def pathTags (s : RS Workspace) : List String :=
  s.events.toList.filterMap fun | .path t => some t | _ => none

def runVM {α : Type} (H : Heap) (m : VM α) (k : α → RS Workspace → Json) : Outcome × List String :=
  match m.run { heap := H, ws := {} } with
  | .ok (a, s) => (.json (k a s), pathTags s)
  | .error e => (classify e, [])

def reinferCase (T : Tables) (j : Json) : Except String (Outcome × Outcome × List String) := do
  let op ← (← getK j "op").getStr?
  let args ← (← getK j "a").getArr?
  let exp ← decodeExpected (← getK j "exp")
  let O := oracle T
  let arg (i : Nat) : Except String Json := arrAt args i
  let (got, paths) ← match op with
    | "r.wrIntersect" => do
      let a ← decWR (← arg 0); let b ← decWR (← arg 1)
      pure (outE (encWR <$> CICache.intersect a b), [])
    | "r.wrUnion" => do
      let a ← decWR (← arg 0); let b ← decWR (← arg 1)
      pure (outE (encWR <$> CICache.union a b), [])
    | "r.wrIn" => do
      let w ← (← arg 0).getNat?; let a ← decWR (← arg 1)
      pure (.bool (a.contains w), [])
    | "r.wrNew" => do
      let k ← (← arg 0).getStr?
      let x ← (← arg 1).getNat?; let y ← (← arg 2).getNat?
      let r := match k with
        | "all" => WorldRange.all
        | "single" => WorldRange.single x
        | _ => WorldRange.ofUnitRange x y
      pure (.json (Json.arr #[r.first, r.last, r.minWorld, r.maxWorld]), [])
    | "r.icc" => do
      let owner ← (← arg 0).getNat?; let wr ← decWR (← arg 1)
      let chain ← (← (← arg 2).getArr?).toList.mapM decEntry
      let c : InternalCodeCache ← if args.size > 3 then do
          match ← (← arg 3).getStr? with
          | "none" => pure (InternalCodeCache.ofArgs owner .none)
          | "single" => pure (InternalCodeCache.ofArgs owner (.single wr.minWorld))
          | "unit" => pure (InternalCodeCache.ofArgs owner (.unitRange wr.minWorld wr.maxWorld))
          | "fields" => pure (InternalCodeCache.ofArgs owner (.fields wr.minWorld wr.maxWorld))
          | _ => pure ⟨owner, wr⟩
        else pure ⟨owner, wr⟩
      let gi : Json := match c.getindex chain with | .ok x => x | .error _ => "KeyError"
      pure (.json (Json.arr #[c.haskey chain, match c.get chain with | some x => x | none => Json.null, gi]), [])
    | "r.iccSet" => do
      let owner ← (← arg 0).getNat?
      let chain ← (← (← arg 1).getArr?).toList.mapM decEntry
      let e ← decEntry (← arg 2)
      let isM ← (← arg 3).getBool?
      let c : InternalCodeCache := ⟨owner, WorldRange.all⟩
      pure (outE ((fun (p, ch) => Json.arr #[Json.bool p, Json.arr (ch.map fun x => (x.ci : Json)).toArray]) <$>
        c.setindex e isM chain), [])
    | "r.exportFlags" => do
      let p ← decPartition (← arg 0)
      let (a, b, c) := exportAffectingPartitionFlags p
      pure (.json (Json.arr #[a, b, c]), [])
    | "r.bindingChanged" => do
      let H ← decHeap (← arg 0); let b ← (← arg 1).getNat?; let w ← (← arg 2).getNat?
      pure (runVM H (bindingChangedSinceRequireWorld (W := Workspace) O b w) fun r _ => Json.bool r)
    | "r.invalidateMethod" => do
      let H ← decHeap (← arg 0); let gr ← (← arg 1).getNat?; let m ← (← arg 2).getNat?
      let w ← (← arg 3).getNat?
      pure (runVM H (invalidateMethodForGlobalref (W := Workspace) gr m w) fun r s =>
        Json.mkObj ([("ret", Json.bool r)] ++ encodeState s.heap))
    | "r.verifyMethod" => do
      let H ← decHeap (← arg 0); let ci ← (← arg 1).getNat?; let vw ← (← arg 2).getNat?
      pure (runVM H (verifyMethod O vfuel ci vw) fun (c, mn, mx) s =>
        Json.mkObj ([("ret", Json.arr #[c, mn, mx])] ++ encodeState s.heap))
    | "r.insertBackedges" => do
      let H ← decHeap (← arg 0)
      let items ← (← (← arg 1).getArr?).toList.mapM decItem
      pure (runVM H (insertBackedges O vfuel items) fun _ s => Json.mkObj (encodeState s.heap))
    | op => throw s!"unknown op {op}"
  return (got, exp, paths)

end ReinferDiff
/-! ## Dominator-tree cases (`difftest/compiler/domtree.jl`)

A case is `{"id": k, "dt": "<op>", ..., "exp": <json>}`; the model's result is built as JSON in
the same shape `difftest/compiler/common.jl` (`CFGSer`) writes and compared with `exp` by
`Json` equality. -/

namespace Domtree

open JuliaLean.Compiler.ssair

def jint (i : Int) : Json := Json.num (Lean.JsonNumber.fromInt i)
def jints (a : Array Int) : Json := Json.arr (a.map jint)

def errJson (e : String) : Json :=
  match e.splitOn ":" with
  | "julia" :: exc :: _ => Json.mkObj [("err", Json.str exc)]
  | _ => Json.mkObj [("fail", Json.str e)]

def ofJM {α : Type} (f : α → Json) : JM α → Json
  | .ok a => f a
  | .error e => errJson e

def decodeInts (j : Json) : Except String (Array Int) := do
  (← j.getArr?).mapM Json.getInt?

def decodeBlocks (j : Json) : Except String Blocks := do
  (← j.getArr?).mapM fun b => do
    let b ← b.getArr?
    pure { preds := ← decodeInts b[0]!, succs := ← decodeInts b[1]! }

def encodeBlocks (bs : Blocks) : Json :=
  Json.arr (bs.map fun b => Json.arr #[jints b.preds, jints b.succs])

/-- The observable state of a dominator tree. `to_post` is `null` where `to_pre` is 0 (Julia
leaves it stale or undefined there), and `from_post` is cut to `length(from_pre)` (the
post-dominator tree's extra slot is undefined). -/
def encodeState (dt : GenericDomTree) : Json :=
  let D := dt.dfsTree
  let post := (Array.range D.toPost.size).map fun i =>
    match D.toPre[i]? with
    | some p => if p != 0 then jint D.toPost[i]! else Json.null
    | none => Json.null
  Json.mkObj [
    ("pre", jints D.toPre), ("fpre", jints D.fromPre), ("par", jints D.toParentPre),
    ("post", Json.arr post), ("fpost", jints (D.fromPost.extract 0 D.fromPre.size)),
    ("semi", Json.arr (dt.sncaState.map fun s => Json.arr #[jint s.semi, jint s.label])),
    ("idom", jints dt.idomsBB),
    ("nodes", Json.arr (dt.nodes.map fun n => Json.arr #[jint n.level, jints n.children]))]

def pairs (j : Json) : Except String (Array (Int × Int)) := do
  (← j.getArr?).mapM fun p => do
    let p ← p.getArr?
    pure (← p[0]!.getInt?, ← p[1]!.getInt?)

def queries (dt : GenericDomTree) (j : Json) (withDominated : Bool) :
    Except String (List (String × Json)) := do
  let q ← pairs (← getK j "q")
  let nq ← pairs (← getK j "nq")
  let dom := q.map fun (a, b) => ofJM Json.bool (dominates dt a b)
  let nca := nq.map fun (a, b) => ofJM jint (nearestCommonDominator dt a b)
  let mut out := [("st", encodeState dt), ("dom", Json.arr dom), ("nca", Json.arr nca)]
  if withDominated then
    let roots ← decodeInts (← getK j "roots")
    let dd := roots.map fun r => ofJM jints (dominated dt r)
    let unr := (irange 1 dt.dfsTree.toPre.size).toArray.map fun b =>
      ofJM Json.bool (bbUnreachable dt b)
    out := out ++ [("dd", Json.arr dd), ("unr", Json.arr unr)]
  return out

/-- One `seq` step: the CFG edit of `ir.jl`, then the matching dynamic domtree update. -/
def step (bs : Blocks) (dt : GenericDomTree) (k : String) (f t : Int) :
    JM (Blocks × GenericDomTree) := do
  if k == "ins" then
    let bs ← cfgInsertEdge bs f t
    pure (bs, ← domtreeInsertEdge! dt bs f t)
  else
    let bs ← cfgDeleteEdge bs f t
    pure (bs, ← domtreeDeleteEdge! dt bs f t)

def runSeq (j : Json) : Except String Json := do
  let bs ← decodeBlocks (← getK j "b")
  let steps ← (← (← getK j "steps").getArr?).mapM fun s => do
    let s ← s.getArr?
    pure (← s[0]!.getStr?, ← s[1]!.getInt?, ← s[2]!.getInt?)
  match constructDomtree bs with
  | .error e => return Json.mkObj [("states", Json.arr #[errJson e])]
  | .ok dt =>
    let mut states := #[encodeState dt]
    let mut cur := (bs, dt)
    let mut failed := false
    for (k, f, t) in steps do
      match step cur.1 cur.2 k f t with
      | .ok c => cur := c; states := states.push (encodeState c.2)
      | .error e => states := states.push (errJson e); failed := true; break
    if failed then return Json.mkObj [("states", Json.arr states)]
    return Json.mkObj ([("states", Json.arr states)] ++ (← queries cur.2 j false))

def run (j : Json) : Except String Json := do
  let op ← (← getK j "dt").getStr?
  match op with
  | "dom" | "pdom" =>
    let bs ← decodeBlocks (← getK j "b")
    let r := if op == "dom" then constructDomtree bs else constructPostdomtree bs
    match r with
    | .error e => return errJson e
    | .ok dt => return Json.mkObj (← queries dt j (op == "dom"))
  | "seq" => runSeq j
  | "naive" =>
    let bs ← decodeBlocks (← getK j "b")
    let post ← getBool j "post"
    return ofJM jints (naiveIdoms bs post)
  | "kill" =>
    let bs ← decodeBlocks (← getK j "b")
    let f ← getInt j "f"
    let t ← getInt j "t"
    let cb : Blocks → Int → Int → Array Json → JM (Array Json) :=
      fun _ a b acc => pure (acc.push (Json.arr #[jint a, jint b]))
    return ofJM (fun (r : Blocks × Array Json) =>
        Json.mkObj [("b", encodeBlocks r.1), ("cb", Json.arr r.2)])
      (killEdge cb (edgeCount bs + 1) bs f t #[])
  | "rename" =>
    let bs ← decodeBlocks (← getK j "b")
    let r ← decodeInts (← getK j "r")
    return ofJM encodeState (do renameNodes! (← constructDomtree bs) r)
  | op => throw s!"unknown domtree op {op}"

end Domtree

/-! ## Escape-analysis cases (`difftest/compiler/escape.jl`)

A case is `{"id": k, "ea": "<op>", ..., "exp": <json>}`, built and compared like the dominator
cases. The encoding is the one `EscSer` in `difftest/compiler/common.jl` writes. -/

namespace Escape

open JuliaLean.Compiler.ssair JuliaLean.Compiler.ssair.EA
open Domtree (jint jints errJson)

def decInts (j : Json) : Except String (List Int) := do
  return (← (← j.getArr?).toList.mapM Json.getInt?)

def encSet (s : List Int) : Json := Json.arr ((IntSet.norm s).map jint).toArray

def decTSet (j : Json) : Except String TSet := do
  if let .ok s := j.getStr? then
    if s == "B" then return .bot
    if s == "T" then return .top
    throw s!"bad thrown {s}"
  return .fresh (IntSet.norm (← decInts j))

def encTSet : TSet → Json
  | .bot => Json.str "B"
  | .top => Json.str "T"
  | .fresh s => encSet s

def decAlias (j : Json) : Except String AliasInfo := do
  if let .ok b := j.getBool? then return .bool b
  if hasK j "i" then
    return .indexable (← (← (← getK j "i").getArr?).toList.mapM decInts)
  return .unindexable (← decInts (← getK j "u"))

/-- An `AInfo` in iteration order (Julia writes `collect(info)`). -/
def encAInfo (s : AInfo) : Json := Json.arr (s.map jint).toArray

def encAlias : AliasInfo → Json
  | .bool b => Json.bool b
  | .indexable infos => Json.mkObj [("i", Json.arr (infos.map encAInfo).toArray)]
  | .unindexable info => Json.mkObj [("u", encAInfo info)]

/-- A lattice-case `EscapeInfo`; `{"h": k}` is the case's `k`-th fresh `Liveness` set. -/
def decInfo (j : Json) : Except String EscapeInfo := do
  let l ← getK j "l"
  let live ← match l.getStr? with
    | .ok "B" => pure LRef.bot
    | .ok "T" => pure LRef.top
    | .ok "A" => pure LRef.arg
    | .ok s => throw s!"bad live {s}"
    | .error _ => pure (LRef.ref (← getNat l "h"))
  return ⟨← getBool j "a", ← getBool j "r", ← decTSet (← getK j "t"), ← decAlias (← getK j "al"),
    live⟩

/-- The output `Liveness`: a constant, `{"x":1}`/`{"y":1}` when it is the same object as the
`Liveness` of input `x`/`y`, else the contents. -/
def encLive (h : Heap) (x y : Option LRef) (r : LRef) : Json :=
  match r with
  | .bot => Json.str "B"
  | .top => Json.str "T"
  | .arg => Json.str "A"
  | .ref _ =>
    if some r == x then Json.mkObj [("x", jint 1)]
    else if some r == y then Json.mkObj [("y", jint 1)]
    else encSet (h.get r)

def encInfo (h : Heap) (x y : Option LRef) (i : EscapeInfo) : Json :=
  Json.mkObj [("a", Json.bool i.analyzed), ("r", Json.bool i.returnEscape),
    ("t", encTSet i.thrown), ("al", encAlias i.alias), ("l", encLive h x y i.live)]

def jbool (b : Bool) : Json := Json.bool b

def ofJMv {α : Type} (f : α → Json) (r : JM α) : Json :=
  match r with
  | .ok a => Json.mkObj [("v", f a)]
  | .error e => errJson e

def lattice (j : Json) : Except String Json := do
  let op ← (← getK j "o").getStr?
  let sets ← (← (← getK j "h").getArr?).mapM fun a => do return IntSet.norm (← decInts a)
  let h : Heap := ⟨sets⟩
  let x ← decInfo (← getK j "x")
  let y ← decInfo (← getK j "y")
  let pc ← getInt j "pc"
  match op with
  | "eq" => return Json.mkObj [("v", jbool (eqE h x y))]
  | "sq" => return ofJMv jbool (sqsub h x y)
  | "sqs" => return ofJMv jbool (sqsubStrict h x y)
  | "ntsq" => return ofJMv jbool (sqsubNe h x y)
  | "join" =>
    let (r, h') := join h x y
    return Json.mkObj [("v", encInfo h' (some x.live) (some y.live) r)]
  | "q" =>
    let (ia, h') := ignoreArgescape h x
    let qs := [jbool (hasNoEscape h x), jbool (hasArgEscape h x), jbool (hasReturnEscape x),
      jbool (hasReturnEscapeAt h x pc), jbool (hasThrownEscape x), jbool (hasThrownEscapeAt x pc),
      ofJMv jbool (hasAllEscape h x), jint (argEscapeInfo x).toNat, jbool (hasNoEscape h' ia)]
    let lx := some x.live
    let igs := [encInfo h' lx none ia, encInfo h lx none (ignoreThrownescapes x),
      encInfo h lx none (ignoreAliasinfo x), encInfo h lx none (ignoreLiveness x)]
    return Json.mkObj [("v", Json.arr qs.toArray), ("ig", Json.arr igs.toArray)]
  | "mai" => return Json.mkObj [("v", encAlias (mergeAliasInfo x.alias y.alias))]
  | "fi" =>
    let bits := UInt8.ofNat (← getNat j "bits")
    let (r, h') := fromInterprocedural h bits pc
    return Json.mkObj [("v", encInfo h' none none r),
      ("b", Json.arr #[jbool (aHasNoEscape bits), jbool (aHasAllEscape bits),
        jbool (aHasReturnEscape bits), jbool (aHasThrownEscape bits)])]
  | op => throw s!"unknown escape lattice op {op}"

def decOpnd (j : Json) : Except String Opnd := do
  if let .ok s := j.getStr? then
    match s with
    | "g" => return .gref
    | "t" => return .tupleExpr
    | "o" => return .other
    | _ => throw s!"bad operand {s}"
  if hasK j "a" then return .arg (← getNat j "a")
  return .ssa (← getNat j "s")

def decOpnds (j : Json) : Except String (Array Opnd) := do (← j.getArr?).mapM decOpnd

def decOptNat (j : Json) : Except String (Option Nat) :=
  if j.isNull then pure none else some <$> j.getNat?

def decOptOpnd (j : Json) : Except String (Option Opnd) :=
  if j.isNull then pure none else some <$> decOpnd j

def decStmt (j : Json) : Except String Stmt := do
  let k ← (← getK j "k").getStr?
  match k with
  | "call" =>
    let fkj ← (← getK j "fk").getStr?
    let fk := match fkj with | "i" => FKind.intrinsic | "o" => .other | n => .builtin n
    let cc ← getK j "cc"
    let condConst ← if cc.isNull then pure none else some <$> cc.getBool?
    return .call (← decOpnds (← getK j "a"))
      { fk, modint := ← getBool j "mi", onflds := ← decOptNat (← getK j "of"),
        ofidx := ← decOptNat (← getK j "ox"), sfNothrow := ← getBool j "sn", condConst }
  | "inv" =>
    let c ← getK j "c"
    let cache ← match c.getBool? with
      | .ok b => pure (Cache.bool b)
      | .error _ => do
        let bits ← (← (← getK c "e").getArr?).mapM fun b => do return UInt8.ofNat (← b.getNat?)
        let al ← (← (← getK c "al").getArr?).toList.mapM fun p => do
          let p ← p.getArr?
          return (← p[0]!.getNat?, ← p[1]!.getNat?)
        pure (Cache.cache bits al)
    return .invoke (← decOpnds (← getK j "a")) cache (← getNat j "mn")
  | "new" => return .new (← decOpnds (← getK j "a"))
  | "fc" =>
    let aa ← getK j "aa"
    let argAny ← if aa.isNull then pure none else
      some <$> (← aa.getArr?).toList.mapM Json.getBool?
    return .foreigncall (← decOpnds (← getK j "a")) argAny
  | "fg" => return .foreignglobal (← decOpnds (← getK j "a"))
  | "tu" => return .throwUndefIfNot (← decOpnds (← getK j "a"))
  | "gpe" =>
    let b ← getK j "b"
    return .gcPreserveEnd (← if b.isNull then pure none else some <$> decOpnds b)
  | "cons" => return .conservative (← decOpnds (← getK j "a"))
  | "skip" => return .skip
  | "noop" => return .noop
  | "enter" =>
    let l ← getK j "l"
    return .enter (← if l.isNull then pure none else some <$> l.getInt?)
  | "ret" => return .ret (← decOptOpnd (← getK j "v"))
  | "phi" => return .phi (← (← (← getK j "v").getArr?).toList.mapM decOptOpnd)
  | "val" => return .val (← decOptOpnd (← getK j "v"))
  | "gl" => return .globalLoad
  | k => throw s!"bad stmt kind {k}"

def decIR (j : Json) : Except String IR := do
  let insts ← (← (← getK j "st").getArr?).mapM fun i => do
    return ({ stmt := ← decStmt (← getK i "s"), idfree := ← getBool i "f",
              nothrow := ← getBool i "n", nflds := ← decOptNat (← getK i "nf") } : Inst)
  let argIdfree ← (← (← getK j "ai").getArr?).mapM Json.getBool?
  return ⟨insts, ← getNat j "nargs", argIdfree⟩

def encNats (l : List Nat) : Json := Json.arr (l.map fun (n : Nat) => jint (n : Int)).toArray

/-- The alias partition: each set of size > 1 as its sorted members, sets ordered by their
least member. -/
def partition (s : IntDisjointSet) : JM Json := do
  let mut s := s
  let mut roots : Array Int := #[]
  for i in List.range s.parents.size do
    let (s', r) ← s.findRoot (i + 1)
    s := s'
    roots := roots.push r
  let groups := (List.range roots.size).filterMap fun i =>
    let r := roots[i]!
    let mem := (List.range roots.size).filter fun k => roots[k]! == r
    if mem.length > 1 && mem.head? == some i then some (mem.map (· + 1)) else none
  return Json.arr (groups.map encNats).toArray

def irCase (j : Json) : Except String Json := do
  let ir ← decIR j
  match analyzeEscapes ir with
  | .error e => return errJson e
  | .ok (estate, h) =>
    let es := estate.escapes.map (encInfo h none none)
    let part := match partition estate.aliasset with
      | .ok p => p
      | .error e => errJson e
    let ac := match argEscapeCache estate with
      | .ok (bits, al) => Json.mkObj [("e", Json.arr (bits.map fun b => jint b.toNat).toArray),
          ("al", Json.arr (al.map fun (a, b) => Json.arr #[jint a, jint b]).toArray)]
      | .error e => errJson e
    let mut st := estate
    let mut ga : Array Json := #[]
    for i in List.range estate.escapes.size do
      match getaliases st (i + 1) with
      | .ok (st', r) =>
        st := st'
        ga := ga.push (match r with | none => Json.null | some l => encNats l)
      | .error e => ga := ga.push (errJson e)
    return Json.mkObj [("es", Json.arr es), ("part", part), ("par", jints estate.aliasset.parents),
      ("rk", jints estate.aliasset.ranks), ("ac", ac), ("ga", Json.arr ga)]

def run (j : Json) : Except String Json := do
  match ← (← getK j "ea").getStr? with
  | "lat" => lattice j
  | "ir" => irCase j
  | op => throw s!"unknown escape op {op}"

end Escape

/-! ## `slot2ssa.jl` cases (`difftest/compiler/slot2ssa.jl`)

A case is `{"id": k, "s2s": "<op>", ..., "exp": <json>}`. IR values use the encoding of
`enc` in `difftest/compiler/slot2ssa.jl`; results are compared by `Json` equality, as for the
dominator-tree cases. -/

namespace S2S

open JuliaLean.Compiler.ssair
open Domtree (jint jints errJson ofJM decodeInts)

partial def decIRV (j : Json) : Except String IRV := do
  if let .ok s := j.getStr? then
    if s == "nothing" then return .nothing
    if s == "undef" then return .undefTok
    throw s!"bad IRV string {s}"
  let opt (k : String) : Except String (Option IRV) :=
    match j.getObjVal? k with
    | .ok v => some <$> decIRV v
    | .error _ => pure none
  let optVals (a : Json) : Except String (Array (Option IRV)) := do
    (← a.getArr?).mapM fun v => if v.isNull then pure none else some <$> decIRV v
  if hasK j "sl" then return .slot (← getInt j "sl")
  if hasK j "s" then return .ssa (← getInt j "s")
  if hasK j "ns" then return .newssa (← getInt j "ns")
  if hasK j "a" then return .arg (← getInt j "a")
  if hasK j "g" then return .glob (← (← getK j "g").getStr?)
  if hasK j "sym" then return .sym (← (← getK j "sym").getStr?)
  if hasK j "l" then return .lit (← (← getK j "l").getStr?)
  if hasK j "q" then return .quot (← (← getK j "q").getStr?)
  if hasK j "e" then
    return .expr (← (← getK j "e").getStr?) (← (← (← getK j "x").getArr?).mapM decIRV)
  if hasK j "goto" then return .goto (← getInt j "goto")
  if hasK j "gin" then return .gotoifnot (← decIRV (← getK j "gin")) (← getInt j "d")
  if hasK j "ret" then return .ret (some (← decIRV (← getK j "ret")))
  if hasK j "ret0" then return .ret none
  if hasK j "enter" then return .enter (← getInt j "enter") (← opt "sc")
  if hasK j "nv" then return .newvar (← getInt j "nv")
  if hasK j "phi" then return .phi (← decodeInts (← getK j "phi")) (← optVals (← getK j "v"))
  if hasK j "phic" then return .phic (← optVals (← getK j "phic"))
  if hasK j "ups" then return .upsilon (some (← decIRV (← getK j "ups")))
  if hasK j "ups0" then return .upsilon none
  if hasK j "pi" then return .pinode (← decIRV (← getK j "pi")) (← (← getK j "t").getStr?)
  throw s!"bad IRV {j.compress}"

partial def encIRV : IRV → Json
  | .nothing => Json.str "nothing"
  | .undefTok => Json.str "undef"
  | .slot n => Json.mkObj [("sl", jint n)]
  | .ssa n => Json.mkObj [("s", jint n)]
  | .newssa n => Json.mkObj [("ns", jint n)]
  | .arg n => Json.mkObj [("a", jint n)]
  | .glob g => Json.mkObj [("g", Json.str g)]
  | .sym x => Json.mkObj [("sym", Json.str x)]
  | .lit x => Json.mkObj [("l", Json.str x)]
  | .quot x => Json.mkObj [("q", Json.str x)]
  | .expr h args => Json.mkObj [("e", Json.str h), ("x", Json.arr (args.map encIRV))]
  | .goto l => Json.mkObj [("goto", jint l)]
  | .gotoifnot c d => Json.mkObj [("gin", encIRV c), ("d", jint d)]
  | .ret (some v) => Json.mkObj [("ret", encIRV v)]
  | .ret none => Json.mkObj [("ret0", Json.bool true)]
  | .enter cd (some sc) => Json.mkObj [("enter", jint cd), ("sc", encIRV sc)]
  | .enter cd none => Json.mkObj [("enter", jint cd)]
  | .newvar n => Json.mkObj [("nv", jint n)]
  | .phi e v => Json.mkObj [("phi", jints e),
      ("v", Json.arr (v.map fun o => match o with | some x => encIRV x | none => Json.null))]
  | .phic v => Json.mkObj
      [("phic", Json.arr (v.map fun o => match o with | some x => encIRV x | none => Json.null))]
  | .upsilon (some v) => Json.mkObj [("ups", encIRV v)]
  | .upsilon none => Json.mkObj [("ups0", Json.bool true)]
  | .pinode v t => Json.mkObj [("pi", encIRV v), ("t", Json.str t)]

def decCFG (j : Json) : Except String SCFG := do
  let bs ← (← (← getK j "b").getArr?).mapM fun b => do
    let b ← b.getArr?
    pure ({ first := ← b[0]!.getInt?, last := ← b[1]!.getInt?, preds := ← decodeInts b[2]!,
            succs := ← decodeInts b[3]! } : SBlock)
  pure ⟨bs, ← decodeInts (← getK j "idx")⟩

def encCFG (cfg : SCFG) : List (String × Json) :=
  [("b", Json.arr (cfg.blocks.map fun b =>
      Json.arr #[jint b.first, jint b.last, jints b.preds, jints b.succs])),
   ("idx", jints cfg.index)]

def encIR (ir : SIR) : Json :=
  Json.mkObj ([("stmts", Json.arr (ir.stmts.map encIRV)),
    ("nn", Json.arr (ir.newNodes.map fun n =>
      Json.arr #[jint n.pos, Json.bool n.attachAfter, encIRV n.stmt]))] ++ encCFG ir.cfg)

def decBools (j : Json) : Except String (Array Bool) := do (← j.getArr?).mapM Json.getBool?

def decInputs (j : Json) : Except String SSAInputs := do
  let bbs ← (← (← getK j "bbs").getArr?).mapM fun b => do
    if b.isNull then return none
    some <$> (← b.getArr?).mapM fun v => do
      let v ← v.getArr?
      pure ({ bottom := ← v[0]!.getBool?, undef := ← v[1]!.getBool?, typ := ← v[2]!.getStr?,
              needPi := ← v[3]!.getBool? } : VarIn)
  let sp ← (← (← getK j "sp").getArr?).mapM fun v =>
    if v.isNull then pure none else some <$> decIRV v
  pure { nargs := ← getInt j "nargs",
         slotnames := ← (← (← getK j "names").getArr?).mapM Json.getStr?,
         bbStates := bbs, handler := ← decodeInts (← getK j "h"), sp }

def encSlotInfos (r : Array SlotInfo) : Json :=
  Json.arr (r.map fun si => Json.arr #[jints si.defs, jints si.uses])

def run (j : Json) : Except String Json := do
  let op ← (← getK j "s2s").getStr?
  match op with
  | "ssa" =>
    let code ← (← (← getK j "code").getArr?).mapM decIRV
    let ir : SIR := { stmts := code, nothrow := ← decBools (← getK j "nt"), cfg := ← decCFG j,
                      newNodes := #[] }
    let I ← decInputs j
    return ofJM encIR (slot2regSsa I ir)
  | "dsort" =>
    let code ← (← (← getK j "code").getArr?).mapM decIRV
    let nn ← (← (← getK j "nn").getArr?).mapM fun x => do
      let x ← x.getArr?
      pure ({ pos := ← x[0]!.getInt?, attachAfter := ← x[1]!.getBool?, stmt := ← decIRV x[2]! } :
        NewNode)
    let ir : SIR := { stmts := code, nothrow := ← decBools (← getK j "nt"), cfg := ← decCFG j,
                      newNodes := nn }
    return ofJM encIR (do domsortSsa! ir (← constructDomtree ir.cfg.domBlocks))
  | "fixup" =>
    let code ← (← (← getK j "code").getArr?).mapM decIRV
    let ir : SIR := { stmts := code, nothrow := ← decBools (← getK j "nt"), cfg := ← decCFG j,
                      newNodes := #[] }
    let sp ← (← (← getK j "sp").getArr?).mapM fun v =>
      if v.isNull then pure none else some <$> decIRV v
    let C : FixCtx := ⟨← (← (← getK j "names").getArr?).mapM Json.getStr?, sp⟩
    return ofJM (fun (r : SIR × Array IRV) => encIR { r.1 with stmts := r.2 })
      (fixupUses! C ir code (← decodeInts (← getK j "uses")) (← getInt j "slot")
        (← decIRV (← getK j "ssa")))
  | "scan" =>
    let code ← (← (← getK j "code").getArr?).mapM decIRV
    return ofJM encSlotInfos (scanSlotDefUse (← getInt j "nargs") (← getNat j "nslots") code)
  | "live" =>
    let cfg ← decCFG j
    return ofJM (fun (l : BlockLiveness) => Json.mkObj [("d", jints l.defBBs),
        ("l", match l.liveInBBs with | some x => jints x | none => Json.null)])
      (computeLiveIns cfg (← decodeInts (← getK j "defs")) (← decodeInts (← getK j "uses")))
  | "idf" =>
    let cfg ← decCFG j
    let live ← getK j "live"
    let li ← if live.isNull then pure none else some <$> decodeInts live
    let lv : BlockLiveness := ⟨← decodeInts (← getK j "defs"), li⟩
    return ofJM jints (do iteratedDominanceFrontier cfg lv (← constructDomtree cfg.domBlocks))
  | "redge" =>
    let ro ← decodeInts (← getK j "ro")
    let br ← decodeInts (← getK j "br")
    let a ← getInt j "x"
    let b ← getInt j "y"
    match ← (← getK j "k").getStr? with
    | "in" => return ofJM jint (renameIncomingEdge a b ro br)
    | "out" => return ofJM jint (renameOutgoingEdge a b ro br)
    | _ =>
      let p ← decIRV (← getK j "p")
      match p with
      | .phi e v => return ofJM encIRV (renamePhinodeEdges e v a ro br)
      | _ => throw "redge: not a phi"
  | "bfi" =>
    let cfg ← decCFG j
    let qs ← decodeInts (← getK j "q")
    return Json.arr (qs.map fun q => ofJM jint (blockForInst cfg q))
  | op => throw s!"unknown slot2ssa op {op}"

end S2S

end CompilerDiff

open CompilerDiff in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut E : CEnv := default
  let mut tns : List (String × TnInfo) := []
  let mut R : ReinferDiff.Tables := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    if line.all Char.isWhitespace then continue
    match Json.parse line with
    | .error e => stdout.putStrLn (Json.mkObj [("error", s!"parse: {e}")]).compress
    | .ok j =>
      if hasK j "dt" || hasK j "ea" || hasK j "s2s" then
        let id := (j.getObjVal? "id").toOption.getD Json.null
        match (if hasK j "ea" then Escape.run j else if hasK j "s2s" then S2S.run j
            else Domtree.run j), getK j "exp" with
        | .ok got, .ok exp =>
          if got == exp then
            stdout.putStrLn (Json.mkObj [("id", id), ("agree", true)]).compress
          else
            stdout.putStrLn (Json.mkObj [("id", id), ("agree", false), ("unmodelled", false),
              ("got", got), ("exp", exp)]).compress
        | .error e, _ | _, .error e =>
          stdout.putStrLn (Json.mkObj [("id", id), ("error", e)]).compress
      else if let .ok u := j.getObjVal? "U" then
        match decodeUniverse E u with
        | .ok E' => E := E'
        | .error e => stdout.putStrLn (Json.mkObj [("error", s!"universe: {e}")]).compress
      else if let .ok u := j.getObjVal? "TF" then
        match decodeTns u with
        | .ok t => tns := tns ++ t
        | .error e => stdout.putStrLn (Json.mkObj [("error", s!"tns: {e}")]).compress
      else if let .ok r := j.getObjVal? "R" then
        match ReinferDiff.addTables R r with
        | .ok R' => R := R'
        | .error e => stdout.putStrLn (Json.mkObj [("error", s!"tables: {e}")]).compress
      else
        let id := (j.getObjVal? "id").toOption.getD Json.null
        let op := (j.getObjVal? "op" >>= Json.getStr?).toOption.getD ""
        let isTf := op.startsWith "tf."
        let isR := op.startsWith "r."
        let isCr := op.startsWith "cr."
        let res := if isR then ReinferDiff.reinferCase R j
          else (fun (g, e) => (g, e, ([] : List String))) <$>
            (if isTf then tfuncsCase { E, tns } j
             else if isCr then cacheresultCase { E, tns } j else runCase E j)
        match res with
        | .error e => stdout.putStrLn (Json.mkObj [("id", id), ("error", e)]).compress
        | .ok (got, exp, paths) =>
          if (if isTf then agreeScoped got exp else agree got exp) then
            let extra := if paths.isEmpty then [] else [("paths", Json.arr (paths.map Json.str).toArray)]
            stdout.putStrLn (Json.mkObj ([("id", id), ("agree", true)] ++ extra)).compress
          else
            let unm := match got with | .fail m => m.startsWith "unmodelled" | _ => false
            stdout.putStrLn (Json.mkObj [("id", id), ("agree", false), ("unmodelled", unm),
              ("got", got.toJson), ("exp", exp.toJson)]).compress
    stdout.flush
  return 0
