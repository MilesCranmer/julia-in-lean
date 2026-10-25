import JuliaLean.Tuples.NamedTuple
import JuliaLean.Float.Basic

/-!
Deterministic differential corpus for the tuple model. `differential` prints
one line per case; the Julia oracle `repro/tuples-differential.jl` prints the
same cases in the same format, and the two outputs are compared with `diff`.
Integer tuples are `(10, 20, ..., 10n)`; comparison cases use the values
`missing, NaN, -0.0, 0.0, 1.0, 2.0` (`v0`..`v5`). Lean side: `lake env lean` on a
file with `#eval JuliaLean.Tuples.Validation.differential`; Julia side:
`julia repro/tuples-differential.jl`.
-/

namespace JuliaLean.Tuples.Validation

open JuliaLean.Tuples
open JuliaLean.Float

def fmtList {β : Type} (f : β → String) (xs : List β) : String :=
  "[" ++ ",".intercalate (xs.map f) ++ "]"

def fmtR {β : Type} (f : β → String) : R β → String
  | .ok a => f a
  | .error e => "E:" ++ e.kind

def fmtOB : Option Bool → String
  | some true => "true"
  | some false => "false"
  | none => "missing"

def fmtB (b : Bool) : String := if b then "true" else "false"
def fmtI (x : Int) : String := toString x
def fmtJ {t : IntTy} (x : JInt t) : String := toString x.val
def fmtON : Option Nat → String
  | some n => toString n
  | none => "nothing"

def tup (n : Nat) : List Int := (List.range n).map fun (k : Nat) => 10 * ((k : Int) + 1)

def allTys : List IntTy := [.i8, .i16, .i32, .i64, .i128, .u8, .u16, .u32, .u64, .u128]

def candidates (t : IntTy) (len : Nat) : List Int :=
  ([t.min, t.max, -1, 0, 1, 2, (len : Int), (len : Int) + 1].filter fun x => t.min ≤ x ∧ x ≤ t.max).eraseDups

def idxLine (len : Nat) (i : Idx) (name : String) : String :=
  let t := tup len
  s!"IDX {len} {name} {fmtI i.val} => get:{fmtR fmtI (getindex t i)} set:{fmtR (fmtList fmtI) (setindex t 0 i)} getd:{fmtR fmtI (get t i (-1))} isas:{fmtR fmtB (isassigned t i)}"

def indexCases : List String := Id.run do
  let mut out := []
  for len in [0, 1, 3] do
    for t in allTys do
      for x in candidates t len do
        out := out ++ [idxLine len (.int t (JInt.lit t x)) t.name]
    for b in [false, true] do
      out := out ++ [idxLine len (.bool b) "Bool"]
  return out

def rangeEnds (len : Nat) : List Int :=
  ([-1, 0, 1, 2, 3, (len : Int) - 2, (len : Int) - 1, len, (len : Int) + 1, (len : Int) + 2]).eraseDups

def rangeCases : List String := Id.run do
  let mut out := []
  for len in [0, 1, 3, 11, 12, 13, 33] do
    for a in rangeEnds len do
      for b in rangeEnds len do
        let r := getindexColon (tup len) (JInt.lit .i64 a) (JInt.lit .i64 b)
        out := out ++ [s!"RNG {len} {a} {b} => {fmtR (fmtList fmtI) r}"]
  for len in [0, 1, 2, 3] do
    for (lo, n) in [(false, 1), (false, 2), (true, 0), (true, 1)] do
      let r := getindexBoolRange (tup len) lo n
      let l := getindexLogical (tup len) (boolRangeValues lo n)
      out := out ++ [s!"BRNG {len} {fmtB lo} {n} => {fmtR (fmtList fmtI) r} | {fmtR (fmtList fmtI) l}"]
  return out

def fmtOpt (o : Option Int) : String := match o with | some x => fmtI x | none => "U"

def fmtNT (nt : NT Int) : String := "(" ++ ",".intercalate (nt.map fun (k, v) => s!"{k}={v}") ++ ")"

def ntOf (names : List String) : NT Int := names.zip ((List.range names.length).map fun (k : Nat) => 10 * ((k : Int) + 1))

def splitCases : List String := Id.run do
  let mut out := []
  for len in [0, 1, 2, 3, 4] do
    for n in [0, 1, 2, 3, 5] do
      for i in (List.range (len + 2)).map (fun (k : Nat) => k + 1) do
        let n' := JInt.lit .i64 n
        let i' := JInt.lit .i64 (i : Int)
        let a := splitRestTuple (tup len) n' i'
        let b := splitRestVector (tup len) n' i'
        let names := (["a", "b", "c", "d"].take len)
        let c := splitRestNT (ntOf names) n' i'
        out := out ++ [s!"SPLIT {len} {n} {i} => {fmtR (fun (x, y) => fmtList fmtI x ++ fmtList fmtI y) a} | {fmtR (fun (x, y) => fmtList fmtOpt x ++ fmtList fmtI y) b} | {fmtR (fun (x, y) => fmtNT x ++ fmtNT y) c}"]
    for i in [0, 1, 2, 3, 4, 5, 6] do
      out := out ++ [s!"REST {len} {i} => {fmtR (fmtList fmtI) (restTuple (tup len) (JInt.lit .i64 i))}"]
    out := out ++ [s!"DESTR {len} => {fmtR (fun (a, b, c) => fmtI a ++ fmtList fmtI b ++ fmtI c) (destructureMid (tup len))}"]
  return out

def ntupleCases : List String := Id.run do
  let mut out := []
  for t in allTys do
    for x in (candidates t 3).filter (fun x => x ≤ 12 ∨ x > IntTy.i64.max) do
      let r := ntuple (fun k => (k : Int)) t (JInt.lit t x)
      let r' := match r with | .ok l => .ok l.length | .error e => .error e
      out := out ++ [s!"NTUP {t.name} {x} => {fmtR toString r'}"]
  for n in [-2, -1, 0, 1, 5, 10, 11, 12] do
    let r := ntupleVal (fun k => (k : Int)) (JInt.lit .i64 n)
    out := out ++ [s!"NTUPV {n} => {fmtR (fmtList fmtI) r}"]
  for len in [0, 1, 2, 3] do
    for n in [-1, 0, 1, 2, 3, 5] do
      out := out ++ [s!"FILL {len} {n} => {fmtR (fmtList fmtI) (fillToLength (tup len) 0 (JInt.lit .i64 n))}"]
  for len in [0, 1, 2, 5, 33] do
    out := out ++ [s!"REV {len} => {fmtList fmtI (revargs (tup len))} {fmtR (fmtList fmtI) (reverseNTuple (tup len))}"]
  for len in [0, 1, 2, 31, 32, 33, 34] do
    out := out ++ [s!"FRONT {len} => {fmtR (fmtList fmtI) (front (tup len))} {fmtR (fmtList fmtI) (tail (tup len))} {fmtR fmtI (first (tup len))} {fmtR fmtI (last (tup len))}"]
  for t in [[], [3], [2, 5], [2, 4611686018427387904, 3]] do
    let t' := t.map (JInt.lit .i64)
    out := out ++ [s!"PROD {fmtList fmtI t} => {fmtR fmtJ (prodTuple t')} {fmtR fmtJ (prodGeneric t')}"]
  return out

def lens : List Nat := [0, 1, 2, 3, 31, 32, 33, 34]
def tupB (n : Nat) : List Int := (List.range n).map fun (k : Nat) => 100 * ((k : Int) + 1)
def tupC (n : Nat) : List Int := (List.range n).map fun (k : Nat) => 1000 * ((k : Int) + 1)
def pat (n : Nat) : List Int := (List.range n).map fun (k : Nat) => ((k : Int) * 7 + 3) % 5

def mapCases : List String := Id.run do
  let mut out := []
  for a in lens do
    out := out ++ [s!"MAP1 {a} => {fmtList fmtI (map1 (· + 1) (tup a))}"]
    for b in lens do
      out := out ++ [s!"MAP2 {a} {b} => {fmtList fmtI (map2 (· + ·) (tup a) (tupB b))}"]
      for c in [0, 2, 33] do
        out := out ++ [s!"MAP3 {a} {b} {c} => {fmtList fmtI (map3 (fun x y z => x + y + z) (tup a) (tupB b) (tupC c))}"]
  for n in [0, 1, 2, 3, 4, 5, 6, 31, 32, 33, 34, 40] do
    let even := fun (x : Int) => x % 2 == 0
    let zero := fun (x : Int) => x == 0
    out := out ++ [s!"FIND {n} => {fmtON (findfirst even (pat n))} {fmtON (findlast even (pat n))} {fmtON (findfirst zero (pat n))} {fmtON (findlast zero (pat n))} {fmtList fmtI (filter even (pat n))}"]
  return out

def fv : List (Option F64) :=
  [none, some F64.nan, some (F64.zero true), some (F64.zero false), some F64.one, some (F64.ofBits 0x4000000000000000)]

def fops : Ops (Option F64) where
  isequal a b := match a, b with
    | none, none => true
    | some x, some y => F64.isequal x y
    | _, _ => false
  isless a b := match a, b with
    | some x, some y => F64.isless x y
    | some _, none => true
    | _, _ => false
  eq a b := match a, b with
    | some x, some y => some (F64.eq x y)
    | _, _ => none
  lt a b := match a, b with
    | some x, some y => some (F64.lt x y)
    | _, _ => none
  hash _ h := h

def smallTuples : List (List Nat) :=
  [[]] ++ (List.range 6).map (fun i => [i]) ++
    ((List.range 6).flatMap fun i => (List.range 6).map fun j => [i, j])

def vals (t : List Nat) : List (Option F64) := t.map fun i => fv.getD i none
def fmtT (t : List Nat) : String := fmtList (fun i => s!"v{i}") t

def cmpCases : List String := Id.run do
  let mut out := []
  for pre in [0, 31] do
    for a in smallTuples do
      for b in smallTuples do
        let x := List.replicate pre (some F64.one) ++ vals a
        let y := List.replicate pre (some F64.one) ++ vals b
        out := out ++ [s!"CMP {pre} {fmtT a} {fmtT b} => {fmtB (isequal fops x y)} {fmtOB (eq fops x y)} {fmtOB (lt fops x y)} {fmtB (isless fops x y)} {cmp fops x y}"]
    for xi in List.range 6 do
      for a in smallTuples do
        let x := fv.getD xi none
        let y := List.replicate pre (some F64.one) ++ vals a
        out := out ++ [s!"IN {pre} v{xi} {fmtT a} => {fmtOB (inTuple fops.eq x y)}"]
  let fl : List (List Nat) := smallTuples.filter fun t => !t.contains 0
  for a in fl do
    for b in fl do
      let x := (vals a).filterMap id
      let y := (vals b).filterMap id
      out := out ++ [s!"FINDIN {fmtT a} {fmtT b} => {fmtList toString (findallIn F64.isequal x y)} {fmtList toString (findallPred F64.eq x y)}"]
  return out

def ntSamples : List (List String) := [[], ["a"], ["b"], ["a", "b"], ["b", "a"], ["a", "b", "c"], ["c", "a"]]
def nameLists : List (List String) := [[], ["a"], ["c"], ["d"], ["a", "b"], ["b", "a"], ["a", "a"], ["c", "d"]]

def keyCases : List (Key × String) :=
  [(.sym "a", "Symbol a"), (.sym "d", "Symbol d")] ++
    ([IntTy.i64, .i32, .u8, .i128].flatMap fun t =>
      [0, 1, 2, 3].map fun x => (Key.int (.int t (JInt.lit t x)), s!"{t.name} {x}")) ++
    [(.int (.bool true), "Bool 1")]

def ntCases : List String := Id.run do
  let mut out := []
  for an in ntSamples do
    let a := ntOf an
    for bn in ntSamples do
      let b : NT Int := bn.zip ((List.range bn.length).map fun (k : Nat) => 100 * ((k : Int) + 1))
      out := out ++ [s!"MERGE {fmtNT a} {fmtNT b} => {fmtNT (merge a b)}"]
    for ks in nameLists do
      out := out ++ [s!"NTSEL {fmtNT a} {fmtList id ks} => {fmtR fmtNT (getindexNames a ks)} {if ks.Nodup then fmtNT (structdiff a ks) else "-"}"]
    for k in ["a", "b", "d"] do
      out := out ++ [s!"NTDEL {fmtNT a} {k} => {fmtR fmtNT (delete a k)} {fmtNT (setindexNT a 7 k)}"]
    for (k, name) in keyCases do
      out := out ++ [s!"HASKEY {fmtNT a} {name} => {fmtR fmtB (haskeyNT a k)} {fmtR fmtI (getNT a k (-1))}"]
  return out

def differential : IO Unit := do
  for l in indexCases ++ rangeCases ++ splitCases ++ ntupleCases ++ mapCases ++ cmpCases ++ ntCases do
    IO.println l

end JuliaLean.Tuples.Validation
