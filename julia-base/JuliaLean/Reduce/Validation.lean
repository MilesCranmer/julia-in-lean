import JuliaLean.Reduce.Props

/-!
Deterministic differential corpus for the reduction models. `differential` holds one
line per case; the Julia oracle `repro/reduce-differential.jl` prints the same cases in
the same format, and the two outputs are compared with `diff`. Inputs come from named
generators (`gen`) evaluated at positions `k = 1..n`; floats are built from fixed bit
patterns. Values print as `Type:value`, floats as `Float64:NaN` or `Float64:0x<bits>`,
errors as `E:<ExceptionType>`, arrays as `<eltype>[mxn][elements]`.
-/

namespace JuliaLean.Reduce.Validation

open JuliaLean.Reduce
open JuliaLean.Float

def errName : Err → String
  | .argumentError => "ArgumentError"
  | .inexactError => "InexactError"
  | .typeError => "TypeError"
  | .methodError => "MethodError"
  | .dimensionMismatch => "DimensionMismatch"

def fmtR {β : Type} (f : β → String) : R β → String
  | .ok a => f a
  | .error e => "E:" ++ errName e

def fmtV : Val → String
  | .int t x => t.name ++ ":" ++ toString x.val
  | .f64 x => if F64.isnan x then "Float64:NaN" else "Float64:0x" ++ String.ofList (Nat.toDigits 16 (F64.toBits x))
  | .bool b => if b then "Bool:true" else "Bool:false"
  | .missing => "missing"

def fmtList {β : Type} (f : β → String) (xs : List β) : String :=
  "[" ++ ",".intercalate (xs.map f) ++ "]"

def tyNames : Ty → List String
  | .int t => [t.name]
  | .f64 => ["Float64"]
  | .bool => ["Bool"]
  | .missing => ["Missing"]
  | .union a b => tyNames a ++ tyNames b
  | .bottom => []

def tyName (t : Ty) : String :=
  match ((tyNames t).eraseDups.mergeSort fun a b => !decide (b < a)) with
  | [] => "Union{}"
  | [x] => x
  | xs => "Union{" ++ ",".intercalate xs ++ "}"

def fmtArr (a : Arr) : String := s!"{tyName a.ty}[{a.m}x{a.n}]{fmtList fmtV a.data}"

def fmtMat (a : Mat Val) : String := s!"[{a.m}x{a.n}]{fmtList fmtV a.data}"

def fmtFind (r : FindRes) : String :=
  fmtArr r.vals ++ " " ++ fmtList (fun (i, j) => s!"({i},{j})") r.idx

def I (t : IntTy) (x : Int) : Val := .int t (JInt.lit t x)
def Fb (bits : Nat) : Val := .f64 (F64.ofBits bits)

/-- `0.1, 1.5, -3.25, 2.0, 0.0, -0.0, NaN, Inf, -Inf, 1e308`. -/
def atom : Nat → Val
  | 0 => Fb 0x3FB999999999999A
  | 1 => Fb 0x3FF8000000000000
  | 2 => Fb 0xC00A000000000000
  | 3 => Fb 0x4000000000000000
  | 4 => Fb 0x0
  | 5 => Fb 0x8000000000000000
  | 6 => Fb 0x7FF8000000000000
  | 7 => Fb 0x7FF0000000000000
  | 8 => Fb 0xFFF0000000000000
  | _ => Fb 0x7FE1CCF385EBC8A0

def cyc (xs : List Nat) (k : Nat) : Val := atom (xs.getD ((k - 1) % xs.length) 0)

def genElt (name : String) (k : Nat) : Val :=
  let ki : Int := k
  match name with
  | "i64" => I .i64 (((k * 37) % 11 : Nat) - 5)
  | "i64big" => I .i64 (IntTy.i64.max - ((k % 3 : Nat) : Int))
  | "i64min" => if k % 2 = 1 then I .i64 IntTy.i64.min else I .i64 (-1)
  | "i8" => if k = 1 then I .i8 127 else if k = 2 then I .i8 (-128) else I .i8 (((k * 77) % 256 : Nat) - 128)
  | "u8" => if k = 1 then I .u8 255 else I .u8 ((k * 97 + 200) % 256 : Nat)
  | "u64" => I .u64 (IntTy.u64.max - ki)
  | "i8small" => I .i8 (((k % 3 : Nat) : Int) - 1)
  | "u8two" => I .u8 2
  | "f64" => cyc [0, 1, 2, 3, 0, 4, 5] k
  | "f64nan" => cyc [1, 6, 5, 7, 4, 8, 3] k
  | "f64z" => cyc [5, 4] k
  | "f64negz" => atom 5
  | "f64big" => atom 9
  | "bool" => .bool (k % 3 = 0)
  | "booltrue" => .bool true
  | "mi" => if k % 4 = 0 then .missing else I .i64 ki
  | "mb" => if k % 3 = 0 then .missing else .bool (k % 3 = 2)
  | "mbf" => if k % 2 = 1 then .missing else .bool false
  | "miss" => .missing
  | "if" => if k % 2 = 1 then I .i64 (3 * ki) else .f64 (F64.ofInt (-ki))
  | _ => .missing

def genTy : String → Ty
  | "i64" | "i64big" | "i64min" => .int .i64
  | "i8" | "i8small" => .int .i8
  | "u8" | "u8two" => .int .u8
  | "u64" => .int .u64
  | "f64" | "f64nan" | "f64z" | "f64negz" | "f64big" => .f64
  | "bool" | "booltrue" => .bool
  | "mi" => .union (.int .i64) .missing
  | "mb" | "mbf" => .union .bool .missing
  | "miss" => .missing
  | "if" => .union (.int .i64) .f64
  | _ => .bottom

def gen (name : String) (n : Nat) : List Val := (List.range n).map fun k => genElt name (k + 1)

def vecGens : List String :=
  ["i64", "i64big", "i64min", "i8", "u8", "u64", "i8small", "u8two", "f64", "f64nan", "f64z",
   "f64negz", "f64big", "bool", "booltrue", "mi", "mb", "mbf", "miss", "if"]

def vecLens : List Nat := [0, 1, 2, 15, 16, 17, 40]

def longGens : List String := ["f64", "f64z", "i8", "u8", "bool", "mi"]

def vecInputs : List (String × Nat) :=
  vecGens.flatMap (fun g => vecLens.map fun n => (g, n)) ++
    longGens.flatMap (fun g => [1025, 2100].map fun n => (g, n))

def inits : List (String × Val) :=
  [("i8_0", I .i8 0), ("i8_m1", I .i8 (-1)), ("u8_0", I .u8 0), ("u8_1", I .u8 1),
   ("i64_0", I .i64 0), ("f_negz", atom 5), ("b_t", .bool true), ("u64_max", I .u64 IntTy.u64.max)]

def fmtPair (p : Val × Val) : String := "(" ++ fmtV p.1 ++ "," ++ fmtV p.2 ++ ")"
def fmtIdx (p : Val × Nat) : String := "(" ++ fmtV p.1 ++ ",Int64:" ++ toString p.2 ++ ")"

def vecCases : List String := Id.run do
  let mut out := []
  for (g, n) in vecInputs do
    let v := gen g n
    let ty := genTy g
    let h := s!"{g} {n} =>"
    out := out ++ [
      s!"SUM {h} {fmtR fmtV (Vec.sum ty v)}",
      s!"PROD {h} {fmtR fmtV (Vec.prod ty v)}",
      s!"MAX {h} {fmtR fmtV (Vec.maximum v)}",
      s!"MIN {h} {fmtR fmtV (Vec.minimum v)}",
      s!"EXTREMA {h} {fmtR fmtPair (Vec.extrema v)}",
      s!"FINDMAX {h} {fmtR fmtIdx (Vec.findmax v)}",
      s!"FINDMIN {h} {fmtR fmtIdx (Vec.findmin v)}",
      s!"MAXABS {h} {fmtR fmtV (Vec.maxAbs ty v)}",
      s!"ANY {h} {fmtR fmtV (Vec.any id v)}",
      s!"ALL {h} {fmtR fmtV (Vec.all id v)}",
      s!"FOLDR {h} {fmtR fmtV (Vec.foldr Val.plus (Vec.emptyPlus ty) v)}"]
    for (iname, init) in inits do
      out := out ++ [
        s!"SUMINIT {iname} {h} {fmtV (Vec.sumInit init v)}",
        s!"PRODINIT {iname} {h} {fmtV (Vec.prodInit init v)}"]
  return out

def boolPat (n : Nat) : List Bool := (List.range n).map fun k => (k + 1) % 3 ≠ 1

def countInits : List (String × Val) :=
  [("i64_0", I .i64 0), ("i8_0", I .i8 0), ("i8_120", I .i8 120), ("u8_250", I .u8 250),
   ("u64_max", I .u64 IntTy.u64.max), ("i64_max", I .i64 IntTy.i64.max), ("f_0", atom 4),
   ("b_t", .bool true)]

def countCases : List String := Id.run do
  let mut out := []
  for n in vecLens ++ [100] do
    for (iname, init) in countInits do
      let xs := boolPat n
      out := out ++ [s!"COUNT {iname} {n} => {fmtR fmtV (Vec.countBoolArray init xs)} {fmtV (Vec.countIter init xs)}"]
  return out

def flattenInputs : List (String × List (List Val)) :=
  [("empty", []), ("one_empty", [[]]), ("two_empty", [[], []]), ("single", [[I .i64 5]]),
   ("mixed", [[], [I .i64 1, I .i64 2], [], [I .i64 3]]),
   ("i8", [[I .i8 100, I .i8 100], [I .i8 100]]),
   ("bool", [[.bool true, .bool true], [.bool true]]),
   ("f64", [[atom 0, atom 0], [atom 0]]),
   ("negz", [[atom 5], [atom 5]]),
   ("wrap", [[I .i64 IntTy.i64.max], [I .i64 1]])]

def flattenCases : List String :=
  flattenInputs.map fun (name, vs) =>
    s!"FLATTEN {name} => {fmtR fmtV (Vec.foldlFlatten Val.addSum Val.firstAddSum vs)}"

def shapes : List (Nat × Nat) := [(0, 0), (0, 3), (3, 0), (1, 1), (1, 20), (2, 3), (20, 2), (3, 2)]

def matGens : List String :=
  ["i64", "i64big", "i8", "u8", "f64", "f64nan", "f64z", "bool", "mi", "mb", "miss", "if"]

def mat (g : String) (m n : Nat) : Mat Val := ⟨m, n, gen g (m * n)⟩

def dimsInits : List (String × Val) :=
  [("i8_0", I .i8 0), ("u8_0", I .u8 0), ("i64_0", I .i64 0), ("f_negz", atom 5)]

def okf (x : Val) : R Val := .ok x

def dimsCases : List String := Id.run do
  let mut out := []
  for g in matGens do
    for (m, n) in shapes do
      let A := mat g m n
      let ty := genTy g
      for d in [1, 2, 3] do
        let h := s!"{g} {m}x{n} {d} =>"
        out := out ++ [
          s!"SUMD {h} {fmtR fmtArr (sumDims okf ty A d)}",
          s!"PRODD {h} {fmtR fmtArr (prodDims okf ty A d)}",
          s!"MAXD {h} {fmtR fmtArr (maxminDims okf true ty A d)}",
          s!"MIND {h} {fmtR fmtArr (maxminDims okf false ty A d)}",
          s!"MAXABSD {h} {fmtR fmtArr (maxAbsDims ty A d)}",
          s!"ANYD {h} {fmtR fmtArr (anyDims id A d)}",
          s!"ALLD {h} {fmtR fmtArr (allDims id A d)}",
          s!"COUNTD i64_0 {h} {fmtR fmtArr (countDims id (I .i64 0) A d)}",
          s!"COUNTD i8_0 {h} {fmtR fmtArr (countDims id (I .i8 0) A d)}",
          s!"FINDMAXD {h} {fmtR fmtFind (findDims id true ty A d)}",
          s!"FINDMIND {h} {fmtR fmtFind (findDims id false ty A d)}"]
        for (iname, init) in dimsInits do
          out := out ++ [s!"MRDI {iname} {h} {fmtR fmtArr (mapreduceDimsInit okf (fun x y => .ok (Val.addSum x y)) 1024 init A d)}"]
  return out

/-- Conversion into the element type `promote_op(+, Int, T)` of an accumulation with an
`Int` `init`. -/
def toInitTy : Val → Val
  | .int _ x => I .i64 x.val
  | .bool b => I .i64 (if b then 1 else 0)
  | v => v

def accGens : List String := ["i64", "i8", "f64", "bool"]

def accCases : List String := Id.run do
  let mut out := []
  for g in accGens do
    for (m, n) in shapes do
      let A := mat g m n
      for d in ([0, 1, 2, 3] : List Int) do
        let h := s!"{g} {m}x{n} {d} =>"
        out := out ++ [
          s!"ACCD none {h} {fmtR fmtMat (accumulateDims Val.plus Val.firstPlus Val.firstPlus none A d)}",
          s!"ACCD i64_10 {h} {fmtR fmtMat (accumulateDims Val.plus toInitTy toInitTy (some (I .i64 10)) A d)}"]
    for n in vecLens do
      let v := gen g n
      for d in ([-1, 0, 1, 2, 3] : List Int) do
        let h := s!"{g} {n} {d} =>"
        out := out ++ [
          s!"ACCV none {h} {fmtR (fmtList fmtV) (accumulateVecDims Val.plus Val.firstPlus Val.firstPlus none v d)}",
          s!"ACCV i64_10 {h} {fmtR (fmtList fmtV) (accumulateVecDims Val.plus toInitTy toInitTy (some (I .i64 10)) v d)}"]
  for g in ["i64", "i64big", "i8", "u8", "bool"] do
    for n in vecLens do
      let v := gen g n
      for d in ([-1, 0, 1, 2] : List Int) do
        out := out ++ [s!"CUMSUM {g} {n} {d} => {fmtR (fmtList fmtV) (cumsumVecDims Val.firstAddSum Val.addSum Val.firstAddSum v d)}"]
  return out

def differential : List String :=
  vecCases ++ countCases ++ flattenCases ++ dimsCases ++ accCases

end JuliaLean.Reduce.Validation
