import JuliaLean.Dicts.Sets

/-!
Deterministic differential corpus for the `Dict`/`Set` model. The Julia oracle
`repro/dicts-differential.jl` draws the same operations from the same LCG,
with keys `struct K; x::Int; end` hashed by five functions (well spread,
`x % 5`, a constant, low/high-bit collisions, groups of four), and prints a
digest of the full table state (size, `ndel`, `count`, `age`, `idxfloor`,
`maxprobe`, every slot byte, key and value, the iteration order) after each
operation. `differential release` prints the same lines; compare with `diff`.
For `release` (1.13.2, no `popcursor`) `pop!(d)` is replaced by `d[k] = v`.
-/

namespace JuliaLean.Dicts.Validation

open JuliaLean.Dicts

inductive Op where
  | set (k v : Nat) | del (k : Nat) | get (k : Nat) | pop (k : Nat) | popd (k d : Nat)
  | getv (k v : Nat) | getf (k v k2 v2 k3 : Nat) | hint (n : Nat) (s : Bool) | empty | filter
  | merge (ps : List (Nat × Nat)) | mergewith (ps : List (Nat × Nat)) | popany

/-- The five key hashes. -/
def hf (f x : Nat) : JInt .u64 :=
  JInt.wrap .u64 <| match f with
    | 0 => (x * 0x9E3779B97F4A7C15) % 2 ^ 64
    | 1 => x % 5
    | 2 => 0x1234
    | 3 => (x % 3) * 2 ^ 60 + x % 7
    | _ => ((x / 4) * 0x9E3779B97F4A7C15) % 2 ^ 64

def kops (f : Nat) : KeyOps Nat := { hash := hf f, eq := fun a b => a == b }

/-- Replace the closure chains of `slots`/`keys`/`vals` by arrays (same values). -/
def mat {V : Type} (t : Table Nat V) : Table Nat V :=
  let n := t.size + 2
  let sa := ((List.range n).map t.slots).toArray
  let ka := ((List.range n).map t.keys).toArray
  let va := ((List.range n).map t.vals).toArray
  { t with slots := fun i => sa.getD i 0, keys := fun i => ka.getD i none,
           vals := fun i => va.getD i none }

def modulus : Nat := 2305843009213693951
def mix (h x : Nat) : Nat := (h * 1000003 + x) % modulus

def digest {V : Type} (t : Table Nat V) (val : V → Nat) (res : Nat) : Nat :=
  let h := [t.size, t.ndel, t.count, t.age.val.toNat, t.idxfloor, t.maxprobe, res].foldl mix 0
  let h := (List.range t.size).foldl (fun h i =>
    let i := i + 1
    let h := mix h (t.slots i)
    if isFilledB (t.slots i) then
      match t.keys i, t.vals i with
      | some k, some v => mix (mix h (k + 1)) (val v + 1)
      | _, _ => mix h 999
    else h) h
  match iterList t with
  | .ok xs => xs.foldl (fun h kv => mix h (kv.1 + 7)) h
  | .error _ => mix h 31337

/-- The LCG `s = s * 6364136223846793005 + 1442695040888963407` (mod 2^64);
a draw below `n` is `(s >> 33) % n`. -/
abbrev Gen := StateM Nat

def rnd (n : Nat) : Gen Nat := do
  let s := ((← get) * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  set s
  pure (s / 2 ^ 33 % n)

def rndPairs (m : Nat) : Gen (List (Nat × Nat)) := do
  let mut ps := []
  for _ in [:m] do
    let k ← rnd 41
    let v ← rnd 1000
    ps := ps ++ [(k, v)]
  pure ps

def hints : List Nat := [0, 3, 10, 20, 40, 100, 300]

def genOp (release : Bool) : Gen Op := do
  let r ← rnd 100
  let k ← rnd 41
  if r < 35 then return .set k (← rnd 1000)
  if r < 55 then return .del k
  if r < 62 then return .get k
  if r < 67 then return .pop k
  if r < 70 then return .popd k (← rnd 1000)
  if r < 74 then return .getv k (← rnd 1000)
  if r < 80 then
    let v ← rnd 1000
    let k2 ← rnd 41
    let v2 ← rnd 1000
    let k3 ← rnd 41
    return .getf k v k2 v2 k3
  if r < 84 then
    let n := hints.getD (← rnd 7) 0
    let s ← rnd 2
    return .hint n (s == 1)
  if r < 85 then return .empty
  if r < 88 then return .filter
  if r < 91 then return .merge (← rndPairs (← rnd 13))
  if r < 94 then return .mergewith (← rndPairs (← rnd 13))
  if r < 97 then
    if release then return .set k (← rnd 1000) else return .popany
  return .set k (← rnd 1000)

def build (f : Nat) (ps : List (Nat × Nat)) : DR (Table Nat Nat) :=
  ps.foldlM (fun t kv => setindex (kops f) t kv.2 kv.1) Table.empty

def step (f : Nat) (t : Table Nat Nat) : Op → DR (Nat × Table Nat Nat)
  | .set k v => do pure (0, ← setindex (kops f) t v k)
  | .del k => do pure (0, ← dictDelete (kops f) t k)
  | .get k => do
    match ← dictGet (kops f) t k with
    | none => pure (1, t)
    | some v => pure (v + 2, t)
  | .pop k =>
    match popKey (kops f) t k with
    | .ok (v, t) => pure (v + 2, t)
    | .error .keyError => pure (1, t)
    | .error e => throw e
  | .popd k d => do let (v, t) ← popKeyDefault (kops f) t k d; pure (v + 2, t)
  | .getv k v => do let (v, t) ← getBangVal (kops f) t k v; pure (v + 2, t)
  | .getf k v k2 v2 k3 => do
    let (r, t) ← getBang (kops f) t k (fun t => do
      let t ← setindex (kops f) t v2 k2
      let t ← dictDelete (kops f) t k3
      pure (v, t))
    pure (r + 2, t)
  | .hint n s => do pure (0, ← sizehint (kops f) t (JInt.lit .i64 n) s)
  | .empty => pure (0, emptyBang t)
  | .filter => do pure (0, ← filterBang t (fun k v => (k + v) % 3 != 0))
  | .merge ps => do let o ← build f ps; pure (0, ← dictMerge (kops f) t o)
  | .mergewith ps => do let o ← build f ps; pure (0, ← mergewith (kops f) (· + ·) t o)
  | .popany =>
    if t.count == 0 then pure (1, t) else do
      let ((k, v), t) ← popAny t
      pure (k * 1000 + v + 2, t)

def rndList (n m : Nat) : Gen (List Nat) := do
  let mut xs := []
  for _ in [:n] do
    xs := xs ++ [← rnd m]
  pure xs

/-- One `Set` case: build `s` and `t`, delete some elements of `s`, apply one operation. -/
def setCase (f : Nat) : Gen (DR (Nat × SetT Nat)) := do
  let a ← rndList (← rnd 26) 31
  let b ← rndList (← rnd 26) 31
  let dels ← rndList (← rnd 7) 31
  let which := (← rnd 7) + 1
  let x ← rnd 31
  let o := kops f
  pure do
    let s ← setOf o (Conv.self o) a
    let s ← dels.foldlM (fun s y => setDelete o s y) s
    let t ← setOf o (Conv.self o) b
    match which with
    | 1 => pure (0, ← unionSet o s t)
    | 2 => pure (0, ← intersectBang o s t)
    | 3 => pure (0, ← setdiffBang o s t)
    | 4 => pure (0, ← symdiffBang o s t)
    | 5 => pure (if ← issubsetSet o s t then 2 else 1, s)
    | 6 => pure (if ← setEq o s t then 2 else 1, s)
    | _ => do let (bb, s) ← inBang o (Conv.self o) s x; pure (if bb then 2 else 1, s)

/-- Print `D hf seq step digest` for 5 × 3 sequences of 150 `Dict` calls and
`S hf case digest` for 5 × 60 `Set` cases. -/
def differential (release : Bool) : IO Unit := do
  for f in [:5] do
    for sq in [1:4] do
      let ops := Id.run (((List.range 150).mapM (fun _ => genOp release)).run' (1000 * f + sq))
      let mut t : Table Nat Nat := Table.empty
      let mut i := 0
      for op in ops do
        i := i + 1
        match step f t op with
        | .error e => IO.println s!"D {f} {sq} {i} error {repr e}"
        | .ok (r, t') =>
          t := mat t'
          IO.println s!"D {f} {sq} {i} {digest t id r}"
    let cases := Id.run (((List.range 60).mapM (fun _ => setCase f)).run' (77 + f))
    let mut c := 0
    for r in cases do
      c := c + 1
      match r with
      | .error e => IO.println s!"S {f} {c} error {repr e}"
      | .ok (res, s) => IO.println s!"S {f} {c} {digest (mat s) (fun _ => 0) res}"

end JuliaLean.Dicts.Validation
