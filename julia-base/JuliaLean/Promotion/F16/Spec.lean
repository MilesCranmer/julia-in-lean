import JuliaLean.Promotion.Hash

/-!
Per-value specifications checked exhaustively over all 65,536 `Float16` bit patterns.
-/

namespace JuliaLean.Promotion.F16

open JuliaLean.Promotion

def allInts : List IntTy := [.i8, .i16, .i32, .i64, .i128, .u8, .u16, .u32, .u64, .u128]

theorem mem_allInts (t : IntTy) : t ∈ allInts := by cases t <;> decide

/-- `Ti(x)` returns the exact value when `x` is an integer in range, else `InexactError`. -/
def toIntOk (t : IntTy) (x : FV .f16) : Bool :=
  let r := x.toRat
  let q := r.1 / (r.2 : Int)
  let rep := x.isfinite && r.1 % (r.2 : Int) == 0 && decide (t.min ≤ q) && decide (q ≤ t.max)
  match toInt .f16 t x with
  | .ok z => rep && z.val == q
  | .error e => !rep && e == .inexactError t.name

/-- `trunc(Ti, x)` returns the truncated value when it is in range, else `InexactError`. -/
def truncOk (t : IntTy) (x : FV .f16) : Bool :=
  let q := x.truncVal
  let rep := x.isfinite && decide (t.min ≤ q) && decide (q ≤ t.max)
  match truncTo .f16 t x with
  | .ok z => rep && z.val == q
  | .error e => !rep && e == .inexactError "round"

/-- `hash(x) == hash(Float64(x))`, and `hash(x) == hash(Int64(x))` when `isequal(x, Int64(x))`. -/
def hashOk (x : FV .f16) : Bool :=
  let q := x.truncVal
  let isInt := x.isfinite && x.isinteger && !(x.iszero && x.signbit)
  hashF16 x .seed == hashF64 (Fl.convert x) .seed &&
    (!isInt || hashF16 x .seed == hashNum (.int .i64 (JInt.wrap .i64 q)) .seed)

def valueOk (x : FV .f16) : Bool := allInts.all (fun t => toIntOk t x && truncOk t x) && hashOk x

def chunkOk (k : Nat) : Bool := (List.range 512).all fun i => valueOk (Fl.ofBits (k * 512 + i))

theorem of_chunk {k : Nat} (h : chunkOk k = true) (i : Nat) (hi : i < 512) :
    valueOk (Fl.ofBits (k * 512 + i)) = true := by
  unfold chunkOk at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range.mpr hi)

end JuliaLean.Promotion.F16
