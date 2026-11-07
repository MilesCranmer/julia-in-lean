import JuliaLean.Proofs.base.reinterpretarray.invariants
import JuliaLean.Proofs.base.reinterpretarray.construction
import JuliaLean.base.reinterpretarray
import JuliaLean.base.range
import JuliaLean.base.indices
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.pointer
import JuliaLean.Proofs.base.int

/-!
# Specifications of `base/reinterpretarray.jl`

Properties refer to the parent-based source methods in `JuliaLean.base.reinterpretarray`.
Runtime layout and indexing interface laws are stated explicitly. Byte windows describe a
value's storage independently of the code that copies it.

## Nothing to promise

throwbits@14: Internal constructor error helper; public validation is specified on the constructors.
throwsize0@18: Internal constructor error helper; public validation is specified on the constructors.
throwsingleton@23: Internal constructor error helper; public validation is specified on the constructors.
throwbitpadding@27: Internal constructor error helper; public validation is specified on the constructors.
thrownonint@74: Internal constructor error helper; public validation is specified on the constructor.
throwaxes1@80: Internal constructor error helper; public validation is specified on the constructor.
throwintmult@108: Internal constructor error helper; reshape validation is specified on the constructor.
throwsize1@113: Internal constructor error helper; reshape validation is specified on the constructor.
throwfromsingleton@119: Internal constructor error helper; reshape validation is specified on the constructor.
reinterpret@104: The same-element-type overload forwards the input unchanged.
reinterpret@145: The same-element-type reshape overload forwards the input unchanged.
ispacked@827: This helper negates the runtime datatype padding metadata.
reinterpret@190: This overload delegates reinterpretation to its parent view without a further transformation.
_checkcontiguous@232: This method only forwards the contiguity query to its parent.
similar@234: This method only forwards similar-array allocation to its parent.
similar@235: This method only forwards type-based similar-array allocation to the parent type.
to_index@279: This conversion preserves the existing static Cartesian index value.
SimdLoop.simd_outer_range@327: This method supplies compiler-facing SIMD outer-range metadata.
SimdLoop.simd_inner_length@328: This method supplies compiler-facing SIMD inner-length metadata.
SimdLoop.simd_index@329: This method supplies compiler-facing SIMD index metadata.
_maybe_reshape@333: This private dispatch helper selects the ordinary Cartesian fallback for static indices.
_maybe_reshape@334: This private dispatch helper preserves an already reshaped array.
_getindex@337: This fallback delegates indexing to the ordinary Cartesian array path.
_setindex!@341: This fallback delegates assignment to the ordinary Cartesian array path.
eachindex@365: This method forwards eachindex to the underlying parent.
parent@369: This method projects the stored parent field of a ReinterpretArray.
dataids@370: This method forwards alias-identity tracking to the stored parent array.
has_offset_axes@401: This method forwards the offset-axes query to the stored parent array.
cconvert@410: This method forwards pointer conversion to the stored parent array.
unsafe_convert@411: This method casts the parent pointer conversion to the target element pointer type.
getindex@430: This zero-dimensional reshaped getter delegates to the first-index getter.
isassigned@433: This Cartesian isassigned overload forwards the query to the parent.
setindex!@580: This zero-dimensional reshaped setter delegates to the shared linear setter.
mapreduce_impl@984: This default reduction helper supplies the pairwise block size to the reduction worker.
-/
namespace JuliaLean.Proofs.base.reinterpretarray
open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Registry

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
@[simp] theorem resultPure {α : Type} (a : α) : (pure a : RResult α) = .ok a := rfl
@[simp] theorem resultBindOk {α β : Type} (a : α) (f : α → RResult β) :
    ((.ok a : RResult α) >>= f) = f a := rfl
@[simp] theorem resultBindError {α β : Type} (e : ReinterpretError) (f : α → RResult β) :
    ((.error e : RResult α) >>= f) = .error e := rfl
@[simp] theorem resultMapOk {α β : Type} (a : α) (f : α → β) :
    f <$> (.ok a : RResult α) = .ok (f a) := rfl
@[simp] theorem resultMapError {α β : Type} (e : ReinterpretError) (f : α → β) :
    f <$> (.error e : RResult α) = .error e := rfl

/-! ## Two's-complement `JInt` wrapping and `Int` arithmetic -/

theorem wrapInt_emod (t : IntTy) (x : Int) : wrapInt t x = wrapInt t (x % 2 ^ t.bits) := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_emod_self (t : IntTy) (x : Int) : wrapInt t x % 2 ^ t.bits = x % 2 ^ t.bits := by
  cases t <;> simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_add (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + wrapInt t b) = wrapInt t (a + b) := by
  rw [wrapInt_emod t (wrapInt t a + wrapInt t b), Int.add_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.add_emod, ← wrapInt_emod]

theorem wrapInt_mul (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a * wrapInt t b) = wrapInt t (a * b) := by
  rw [wrapInt_emod t (wrapInt t a * wrapInt t b), Int.mul_emod, wrapInt_emod_self,
    wrapInt_emod_self, ← Int.mul_emod, ← wrapInt_emod]

theorem wrapInt_sub (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a - wrapInt t b) = wrapInt t (a - b) := by
  rw [wrapInt_emod t (wrapInt t a - wrapInt t b), wrapInt_emod t (a - b), Int.sub_emod,
    wrapInt_emod_self, wrapInt_emod_self, ← Int.sub_emod]

theorem val_add {t : IntTy} (a b : JInt t) : (a + b).val = wrapInt t (a.val + b.val) := rfl
theorem val_sub {t : IntTy} (a b : JInt t) : (a - b).val = wrapInt t (a.val - b.val) := rfl
theorem val_mul {t : IntTy} (a b : JInt t) : (a * b).val = wrapInt t (a.val * b.val) := rfl
theorem val_lit (t : IntTy) (x : Int) : (JInt.lit t x).val = wrapInt t x := rfl
theorem val_wrap (t : IntTy) (x : Int) : (JInt.wrap t x).val = wrapInt t x := rfl

theorem i64_min_nonpos : IntTy.min .i64 ≤ 0 := by decide
theorem i64_one_le_max : (1 : Int) ≤ IntTy.max .i64 := by decide

theorem wrapInt_nat (k : Nat) (h : (k : Int) ≤ IntTy.max .i64) : wrapInt .i64 (k : Int) = k :=
  wrapInt_of_inRange .i64 (k : Int) ⟨Int.le_trans i64_min_nonpos (Int.natCast_nonneg k), h⟩

theorem lit_nat (k : Nat) (h : (k : Int) ≤ IntTy.max .i64) : (JInt.lit .i64 (k : Int)).val = k := by
  rw [val_lit]; exact wrapInt_nat k h

theorem wrap_nat (k : Nat) (h : (k : Int) ≤ IntTy.max .i64) :
    (JInt.wrap .i64 (k : Int)).val = k := by
  rw [val_wrap]; exact wrapInt_nat k h

theorem one_val : one.val = 1 := by decide
theorem zero_val : zero.val = 0 := by decide

theorem add_nat {a b : I64} {m n : Nat} (ha : a.val = m) (hb : b.val = n)
    (h : ((m + n : Nat) : Int) ≤ IntTy.max .i64) : (a + b).val = ((m + n : Nat) : Int) := by
  rw [val_add, ha, hb, ← Int.natCast_add]; exact wrapInt_nat _ h

theorem sub_nat {a b : I64} {m n : Nat} (ha : a.val = m) (hb : b.val = n) (hmn : n ≤ m)
    (_h : (m : Int) ≤ IntTy.max .i64) : (a - b).val = ((m - n : Nat) : Int) := by
  rw [val_sub, ha, hb, show (m : Int) - (n : Int) = ((m - n : Nat) : Int) by omega]
  exact wrapInt_nat _ (by omega)

theorem mul_nat {a b : I64} {m n : Nat} (ha : a.val = m) (hb : b.val = n)
    (h : ((m * n : Nat) : Int) ≤ IntTy.max .i64) : (a * b).val = ((m * n : Nat) : Int) := by
  rw [val_mul, ha, hb, ← Int.natCast_mul]; exact wrapInt_nat _ h

theorem fits {k P : Nat} (hP : (P : Int) ≤ IntTy.max .i64) (h : k ≤ P) :
    (k : Int) ≤ IntTy.max .i64 :=
  Int.le_trans (Int.ofNat_le.mpr h) hP

theorem divInt_nat {a b : I64} {m n : Nat} (ha : a.val = m) (hb : b.val = n) (hn : 0 < n) :
    divInt a b = .ok (JInt.wrap .i64 ((m / n : Nat) : Int)) := by
  unfold divInt JInt.div
  rw [ite_eq_right (by omega), ite_eq_right (fun h => by have := h.2.2; omega), ha, hb]
  rw [show (m : Int).tdiv (n : Int) = ((m / n : Nat) : Int) from rfl]
  rfl

theorem remInt_nat {a b : I64} {m n : Nat} (ha : a.val = m) (hb : b.val = n) (hn : 0 < n) :
    remInt a b = .ok (JInt.wrap .i64 ((m % n : Nat) : Int)) := by
  unfold remInt JInt.remInt
  rw [ite_eq_right (by omega), ha, hb]
  rw [show (m : Int).tmod (n : Int) = ((m % n : Nat) : Int) from rfl]
  rfl

theorem divremInt_nat {a b : I64} {m n : Nat} (ha : a.val = m) (hb : b.val = n) (hn : 0 < n) :
    divremInt a b = .ok (JInt.wrap .i64 ((m / n : Nat) : Int), JInt.wrap .i64 ((m % n : Nat) : Int)) := by
  simp [divremInt, divInt_nat ha hb hn, remInt_nat ha hb hn]

theorem lt_iff_val {a b : I64} : (a < b) ↔ a.val < b.val := Iff.rfl
theorem le_iff_val {a b : I64} : (a ≤ b) ↔ a.val ≤ b.val := Iff.rfl

theorem jint_eq_of_val {a b : I64} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

theorem beq_iff_val {a b : I64} : (a == b) = decide (a.val = b.val) := by
  by_cases h : a.val = b.val
  · have hab := jint_eq_of_val h; subst hab; simp
  · have hab : a ≠ b := fun he => h (by rw [he])
    simp [h]

theorem bne_iff_val {a b : I64} : (a != b) = decide (a.val ≠ b.val) := by
  unfold bne
  rw [beq_iff_val]
  by_cases h : a.val = b.val <;> simp [h]

theorem lt_of_mul_lt {a b s : Nat} (h : a * s < b * s) : a < b := by
  rcases Nat.lt_or_ge a b with h' | h'
  · exact h'
  · have := Nat.mul_le_mul_right s h'; omega

theorem le_of_mul_le {a b s : Nat} (hs : 0 < s) (h : a * s ≤ b * s) : a ≤ b := by
  rcases Nat.lt_or_ge b a with h' | h'
  · have := Nat.mul_le_mul_right s (show b + 1 ≤ a from h')
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · exact h'

theorem rem_add_le {k sS sT : Nat} (hS : 0 < sS) (h : sS % sT = 0) :
    k * sT % sS + sT ≤ sS := by
  obtain ⟨m, hm⟩ : ∃ m, sS = m * sT :=
    ⟨sS / sT, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm⟩
  subst hm
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hS
    · exact h0
  rw [Nat.mul_mod_mul_right]
  have h2 := Nat.mul_le_mul_right sT (show k % m + 1 ≤ m from Nat.mod_lt k hm0)
  rw [Nat.add_mul, Nat.one_mul] at h2
  exact h2

/-! ## Byte lists and `overwriteBytes` -/

theorem take_app_add {α : Type} (a b : List α) (i : Nat) :
    (a ++ b).take (a.length + i) = a ++ b.take i := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.cons_append, List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega,
      List.take_succ_cons, ih]; rfl

theorem drop_app_add {α : Type} (a b : List α) (i : Nat) :
    (a ++ b).drop (a.length + i) = b.drop i := by
  induction a with
  | nil => simp
  | cons x a ih =>
    rw [List.cons_append, List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega,
      List.drop_succ_cons, ih]

theorem take_app_le {α : Type} : ∀ (a b : List α) (i : Nat), i ≤ a.length → (a ++ b).take i = a.take i
  | _, _, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | _ :: a, b, i + 1, h => by
    rw [List.cons_append, List.take_succ_cons, List.take_succ_cons,
      take_app_le a b i (by simp at h; omega)]

theorem drop_app_le {α : Type} : ∀ (a b : List α) (i : Nat), i ≤ a.length → (a ++ b).drop i = a.drop i ++ b
  | _, _, 0, _ => by simp
  | [], _, _ + 1, h => by simp at h
  | _ :: a, b, i + 1, h => by
    rw [List.cons_append, List.drop_succ_cons, List.drop_succ_cons,
      drop_app_le a b i (by simp at h; omega)]

theorem take_app {α : Type} (a b : List α) (m : Nat) :
    (a ++ b).take m = a.take m ++ b.take (m - a.length) := by
  by_cases h : m ≤ a.length
  · rw [take_app_le _ _ _ h, show m - a.length = 0 by omega, List.take_zero, List.append_nil]
  · have := take_app_add a b (m - a.length)
    rw [show a.length + (m - a.length) = m by omega] at this
    rw [this, List.take_of_length_le (show a.length ≤ m by omega)]

theorem take_add_drop {α : Type} (xs : List α) (a b : Nat) :
    xs.take (a + b) = xs.take a ++ (xs.drop a).take b :=
  List.take_add

/-- Every element of a parent column has `sS` bytes. -/
def WellFormed (sS : Nat) (col : List Bytes) : Prop := ∀ s ∈ col, s.length = sS

theorem wf_cons {sS : Nat} {s : Bytes} {c : List Bytes} (h : WellFormed sS (s :: c)) :
    s.length = sS ∧ WellFormed sS c :=
  ⟨h s (by simp), fun x hx => h x (by simp [hx])⟩

theorem wf_drop {sS : Nat} {c : List Bytes} (h : WellFormed sS c) (j : Nat) :
    WellFormed sS (c.drop j) := fun x hx => h x (List.mem_of_mem_drop hx)

theorem wf_take {sS : Nat} {c : List Bytes} (h : WellFormed sS c) (j : Nat) :
    WellFormed sS (c.take j) := fun x hx => h x (List.mem_of_mem_take hx)

theorem wf_set {sS : Nat} {c : List Bytes} (h : WellFormed sS c) (e : Nat) (y : Bytes)
    (hy : y.length = sS) : WellFormed sS (c.set e y) := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact h x hx
  · rw [hx]; exact hy

theorem length_flatten_wf {sS : Nat} : ∀ (c : List Bytes), WellFormed sS c →
    c.flatten.length = c.length * sS
  | [], _ => by simp
  | s :: c, h => by
    obtain ⟨hs, hc⟩ := wf_cons h
    rw [List.flatten_cons, List.length_append, hs, length_flatten_wf c hc, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem flatten_drop_mul {sS : Nat} : ∀ (c : List Bytes) (j : Nat), WellFormed sS c →
    (c.drop j).flatten = c.flatten.drop (j * sS)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | s :: c, j + 1, h => by
    obtain ⟨hs, hc⟩ := wf_cons h
    rw [List.drop_succ_cons, flatten_drop_mul c j hc, List.flatten_cons,
      show (j + 1) * sS = s.length + j * sS by rw [hs, Nat.add_mul, Nat.one_mul, Nat.add_comm],
      drop_app_add]

theorem flatten_take_mul {sS : Nat} : ∀ (c : List Bytes) (n : Nat), WellFormed sS c →
    (c.take n).flatten = c.flatten.take (n * sS)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | s :: c, n + 1, h => by
    obtain ⟨hs, hc⟩ := wf_cons h
    rw [List.take_succ_cons, List.flatten_cons, flatten_take_mul c n hc, List.flatten_cons,
      show (n + 1) * sS = s.length + n * sS by rw [hs, Nat.add_mul, Nat.one_mul, Nat.add_comm],
      take_app_add]

theorem length_flatten_take {sS : Nat} (c : List Bytes) (h : WellFormed sS c) (e : Nat)
    (he : e ≤ c.length) : (c.take e).flatten.length = e * sS := by
  rw [length_flatten_wf _ (wf_take h e), List.length_take, Nat.min_eq_left he]

theorem flatten_split (c : List Bytes) (e : Nat) (he : e < c.length) :
    c.flatten = (c.take e).flatten ++ (c[e] ++ (c.drop (e + 1)).flatten) := by
  have h : c = c.take e ++ c[e] :: c.drop (e + 1) := by
    rw [← List.drop_eq_getElem_cons he, List.take_append_drop]
  conv => lhs; rw [h]
  rw [List.flatten_append, List.flatten_cons]

theorem set_split : ∀ (c : List Bytes) (e : Nat) (y : Bytes), e < c.length →
    c.set e y = c.take e ++ y :: c.drop (e + 1)
  | [], _, _, h => by simp at h
  | _ :: c, 0, y, _ => by simp
  | s :: c, e + 1, y, h => by
    rw [List.set_cons_succ, set_split c e y (by simp at h; omega)]; simp

theorem drop_flatten_at {sS : Nat} (c : List Bytes) (h : WellFormed sS c) (e r : Nat)
    (he : e < c.length) (hr : r ≤ sS) :
    c.flatten.drop (e * sS + r) = c[e].drop r ++ (c.drop (e + 1)).flatten := by
  rw [flatten_split c e he, ← length_flatten_take c h e (Nat.le_of_lt he), drop_app_add,
    drop_app_le _ _ _ (by rw [h _ (List.getElem_mem he)]; exact hr)]

theorem overwriteBytes_length (d s : Bytes) (o : Nat) (h : o + s.length ≤ d.length) :
    (overwriteBytes d o s).length = d.length := by
  simp only [overwriteBytes, List.length_append, List.length_take, List.length_drop]; omega

theorem overwriteBytes_getElem? (d s : Bytes) (o i : Nat) (h : o + s.length ≤ d.length) :
    (overwriteBytes d o s)[i]? =
      if i < o then d[i]? else if i < o + s.length then s[i - o]? else d[i]? := by
  have ht : (d.take o).length = o := by rw [List.length_take]; omega
  unfold overwriteBytes
  rw [List.append_assoc]
  by_cases h1 : i < o
  · rw [ite_eq_left h1, List.getElem?_append_left (by rw [ht]; exact h1), List.getElem?_take,
      ite_eq_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by rw [ht]; omega), ht]
    by_cases h2 : i < o + s.length
    · rw [ite_eq_left h2, List.getElem?_append_left (by omega)]
    · rw [ite_eq_right h2, List.getElem?_append_right (by omega), List.getElem?_drop,
        show o + s.length + (i - o - s.length) = i by omega]

theorem overwriteBytes_overwriteBytes (d s1 s2 : Bytes) (o : Nat)
    (h : o + s1.length + s2.length ≤ d.length) :
    overwriteBytes (overwriteBytes d o s1) (o + s1.length) s2 = overwriteBytes d o (s1 ++ s2) := by
  have h1 : o + s1.length ≤ d.length := by omega
  apply List.ext_getElem?
  intro i
  rw [overwriteBytes_getElem? (overwriteBytes d o s1) s2 (o + s1.length) i
      (by rw [overwriteBytes_length _ _ _ h1]; omega),
    overwriteBytes_getElem? d s1 o i h1,
    overwriteBytes_getElem? d (s1 ++ s2) o i (by rw [List.length_append]; omega),
    List.getElem?_append, List.length_append]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (congr 1; omega)

theorem overwriteBytes_nil (d : Bytes) (o : Nat) : overwriteBytes d o [] = d := by
  simp [overwriteBytes]

theorem overwriteBytes_full (X w : Bytes) (h : w.length = X.length) : overwriteBytes X 0 w = w := by
  unfold overwriteBytes
  rw [List.take_zero, List.nil_append, Nat.zero_add, List.drop_of_length_le (by omega),
    List.append_nil]

theorem overwriteBytes_app (A X B w : Bytes) (r : Nat) (h : r + w.length ≤ X.length) :
    overwriteBytes (A ++ (X ++ B)) (A.length + r) w = A ++ (overwriteBytes X r w ++ B) := by
  unfold overwriteBytes
  rw [take_app_add, take_app_le _ _ _ (by omega), Nat.add_assoc, drop_app_add,
    drop_app_le _ _ _ h]
  simp only [List.append_assoc]

theorem set_overwriteBytes_flatten {sS : Nat} (c : List Bytes) (hc : WellFormed sS c) (e r : Nat)
    (he : e < c.length) (w : Bytes) (hw : r + w.length ≤ sS) :
    (c.set e (overwriteBytes c[e] r w)).flatten = overwriteBytes c.flatten (e * sS + r) w := by
  have hce : c[e].length = sS := hc _ (List.getElem_mem he)
  rw [set_split c e _ he, List.flatten_append, List.flatten_cons, flatten_split c e he,
    ← length_flatten_take c hc e (Nat.le_of_lt he),
    overwriteBytes_app _ _ _ _ _ (by rw [hce]; exact hw)]

theorem set_flatten {sS : Nat} (c : List Bytes) (hc : WellFormed sS c) (e : Nat)
    (he : e < c.length) (y : Bytes) (hy : y.length = sS) :
    (c.set e y).flatten = overwriteBytes c.flatten (e * sS) y := by
  have hce : c[e].length = sS := hc _ (List.getElem_mem he)
  have := set_overwriteBytes_flatten c hc e 0 he y (by omega)
  rw [overwriteBytes_full _ _ (by rw [hy, hce]), Nat.add_zero] at this
  exact this

/-! ## Column parent operations and loop invariants -/

/-- `a.parent[j, tail...]` for a 1-based parent column (`tail = []`). -/
def colGet (col : List Bytes) (inds : List I64) : RResult Bytes :=
  match inds with
  | [j] =>
    if 1 ≤ j.val ∧ j.val ≤ col.length then .ok (col.getD (j.val - 1).toNat [])
    else .error .bounds
  | _ => .error .bounds

/-- `a.parent[j, tail...] = s` for a 1-based parent column (`tail = []`). -/
def colSet (col : List Bytes) (inds : List I64) (s : Bytes) : RResult (List Bytes) :=
  match inds with
  | [j] =>
    if 1 ≤ j.val ∧ j.val ≤ col.length then .ok (col.set (j.val - 1).toNat s)
    else .error .bounds
  | _ => .error .bounds

def colParentOps : ParentOps (List Bytes) := ⟨colGet, colSet⟩

/-- `checkbounds(a, i1, tail...)` on a 1D view of length `sz1`. -/
def checkFirst1D {T S A : Type} (sz1 : I64) (_a : ReinterpretArray T S A)
    (i1 : I64) (tail : List I64) : RResult Unit :=
  if tail.isEmpty && decide (1 ≤ i1.val ∧ i1.val ≤ sz1.val) then .ok () else .error .bounds

theorem colGet_ok (c : List Bytes) (j : I64) (e : Nat) (hj : j.val = (e : Int) + 1)
    (he : e < c.length) : colGet c [j] = .ok c[e] := by
  unfold colGet
  dsimp only
  rw [ite_eq_left ⟨by omega, by omega⟩, show (j.val - 1).toNat = e by omega]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he]

theorem colSet_ok (c : List Bytes) (j : I64) (e : Nat) (y : Bytes) (hj : j.val = (e : Int) + 1)
    (he : e < c.length) : colSet c [j] y = .ok (c.set e y) := by
  unfold colSet
  dsimp only
  rw [ite_eq_left ⟨by omega, by omega⟩, show (j.val - 1).toNat = e by omega]

@[simp] theorem forIn_nil {α β : Type} (b : β) (f : α → β → RResult (ForInStep β)) :
    forIn ([] : List α) b f = .ok b := rfl

theorem forIn_cons_yield {α β : Type} (x : α) (xs : List α) (b b' : β)
    (f : α → β → RResult (ForInStep β)) (r : β)
    (h1 : f x b = .ok (.yield b'))
    (h2 : forIn xs b' f = .ok r) :
    forIn (x :: xs) b f = .ok r := by
  rw [List.forIn_cons, h1, resultBindOk]
  exact h2

theorem intRange_one {hi : I64} {n : Nat} (h : hi.val = n) :
    intRange one hi = (List.range n).map (fun (m : Nat) => one + JInt.lit .i64 (m : Int)) := by
  unfold intRange
  rw [h, one_val, Int.sub_add_cancel, Int.toNat_natCast]

theorem loop_idx_facts {start ss : I64} {base s sS P : Nat}
    (hstart : start.val = base) (hss : ss.val = sS) (hS : 0 < sS)
    (hB : (P : Int) ≤ IntTy.max .i64) (hb : (base + s + 1) * sS ≤ P) :
    (start + (one + JInt.lit .i64 (s : Int))).val = ((base + s : Nat) : Int) + 1 ∧
    (((one + JInt.lit .i64 (s : Int)) - one) * ss).val = ((s * sS : Nat) : Int) ∧
    (((one + JInt.lit .i64 (s : Int)) - one) * ss).val.toNat = s * sS := by
  have h1 : base + s + 1 ≤ P := by
    have := Nat.mul_le_mul_left (base + s + 1) (show 1 ≤ sS from hS)
    rw [Nat.mul_one] at this; omega
  have hsP : s ≤ P := by omega
  have h1sP : 1 + s ≤ P := by omega
  have hbsP : base + (1 + s) ≤ P := by omega
  have hmulP : s * sS ≤ P := by
    have := Nat.mul_le_mul_right sS (show s ≤ base + s + 1 by omega)
    omega
  have heq1 : ((base + (1 + s) : Nat) : Int) = ((base + s : Nat) : Int) + 1 := by omega
  have heq2 : 1 + s - 1 = s := by omega
  have hs_lit : (JInt.lit .i64 (s : Int)).val = (s : Int) := lit_nat s (fits hB hsP)
  have hidx : (one + JInt.lit .i64 (s : Int)).val = ((1 + s : Nat) : Int) :=
    add_nat one_val hs_lit (fits hB h1sP)
  have hsi : (start + (one + JInt.lit .i64 (s : Int))).val = ((base + (1 + s) : Nat) : Int) :=
    add_nat hstart hidx (fits hB hbsP)
  have hsub : ((one + JInt.lit .i64 (s : Int)) - one).val = ((1 + s - 1 : Nat) : Int) :=
    sub_nat hidx one_val (Nat.le_add_right 1 s) (fits hB h1sP)
  rw [heq2] at hsub
  have hmul : (((one + JInt.lit .i64 (s : Int)) - one) * ss).val = ((s * sS : Nat) : Int) :=
    mul_nat hsub hss (fits hB hmulP)
  exact ⟨hsi.trans heq1, hmul, by rw [hmul, Int.toNat_natCast]⟩

theorem forIn_get_mult {sS : Nat} (col : List Bytes) (hc : WellFormed sS col)
    (D : Bytes) (start ss : I64) (base : Nat) (hstart : start.val = base) (hss : ss.val = sS)
    (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64) (hS : 0 < sS) :
    ∀ (m s : Nat) (res : Bytes),
      base + s + m ≤ col.length →
      (s + m) * sS ≤ D.length →
      res = overwriteBytes D 0 (((col.drop base).take s).flatten) →
      forIn ((List.range' s m).map (fun (j : Nat) => one + JInt.lit .i64 (j : Int))) res
        (fun i r => do
          let bytes ← colGet col [start + i]
          pure (ForInStep.yield (memcpyValue r bytes ((i - one) * ss) zero ss))) =
        .ok (overwriteBytes D 0 (((col.drop base).take (s + m)).flatten)) := by
  intro m
  induction m with
  | zero =>
    intro s res _ _ hres
    rw [Nat.add_zero, ← hres]; rfl
  | succ m ih =>
    intro s res hlen hD hres
    have he : base + s < col.length := by omega
    have hce : col[base + s].length = sS := hc _ (List.getElem_mem he)
    have hfl_len : (((col.drop base).take s).flatten).length = s * sS := by
      rw [length_flatten_take (col.drop base) (wf_drop hc base) s
        (by rw [List.length_drop]; omega)]
    have hstep_res : overwriteBytes res (s * sS) col[base + s] =
        overwriteBytes D 0 (((col.drop base).take (s + 1)).flatten) := by
      have hdrop : (col.drop base).drop s = col[base + s] :: col.drop (base + s + 1) := by
        rw [List.drop_drop, List.drop_eq_getElem_cons he]
      have htake1 : (col.drop base).take (s + 1) = (col.drop base).take s ++ [col[base + s]] := by
        conv => lhs; rw [← List.take_append_drop s (col.drop base)]
        rw [hdrop, show s + 1 = ((col.drop base).take s).length + 1 by
          rw [List.length_take, List.length_drop]; omega,
          take_app_add ((col.drop base).take s) (col[base + s] :: col.drop (base + s + 1)) 1,
          List.take_succ_cons, List.take_zero]
      rw [hres, show s * sS = 0 + (((col.drop base).take s).flatten).length by rw [hfl_len]; omega,
        overwriteBytes_overwriteBytes D _ _ 0 (by
          have := Nat.mul_le_mul_right sS (show s + 1 ≤ s + (m + 1) by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          rw [hfl_len, hce]; omega),
        htake1, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
    have hlen_next : base + (s + 1) + m ≤ col.length := by omega
    have hD_next : (s + 1 + m) * sS ≤ D.length := by
      rw [show s + 1 + m = s + (m + 1) by omega]; exact hD
    have hadd_assoc : s + (m + 1) = (s + 1) + m := by omega
    obtain ⟨hsi, hmul, _⟩ := loop_idx_facts hstart hss hS hB
      (Nat.mul_le_mul_right sS (show base + s + 1 ≤ col.length by omega))
    have hget := colGet_ok col (start + (one + JInt.lit .i64 (s : Int))) (base + s) hsi he
    have hmc : memcpyValue res col[base + s] (((one + JInt.lit .i64 (s : Int)) - one) * ss) zero ss =
        overwriteBytes res (s * sS) col[base + s] := by
      unfold memcpyValue byteWindow
      simp only [hmul, zero_val, hss, Int.toNat_natCast, Int.toNat_zero, List.drop_zero,
        List.take_of_length_le (Nat.le_of_eq hce)]
    rw [List.range'_succ, List.map_cons]
    apply forIn_cons_yield _ _ _ (overwriteBytes res (s * sS) col[base + s])
    · rw [hget, resultBindOk, hmc]
      rfl
    · rw [hadd_assoc]
      exact ih (s + 1) _ hlen_next hD_next hstep_res

theorem forIn_set_mult {sS : Nat} (v F : Bytes) (start ss : I64) (base : Nat)
    (hstart : start.val = base) (hss : ss.val = sS) (hS : 0 < sS) :
    ∀ (m s : Nat) (c : List Bytes),
      WellFormed sS c → c.length * sS = F.length →
      ((c.length * sS : Nat) : Int) ≤ IntTy.max .i64 →
      base + s + m ≤ c.length → (s + m) * sS ≤ v.length →
      c.flatten = overwriteBytes F (base * sS) (v.take (s * sS)) →
      ∃ c', forIn ((List.range' s m).map (fun (j : Nat) => one + JInt.lit .i64 (j : Int))) c
        (fun i p => do
          let bytes := byteWindow v ((i - one) * ss).val.toNat ss.val.toNat
          let p' ← colSet p [start + i] bytes
          pure (ForInStep.yield p')) = .ok c' ∧
        WellFormed sS c' ∧ c'.length = c.length ∧
        c'.flatten = overwriteBytes F (base * sS) (v.take ((s + m) * sS)) := by
  intro m
  induction m with
  | zero =>
    intro s c hc _ _ _ _ hfl
    exact ⟨c, rfl, hc, rfl, by rw [Nat.add_zero]; exact hfl⟩
  | succ m ih =>
    intro s c hc hcl hB hb hvl hfl
    have he : base + s < c.length := by omega
    have hs1 : (s + 1) * sS ≤ v.length :=
      Nat.le_trans (Nat.mul_le_mul_right sS (by omega)) hvl
    rw [Nat.add_mul, Nat.one_mul] at hs1
    have hw : ((v.drop (s * sS)).take sS).length = sS := by
      rw [List.length_take, List.length_drop]; omega
    have hbF : (base + s + 1) * sS ≤ F.length := by
      rw [← hcl]; exact Nat.mul_le_mul_right sS (by omega)
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hbF
    have htl : (v.take (s * sS)).length = s * sS := by rw [List.length_take]; omega
    have hb_next : base + (s + 1) + m ≤ c.length := by omega
    have hadd_assoc : s + 1 + m = s + (m + 1) := by omega
    have hfl_next : (c.set (base + s) ((v.drop (s * sS)).take sS)).flatten =
        overwriteBytes F (base * sS) (v.take ((s + 1) * sS)) := by
      rw [set_flatten c hc _ he _ hw, hfl,
        show (base + s) * sS = base * sS + (v.take (s * sS)).length by rw [htl, Nat.add_mul],
        overwriteBytes_overwriteBytes F _ _ _ (by rw [htl, hw]; omega),
        show (s + 1) * sS = s * sS + sS by rw [Nat.add_mul, Nat.one_mul], List.take_add]
    obtain ⟨hsi, _, hmul_nat⟩ := loop_idx_facts hstart hss hS hB
      (Nat.mul_le_mul_right sS (show base + s + 1 ≤ c.length by omega))
    have hset := colSet_ok c (start + (one + JInt.lit .i64 (s : Int))) (base + s)
      ((v.drop (s * sS)).take sS) hsi he
    have hbw : byteWindow v (((one + JInt.lit .i64 (s : Int)) - one) * ss).val.toNat ss.val.toNat =
        (v.drop (s * sS)).take sS := by
      unfold byteWindow
      rw [hmul_nat, hss, Int.toNat_natCast]
    obtain ⟨c', hrun, h1, h2, h3⟩ := ih (s + 1)
      (c.set (base + s) ((v.drop (s * sS)).take sS)) (wf_set hc _ _ hw)
      (by rw [List.length_set]; exact hcl) (by rw [List.length_set]; exact hB)
      (by rw [List.length_set]; exact hb_next)
      (by rw [hadd_assoc]; exact hvl)
      hfl_next
    refine ⟨c', ?_, h1, by rw [h2, List.length_set], ?_⟩
    · rw [List.range'_succ, List.map_cons]
      apply forIn_cons_yield _ _ _ (c.set (base + s) ((v.drop (s * sS)).take sS))
      · dsimp only
        rw [hbw, hset, resultBindOk]
        rfl
      · exact hrun
    · rw [h3, hadd_assoc]

theorem copyLoop_nb_facts {ss sidx ts copied : I64} {sS r sT c P : Nat}
    (hss : ss.val = sS) (hsidx : sidx.val = r) (hts : ts.val = sT) (hcp : copied.val = c)
    (hr : r < sS) (hc : c < sT) (hsSP : sS ≤ P) (hsTP : sT ≤ P) (hB : (P : Int) ≤ IntTy.max .i64) :
    (if ss - sidx < ts - copied then ss - sidx else ts - copied).val =
      ((min (sS - r) (sT - c) : Nat) : Int) ∧
    (if ss - sidx < ts - copied then ss - sidx else ts - copied).val.toNat =
      min (sS - r) (sT - c) ∧
    (copied + (if ss - sidx < ts - copied then ss - sidx else ts - copied)).val =
      ((c + min (sS - r) (sT - c) : Nat) : Int) ∧
    0 < min (sS - r) (sT - c) ∧ c + min (sS - r) (sT - c) ≤ sT ∧
    (c + min (sS - r) (sT - c) < sT → r + min (sS - r) (sT - c) = sS) := by
  have hr_le : r ≤ sS := by omega
  have hc_le : c ≤ sT := by omega
  have hcp_leP : c + min (sS - r) (sT - c) ≤ P := by omega
  have hpos : 0 < min (sS - r) (sT - c) := by omega
  have hleT : c + min (sS - r) (sT - c) ≤ sT := by omega
  have hfull : c + min (sS - r) (sT - c) < sT → r + min (sS - r) (sT - c) = sS := fun _ => by omega
  have hss_sub : (ss - sidx).val = ((sS - r : Nat) : Int) :=
    sub_nat hss hsidx hr_le (fits hB hsSP)
  have hts_sub : (ts - copied).val = ((sT - c : Nat) : Int) :=
    sub_nat hts hcp hc_le (fits hB hsTP)
  have hnb : (if ss - sidx < ts - copied then ss - sidx else ts - copied).val =
      ((min (sS - r) (sT - c) : Nat) : Int) := by
    by_cases hm : sS - r < sT - c
    · have hmin1 : min (sS - r) (sT - c) = sS - r := Nat.min_eq_left (Nat.le_of_lt hm)
      have hlt_b : ss - sidx < ts - copied := by
        rw [lt_iff_val, hss_sub, hts_sub]; exact Int.ofNat_lt.mpr hm
      rw [ite_eq_left hlt_b, hmin1, hss_sub]
    · have hge : sT - c ≤ sS - r := Nat.le_of_not_lt hm
      have hmin2 : min (sS - r) (sT - c) = sT - c := Nat.min_eq_right hge
      have hnlt_b : ¬ (ss - sidx < ts - copied) := by
        rw [lt_iff_val, hss_sub, hts_sub]; exact fun h => hm (Int.ofNat_lt.mp h)
      rw [ite_eq_right hnlt_b, hmin2, hts_sub]
  have hcp_next : (copied + (if ss - sidx < ts - copied then ss - sidx else ts - copied)).val =
      ((c + min (sS - r) (sT - c) : Nat) : Int) :=
    add_nat hcp hnb (fits hB hcp_leP)
  exact ⟨hnb, by rw [hnb, Int.toNat_natCast], hcp_next, hpos, hleT, hfull⟩

theorem copyLoop_ok {sS sT : Nat} (col : List Bytes) (hc : WellFormed sS col)
    (start ss ts : I64) (q k : Nat) (hq : start.val = q) (hss : ss.val = sS) (hts : ts.val = sT)
    (hS : 0 < sS) (hkb : k * sT + sT ≤ col.length * sS)
    (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64) :
    ∀ (rem step c r : Nat) (i copied sidx : I64) (res : Bytes),
      sT - c ≤ rem → c ≤ sT → r < sS →
      (c < sT → i.val = (step : Int) + 1) → copied.val = c → sidx.val = r →
      (c < sT → k * sT + c = (q + step) * sS + r) →
      res = overwriteBytes (List.replicate sT 0) 0 ((col.flatten.drop (k * sT)).take c) →
      m473_getindexNonReshaped.copyLoop colGet col [] start ss ts i copied sidx res =
        .ok ((col.flatten.drop (k * sT)).take sT) := by
  intro rem
  induction rem with
  | zero =>
    intro step c r i copied sidx res hrem hcsT _ _ hcp _ _ hres
    have hc_eq : c = sT := by omega
    subst hc_eq
    have hncond : ¬ (copied < ts) := by rw [lt_iff_val, hcp, hts]; omega
    rw [m473_getindexNonReshaped.copyLoop.eq_def, ite_eq_right hncond, hres]
    have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hc
    have htl : ((col.flatten.drop (k * c)).take c).length = c := by
      rw [List.length_take, List.length_drop, hFl]; omega
    rw [overwriteBytes_full _ _ (by rw [htl, List.length_replicate])]
  | succ rem ih =>
    intro step c r i copied sidx res hrem hcsT hrS hi hcp hsidx hinv hres
    by_cases hlt : c < sT
    · have hcond : copied < ts := by rw [lt_iff_val, hcp, hts]; omega
      have hpos := hinv hlt
      have hi_hlt := hi hlt
      have he : q + step < col.length :=
        lt_of_mul_lt (by omega : (q + step) * sS < col.length * sS)
      have hce : col[q + step].length = sS := hc _ (List.getElem_mem he)
      have h1L : q + (step + 1) ≤ col.length * sS := by
        have := Nat.mul_le_mul_right sS (show q + step + 1 ≤ col.length by omega)
        have h1 : q + step + 1 ≤ (q + step + 1) * sS := by
          have := Nat.mul_le_mul_left (q + step + 1) (show 1 ≤ sS from hS)
          rw [Nat.mul_one] at this; exact this
        omega
      have hsSP : sS ≤ col.length * sS := by
        have := Nat.mul_le_mul_right sS (show 1 ≤ col.length by omega)
        rw [Nat.one_mul] at this; exact this
      have hsTP : sT ≤ col.length * sS := by omega
      have hrem_next : sT - (c + min (sS - r) (sT - c)) ≤ rem := by omega
      have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hc
      have htl_c : ((col.flatten.drop (k * sT)).take c).length = c := by
        rw [List.length_take, List.length_drop, hFl]; omega
      have htl_nb : ((col.flatten.drop (k * sT + c)).take (min (sS - r) (sT - c))).length =
          min (sS - r) (sT - c) := by
        rw [List.length_take, List.length_drop, hFl]; omega
      have hinv_next : c + min (sS - r) (sT - c) < sT →
          k * sT + (c + min (sS - r) (sT - c)) = (q + (step + 1)) * sS + 0 := by
        intro hlt'
        have hmin : min (sS - r) (sT - c) = sS - r := by omega
        have hqs : q + (step + 1) = (q + step) + 1 := by omega
        rw [hqs, Nat.add_mul, Nat.one_mul]; omega
      have hstep2_P : c + min (sS - r) (sT - c) < sT → step + 1 + 1 ≤ col.length * sS := by
        intro hlt'
        have hpos' := hinv_next hlt'
        have he' : q + (step + 1) < col.length :=
          lt_of_mul_lt (by omega : (q + (step + 1)) * sS < col.length * sS)
        have := Nat.mul_le_mul_right sS (show q + (step + 1) + 1 ≤ col.length by omega)
        have h1 : q + (step + 1) + 1 ≤ (q + (step + 1) + 1) * sS := by
          have := Nat.mul_le_mul_left (q + (step + 1) + 1) (show 1 ≤ sS from hS)
          rw [Nat.mul_one] at this; exact this
        omega
      have hi' : i.val = ((step + 1 : Nat) : Int) := by omega
      have hsi_eq : ((q + (step + 1) : Nat) : Int) = ((q + step : Nat) : Int) + 1 := by omega
      have hi_next_eq : ((step + 1 + 1 : Nat) : Int) = ((step + 1 : Nat) : Int) + 1 := by omega
      have hsi : (start + i).val = ((q + step : Nat) : Int) + 1 :=
        (add_nat hq hi' (fits hB h1L)).trans hsi_eq
      have hget := colGet_ok col (start + i) (q + step) hsi he
      obtain ⟨_, hnb_nat, hcp_next, _, hnb_leT, _⟩ :=
        copyLoop_nb_facts hss hsidx hts hcp hrS hlt hsSP hsTP hB
      have hi_next : c + min (sS - r) (sT - c) < sT → (i + one).val = ((step + 1 : Nat) : Int) + 1 :=
        fun hlt' => (add_nat hi' one_val (fits hB (hstep2_P hlt'))).trans hi_next_eq
      have hslice : byteWindow col[q + step] sidx.val.toNat
          (if ss - sidx < ts - copied then ss - sidx else ts - copied).val.toNat =
          (col.flatten.drop (k * sT + c)).take (min (sS - r) (sT - c)) := by
        unfold byteWindow
        rw [hsidx, Int.toNat_natCast, hnb_nat, hpos, drop_flatten_at col hc (q + step) r he (Nat.le_of_lt hrS),
          take_app_le _ _ _ (by rw [List.length_drop, hce]; exact Nat.min_le_left _ _)]
      have hmc : memcpyValue res col[q + step] copied sidx
          (if ss - sidx < ts - copied then ss - sidx else ts - copied) =
          overwriteBytes (List.replicate sT 0) 0
            ((col.flatten.drop (k * sT)).take (c + min (sS - r) (sT - c))) := by
        unfold memcpyValue
        rw [hslice, hcp, Int.toNat_natCast, hres]
        have h0c : c = 0 + ((col.flatten.drop (k * sT)).take c).length := by
          rw [htl_c, Nat.zero_add]
        conv => lhs; arg 2; rw [h0c]
        rw [overwriteBytes_overwriteBytes (List.replicate sT 0) _ _ 0
            (by rw [htl_c, htl_nb, List.length_replicate, Nat.zero_add]; exact hnb_leT),
          ← List.drop_drop, ← take_add_drop]
      rw [m473_getindexNonReshaped.copyLoop.eq_def, ite_eq_left hcond, hget]
      dsimp only
      exact ih (step + 1) (c + min (sS - r) (sT - c)) 0
        (i + one) (copied + (if ss - sidx < ts - copied then ss - sidx else ts - copied))
        zero _
        hrem_next hnb_leT hS hi_next hcp_next zero_val hinv_next hmc
    · have hc_eq : c = sT := by omega
      subst hc_eq
      have hncond : ¬ (copied < ts) := by rw [lt_iff_val, hcp, hts]; omega
      rw [m473_getindexNonReshaped.copyLoop.eq_def, ite_eq_right hncond, hres]
      have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hc
      have htl : ((col.flatten.drop (k * c)).take c).length = c := by
        rw [List.length_take, List.length_drop, hFl]; omega
      rw [overwriteBytes_full _ _ (by rw [htl, List.length_replicate])]

theorem mainLoop_ok {sS sT : Nat} (hS : 0 < sS) (q k : Nat) (v F : Bytes) (hv : v.length = sT)
    (hpF : k * sT + sT ≤ F.length) (start ss ts : I64)
    (hq : start.val = q) (hss : ss.val = sS) (hts : ts.val = sT) :
    ∀ (rem : Nat) (c : List Bytes) (s : Bytes) (cp step : Nat) (copied i : I64),
      sT - cp ≤ rem →
      WellFormed sS c → c.length * sS = F.length →
      ((c.length * sS : Nat) : Int) ≤ IntTy.max .i64 →
      s.length = sS → cp ≤ sT →
      copied.val = cp → (cp < sT → i.val = (step : Int) + 1) →
      c.flatten = overwriteBytes F (k * sT) (v.take cp) →
      (cp < sT → k * sT + cp = (q + step) * sS) →
      ∃ (c' : List Bytes) (s' : Bytes) (cp' step' : Nat) (copied' i' : I64),
        m619_setindexNonReshaped.mainLoop colParentOps [] v start ss ts c s copied i =
          .ok (c', s', copied', i') ∧
        WellFormed sS c' ∧ c'.length = c.length ∧ cp' ≤ sT ∧
        copied'.val = cp' ∧ (cp' < sT → i'.val = (step' : Int) + 1) ∧
        c'.flatten = overwriteBytes F (k * sT) (v.take cp') ∧
        (cp' < sT → k * sT + cp' = (q + step') * sS) ∧
        ¬ (cp' < sT ∧ sS < sT - cp') := by
  intro rem
  induction rem with
  | zero =>
    intro c s cp step copied i hrem hc _ _ _ hcp hcopied hi hfl hinv
    have hcp_eq : cp = sT := by omega
    subst hcp_eq
    have hnlt : ¬ (copied < ts) := by rw [lt_iff_val, hcopied, hts]; omega
    have hcond_b : ¬ ((decide (copied < ts) && decide (ss < ts - copied)) = true) := by
      simp [hnlt]
    rw [m619_setindexNonReshaped.mainLoop.eq_def, ite_eq_right hcond_b]
    exact ⟨c, s, cp, step, copied, i, rfl, hc, rfl, hcp, hcopied, hi, hfl, hinv, by omega⟩
  | succ rem ih =>
    intro c s cp step copied i hrem hc hcl hB hs hcp hcopied hi hfl hinv
    have hsTP : sT ≤ c.length * sS := by omega
    by_cases hcond : cp < sT ∧ sS < sT - cp
    · have he1 := hinv hcond.1
      have hi_hlt := hi hcond.1
      have heL : q + step < c.length := lt_of_mul_lt (by omega : (q + step) * sS < c.length * sS)
      have hlt1 : copied < ts := by rw [lt_iff_val, hcopied, hts]; omega
      have h1L : q + (step + 1) ≤ c.length * sS := by
        have := Nat.mul_le_mul_right sS (show q + step + 1 ≤ c.length by omega)
        have h1 : q + step + 1 ≤ (q + step + 1) * sS := by
          have := Nat.mul_le_mul_left (q + step + 1) (show 1 ≤ sS from hS)
          rw [Nat.mul_one] at this; exact this
        omega
      have hcp_sS_leT : cp + sS ≤ sT := by omega
      have hcp_sS_leP : cp + sS ≤ c.length * sS := by omega
      have hrem_next : sT - (cp + sS) ≤ rem := by omega
      have hw : ((v.drop cp).take sS).length = sS := by
        rw [List.length_take, List.length_drop, hv]; omega
      have htl : (v.take cp).length = cp := by rw [List.length_take, hv]; omega
      have hfl_next : (c.set (q + step) ((v.drop cp).take sS)).flatten =
          overwriteBytes F (k * sT) (v.take (cp + sS)) := by
        rw [set_flatten c hc (q + step) heL _ hw, hfl,
          show (q + step) * sS = k * sT + (v.take cp).length by rw [htl]; omega,
          overwriteBytes_overwriteBytes F _ _ _ (by rw [htl, hw]; omega), ← List.take_add]
      have hinv_next : cp + sS < sT → k * sT + (cp + sS) = (q + (step + 1)) * sS := by
        intro _
        have hqs : q + (step + 1) = (q + step) + 1 := by omega
        rw [hqs, Nat.add_mul, Nat.one_mul]; omega
      have hstep2_P : cp + sS < sT → step + 1 + 1 ≤ c.length * sS := by
        intro hlt'
        have hpos' := hinv_next hlt'
        have he' : q + (step + 1) < c.length :=
          lt_of_mul_lt (by omega : (q + (step + 1)) * sS < c.length * sS)
        have := Nat.mul_le_mul_right sS (show q + (step + 1) + 1 ≤ c.length by omega)
        have h1 : q + (step + 1) + 1 ≤ (q + (step + 1) + 1) * sS := by
          have := Nat.mul_le_mul_left (q + (step + 1) + 1) (show 1 ≤ sS from hS)
          rw [Nat.mul_one] at this; exact this
        omega
      have hi' : i.val = ((step + 1 : Nat) : Int) := by omega
      have hsi_eq : ((q + (step + 1) : Nat) : Int) = ((q + step : Nat) : Int) + 1 := by omega
      have hi_next_eq : ((step + 1 + 1 : Nat) : Int) = ((step + 1 : Nat) : Int) + 1 := by omega
      have hts_sub : (ts - copied).val = ((sT - cp : Nat) : Int) :=
        sub_nat hts hcopied hcp (fits hB hsTP)
      have hlt2 : ss < ts - copied := by
        rw [lt_iff_val, hss, hts_sub]; exact Int.ofNat_lt.mpr hcond.2
      have hcond_b : (decide (copied < ts) && decide (ss < ts - copied)) = true := by
        simp [hlt1, hlt2]
      have hsi : (start + i).val = ((q + step : Nat) : Int) + 1 :=
        (add_nat hq hi' (fits hB h1L)).trans hsi_eq
      have hmc : memcpyValue s v zero copied (if ss < ts - copied then ss else ts - copied) =
          (v.drop cp).take sS := by
        rw [ite_eq_left hlt2]
        unfold memcpyValue byteWindow
        rw [zero_val, hcopied, hss, Int.toNat_zero, Int.toNat_natCast, Int.toNat_natCast,
          overwriteBytes_full s _ (by rw [hw, hs])]
      have hcp_next : (copied + (if ss < ts - copied then ss else ts - copied)).val =
          ((cp + sS : Nat) : Int) := by
        rw [ite_eq_left hlt2]
        exact add_nat hcopied hss (fits hB hcp_sS_leP)
      have hi_next : cp + sS < sT → (i + one).val = ((step + 1 : Nat) : Int) + 1 :=
        fun hlt' => (add_nat hi' one_val (fits hB (hstep2_P hlt'))).trans hi_next_eq
      have hset : colParentOps.set c [start + i]
          (memcpyValue s v zero copied (if ss < ts - copied then ss else ts - copied)) =
          .ok (c.set (q + step) ((v.drop cp).take sS)) := by
        rw [hmc]; exact colSet_ok c (start + i) (q + step) _ hsi heL
      obtain ⟨c', s', cp', step', copied', i', hrun, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        ih (c.set (q + step) ((v.drop cp).take sS)) ((v.drop cp).take sS) (cp + sS) (step + 1)
          (copied + (if ss < ts - copied then ss else ts - copied)) (i + one)
          hrem_next (wf_set hc (q + step) _ hw) (by rw [List.length_set]; exact hcl)
          (by rw [List.length_set]; exact hB) hw hcp_sS_leT hcp_next hi_next
          hfl_next hinv_next
      refine ⟨c', s', cp', step', copied', i', ?_, h1, by rw [h2, List.length_set], h3, h4, h5, h6, h7, h8⟩
      rw [m619_setindexNonReshaped.mainLoop.eq_def, ite_eq_left hcond_b]
      dsimp only
      rw [hset]
      dsimp only
      rw [hmc]
      exact hrun
    · have hts_sub : (ts - copied).val = ((sT - cp : Nat) : Int) :=
        sub_nat hts hcopied hcp (fits hB hsTP)
      have hcond_b : ¬ ((decide (copied < ts) && decide (ss < ts - copied)) = true) := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, lt_iff_val, hcopied, hts, hss, hts_sub]
        exact fun ⟨h1, h2⟩ => hcond ⟨Int.ofNat_lt.mp h1, Int.ofNat_lt.mp h2⟩
      rw [m619_setindexNonReshaped.mainLoop.eq_def, ite_eq_right hcond_b]
      exact ⟨c, s, cp, step, copied, i, rfl, hc, rfl, hcp, hcopied, hi, hfl, hinv, hcond⟩

theorem setTail_ok {sS sT : Nat} (hS : 0 < sS) (q k : Nat) (v F : Bytes) (hv : v.length = sT)
    (hpF : k * sT + sT ≤ F.length) (start ss ts : I64)
    (hq : start.val = q) (hss : ss.val = sS) (hts : ts.val = sT)
    (c : List Bytes) (cp step : Nat) (copied i : I64)
    (hc : WellFormed sS c) (hcl : c.length * sS = F.length)
    (hB : ((c.length * sS : Nat) : Int) ≤ IntTy.max .i64)
    (hcp : cp ≤ sT) (hcopied : copied.val = cp) (hi : cp < sT → i.val = (step : Int) + 1)
    (hfl : c.flatten = overwriteBytes F (k * sT) (v.take cp))
    (hinv : cp < sT → k * sT + cp = (q + step) * sS)
    (hstop : ¬ (cp < sT ∧ sS < sT - cp)) :
    ∃ c', (if copied < ts then do
        let s' ← colParentOps.get c [start + i]
        let nb := if ss < ts - copied then ss else ts - copied
        let s' := memcpyValue s' v zero copied nb
        colParentOps.set c [start + i] s'
      else pure c) = .ok c' ∧
      WellFormed sS c' ∧ c'.length = c.length ∧
      c'.flatten = overwriteBytes F (k * sT) v := by
  by_cases hlt : cp < sT
  · have he1 := hinv hlt
    have hi_hlt := hi hlt
    have heL : q + step < c.length := lt_of_mul_lt (by omega : (q + step) * sS < c.length * sS)
    have hce : c[q + step].length = sS := hc _ (List.getElem_mem heL)
    have h1L : q + (step + 1) ≤ c.length * sS := by
      have := Nat.mul_le_mul_right sS (show q + step + 1 ≤ c.length by omega)
      have h1 : q + step + 1 ≤ (q + step + 1) * sS := by
        have := Nat.mul_le_mul_left (q + step + 1) (show 1 ≤ sS from hS)
        rw [Nat.mul_one] at this; exact this
      omega
    have hsTP : sT ≤ c.length * sS := by omega
    have hnot_lt_sS : ¬ (sS < sT - cp) := fun h => hstop ⟨hlt, h⟩
    have hle_sS : sT - cp ≤ sS := by omega
    have hwl : ((v.drop cp).take (sT - cp)).length = sT - cp := by
      rw [List.length_take, List.length_drop, hv]; omega
    have htl : (v.take cp).length = cp := by rw [List.length_take, hv]; omega
    have hfl_final : (c.set (q + step) (overwriteBytes c[q + step] 0 ((v.drop cp).take (sT - cp)))).flatten =
        overwriteBytes F (k * sT) v := by
      rw [set_overwriteBytes_flatten c hc (q + step) 0 heL _ (by rw [hwl]; omega), Nat.add_zero, hfl,
        show (q + step) * sS = k * sT + (v.take cp).length by rw [htl]; omega,
        overwriteBytes_overwriteBytes F _ _ _ (by rw [htl, hwl]; omega), ← List.take_add,
        List.take_of_length_le (by rw [hv]; omega)]
    have hi' : i.val = ((step + 1 : Nat) : Int) := by omega
    have hsi_eq : ((q + (step + 1) : Nat) : Int) = ((q + step : Nat) : Int) + 1 := by omega
    have hsi : (start + i).val = ((q + step : Nat) : Int) + 1 :=
      (add_nat hq hi' (fits hB h1L)).trans hsi_eq
    have hcond : copied < ts := by rw [lt_iff_val, hcopied, hts]; omega
    have hts_sub : (ts - copied).val = ((sT - cp : Nat) : Int) :=
      sub_nat hts hcopied hcp (fits hB hsTP)
    have hnlt2 : ¬ (ss < ts - copied) := by
      rw [lt_iff_val, hss, hts_sub]; exact fun h => hnot_lt_sS (Int.ofNat_lt.mp h)
    have hget : colParentOps.get c [start + i] = .ok c[q + step] := colGet_ok c (start + i) (q + step) hsi heL
    have hmc : memcpyValue c[q + step] v zero copied (if ss < ts - copied then ss else ts - copied) =
        overwriteBytes c[q + step] 0 ((v.drop cp).take (sT - cp)) := by
      rw [ite_eq_right hnlt2]
      unfold memcpyValue byteWindow
      rw [zero_val, hcopied, hts_sub, Int.toNat_zero, Int.toNat_natCast, Int.toNat_natCast]
    have hset : colParentOps.set c [start + i] (overwriteBytes c[q + step] 0 ((v.drop cp).take (sT - cp))) =
        .ok (c.set (q + step) (overwriteBytes c[q + step] 0 ((v.drop cp).take (sT - cp)))) :=
      colSet_ok c (start + i) (q + step) _ hsi heL
    rw [ite_eq_left hcond]
    dsimp only
    rw [hget, resultBindOk, hmc, hset]
    refine ⟨_, rfl, wf_set hc (q + step) _ ?_, by rw [List.length_set], hfl_final⟩
    rw [overwriteBytes_length _ _ _ (by rw [hwl, hce, Nat.zero_add]; exact hle_sS), hce]
  · have hncond : ¬ (copied < ts) := by rw [lt_iff_val, hcopied, hts]; omega
    rw [ite_eq_right hncond]
    refine ⟨c, rfl, hc, rfl, ?_⟩
    rw [hfl, List.take_of_length_le (by rw [hv]; omega)]

/-- A byte-sized layout of aligned byte width `size`, either primitive (`primitive = true`) or a
packed non-primitive layout (`primitive = false`). -/
def sizedLayout (id size : Nat) (primitive : Bool) : TypeLayout :=
  .mk ⟨id, size * 8, JInt.lit .i64 size, true, primitive, false, size == 0, false⟩ [] []

/-- A byte-sized, packed primitive layout. -/
def primitiveLayout (id size : Nat) : TypeLayout := sizedLayout id size true

@[simp] theorem hasBitPadding_sizedLayout (id size : Nat) (primitive : Bool) :
    m828_hasBitPadding (sizedLayout id size primitive) = false := by
  rw [m828_hasBitPadding.eq_def]
  cases primitive
  · rfl
  · have hp : (sizedLayout id size true).primitive = true := rfl
    rw [ite_eq_left hp]
    change (size * 8 % 8 != 0) = false
    simp

@[simp] theorem hasBitPadding_primitiveLayout (id size : Nat) :
    m828_hasBitPadding (primitiveLayout id size) = false :=
  hasBitPadding_sizedLayout id size true

@[simp] theorem ispacked_sizedLayout (id size : Nat) (primitive : Bool) :
    m824_ispacked (sizedLayout id size primitive) = true := rfl

@[simp] theorem packedsize_sizedLayout (id size : Nat) (primitive : Bool) :
    m816_packedsize (sizedLayout id size primitive) = .ok (JInt.lit .i64 size).val.toNat := rfl

@[simp] theorem alignedSize_sizedLayout (id size : Nat) (primitive : Bool) :
    (sizedLayout id size primitive).alignedSize = JInt.lit .i64 size := rfl
theorem reinterpret_packed (out inp : TypeLayout) (src dst : Bytes) (ps : Nat)
    (hb1 : out.isBits = true) (hb2 : inp.isBits = true)
    (hbp1 : m828_hasBitPadding out = false) (hbp2 : m828_hasBitPadding inp = false)
    (hps1 : m816_packedsize out = .ok ps) (hps2 : m816_packedsize inp = .ok ps)
    (hisp1 : m824_ispacked out = true) (hisp2 : m824_ispacked inp = true) :
    m882_reinterpret out inp src dst = .ok (memcpyValue dst src zero zero out.alignedSize) := by
  unfold m882_reinterpret
  simp [hb1, hb2, hbp1, hbp2, hps1, hps2, hisp1, hisp2]

/-! ## Entry 1: `reinterpretarrays-size-overflow` (refuted) -/

/-- The source and target first-dimension byte counts agree as mathematical integers. -/
def ReinterpretSizeOverflow : Prop :=
  ∀ {T S A : Type} (target source : TypeLayout) (input : ArrayInput A)
    (view : ReinterpretArray T S (ArrayInput A)) (dims : List I64),
    m73_reinterpret target source input = .ok view →
    m374_sizeNonReshaped ArrayInput.size divInt view = .ok dims →
    (dims.headD zero).val * target.alignedSize.val =
      (input.size.headD zero).val * source.alignedSize.val

def overflowInput : ArrayInput Unit :=
  ⟨(), 1, [JInt.lit .i64 (2^61)], [⟨one, JInt.lit .i64 (2^61)⟩]⟩
def overflowView : ReinterpretArray Unit Unit (ArrayInput Unit) :=
  ⟨overflowInput, 1, primitiveLayout 32 4, primitiveLayout 64 8, true, true, false⟩



/-! ## Sizes and index arithmetic -/

theorem lit_mul_lit (L sS : Nat) (hB : ((L * sS : Nat) : Int) ≤ IntTy.max .i64) :
    (JInt.lit .i64 (L : Int) * JInt.lit .i64 (sS : Int)).val = ((L * sS : Nat) : Int) := by
  rw [val_mul, val_lit, val_lit, wrapInt_mul, ← Int.natCast_mul]
  exact wrapInt_nat _ hB

theorem rem_zero_mod {sT P : Nat} {prod : I64} (hT : 0 < sT) (hTM : (sT : Int) ≤ IntTy.max .i64)
    (hmul : prod.val = (P : Int))
    (hrem : remInt prod (JInt.lit .i64 (sT : Int)) = .ok zero) : P % sT = 0 := by
  have hTv : (JInt.lit .i64 (sT : Int)).val = sT := lit_nat sT hTM
  have hlt : P % sT < sT := Nat.mod_lt P hT
  have hr : (JInt.wrap .i64 ((P % sT : Nat) : Int)).val = ((P % sT : Nat) : Int) :=
    wrap_nat _ (Int.le_trans (Int.ofNat_le.mpr (Nat.le_of_lt hlt)) hTM)
  have h1 := remInt_nat hmul hTv hT
  rw [hrem] at h1
  have h2 : (JInt.wrap .i64 ((P % sT : Nat) : Int)).val = zero.val :=
    congrArg Subtype.val (Except.ok.inj h1.symm)
  rw [hr, zero_val] at h2
  exact Int.ofNat_inj.mp h2

theorem div_size_val {sT P : Nat} {prod sz1 : I64} (hT : 0 < sT)
    (hTM : (sT : Int) ≤ IntTy.max .i64) (hB : (P : Int) ≤ IntTy.max .i64)
    (hmul : prod.val = (P : Int))
    (hdiv : divInt prod (JInt.lit .i64 (sT : Int)) = .ok sz1) :
    sz1.val = ((P / sT : Nat) : Int) := by
  have hTv : (JInt.lit .i64 (sT : Int)).val = sT := lit_nat sT hTM
  have h1 := divInt_nat hmul hTv hT
  rw [hdiv] at h1
  have h2 := Except.ok.inj h1.symm
  subst h2
  exact wrap_nat _ (fits hB (Nat.div_le_self _ _))

theorem size_facts {sS sT : Nat} {col : List Bytes} {sz1 : I64} (hT : 0 < sT)
    (hTM : (sT : Int) ≤ IntTy.max .i64) (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64)
    (hrem : remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero)
    (hdiv : divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1) :
    ∃ N : Nat, sz1.val = N ∧ N * sT = col.length * sS := by
  have hmul := lit_mul_lit col.length sS hB
  have hmod := rem_zero_mod hT hTM hmul hrem
  exact ⟨col.length * sS / sT, div_size_val hT hTM hB hmul hdiv,
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)⟩

theorem index_facts {sS sT : Nat} {col : List Bytes} {i1 : I64} {k : Nat} (hS : 0 < sS)
    (hT : 0 < sT) (hk : i1.val = (k : Int) + 1) (hkb : k * sT + sT ≤ col.length * sS)
    (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64) :
    divremInt ((i1 - one) * JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
      .ok (JInt.wrap .i64 ((k * sT / sS : Nat) : Int), JInt.wrap .i64 ((k * sT % sS : Nat) : Int)) ∧
    (JInt.wrap .i64 ((k * sT / sS : Nat) : Int)).val = ((k * sT / sS : Nat) : Int) ∧
    (JInt.wrap .i64 ((k * sT % sS : Nat) : Int)).val = ((k * sT % sS : Nat) : Int) := by
  have hL1 : 1 ≤ col.length := by
    rcases Nat.eq_zero_or_pos col.length with h0 | h0
    · rw [h0, Nat.zero_mul] at hkb; omega
    · exact h0
  have hSle : sS ≤ col.length * sS := by
    have := Nat.mul_le_mul_right sS hL1
    rw [Nat.one_mul] at this; exact this
  have hkle : k ≤ k * sT := by
    have := Nat.mul_le_mul_left k (show 1 ≤ sT from hT)
    rw [Nat.mul_one] at this; exact this
  have hkP : k * sT ≤ col.length * sS := Nat.le_trans (Nat.le_add_right _ _) hkb
  have hTle : sT ≤ col.length * sS := Nat.le_trans (Nat.le_add_left _ _) hkb
  have hqle : k * sT / sS ≤ k * sT := Nat.div_le_self _ _
  have hrl : k * sT % sS < sS := Nat.mod_lt _ hS
  have hk1_eq : (k : Int) + 1 - 1 = (k : Int) := by omega
  have hsub : (i1 - one).val = (k : Int) := by
    rw [val_sub, hk, one_val, hk1_eq]
    exact wrapInt_nat k (fits hB (Nat.le_trans hkle hkP))
  have hTv := lit_nat sT (fits hB hTle)
  have hSv := lit_nat sS (fits hB hSle)
  have hx := mul_nat hsub hTv (fits hB hkP)
  exact ⟨divremInt_nat hx hSv hS,
    wrap_nat _ (fits hB (Nat.le_trans hqle hkP)),
    wrap_nat _ (fits hB (Nat.le_trans (Nat.le_of_lt hrl) hSle))⟩

theorem checkFirst1D_ok {T S A : Type} (sz1 i1 : I64) (a : ReinterpretArray T S A)
    (hin : 1 ≤ i1.val ∧ i1.val ≤ sz1.val) :
    checkFirst1D sz1 a i1 [] = .ok () := by
  unfold checkFirst1D; simp [hin]

theorem checkFirst1D_err {T S A : Type} (sz1 i1 : I64) (a : ReinterpretArray T S A)
    (hin : ¬ (1 ≤ i1.val ∧ i1.val ≤ sz1.val)) :
    checkFirst1D sz1 a i1 [] = .error .bounds := by
  unfold checkFirst1D; simp [hin]

/-- The bytes of element `i1` of `reinterpret(T, A)`: bytes `(i1-1)*sT+1 : i1*sT` of the column. -/
def expectedBytes (sT : Nat) (col : List Bytes) (i1 : Int) : Bytes :=
  (col.flatten.drop ((i1.toNat - 1) * sT)).take sT

theorem raGetNonReshaped_eq {sS sT : Nat} {scalar : Bool} {col : List Bytes} {i1 sz1 : I64}
    (hS : 0 < sS) (hT : 0 < sT) (hTM : (sT : Int) ≤ IntTy.max .i64)
    (hsc : scalar = true → sS = sT) (hwf : WellFormed sS col)
    (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64)
    (hrem : remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero)
    (hdiv : divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1) :
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 1, sizedLayout 1 sT scalar, sizedLayout 2 sS scalar, true, true, false⟩
    m473_getindexNonReshaped (checkFirst1D sz1) colGet a i1 [] =
      if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then .ok (expectedBytes sT col i1.val)
      else .error .bounds := by
  dsimp only
  obtain ⟨N, hN, hNT⟩ := size_facts hT hTM hB hrem hdiv
  have hsing : (sizedLayout 1 sT scalar).singleton = false := by
    unfold sizedLayout TypeLayout.singleton LayoutInfo.singleton
    exact beq_eq_false_iff_ne.mpr (by omega)
  have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hwf
  by_cases hin : 1 ≤ i1.val ∧ i1.val ≤ sz1.val
  · rw [ite_eq_left hin]
    obtain ⟨k, hk⟩ : ∃ k : Nat, i1.val = (k : Int) + 1 := ⟨(i1.val - 1).toNat, by omega⟩
    have hkN : k + 1 ≤ N := by omega
    have hkb : k * sT + sT ≤ col.length * sS := by
      have := Nat.mul_le_mul_right sT hkN
      rw [Nat.add_mul, Nat.one_mul, hNT] at this
      exact this
    have hexp : expectedBytes sT col i1.val = (col.flatten.drop (k * sT)).take sT := by
      unfold expectedBytes
      rw [show i1.val.toNat - 1 = k by omega]
    rw [hexp]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hkL : k < col.length := lt_of_mul_lt (by omega : k * sS < col.length * sS)
      have hck : col[k].length = sS := hwf _ (List.getElem_mem hkL)
      have hsc_true : m469_scalarApplicable (sizedLayout 1 sS true) (sizedLayout 2 sS true) = true := by
        simp [m469_scalarApplicable, sizedLayout, TypeLayout.primitive, TypeLayout.bits, TypeLayout.info]
      have hlit_sS : (JInt.lit .i64 (sS : Int)).val.toNat = sS := by
        rw [lit_nat sS hTM, Int.toNat_natCast]
      have hps1 : m816_packedsize (sizedLayout 1 sS true) = .ok sS := by
        rw [packedsize_sizedLayout, hlit_sS]
      have hps2 : m816_packedsize (sizedLayout 2 sS true) = .ok sS := by
        rw [packedsize_sizedLayout, hlit_sS]
      have hget := colGet_ok col i1 k hk hkL
      have hmc : memcpyValue (List.replicate (JInt.lit .i64 (sS : Int)).val.toNat 0) col[k] zero zero
          (JInt.lit .i64 (sS : Int)) = col[k] := by
        unfold memcpyValue byteWindow
        rw [zero_val, hlit_sS, Int.toNat_zero, List.drop_zero,
          List.take_of_length_le (Nat.le_of_eq hck),
          overwriteBytes_full _ _ (by rw [hck, List.length_replicate])]
      unfold m473_getindexNonReshaped
      rw [hsing, ite_eq_right Bool.false_ne_true, ite_eq_left hsc_true, hget, resultBindOk,
        reinterpret_packed (sizedLayout 1 sS true) (sizedLayout 2 sS true) col[k] _ sS
          rfl rfl (hasBitPadding_sizedLayout _ _ _) (hasBitPadding_sizedLayout _ _ _)
          hps1 hps2 rfl rfl]
      change Except.ok (memcpyValue (List.replicate (JInt.lit .i64 (sS : Int)).val.toNat 0) col[k] zero zero
        (JInt.lit .i64 (sS : Int))) = _
      rw [hmc, ← flatten_drop_mul col k hwf, List.drop_eq_getElem_cons hkL, List.flatten_cons,
        take_app_le _ _ _ (Nat.le_of_eq hck.symm), List.take_of_length_le (Nat.le_of_eq hck)]
    | false =>
      have hsc_false : m469_scalarApplicable (sizedLayout 1 sT false) (sizedLayout 2 sS false) = false := rfl
      have hcf := checkFirst1D_ok (T := Unit) (S := Unit) sz1 i1
        ⟨col, 1, sizedLayout 1 sT false, sizedLayout 2 sS false, true, true, false⟩ hin
      have hdm : k * sT / sS * sS + k * sT % sS = k * sT := by
        have := Nat.div_add_mod (k * sT) sS
        have := Nat.mul_comm sS (k * sT / sS)
        omega
      have hrl : k * sT % sS < sS := Nat.mod_lt _ hS
      have hL1 : 1 ≤ col.length := by
        rcases Nat.eq_zero_or_pos col.length with h0 | h0
        · rw [h0, Nat.zero_mul] at hkb; omega
        · exact h0
      have hSle : sS ≤ col.length * sS := by
        have := Nat.mul_le_mul_right sS hL1
        rw [Nat.one_mul] at this; exact this
      have hTle : sT ≤ col.length * sS := Nat.le_trans (Nat.le_add_left _ _) hkb
      have hqL : k * sT / sS < col.length :=
        lt_of_mul_lt (by omega : k * sT / sS * sS < col.length * sS)
      have h1L : k * sT / sS + 1 ≤ col.length * sS := by
        have := Nat.mul_le_mul_right sS (show k * sT / sS + 1 ≤ col.length by omega)
        have h1' : k * sT / sS + 1 ≤ (k * sT / sS + 1) * sS := by
          have := Nat.mul_le_mul_left (k * sT / sS + 1) (show 1 ≤ sS from hS)
          rw [Nat.mul_one] at this; exact this
        omega
      have hTv := lit_nat sT (fits hB hTle)
      have hSv := lit_nat sS (fits hB hSle)
      have hTv_nat : (JInt.lit .i64 (sT : Int)).val.toNat = sT := by rw [hTv, Int.toNat_natCast]
      obtain ⟨hdivrem, hqv, hrv⟩ := index_facts hS hT hk hkb hB
      have hrem_ts : remInt (JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
          .ok (JInt.wrap .i64 ((sT % sS : Nat) : Int)) := remInt_nat hTv hSv hS
      have hrem_ts_val : (JInt.wrap .i64 ((sT % sS : Nat) : Int)).val = ((sT % sS : Nat) : Int) :=
        wrap_nat _ (fits hB (Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hS)) hSle))
      have hrem_st : remInt (JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int)) =
          .ok (JInt.wrap .i64 ((sS % sT : Nat) : Int)) := remInt_nat hSv hTv hT
      have hrem_st_val : (JInt.wrap .i64 ((sS % sT : Nat) : Int)).val = ((sS % sT : Nat) : Int) :=
        wrap_nat _ (fits hB (Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hT)) hTle))
      unfold m473_getindexNonReshaped
      rw [hsing, hsc_false, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        hcf, resultBindOk, alignedSize_sizedLayout, alignedSize_sizedLayout]
      dsimp only
      rw [hdivrem, resultBindOk]
      dsimp only
      rw [hrem_ts, resultBindOk]
      by_cases h1 : sT % sS = 0
      · have hbeq1 : (JInt.wrap .i64 ((sT % sS : Nat) : Int) == zero) = true := by
          rw [beq_iff_val, hrem_ts_val, zero_val, h1]; rfl
        obtain ⟨n, hn⟩ : ∃ n, sT = n * sS :=
          ⟨sT / sS, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)).symm⟩
        have hn' : sT / sS = n := by rw [hn, Nat.mul_div_cancel _ hS]
        have hq : k * sT / sS = k * n := by rw [hn, ← Nat.mul_assoc, Nat.mul_div_cancel _ hS]
        have hkn : k * n + n ≤ col.length := by
          apply le_of_mul_le hS
          rw [Nat.add_mul, Nat.mul_assoc, ← hn]
          exact hkb
        have hn_le : n ≤ col.length * sS := by
          have h1sS : n * 1 ≤ n * sS := Nat.mul_le_mul_left n hS
          rw [Nat.mul_one, ← hn] at h1sS
          exact Nat.le_trans h1sS hTle
        have hdiv_ts : divInt (JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
            .ok (JInt.wrap .i64 (n : Int)) := by
          rw [divInt_nat hTv hSv hS, hn']
        have hn_val : (JInt.wrap .i64 (n : Int)).val = (n : Int) :=
          wrap_nat n (fits hB hn_le)
        have hqv' : (JInt.wrap .i64 ((k * sT / sS : Nat) : Int)).val = ((k * n : Nat) : Int) := by
          rw [hqv, hq]
        have hfl_n : (((col.drop (k * n)).take n).flatten).length = sT := by
          rw [length_flatten_take (col.drop (k * n)) (wf_drop hwf _) n
            (by rw [List.length_drop]; exact Nat.le_sub_of_add_le' hkn), hn]
        rw [hbeq1, ite_eq_left rfl, hdiv_ts, resultBindOk, hTv_nat,
          intRange_one hn_val, List.range_eq_range',
          forIn_get_mult col hwf (List.replicate sT 0) _ _ (k * n) hqv' hSv hB hS n 0
            (List.replicate sT 0) (by rw [Nat.add_zero]; exact hkn)
            (by rw [Nat.zero_add, List.length_replicate, hn]; exact Nat.le_refl _)
            (by rw [List.take_zero, List.flatten_nil, overwriteBytes_nil]),
          resultBindOk, resultPure, Nat.zero_add,
          overwriteBytes_full _ _ (by rw [hfl_n, List.length_replicate]),
          flatten_take_mul _ n (wf_drop hwf _), flatten_drop_mul col _ hwf,
          Nat.mul_assoc, ← hn]
      · have hbeq1 : (JInt.wrap .i64 ((sT % sS : Nat) : Int) == zero) = false := by
          rw [beq_iff_val, hrem_ts_val, zero_val]
          exact decide_eq_false (fun h => h1 (Int.ofNat_inj.mp h))
        rw [hbeq1, ite_eq_right Bool.false_ne_true, hrem_st, resultBindOk]
        by_cases h2 : sS % sT = 0
        · have hbeq2 : (JInt.wrap .i64 ((sS % sT : Nat) : Int) == zero) = true := by
            rw [beq_iff_val, hrem_st_val, zero_val, h2]; rfl
          have hrs : k * sT % sS + sT ≤ sS := rem_add_le hS h2
          have hce : col[k * sT / sS].length = sS := hwf _ (List.getElem_mem hqL)
          have hstart1 : (JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one).val =
              ((k * sT / sS : Nat) : Int) + 1 :=
            add_nat hqv one_val (fits hB h1L)
          have hget := colGet_ok col _ (k * sT / sS) hstart1 hqL
          rw [hbeq2, ite_eq_left rfl, hget, resultBindOk, resultPure]
          unfold byteWindow
          rw [hrv, Int.toNat_natCast, hTv_nat,
            show col.flatten.drop (k * sT) = col.flatten.drop (k * sT / sS * sS + k * sT % sS) by
              rw [hdm],
            drop_flatten_at col hwf (k * sT / sS) (k * sT % sS) hqL (Nat.le_of_lt hrl),
            take_app_le _ _ _ (by rw [List.length_drop, hce]; exact Nat.le_sub_of_add_le' hrs)]
        · have hbeq2 : (JInt.wrap .i64 ((sS % sT : Nat) : Int) == zero) = false := by
            rw [beq_iff_val, hrem_st_val, zero_val]
            exact decide_eq_false (fun h => h2 (Int.ofNat_inj.mp h))
          rw [hbeq2, ite_eq_right Bool.false_ne_true, hTv_nat]
          exact copyLoop_ok col hwf _ _ _ (k * sT / sS) k hqv hSv hTv hS hkb hB
            sT 0 0 (k * sT % sS) one zero _ (List.replicate sT 0)
            (Nat.sub_zero sT ▸ Nat.le_refl sT) (Nat.zero_le sT) hrl
            (fun _ => one_val) zero_val hrv
            (fun _ => by rw [Nat.add_zero, Nat.add_zero, hdm])
            (by rw [List.take_zero, overwriteBytes_nil])
  · rw [ite_eq_right hin]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hNL : N = col.length := Nat.eq_of_mul_eq_mul_right hS hNT
      have hsc_true : m469_scalarApplicable (sizedLayout 1 sS true) (sizedLayout 2 sS true) = true := by
        simp [m469_scalarApplicable, sizedLayout, TypeLayout.primitive, TypeLayout.bits, TypeLayout.info]
      have hget : colGet col [i1] = .error .bounds := by
        unfold colGet; dsimp only
        rw [ite_eq_right (by omega)]
      unfold m473_getindexNonReshaped
      rw [hsing, ite_eq_right Bool.false_ne_true, ite_eq_left hsc_true, hget, resultBindError]
    | false =>
      have hsc_false : m469_scalarApplicable (sizedLayout 1 sT false) (sizedLayout 2 sS false) = false := rfl
      have hcf := checkFirst1D_err (T := Unit) (S := Unit) sz1 i1
        ⟨col, 1, sizedLayout 1 sT false, sizedLayout 2 sS false, true, true, false⟩ hin
      unfold m473_getindexNonReshaped
      rw [hsing, hsc_false, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
      dsimp only
      rw [hcf, resultBindError]

@[simp] theorem colParentOps_get : colParentOps.get = colGet := rfl
@[simp] theorem colParentOps_set : colParentOps.set = colSet := rfl

theorem map_setTail2 {α β γ : Type} (cond : Prop) [Decidable cond]
    (m1 : RResult α) (m2 : α → RResult β) (x y : β) (f : β → γ)
    (h : (if cond then (m1 >>= m2) else pure x) = .ok y) :
    (if cond then (m1 >>= fun a => m2 a >>= fun p => pure (f p)) else pure (f x)) = .ok (f y) := by
  by_cases hc : cond
  · rw [ite_eq_left hc] at h ⊢
    rcases hm1 : m1 with e | a
    · rw [hm1, resultBindError] at h; cases h
    · rw [hm1, resultBindOk] at h
      rw [resultBindOk, h, resultBindOk]; rfl
  · rw [ite_eq_right hc] at h ⊢
    cases h; rfl
theorem setStart_nb_facts {ss sidx ts : I64} {sS r sT P : Nat}
    (hss : ss.val = sS) (hsidx : sidx.val = r) (hts : ts.val = sT)
    (hr : r < sS) (hsSP : sS ≤ P) (hB : (P : Int) ≤ IntTy.max .i64) :
    (if ss - sidx < ts then ss - sidx else ts).val =
      ((min (sS - r) sT : Nat) : Int) ∧
    (if ss - sidx < ts then ss - sidx else ts).val.toNat =
      min (sS - r) sT ∧
    (zero + (if ss - sidx < ts then ss - sidx else ts)).val =
      ((min (sS - r) sT : Nat) : Int) ∧
    min (sS - r) sT ≤ sT ∧
    (min (sS - r) sT < sT → r + min (sS - r) sT = sS) := by
  have hr_le : r ≤ sS := by omega
  have hmin_leP : 0 + min (sS - r) sT ≤ P := by omega
  have hleT : min (sS - r) sT ≤ sT := by omega
  have hfull : min (sS - r) sT < sT → r + min (sS - r) sT = sS := fun _ => by omega
  have hss_sub : (ss - sidx).val = ((sS - r : Nat) : Int) :=
    sub_nat hss hsidx hr_le (fits hB hsSP)
  have hnb : (if ss - sidx < ts then ss - sidx else ts).val =
      ((min (sS - r) sT : Nat) : Int) := by
    by_cases hm : sS - r < sT
    · have hmin1 : min (sS - r) sT = sS - r := Nat.min_eq_left (Nat.le_of_lt hm)
      have hlt_b : ss - sidx < ts := by
        rw [lt_iff_val, hss_sub, hts]; exact Int.ofNat_lt.mpr hm
      rw [ite_eq_left hlt_b, hmin1, hss_sub]
    · have hge : sT ≤ sS - r := Nat.le_of_not_lt hm
      have hmin2 : min (sS - r) sT = sT := Nat.min_eq_right hge
      have hnlt_b : ¬ (ss - sidx < ts) := by
        rw [lt_iff_val, hss_sub, hts]; exact fun h => hm (Int.ofNat_lt.mp h)
      rw [ite_eq_right hnlt_b, hmin2, hts]
  have hcp1 : (zero + (if ss - sidx < ts then ss - sidx else ts)).val =
      ((0 + min (sS - r) sT : Nat) : Int) :=
    add_nat zero_val hnb (fits hB hmin_leP)
  rw [Nat.zero_add] at hcp1
  exact ⟨hnb, by rw [hnb, Int.toNat_natCast], hcp1, hleT, hfull⟩

theorem raSetNonReshaped_eq {sS sT : Nat} {scalar : Bool} {col : List Bytes} {i1 sz1 : I64} {v : Bytes}
    (hS : 0 < sS) (hT : 0 < sT) (hTM : (sT : Int) ≤ IntTy.max .i64)
    (hsc : scalar = true → sS = sT) (hwf : WellFormed sS col) (hv : v.length = sT)
    (hB : ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64)
    (hrem : remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero)
    (hdiv : divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1) :
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 1, sizedLayout 1 sT scalar, sizedLayout 2 sS scalar, true, true, false⟩
    if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then
      ∃ col', m619_setindexNonReshaped (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 [] =
        .ok { a with parent := col' } ∧
        WellFormed sS col' ∧ col'.length = col.length ∧
        col'.flatten = overwriteBytes col.flatten ((i1.val.toNat - 1) * sT) v
    else
      m619_setindexNonReshaped (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 [] =
        .error .bounds := by
  dsimp only
  obtain ⟨N, hN, hNT⟩ := size_facts hT hTM hB hrem hdiv
  have hsing : (sizedLayout 1 sT scalar).singleton = false := by
    unfold sizedLayout TypeLayout.singleton LayoutInfo.singleton
    exact beq_eq_false_iff_ne.mpr (by omega)
  have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hwf
  by_cases hin : 1 ≤ i1.val ∧ i1.val ≤ sz1.val
  · rw [ite_eq_left hin]
    obtain ⟨k, hk⟩ : ∃ k : Nat, i1.val = (k : Int) + 1 := ⟨(i1.val - 1).toNat, by omega⟩
    have hkN : k + 1 ≤ N := by omega
    have hkb : k * sT + sT ≤ col.length * sS := by
      have := Nat.mul_le_mul_right sT hkN
      rw [Nat.add_mul, Nat.one_mul, hNT] at this
      exact this
    rw [show i1.val.toNat - 1 = k by omega]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hkL : k < col.length := lt_of_mul_lt (by omega : k * sS < col.length * sS)
      have hsc_true : m469_scalarApplicable (sizedLayout 1 sS true) (sizedLayout 2 sS true) = true := by
        simp [m469_scalarApplicable, sizedLayout, TypeLayout.primitive, TypeLayout.bits, TypeLayout.info]
      have hlit_sS : (JInt.lit .i64 (sS : Int)).val.toNat = sS := by
        rw [lit_nat sS hTM, Int.toNat_natCast]
      have hps1 : m816_packedsize (sizedLayout 2 sS true) = .ok sS := by
        rw [packedsize_sizedLayout, hlit_sS]
      have hps2 : m816_packedsize (sizedLayout 1 sS true) = .ok sS := by
        rw [packedsize_sizedLayout, hlit_sS]
      have hmc : memcpyValue (List.replicate (JInt.lit .i64 (sS : Int)).val.toNat 0) v zero zero
          (JInt.lit .i64 (sS : Int)) = v := by
        unfold memcpyValue byteWindow
        rw [zero_val, hlit_sS, Int.toNat_zero, List.drop_zero,
          List.take_of_length_le (Nat.le_of_eq hv),
          overwriteBytes_full _ _ (by rw [hv, List.length_replicate])]
      have hset : colParentOps.set col [i1] v = .ok (col.set k v) := colSet_ok col i1 k v hk hkL
      refine ⟨col.set k v, ?_, wf_set hwf k v hv, by rw [List.length_set],
        set_flatten col hwf k hkL v hv⟩
      unfold m619_setindexNonReshaped
      rw [resultBindOk, hsing, ite_eq_right Bool.false_ne_true, ite_eq_left hsc_true,
        reinterpret_packed (sizedLayout 2 sS true) (sizedLayout 1 sS true) v _ sS
          rfl rfl (hasBitPadding_sizedLayout _ _ _) (hasBitPadding_sizedLayout _ _ _)
          hps1 hps2 rfl rfl,
        resultBindOk, alignedSize_sizedLayout, hmc, hset, resultBindOk, resultPure]
    | false =>
      have hsc_false : m469_scalarApplicable (sizedLayout 1 sT false) (sizedLayout 2 sS false) = false := rfl
      have hcf := checkFirst1D_ok (T := Unit) (S := Unit) sz1 i1
        ⟨col, 1, sizedLayout 1 sT false, sizedLayout 2 sS false, true, true, false⟩ hin
      have hdm : k * sT / sS * sS + k * sT % sS = k * sT := by
        have := Nat.div_add_mod (k * sT) sS
        have := Nat.mul_comm sS (k * sT / sS)
        omega
      have hrl : k * sT % sS < sS := Nat.mod_lt _ hS
      have hrm_le : k * sT % sS + min (sS - k * sT % sS) sT ≤ sS := by omega
      have hpF : k * sT + sT ≤ col.flatten.length := by rw [hFl]; exact hkb
      have hL1 : 1 ≤ col.length := by
        rcases Nat.eq_zero_or_pos col.length with h0 | h0
        · rw [h0, Nat.zero_mul] at hkb; omega
        · exact h0
      have hSle : sS ≤ col.length * sS := by
        have := Nat.mul_le_mul_right sS hL1
        rw [Nat.one_mul] at this; exact this
      have hTle : sT ≤ col.length * sS := Nat.le_trans (Nat.le_add_left _ _) hkb
      have hqL : k * sT / sS < col.length :=
        lt_of_mul_lt (by omega : k * sT / sS * sS < col.length * sS)
      have hce : col[k * sT / sS].length = sS := hwf _ (List.getElem_mem hqL)
      have h1L : k * sT / sS + 1 ≤ col.length * sS := by
        have := Nat.mul_le_mul_right sS (show k * sT / sS + 1 ≤ col.length by omega)
        have h1' : k * sT / sS + 1 ≤ (k * sT / sS + 1) * sS := by
          have := Nat.mul_le_mul_left (k * sT / sS + 1) (show 1 ≤ sS from hS)
          rw [Nat.mul_one] at this; exact this
        omega
      have hinv1 : min (sS - k * sT % sS) sT < sT →
          k * sT + min (sS - k * sT % sS) sT = (k * sT / sS + 1) * sS := by
        intro hlt'
        rw [Nat.add_mul, Nat.one_mul]; omega
      have hTv := lit_nat sT (fits hB hTle)
      have hSv := lit_nat sS (fits hB hSle)
      have hSv_nat : (JInt.lit .i64 (sS : Int)).val.toNat = sS := by rw [hSv, Int.toNat_natCast]
      obtain ⟨hdivrem, hqv, hrv⟩ := index_facts hS hT hk hkb hB
      have hrem_ts : remInt (JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
          .ok (JInt.wrap .i64 ((sT % sS : Nat) : Int)) := remInt_nat hTv hSv hS
      have hrem_ts_val : (JInt.wrap .i64 ((sT % sS : Nat) : Int)).val = ((sT % sS : Nat) : Int) :=
        wrap_nat _ (fits hB (Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hS)) hSle))
      have hrem_st : remInt (JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int)) =
          .ok (JInt.wrap .i64 ((sS % sT : Nat) : Int)) := remInt_nat hSv hTv hT
      have hrem_st_val : (JInt.wrap .i64 ((sS % sT : Nat) : Int)).val = ((sS % sT : Nat) : Int) :=
        wrap_nat _ (fits hB (Nat.le_trans (Nat.le_of_lt (Nat.mod_lt _ hT)) hTle))
      unfold m619_setindexNonReshaped
      rw [resultBindOk, hsing, hsc_false, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        hcf, resultBindOk, alignedSize_sizedLayout, alignedSize_sizedLayout]
      dsimp only
      rw [hdivrem, resultBindOk]
      dsimp only
      rw [hrem_ts, resultBindOk]
      by_cases h1 : sT % sS = 0
      · have hbeq1 : (JInt.wrap .i64 ((sT % sS : Nat) : Int) == zero) = true := by
          rw [beq_iff_val, hrem_ts_val, zero_val, h1]; rfl
        obtain ⟨n, hn⟩ : ∃ n, sT = n * sS :=
          ⟨sT / sS, (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h1)).symm⟩
        have hn' : sT / sS = n := by rw [hn, Nat.mul_div_cancel _ hS]
        have hq : k * sT / sS = k * n := by rw [hn, ← Nat.mul_assoc, Nat.mul_div_cancel _ hS]
        have hkn : k * n + n ≤ col.length := by
          apply le_of_mul_le hS
          rw [Nat.add_mul, Nat.mul_assoc, ← hn]
          exact hkb
        have hn_le : n ≤ col.length * sS := by
          have h1sS : n * 1 ≤ n * sS := Nat.mul_le_mul_left n hS
          rw [Nat.mul_one, ← hn] at h1sS
          exact Nat.le_trans h1sS hTle
        have hdiv_ts : divInt (JInt.lit .i64 (sT : Int)) (JInt.lit .i64 (sS : Int)) =
            .ok (JInt.wrap .i64 (n : Int)) := by
          rw [divInt_nat hTv hSv hS, hn']
        have hn_val : (JInt.wrap .i64 (n : Int)).val = (n : Int) :=
          wrap_nat n (fits hB hn_le)
        have hqv' : (JInt.wrap .i64 ((k * sT / sS : Nat) : Int)).val = ((k * n : Nat) : Int) := by
          rw [hqv, hq]
        obtain ⟨c', hrun, h1', h2', h3'⟩ :=
          forIn_set_mult v col.flatten (JInt.wrap .i64 ((k * sT / sS : Nat) : Int))
            (JInt.lit .i64 (sS : Int)) (k * n) hqv' hSv hS n 0 col hwf hFl.symm hB
            (by rw [Nat.add_zero]; exact hkn)
            (by rw [Nat.zero_add, hv, hn]; exact Nat.le_refl _)
            (by rw [Nat.zero_mul, List.take_zero, overwriteBytes_nil])
        refine ⟨c', ?_, h1', h2', ?_⟩
        · rw [hbeq1, ite_eq_left rfl, hdiv_ts, resultBindOk, intRange_one hn_val, List.range_eq_range']
          dsimp only [colParentOps]
          rw [hrun, resultBindOk, resultPure]
        · rw [h3', Nat.zero_add, List.take_of_length_le (Nat.le_of_eq (by rw [hv, hn])),
            Nat.mul_assoc, ← hn]
      · have hbeq1 : (JInt.wrap .i64 ((sT % sS : Nat) : Int) == zero) = false := by
          rw [beq_iff_val, hrem_ts_val, zero_val]
          exact decide_eq_false (fun h => h1 (Int.ofNat_inj.mp h))
        have hstart1 : (JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one).val =
            ((k * sT / sS : Nat) : Int) + 1 :=
          add_nat hqv one_val (fits hB h1L)
        rw [hbeq1, ite_eq_right Bool.false_ne_true, hrem_st, resultBindOk]
        by_cases h2 : sS % sT = 0
        · have hbeq2 : (JInt.wrap .i64 ((sS % sT : Nat) : Int) == zero) = true := by
            rw [beq_iff_val, hrem_st_val, zero_val, h2]; rfl
          have hrs : k * sT % sS + sT ≤ sS := rem_add_le hS h2
          have hget : colGet col [JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one] =
              .ok col[k * sT / sS] :=
            colGet_ok col (JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one) (k * sT / sS) hstart1 hqL
          have hmc : memcpyValue col[k * sT / sS] v (JInt.wrap .i64 ((k * sT % sS : Nat) : Int))
              zero (JInt.lit .i64 (sT : Int)) =
              overwriteBytes col[k * sT / sS] (k * sT % sS) v := by
            unfold memcpyValue byteWindow
            rw [hrv, zero_val, hTv, Int.toNat_natCast, Int.toNat_zero, Int.toNat_natCast,
              List.drop_zero, List.take_of_length_le (Nat.le_of_eq hv)]
          have hset : colSet col [JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one]
              (overwriteBytes col[k * sT / sS] (k * sT % sS) v) =
              .ok (col.set (k * sT / sS) (overwriteBytes col[k * sT / sS] (k * sT % sS) v)) :=
            colSet_ok col (JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one) (k * sT / sS) _ hstart1 hqL
          refine ⟨col.set (k * sT / sS) (overwriteBytes col[k * sT / sS] (k * sT % sS) v),
            ?_, wf_set hwf _ _ ?_, by rw [List.length_set], ?_⟩
          · rw [hbeq2, ite_eq_left rfl]
            dsimp only [colParentOps]
            rw [hget, resultBindOk, hmc, hset, resultBindOk, resultPure]
          · rw [overwriteBytes_length _ _ _ (by rw [hce, hv]; exact hrs), hce]
          · rw [set_overwriteBytes_flatten col hwf _ _ hqL v (by rw [hv]; exact hrs), hdm]
        · have hbeq2 : (JInt.wrap .i64 ((sS % sT : Nat) : Int) == zero) = false := by
            rw [beq_iff_val, hrem_st_val, zero_val]
            exact decide_eq_false (fun h => h2 (Int.ofNat_inj.mp h))
          rw [hbeq2, ite_eq_right Bool.false_ne_true, hSv_nat]
          by_cases hr0 : k * sT % sS = 0
          · have hinv0 : k * sT + 0 = (k * sT / sS + 0) * sS := by
              rw [Nat.add_zero, Nat.add_zero]
              have := hdm.symm
              rw [hr0, Nat.add_zero] at this
              exact this
            have hbne : (JInt.wrap .i64 ((k * sT % sS : Nat) : Int) != zero) = false := by
              rw [bne_iff_val, hrv, zero_val, hr0]; rfl
            obtain ⟨c', s', cp', step', copied', i', hrun, h1', h2', h3', h4', h5', h6', h7', h8'⟩ :=
              mainLoop_ok hS (k * sT / sS) k v col.flatten hv hpF
                (JInt.wrap .i64 ((k * sT / sS : Nat) : Int))
                (JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int))
                hqv hSv hTv sT col (List.replicate sS 0) 0 0 zero one
                (Nat.sub_zero sT ▸ Nat.le_refl sT) hwf hFl.symm hB
                (List.length_replicate) (Nat.zero_le sT) zero_val (fun _ => one_val)
                (by rw [List.take_zero, overwriteBytes_nil])
                (fun _ => hinv0)
            obtain ⟨c'', hc1, hc2, hc3, hc4⟩ :=
              setTail_ok hS (k * sT / sS) k v col.flatten hv hpF
                (JInt.wrap .i64 ((k * sT / sS : Nat) : Int))
                (JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int))
                hqv hSv hTv c' cp' step' copied' i' h1' (by rw [h2']; exact hFl.symm)
                (by rw [h2']; exact hB) h3' h4' h5' h6' h7' h8'
            refine ⟨c'', ?_, hc2, by rw [hc3, h2'], hc4⟩
            rw [hbne, ite_eq_right Bool.false_ne_true, hrun, resultBindOk]
            dsimp only
            exact map_setTail2 (copied' < JInt.lit .i64 sT) _ _ c' c''
              (fun p => ReinterpretArray.mk (T := Unit) (S := Unit) p 1 (sizedLayout 1 sT false) (sizedLayout 2 sS false) true true false) hc1
          · have hbne : (JInt.wrap .i64 ((k * sT % sS : Nat) : Int) != zero) = true := by
              rw [bne_iff_val, hrv, zero_val]
              exact decide_eq_true (fun h => hr0 (Int.ofNat_inj.mp h))
            have hget0 : colParentOps.get col [JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one] =
                .ok col[k * sT / sS] := by
              rw [colParentOps_get]
              exact colGet_ok col (JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one) (k * sT / sS) hstart1 hqL
            obtain ⟨_, hnb0_nat, hcp1, hnb0_leT, hnb0_full⟩ :=
              setStart_nb_facts hSv hrv hTv hrl hSle hB
            have hwl0 : (v.take (min (sS - k * sT % sS) sT)).length = min (sS - k * sT % sS) sT := by
              rw [List.length_take, hv]; exact Nat.min_eq_left hnb0_leT
            have hmc0 : memcpyValue col[k * sT / sS] v
                (JInt.wrap .i64 ((k * sT % sS : Nat) : Int)) zero
                (if JInt.lit .i64 (sS : Int) - JInt.wrap .i64 ((k * sT % sS : Nat) : Int) < JInt.lit .i64 (sT : Int)
                 then JInt.lit .i64 (sS : Int) - JInt.wrap .i64 ((k * sT % sS : Nat) : Int)
                 else JInt.lit .i64 (sT : Int)) =
                overwriteBytes col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT)) := by
              unfold memcpyValue byteWindow
              rw [hrv, zero_val, Int.toNat_natCast, Int.toNat_zero, List.drop_zero, hnb0_nat]
            have hs1_len : (overwriteBytes col[k * sT / sS] (k * sT % sS)
                (v.take (min (sS - k * sT % sS) sT))).length = sS := by
              rw [overwriteBytes_length _ _ _ (by rw [hwl0, hce]; exact hrm_le), hce]
            have hset0 : colParentOps.set col [JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one]
                (overwriteBytes col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT))) =
                .ok (col.set (k * sT / sS) (overwriteBytes col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT)))) := by
              rw [colParentOps_set]
              exact colSet_ok col (JInt.wrap .i64 ((k * sT / sS : Nat) : Int) + one) (k * sT / sS) _ hstart1 hqL
            have hi2_val : (one + one).val = ((1 : Nat) : Int) + 1 := by decide
            obtain ⟨c', s', cp', step', copied', i', hrun, h1', h2', h3', h4', h5', h6', h7', h8'⟩ :=
              mainLoop_ok hS (k * sT / sS) k v col.flatten hv hpF
                (JInt.wrap .i64 ((k * sT / sS : Nat) : Int))
                (JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int))
                hqv hSv hTv sT
                (col.set (k * sT / sS) (overwriteBytes col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT))))
                (overwriteBytes col[k * sT / sS] (k * sT % sS) (v.take (min (sS - k * sT % sS) sT)))
                (min (sS - k * sT % sS) sT) 1
                (zero + (if JInt.lit .i64 (sS : Int) - JInt.wrap .i64 ((k * sT % sS : Nat) : Int) < JInt.lit .i64 (sT : Int)
                 then JInt.lit .i64 (sS : Int) - JInt.wrap .i64 ((k * sT % sS : Nat) : Int)
                 else JInt.lit .i64 (sT : Int)))
                (one + one)
                (Nat.sub_le sT _) (wf_set hwf _ _ hs1_len)
                (by rw [List.length_set]; exact hFl.symm)
                (by rw [List.length_set]; exact hB)
                hs1_len hnb0_leT hcp1 (fun _ => hi2_val)
                (by rw [set_overwriteBytes_flatten col hwf _ _ hqL _ (by rw [hwl0]; exact hrm_le), hdm])
                hinv1
            obtain ⟨c'', hc1, hc2, hc3, hc4⟩ :=
              setTail_ok hS (k * sT / sS) k v col.flatten hv hpF
                (JInt.wrap .i64 ((k * sT / sS : Nat) : Int))
                (JInt.lit .i64 (sS : Int)) (JInt.lit .i64 (sT : Int))
                hqv hSv hTv c' cp' step' copied' i' h1' (by rw [h2', List.length_set]; exact hFl.symm)
                (by rw [h2', List.length_set]; exact hB) h3' h4' h5' h6' h7' h8'
            refine ⟨c'', ?_, hc2, by rw [hc3, h2', List.length_set], hc4⟩
            rw [hbne, ite_eq_left rfl, hget0, resultBindOk, hmc0, hset0, resultBindOk, hrun, resultBindOk]
            dsimp only
            exact map_setTail2 (copied' < JInt.lit .i64 sT) _ _ c' c''
              (fun p => ReinterpretArray.mk (T := Unit) (S := Unit) p 1 (sizedLayout 1 sT false) (sizedLayout 2 sS false) true true false) hc1
  · rw [ite_eq_right hin]
    cases scalar with
    | true =>
      have hST : sS = sT := hsc rfl
      subst hST
      have hNL : N = col.length := Nat.eq_of_mul_eq_mul_right hS hNT
      have hout : ¬ (1 ≤ i1.val ∧ i1.val ≤ col.length) := by omega
      have hsc_true : m469_scalarApplicable (sizedLayout 1 sS true) (sizedLayout 2 sS true) = true := by
        simp [m469_scalarApplicable, sizedLayout, TypeLayout.primitive, TypeLayout.bits, TypeLayout.info]
      have hlit_sS : (JInt.lit .i64 (sS : Int)).val.toNat = sS := by
        rw [lit_nat sS hTM, Int.toNat_natCast]
      have hps1 : m816_packedsize (sizedLayout 2 sS true) = .ok sS := by
        rw [packedsize_sizedLayout, hlit_sS]
      have hps2 : m816_packedsize (sizedLayout 1 sS true) = .ok sS := by
        rw [packedsize_sizedLayout, hlit_sS]
      have hset : colParentOps.set col [i1]
          (memcpyValue (List.replicate (JInt.lit .i64 (sS : Int)).val.toNat 0) v zero zero (JInt.lit .i64 (sS : Int))) =
          .error .bounds := by
        unfold colParentOps colSet; dsimp only
        rw [ite_eq_right hout]
      unfold m619_setindexNonReshaped
      rw [resultBindOk, hsing, ite_eq_right Bool.false_ne_true, ite_eq_left hsc_true,
        reinterpret_packed (sizedLayout 2 sS true) (sizedLayout 1 sS true) v _ sS
          rfl rfl (hasBitPadding_sizedLayout _ _ _) (hasBitPadding_sizedLayout _ _ _)
          hps1 hps2 rfl rfl,
        resultBindOk, alignedSize_sizedLayout, hset, resultBindError]
    | false =>
      have hsc_false : m469_scalarApplicable (sizedLayout 1 sT false) (sizedLayout 2 sS false) = false := rfl
      have hcf := checkFirst1D_err (T := Unit) (S := Unit) sz1 i1
        ⟨col, 1, sizedLayout 1 sT false, sizedLayout 2 sS false, true, true, false⟩ hin
      unfold m619_setindexNonReshaped
      rw [resultBindOk, hsing, hsc_false, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        hcf, resultBindError]

/-! ## Entry 2: `reinterpretarrays-ra-getindex-bytes` (`413`, `430`, `436`, `469`, `473`) -/

/-- `reinterpret(T, A)[i1, J...]` returns the `aligned_sizeof(T)` parent bytes starting at byte
`(i1-1)*aligned_sizeof(T)` of column `J` across all `_getindex_ra` branches, throws `BoundsError`
outside `1:size(R, 1)`, and routes zero-dimensional indexing through scalar reinterpretation or
`firstindex(a)`. -/
def RaGetCorrect : Prop :=
  (∀ (sS sT : Nat) (scalar : Bool) (col : List Bytes) (i1 sz1 : I64)
      (ops : PointerReadOps Unit Unit (List Bytes)) (checkParent : List Bytes → Bool),
    0 < sS → 0 < sT → (sT : Int) ≤ IntTy.max .i64 →
    (scalar = true → sS = sT) → WellFormed sS col →
    ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64 →
    remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero →
    divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1 →
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 1, sizedLayout 1 sT scalar, sizedLayout 2 sS scalar, true, true, false⟩
    m469_scalarApplicable a.target a.source = scalar ∧
    (m421_checkPtrIndexable checkParent a = false →
      m436_getindex ops checkParent (fun _ => .linear) (fun _ => one) (checkFirst1D sz1) colGet a i1 [] =
        m473_getindexNonReshaped (checkFirst1D sz1) colGet a i1 []) ∧
    m473_getindexNonReshaped (checkFirst1D sz1) colGet a i1 [] =
      if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then .ok (expectedBytes sT col i1.val)
      else .error .bounds) ∧
  (∀ {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
      (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (getParent : A → List I64 → RResult Bytes)
      (toSubscripts : ReinterpretArray T S A → I64 → List I64)
      (a : ReinterpretArray T S A),
    m430_getindexZeroReshaped ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a =
      m442_getindexLinear ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a (firstindex a) ∧
    (m469_scalarApplicable a.target a.source = false →
      m413_getindexZero ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a =
        m442_getindexLinear ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a (firstindex a)) ∧
    (m469_scalarApplicable a.target a.source = true →
      m413_getindexZero ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a =
        (getParent a.parent [] >>= fun bytes =>
          m882_reinterpret a.target a.source bytes (List.replicate a.target.alignedSize.val.toNat 0))))

theorem raGetCorrect : RaGetCorrect := by
  refine ⟨?_, ?_⟩
  · intro sS sT scalar col i1 sz1 ops checkParent hS hT hTM hsc hwf hB hrem hdiv
    dsimp only
    refine ⟨?_, ?_, raGetNonReshaped_eq hS hT hTM hsc hwf hB hrem hdiv⟩
    · cases scalar
      · rfl
      · have hST := hsc rfl
        subst hST
        simp [m469_scalarApplicable, sizedLayout, TypeLayout.primitive, TypeLayout.bits, TypeLayout.info]
    · intro hptr
      unfold m436_getindex m237_checkReadable
      simp [hptr]
  · intro T S A ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a
    refine ⟨rfl, fun h => ?_, fun h => ?_⟩
    · unfold m413_getindexZero; rw [h]; rfl
    · unfold m413_getindexZero; rw [h]; rfl

/-! ## Entry 3: `reinterpretarrays-ra-setindex-bytes` (`572`, `580`, `582`, `619`) -/

/-- `reinterpret(T, A)[i1, J...] = v` overwrites the `aligned_sizeof(T)` parent bytes starting at
byte `(i1-1)*aligned_sizeof(T)` of column `J` with `v`, preserves all other bytes, throws
`BoundsError` outside `1:size(R, 1)`, and routes zero-dimensional assignment through scalar
reinterpretation or `firstindex(a)`. -/
def RaSetCorrect : Prop :=
  (∀ (sS sT : Nat) (scalar : Bool) (col : List Bytes) (i1 sz1 : I64) (v : Bytes)
      (ops : PointerWriteOps Unit Unit (List Bytes) Bytes) (checkParent : List Bytes → Bool),
    0 < sS → 0 < sT → (sT : Int) ≤ IntTy.max .i64 →
    (scalar = true → sS = sT) → WellFormed sS col → v.length = sT →
    ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64 →
    remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero →
    divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1 →
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 1, sizedLayout 1 sT scalar, sizedLayout 2 sS scalar, true, true, false⟩
    (m421_checkPtrIndexable checkParent a = false →
      m582_setindex ops checkParent (fun _ => .linear) (fun _ => one) (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 [] =
        m619_setindexNonReshaped (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 []) ∧
    (if 1 ≤ i1.val ∧ i1.val ≤ sz1.val then
      ∃ col', m619_setindexNonReshaped (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 [] =
        .ok { a with parent := col' } ∧
        WellFormed sS col' ∧ col'.length = col.length ∧
        col'.flatten = overwriteBytes col.flatten ((i1.val.toNat - 1) * sT) v
    else
      m619_setindexNonReshaped (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 [] =
        .error .bounds)) ∧
  (∀ {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
      (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
      (toSubscripts : ReinterpretArray T S A → I64 → List I64)
      (a : ReinterpretArray T S A) (v : V),
    m580_setindexZeroReshaped ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v =
      m588_setindexLinear ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v (firstindex a) ∧
    (m469_scalarApplicable a.target a.source = false →
      m572_setindexZero ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v =
        m588_setindexLinear ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v (firstindex a)) ∧
    (m469_scalarApplicable a.target a.source = true →
      m572_setindexZero ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v =
        (do
          let bytes ← convertValue a.target v
          let sourceBytes ← m882_reinterpret a.source a.target bytes (List.replicate a.source.alignedSize.val.toNat 0)
          let p ← parent.set a.parent [] sourceBytes
          pure { a with parent := p })))

theorem raSetCorrect : RaSetCorrect := by
  refine ⟨?_, ?_⟩
  · intro sS sT scalar col i1 sz1 v ops checkParent hS hT hTM hsc hwf hv hB hrem hdiv
    dsimp only
    refine ⟨?_, raSetNonReshaped_eq hS hT hTM hsc hwf hv hB hrem hdiv⟩
    intro hptr
    unfold m582_setindex m244_checkWritable
    simp [hptr]
  · intro T S A V ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v
    refine ⟨rfl, fun h => ?_, fun h => ?_⟩
    · unfold m572_setindexZero; rw [h]; rfl
    · unfold m572_setindexZero; rw [h]; rfl

/-! ## Entry 4: `memsafety-reinterpretarray-getindex` (`403`, `410`, `411`, `421`-`428`, `436`, `461`, `473`) -/

/-- Pointer eligibility requires distinct element sizes and recurses through `parent(a)`;
`_getindex_ptr` checks bounds before computing `elsize(a) * (li - firstindex(a))`, and every
non-pointer read stays in bounds of `a.parent` and returns a slice of width `aligned_sizeof(T)`
within `col.flatten`. -/
def ReinterpretGetMemorySafe : Prop :=
  (∀ {T S A P R : Type} (checkParent : A → Bool) (parentElsize : A → I64)
      (parent : A → P) (unsafeConvert : TypeLayout → A → R) (castPointer : TypeLayout → R → R)
      (a : ReinterpretArray T S A) (x : A),
    (a.target.alignedSize = a.source.alignedSize →
      m421_checkPtrIndexable checkParent a = false ∧
      m403_elsize parentElsize a = parentElsize a.parent) ∧
    (a.target.alignedSize ≠ a.source.alignedSize →
      m421_checkPtrIndexable checkParent a = checkParent (m369_parent a) ∧
      m403_elsize parentElsize a = a.target.alignedSize) ∧
    m411_unsafeConvert unsafeConvert castPointer a.target a =
      castPointer a.target (unsafeConvert a.source (m369_parent a)) ∧
    m425_checkPtrReshaped parent m427_checkPtrDense x = true ∧
    m426_checkPtrSubarray parent m428_checkPtrAbstract x = false) ∧
  (∀ {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
      (parentStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (getParent : A → List I64 → RResult Bytes)
      (a : ReinterpretArray T S A) (i1 : I64) (tail : List I64),
    (ops.checkbounds a (i1 :: tail) = .error .bounds →
      m461_getindexPtr ops a (i1 :: tail) = .error .bounds) ∧
    (a.readable = true → a.target.alignedSize ≠ a.source.alignedSize →
      checkParent a.parent = true → ops.checkbounds a (i1 :: tail) = .ok () →
      m436_getindex ops checkParent parentStyle firstindex checkbounds getParent a i1 tail =
        ops.load a.parent (ops.addPointer (ops.unsafeConvert a.target (m410_cconvert ops.parentCconvert a))
          (a.target.alignedSize * (ops.linearIndex a (i1 :: tail) - ops.firstindex a))))) ∧
  (∀ (sS sT : Nat) (scalar : Bool) (col : List Bytes) (i1 sz1 : I64),
    0 < sS → 0 < sT → (sT : Int) ≤ IntTy.max .i64 →
    (scalar = true → sS = sT) → WellFormed sS col →
    ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64 →
    remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero →
    divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1 →
    1 ≤ i1.val ∧ i1.val ≤ sz1.val →
    ∃ bytes,
      m473_getindexNonReshaped (T := Unit) (S := Unit) (checkFirst1D sz1) colGet
        ⟨col, 1, sizedLayout 1 sT scalar, sizedLayout 2 sS scalar, true, true, false⟩ i1 [] = .ok bytes ∧
      bytes.length = sT ∧
      (i1.val.toNat - 1) * sT + sT ≤ col.flatten.length)

theorem reinterpretGetMemorySafe : ReinterpretGetMemorySafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro T S A P R checkParent parentElsize parent unsafeConvert castPointer a x
    refine ⟨fun h => ?_, fun h => ?_, rfl, rfl, rfl⟩
    · simp [m421_checkPtrIndexable, m403_elsize, h]
    · have hne_val : a.target.alignedSize.val ≠ a.source.alignedSize.val := fun he => h (jint_eq_of_val he)
      simp [m421_checkPtrIndexable, m403_elsize, m369_parent, hne_val]
  · intro T S A ops checkParent parentStyle firstindex checkbounds getParent a i1 tail
    refine ⟨fun h => by simp [m461_getindexPtr, h], fun hr hne hcp hcb => ?_⟩
    have hne_val : a.target.alignedSize.val ≠ a.source.alignedSize.val := fun he => hne (jint_eq_of_val he)
    simp [m436_getindex, m237_checkReadable, hr, m421_checkPtrIndexable, m369_parent,
      hne_val, hcp, m461_getindexPtr, hcb, m403_elsize]
  · intro sS sT scalar col i1 sz1 hS hT hTM hsc hwf hB hrem hdiv hin
    obtain ⟨N, hN, hNT⟩ := size_facts hT hTM hB hrem hdiv
    have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hwf
    have hkN : (i1.val.toNat - 1) + 1 ≤ N := by omega
    have hkb : (i1.val.toNat - 1) * sT + sT ≤ col.flatten.length := by
      rw [hFl]
      have := Nat.mul_le_mul_right sT hkN
      rw [Nat.add_mul, Nat.one_mul, hNT] at this
      exact this
    have hget := raGetNonReshaped_eq (scalar := scalar) (i1 := i1) hS hT hTM hsc hwf hB hrem hdiv
    dsimp only at hget
    rw [ite_eq_left hin] at hget
    refine ⟨expectedBytes sT col i1.val, hget, ?_, hkb⟩
    unfold expectedBytes
    rw [List.length_take, List.length_drop]
    omega

/-! ## Entry 5: `memsafety-reinterpretarray-setindex` (`582`, `610`, `619`, `688`) -/

/-- `_setindex_ptr!` checks bounds before storing at `elsize(a) * (li - firstindex(a))`, conversion
errors propagate without mutating the parent, and every non-pointer write preserves the parent byte
length and all bytes outside the target window `[(i1-1)*sT, i1*sT)`. -/
def ReinterpretSetMemorySafe : Prop :=
  (∀ {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
      (parentStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
      (a : ReinterpretArray T S A) (v : V) (i1 : I64) (tail : List I64),
    (ops.checkbounds a (i1 :: tail) = .error .bounds →
      m610_setindexPtr ops a v (i1 :: tail) = .error .bounds) ∧
    (a.writable = true → a.target.alignedSize ≠ a.source.alignedSize →
      checkParent a.parent = true → ops.checkbounds a (i1 :: tail) = .ok () →
      ops.store a.parent (ops.addPointer (ops.unsafeConvert a.target (m410_cconvert ops.parentCconvert a))
        (a.target.alignedSize * (ops.linearIndex a (i1 :: tail) - ops.firstindex a))) v = .ok a.parent →
      m582_setindex ops checkParent parentStyle firstindex checkbounds convertValue parent a v i1 tail = .ok a)) ∧
  (∀ {T S A V : Type} (bounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (convert : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
      (style : A → IndexStyleModel) (first : ReinterpretArray T S A → I64)
      (a : ReinterpretArray T S A) (v : V) (i1 : I64) (tail : List I64) (e : ReinterpretError),
    convert a.target v = .error e →
    m619_setindexNonReshaped bounds convert parent a v i1 tail = .error e ∧
    m688_setindexReshaped bounds convert parent style first a v i1 tail = .error e) ∧
  (∀ (sS sT : Nat) (scalar : Bool) (col : List Bytes) (i1 sz1 : I64) (v : Bytes),
    0 < sS → 0 < sT → (sT : Int) ≤ IntTy.max .i64 →
    (scalar = true → sS = sT) → WellFormed sS col → v.length = sT →
    ((col.length * sS : Nat) : Int) ≤ IntTy.max .i64 →
    remInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok zero →
    divInt (JInt.lit .i64 col.length * JInt.lit .i64 sS) (JInt.lit .i64 sT) = .ok sz1 →
    1 ≤ i1.val ∧ i1.val ≤ sz1.val →
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 1, sizedLayout 1 sT scalar, sizedLayout 2 sS scalar, true, true, false⟩
    ∃ col',
      m619_setindexNonReshaped (checkFirst1D sz1) (fun _ x => .ok x) colParentOps a v i1 [] =
        .ok { a with parent := col' } ∧
      col'.flatten.length = col.flatten.length ∧
      ∀ b, (b < (i1.val.toNat - 1) * sT ∨ (i1.val.toNat - 1) * sT + sT ≤ b) →
        col'.flatten[b]? = col.flatten[b]?)

theorem reinterpretSetMemorySafe : ReinterpretSetMemorySafe := by
  refine ⟨?_, ?_, ?_⟩
  · intro T S A V ops checkParent parentStyle firstindex checkbounds convertValue parent a v i1 tail
    refine ⟨fun h => by simp [m610_setindexPtr, h], fun hw hne hcp hcb hst => ?_⟩
    have hne_val : a.target.alignedSize.val ≠ a.source.alignedSize.val := fun he => hne (jint_eq_of_val he)
    simp [m582_setindex, m244_checkWritable, hw, m421_checkPtrIndexable, m369_parent,
      hne_val, hcp, m610_setindexPtr, hcb, m403_elsize, hst]
    cases a; simp_all
  · intro T S A V bounds convert parent style first a v i1 tail e h
    simp [m619_setindexNonReshaped, m688_setindexReshaped, h]
  · intro sS sT scalar col i1 sz1 v hS hT hTM hsc hwf hv hB hrem hdiv hin
    dsimp only
    obtain ⟨N, hN, hNT⟩ := size_facts hT hTM hB hrem hdiv
    have hFl : col.flatten.length = col.length * sS := length_flatten_wf col hwf
    have hkN : (i1.val.toNat - 1) + 1 ≤ N := by omega
    have hkb : (i1.val.toNat - 1) * sT + v.length ≤ col.flatten.length := by
      rw [hv, hFl]
      have := Nat.mul_le_mul_right sT hkN
      rw [Nat.add_mul, Nat.one_mul, hNT] at this
      exact this
    have hset := raSetNonReshaped_eq (scalar := scalar) (i1 := i1) hS hT hTM hsc hwf hv hB hrem hdiv
    dsimp only at hset
    rw [ite_eq_left hin] at hset
    obtain ⟨col', hrun, hwf', hlen', hfl'⟩ := hset
    refine ⟨col', hrun, by rw [length_flatten_wf col' hwf', hlen', hFl], ?_⟩
    intro b hb
    rw [hfl', overwriteBytes_getElem? col.flatten v ((i1.val.toNat - 1) * sT) b hkb, hv]
    rcases hb with hlt | hge
    · rw [ite_eq_left hlt]
    · have hnot1 : ¬ (b < (i1.val.toNat - 1) * sT) := by omega
      have hnot2 : ¬ (b < (i1.val.toNat - 1) * sT + sT) := by omega
      rw [ite_eq_right hnot1, ite_eq_right hnot2]

/-! ## Entry 15: `reinterpretarray-reshaped-get` (`527`, `688`) -/

/-- Reshaped element reads and writes (`_getindex_ra` and `_setindex_ra!`) perform bounds-checked
no-ops on singleton targets, copy the exact parent element when `aligned_sizeof(T) == aligned_sizeof(S)`,
and slice/overwrite the `i1`-th channel of `a.parent[tail...]` when `aligned_sizeof(T) < aligned_sizeof(S)`. -/
def ReinterpretReshapedGetSet : Prop :=
  (∀ {T S A : Type} (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (getParent : A → List I64 → RResult Bytes) (parent : ParentOps A)
      (style : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (a : ReinterpretArray T S A) (v : Bytes) (i1 : I64) (tail : List I64),
    a.target.singleton = true →
    m527_getindexReshaped checkbounds getParent style firstindex a i1 tail =
      (checkbounds a i1 tail >>= fun _ => .ok []) ∧
    m688_setindexReshaped checkbounds (fun _ x => .ok x) parent style firstindex a v i1 tail =
      (checkbounds a i1 tail >>= fun _ => .ok a)) ∧
  (∀ (sT : Nat) (col : List Bytes) (v : Bytes) (i1 : I64),
    0 < sT → (sT : Int) ≤ IntTy.max .i64 →
    WellFormed sT col → v.length = sT →
    1 ≤ i1.val ∧ i1.val ≤ col.length →
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 1, sizedLayout 1 sT false, sizedLayout 2 sT false, true, true, true⟩
    m527_getindexReshaped (fun _ _ _ => .ok ()) colGet (fun _ => .linear) (fun _ => one) a i1 [] =
      .ok (col.getD (i1.val - 1).toNat []) ∧
    m688_setindexReshaped (fun _ _ _ => .ok ()) (fun _ x => .ok x) colParentOps
      (fun _ => .linear) (fun _ => one) a v i1 [] =
      .ok { a with parent := col.set (i1.val - 1).toNat v }) ∧
  (∀ (sT K : Nat) (col : List Bytes) (v : Bytes) (i1 j : I64),
    0 < sT → 1 < K → ((K * sT : Nat) : Int) ≤ IntTy.max .i64 →
    WellFormed (K * sT) col → v.length = sT →
    1 ≤ i1.val ∧ i1.val ≤ K → 1 ≤ j.val ∧ j.val ≤ col.length →
    let a : ReinterpretArray Unit Unit (List Bytes) :=
      ⟨col, 2, sizedLayout 1 sT false, sizedLayout 2 (K * sT) false, true, true, true⟩
    m527_getindexReshaped (fun _ _ _ => .ok ()) colGet (fun _ => .linear) (fun _ => one) a i1 [j] =
      .ok (byteWindow (col.getD (j.val - 1).toNat []) ((i1.val - 1).toNat * sT) sT) ∧
    m688_setindexReshaped (fun _ _ _ => .ok ()) (fun _ x => .ok x) colParentOps
      (fun _ => .linear) (fun _ => one) a v i1 [j] =
      .ok { a with parent := col.set (j.val - 1).toNat (overwriteBytes (col.getD (j.val - 1).toNat []) ((i1.val - 1).toNat * sT) v) })

theorem reinterpretReshapedGetSet : ReinterpretReshapedGetSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro T S A checkbounds getParent parent style firstindex a v i1 tail hsing
    constructor
    · unfold m527_getindexReshaped
      rw [hsing, ite_eq_left rfl]; rfl
    · unfold m688_setindexReshaped
      rw [resultBindOk, hsing, ite_eq_left rfl]; rfl
  · intro sT col v i1 hsT hTM hwf hv hin
    dsimp only
    have hsing : (sizedLayout 1 sT false).singleton = false := by
      unfold sizedLayout TypeLayout.singleton LayoutInfo.singleton
      exact beq_eq_false_iff_ne.mpr (by omega)
    have hsc : m469_scalarApplicable (sizedLayout 1 sT false) (sizedLayout 2 sT false) = false := rfl
    let k := (i1.val - 1).toNat
    have hk : i1.val = (k : Int) + 1 := by dsimp [k]; omega
    have hkL : k < col.length := by dsimp [k]; omega
    have hck : col[k].length = sT := hwf _ (List.getElem_mem hkL)
    have hlit : (JInt.lit .i64 (sT : Int)).val.toNat = sT := by
      rw [lit_nat sT hTM, Int.toNat_natCast]
    have hle : JInt.lit .i64 (sT : Int) ≤ JInt.lit .i64 (sT : Int) := Int.le_refl _
    have hnlt : ¬ (JInt.lit .i64 (sT : Int) < JInt.lit .i64 (sT : Int)) := Int.lt_irrefl _
    have hget := colGet_ok col i1 k hk hkL
    have hset := colSet_ok col i1 k v hk hkL
    have hmc : memcpyValue (List.replicate sT 0) col[k] zero zero (JInt.lit .i64 (sT : Int)) = col[k] := by
      unfold memcpyValue byteWindow
      rw [zero_val, hlit, Int.toNat_zero, List.drop_zero,
        List.take_of_length_le (Nat.le_of_eq hck),
        overwriteBytes_full _ _ (by rw [hck, List.length_replicate])]
    have hbw : byteWindow v 0 sT = v := by
      unfold byteWindow
      rw [List.drop_zero, List.take_of_length_le (Nat.le_of_eq hv)]
    constructor
    · unfold m527_getindexReshaped
      rw [hsing, hsc, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        resultBindOk, alignedSize_sizedLayout, alignedSize_sizedLayout]
      dsimp only
      rw [ite_eq_left hle, ite_eq_right hnlt, hlit, hget, resultBindOk, hmc, resultPure,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkL]
      rfl
    · unfold m688_setindexReshaped
      rw [resultBindOk, hsing, hsc, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        resultBindOk, alignedSize_sizedLayout, alignedSize_sizedLayout]
      dsimp only
      rw [ite_eq_left hle, ite_eq_right hnlt, hlit, hbw, colParentOps_set, hset, resultBindOk, resultPure]
  · intro sT K col v i1 j hsT hK hB hwf hv hi hj
    dsimp only
    have hsing : (sizedLayout 1 sT false).singleton = false := by
      unfold sizedLayout TypeLayout.singleton LayoutInfo.singleton
      exact beq_eq_false_iff_ne.mpr (by omega)
    have hsc : m469_scalarApplicable (sizedLayout 1 sT false) (sizedLayout 2 (K * sT) false) = false := rfl
    let jNat := (j.val - 1).toNat
    let iNat := (i1.val - 1).toNat
    have hj_val : j.val = (jNat : Int) + 1 := by dsimp [jNat]; omega
    have hjL : jNat < col.length := by dsimp [jNat]; omega
    have hTM : (sT : Int) ≤ IntTy.max .i64 := by
      have : sT ≤ K * sT := Nat.le_mul_of_pos_left sT (by omega)
      omega
    have hi_le : iNat ≤ K * sT := by
      have := Nat.mul_le_mul_left K (show 1 ≤ sT from hsT)
      dsimp [iNat]; omega
    have hi_mul_le : iNat * sT ≤ K * sT :=
      Nat.mul_le_mul_right sT (by dsimp [iNat]; omega)
    have hlt_sz : sT < K * sT := by
      have := Nat.mul_le_mul_right sT (show 2 ≤ K from hK)
      omega
    have hi_eq : i1.val - 1 = (iNat : Int) := by dsimp [iNat]; omega
    have hTv := lit_nat sT hTM
    have hSv := lit_nat (K * sT) hB
    have hTv_nat : (JInt.lit .i64 (sT : Int)).val.toNat = sT := by rw [hTv, Int.toNat_natCast]
    have hnle : ¬ (JInt.lit .i64 ((K * sT : Nat) : Int) ≤ JInt.lit .i64 (sT : Int)) := by
      rw [le_iff_val, hSv, hTv]; exact fun h => Nat.not_le_of_gt hlt_sz (Int.ofNat_le.mp h)
    have hsub : (i1 - one).val = (iNat : Int) := by
      rw [val_sub, one_val, hi_eq]
      exact wrapInt_nat iNat (fits hB hi_le)
    have hmul : ((i1 - one) * JInt.lit .i64 (sT : Int)).val = ((iNat * sT : Nat) : Int) :=
      mul_nat hsub hTv (fits hB hi_mul_le)
    have hmul_nat : ((i1 - one) * JInt.lit .i64 (sT : Int)).val.toNat = iNat * sT := by
      rw [hmul, Int.toNat_natCast]
    have hget := colGet_ok col j jNat hj_val hjL
    have hmc : memcpyValue col[jNat] v ((i1 - one) * JInt.lit .i64 (sT : Int)) zero (JInt.lit .i64 (sT : Int)) =
        overwriteBytes col[jNat] (iNat * sT) v := by
      unfold memcpyValue byteWindow
      rw [hmul_nat, zero_val, hTv_nat, Int.toNat_zero, List.drop_zero,
        List.take_of_length_le (Nat.le_of_eq hv)]
    have hset := colSet_ok col j jNat (overwriteBytes col[jNat] (iNat * sT) v) hj_val hjL
    constructor
    · unfold m527_getindexReshaped
      rw [hsing, hsc, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        resultBindOk, alignedSize_sizedLayout, alignedSize_sizedLayout]
      dsimp only
      rw [ite_eq_right hnle, hget, resultBindOk, hmul_nat, hTv_nat, resultPure,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjL]
      rfl
    · unfold m688_setindexReshaped
      rw [resultBindOk, hsing, hsc, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
        resultBindOk, alignedSize_sizedLayout, alignedSize_sizedLayout]
      dsimp only
      rw [ite_eq_right hnle, colParentOps_get, hget, resultBindOk, hmc,
        colParentOps_set, hset, resultBindOk, resultPure,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjL]
      rfl

theorem wrapInt_add_left (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a + b) = wrapInt t (a + b) := by
  rw [wrapInt_emod t (wrapInt t a + b), Int.add_emod, wrapInt_emod_self, ← Int.add_emod, ← wrapInt_emod]

theorem wrapInt_add_right (t : IntTy) (a b : Int) :
    wrapInt t (a + wrapInt t b) = wrapInt t (a + b) := by
  rw [wrapInt_emod t (a + wrapInt t b), Int.add_emod, wrapInt_emod_self, ← Int.add_emod, ← wrapInt_emod]

theorem wrapInt_sub_left (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a - b) = wrapInt t (a - b) := by
  rw [wrapInt_emod t (wrapInt t a - b), wrapInt_emod t (a - b), Int.sub_emod, wrapInt_emod_self, ← Int.sub_emod]

theorem wrapInt_sub_right (t : IntTy) (a b : Int) :
    wrapInt t (a - wrapInt t b) = wrapInt t (a - b) := by
  rw [wrapInt_emod t (a - wrapInt t b), wrapInt_emod t (a - b), Int.sub_emod, wrapInt_emod_self, ← Int.sub_emod]


theorem jint_val_eq {a b : I64} (h : a = b) : a.val = b.val := by rw [h]

/-! ## Entry 8: Constructor validation and rank invariants -/

/-- Both public constructors reject non-`isbits` layouts and bit-padded layouts,
and on success establish the documented rank, parent, reshape, and padding-flag invariants. -/
def ReinterpretConstructorValidation : Prop :=
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A),
    (target.isBits = false ∨ source.isBits = false ∨
      m828_hasBitPadding target = true ∨ m828_hasBitPadding source = true) →
    m73_reinterpret (T := T) (S := S) target source a = .error .argument ∧
    m107_reinterpretReshape (T := T) (S := S) target source a = .error .argument ∧
    m188_reinterpretReshape (T := T) (S := S) target source a = .error .argument) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    m73_reinterpret target source a = .ok r →
    m369_parent r = a ∧ r.rank = a.rank ∧ r.reshaped = false ∧
    r.target = target ∧ r.source = source ∧
    m772_arraySubpadding target source = .ok r.readable ∧
    m772_arraySubpadding source target = .ok r.writable ∧
    (a.rank = 0 → target.alignedSize = source.alignedSize) ∧
    (a.rank ≠ 0 → source.alignedSize ≠ target.alignedSize →
      (a.axes.headD ⟨one, zero⟩).first = one ∧
      (target.singleton = true → source.singleton = true) ∧
      (target.singleton = false →
        remInt ((a.axes.headD ⟨one, zero⟩).length * source.alignedSize) target.alignedSize = .ok zero))) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (a : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    m188_reinterpretReshape target source a = .ok r →
    m107_reinterpretReshape target source a = .ok r ∧
    m369_parent r = a ∧ r.reshaped = true ∧
    r.target = target ∧ r.source = source ∧
    m772_arraySubpadding target source = .ok r.readable ∧
    m772_arraySubpadding source target = .ok r.writable ∧
    (source.alignedSize = target.alignedSize → r.rank = a.rank) ∧
    (target.alignedSize < source.alignedSize →
      target.singleton = false ∧ remInt source.alignedSize target.alignedSize = .ok zero ∧
      r.rank = a.rank + 1) ∧
    (source.alignedSize < target.alignedSize →
      source.singleton = false ∧ remInt target.alignedSize source.alignedSize = .ok zero ∧
      0 < a.rank ∧ r.rank + 1 = a.rank))

theorem reinterpretConstructorValidation : ReinterpretConstructorValidation := by
  refine ⟨?_, ?_, ?_⟩
  · intro T S A target source a h
    rcases h with ht | hs | hpt | hps
    · simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, m14_throwbits]
    · by_cases ht : target.isBits = true
      · simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, hs, m14_throwbits]
      · have ht' : target.isBits = false := Bool.eq_false_iff.mpr ht
        simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht', m14_throwbits]
    · by_cases ht : target.isBits = true
      · by_cases hs : source.isBits = true
        · simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, hs, hpt, m27_throwbitpadding]
        · have hs' : source.isBits = false := Bool.eq_false_iff.mpr hs
          simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, hs', m14_throwbits]
      · have ht' : target.isBits = false := Bool.eq_false_iff.mpr ht
        simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht', m14_throwbits]
    · by_cases ht : target.isBits = true
      · by_cases hs : source.isBits = true
        · by_cases hpt : m828_hasBitPadding target = true
          · simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, hs, hpt, m27_throwbitpadding]
          · have hpt' : m828_hasBitPadding target = false := Bool.eq_false_iff.mpr hpt
            simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, hs, hpt', hps, m27_throwbitpadding]
        · have hs' : source.isBits = false := Bool.eq_false_iff.mpr hs
          simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht, hs', m14_throwbits]
      · have ht' : target.isBits = false := Bool.eq_false_iff.mpr ht
        simp [m73_reinterpret, m107_reinterpretReshape, m188_reinterpretReshape, ht', m14_throwbits]
  · intro T S A target source a r h
    unfold m73_reinterpret at h
    simp only [m14_throwbits, m27_throwbitpadding, m18_throwsize0, m23_throwsingleton,
      m74_thrownonint, m80_throwaxes1, bind, pure, Except.bind, Except.pure,
      bne_iff_ne] at h
    repeat' split at h
    all_goals try contradiction
    all_goals (
      cases h
      refine ⟨rfl, rfl, rfl, rfl, rfl, by assumption, by assumption, ?_, ?_⟩
      · intro hr0; simp_all
      · intro hr0 hne; simp_all
    )
  · intro T S A target source a r h
    have h107 : m107_reinterpretReshape target source a = .ok r := h
    unfold m188_reinterpretReshape m107_reinterpretReshape at h
    simp only [m14_throwbits, m27_throwbitpadding, m23_throwsingleton, m108_throwintmult,
      m119_throwfromsingleton, m18_throwsize0, m113_throwsize1,
      bind, pure, Except.bind, Except.pure, bne_iff_ne, beq_iff_eq, lt_iff_val] at h
    repeat' split at h
    all_goals try contradiction
    · cases h
      have hval := jint_val_eq ‹source.alignedSize = target.alignedSize›
      refine ⟨h107, rfl, rfl, rfl, rfl, by assumption, by assumption, fun _ => rfl, ?_, ?_⟩
      · intro hlt; rw [lt_iff_val] at hlt; omega
      · intro hgt; rw [lt_iff_val] at hgt; omega
    · cases h
      have hlt_val := ‹target.alignedSize.val < source.alignedSize.val›
      refine ⟨h107, rfl, rfl, rfl, rfl, by assumption, by assumption,
        fun heq => absurd heq ‹¬source.alignedSize = target.alignedSize›, ?_, ?_⟩
      · intro _
        refine ⟨Bool.eq_false_iff.mpr ‹¬target.singleton = true›, ?_, rfl⟩
        simp_all
      · intro hgt; rw [lt_iff_val] at hgt; omega
    · cases h
      have hr0 := ‹¬a.rank = 0›
      refine ⟨h107, rfl, rfl, rfl, rfl, by assumption, by assumption,
        fun heq => absurd heq ‹¬source.alignedSize = target.alignedSize›, ?_, ?_⟩
      · intro hlt; rw [lt_iff_val] at hlt; exact absurd hlt ‹¬target.alignedSize.val < source.alignedSize.val›
      · intro _
        refine ⟨Bool.eq_false_iff.mpr ‹¬source.singleton = true›, ?_, by omega, by dsimp; omega⟩
        simp_all

/-! ## Entry 9: Nested dispatch, identity specializations, parent metadata, and `unaliascopy` -/

/-- Nested reinterpretation collapses to the parent array via the identity overloads when
reinterpreting back to the parent type, and `unaliascopy` on any valid view succeeds whenever
copying the parent preserves its rank and axes. -/
def ReinterpretNestedDispatch : Prop :=
  (∀ {T S A R : Type} (target : TypeLayout) (a : ReinterpretArray T S (ArrayInput A))
      (dataids : ArrayInput A → R) (hasOffset : ArrayInput A → Bool),
    target.id = a.source.id →
    m190_reinterpretParent target a = .ok (.parent (m104_reinterpretIdentity a.parent)) ∧
    m370_dataids dataids a = dataids (m104_reinterpretIdentity (m369_parent a)) ∧
    m401_hasOffset hasOffset a = hasOffset (m104_reinterpretIdentity (m369_parent a))) ∧
  (∀ {T S A : Type} (target : TypeLayout) (a : ReinterpretArray T S (ArrayInput A)),
    target.id ≠ a.source.id →
    m190_reinterpretParent target a = (m73_reinterpret target a.source a.parent).map ReinterpretOutcome.view) ∧
  (∀ {T S P A : Type} (target : TypeLayout) (parentSize : ArrayInput A → List I64)
      (parentAxes : ArrayInput A → List Axis) (a : ReinterpretArray S P (ArrayInput A)),
    target.alignedSize = a.source.alignedSize → target.id = a.source.id →
    m191_reinterpretReshapedParent (T := T) target parentSize parentAxes a =
      .ok (.parent (m145_reinterpretReshapeIdentity a.parent))) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (p p' : ArrayInput A)
      (a : ReinterpretArray T S (ArrayInput A))
      (copy : ArrayInput A → RResult (ArrayInput A)),
    target.id ≠ source.id →
    copy p = .ok p' → p'.rank = p.rank → p'.axes = p.axes →
    m73_reinterpret target source p = .ok a →
    m371_unaliascopy copy a =
      .ok (.view ⟨p', a.rank, a.target, a.source, a.readable, a.writable, false⟩)) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (p p' : ArrayInput A)
      (a : ReinterpretArray T S (ArrayInput A))
      (copy : ArrayInput A → RResult (ArrayInput A)),
    target.id ≠ source.id →
    copy p = .ok p' → p'.rank = p.rank → p'.axes = p.axes →
    m188_reinterpretReshape target source p = .ok a →
    m372_unaliascopyReshaped copy a =
      .ok (.view ⟨p', a.rank, a.target, a.source, a.readable, a.writable, true⟩))

theorem m73_congr_parent {T S A : Type} (target source : TypeLayout) (p p' : ArrayInput A)
    (a : ReinterpretArray T S (ArrayInput A))
    (hrank : p'.rank = p.rank) (haxes : p'.axes = p.axes)
    (h : m73_reinterpret (T := T) (S := S) target source p = .ok a) :
    m73_reinterpret (T := T) (S := S) target source p' =
      .ok ⟨p', a.rank, a.target, a.source, a.readable, a.writable, false⟩ ∧
    a.target = target ∧ a.source = source ∧ a.parent = p := by
  unfold m73_reinterpret at h ⊢
  rw [hrank, haxes]
  simp only [m14_throwbits, m27_throwbitpadding, m18_throwsize0, m23_throwsingleton,
    m74_thrownonint, m80_throwaxes1, bind, pure, Except.bind, Except.pure] at h ⊢
  repeat' split at h
  all_goals try contradiction
  all_goals (
    cases h
    refine ⟨?_, rfl, rfl, rfl⟩
    simp only [*, Bool.false_eq_true, ↓reduceIte]
  )

theorem m107_congr_parent {T S A : Type} (target source : TypeLayout) (p p' : ArrayInput A)
    (a : ReinterpretArray T S (ArrayInput A))
    (hrank : p'.rank = p.rank) (haxes : p'.axes = p.axes)
    (h : m107_reinterpretReshape (T := T) (S := S) target source p = .ok a) :
    m107_reinterpretReshape (T := T) (S := S) target source p' =
      .ok ⟨p', a.rank, a.target, a.source, a.readable, a.writable, true⟩ ∧
    a.target = target ∧ a.source = source ∧ a.parent = p := by
  unfold m107_reinterpretReshape at h ⊢
  rw [hrank, haxes]
  simp only [m14_throwbits, m27_throwbitpadding, m23_throwsingleton, m108_throwintmult,
    m119_throwfromsingleton, m18_throwsize0, m113_throwsize1,
    bind, pure, Except.bind, Except.pure] at h ⊢
  repeat' split at h
  all_goals try contradiction
  all_goals (
    cases h
    refine ⟨?_, rfl, rfl, rfl⟩
    simp only [*, Bool.false_eq_true, ↓reduceIte]
  )

theorem reinterpretNestedDispatch : ReinterpretNestedDispatch := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T S A R target a dataids hasOffset hid
    simp [m190_reinterpretParent, hid, m104_reinterpretIdentity, m370_dataids, m401_hasOffset, m369_parent]
  · intro T S A target a hid
    simp [m190_reinterpretParent, hid]
  · intro T S P A target parentSize parentAxes a hsz hid
    simp [m191_reinterpretReshapedParent, hsz, hid, m145_reinterpretReshapeIdentity]
  · intro T S A target source p p' a copy hid hcopy hrank haxes h73
    obtain ⟨h73', ht, hs, hp⟩ := m73_congr_parent target source p p' a hrank haxes h73
    simp [m371_unaliascopy, hp, hcopy, ht, hs, hid, h73']
  · intro T S A target source p p' a copy hid hcopy hrank haxes h188
    obtain ⟨h107', ht, hs, hp⟩ := m107_congr_parent target source p p' a hrank haxes h188
    simp [m372_unaliascopyReshaped, m188_reinterpretReshape, hp, hcopy, ht, hs, hid, h107']

/-! ## Entry 10: Shape and axes consistency across non-reshaped, 0D, and reshaped views -/

/-- Standard `oftype(ax, f:l)` constructs an `Axis` with start `f` and length `l - f + 1`. -/
def standardOftype (_ax : Axis) (f l : I64) : Axis := ⟨f, l - f + one⟩

/-- Across non-reshaped, zero-dimensional, and reshaped views, `size` and `axes` agree on rank,
axis lengths (`axs.map Axis.length = dims`), and trailing parent dimensions. -/
def ReinterpretShapeDimensions : Prop :=
  (∀ {T S A : Type} (a : ReinterpretArray T S (ArrayInput A)) (dims : List I64) (axs : List Axis),
    a.parent.size = a.parent.axes.map Axis.length →
    0 < a.parent.axes.length →
    m374_sizeNonReshaped ArrayInput.size divInt a = .ok dims →
    m387_axesNonReshaped ArrayInput.axes divInt standardOftype a = .ok axs →
    axs.map Axis.length = dims ∧
    dims.length = a.parent.size.length ∧
    dims.drop 1 = a.parent.size.drop 1 ∧
    axs.drop 1 = a.parent.axes.drop 1 ∧
    (axs.headD ⟨one, zero⟩).first = (a.parent.axes.headD ⟨one, zero⟩).first) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    m385_sizeZero a = [] ∧ m399_axesZero a = [] ∧
    (m399_axesZero a).map Axis.length = m385_sizeZero a) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (p : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    p.size = p.axes.map Axis.length →
    p.axes.length = p.rank →
    0 < target.alignedSize.val → 0 < source.alignedSize.val →
    m107_reinterpretReshape target source p = .ok r →
    ∃ dims axs,
      m379_sizeReshaped ArrayInput.size divInt r = .ok dims ∧
      m393_axesReshaped ArrayInput.axes divInt r = .ok axs ∧
      axs.map Axis.length = dims ∧
      dims.length = r.rank)

/-- Successful plain constructors preserve rank; reshape constructors add or remove
one dimension exactly when the target elements are smaller or larger. -/
def ReinterpretConstructorRank : Prop :=
  (∀ {T S A : Type} (target source : TypeLayout) (p : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    m73_reinterpret target source p = .ok r → r.rank = p.rank) ∧
  (∀ {T S A : Type} (target source : TypeLayout) (p : ArrayInput A)
      (r : ReinterpretArray T S (ArrayInput A)),
    m107_reinterpretReshape target source p = .ok r →
      (source.alignedSize = target.alignedSize → r.rank = p.rank) ∧
      (target.alignedSize < source.alignedSize → r.rank = p.rank + 1) ∧
      (source.alignedSize < target.alignedSize → r.rank + 1 = p.rank))



/-- `_checked_strides` divides byte strides iff every byte stride is an exact multiple of `els`,
`m211_strides` preserves physical byte strides `st * sizeof(T) = stp * sizeof(S)`, and
`m208_stride` selects the indexed stride from `m207_strides` in bounds and `length(A)` past `ndims(A)`. -/
def ReinterpretStrideInvariant : Prop :=
  (∀ (s e q r : I64),
    divremInt s e = .ok (q, r) →
    (r = zero → m225_checkedStrides divremInt (· == zero) [s] e = .ok [q]) ∧
    (r ≠ zero → m225_checkedStrides divremInt (· == zero) [s] e = .error .nonIntegralStride)) ∧
  (∀ {T S A : Type} (contiguous : A → Bool) (size : ReinterpretArray T S A → List I64)
      (sizeToStrides : I64 → List I64 → List I64) (parentStrides : A → List I64)
      (parentElsize : A → I64) (a : ReinterpretArray T S A) (s2 q2 : I64),
    contiguous (m369_parent a) = false →
    a.reshaped = false →
    a.target.alignedSize ≠ a.source.alignedSize →
    parentElsize (m369_parent a) = a.source.alignedSize →
    parentStrides (m369_parent a) = [one, s2] →
    one * a.source.alignedSize = a.source.alignedSize →
    divremInt (s2 * a.source.alignedSize) a.target.alignedSize = .ok (q2, zero) →
    m211_strides contiguous size sizeToStrides parentStrides parentElsize divremInt (· == zero) a =
      .ok [one, q2]) ∧
  (∀ {T S A : Type} (contiguous : A → Bool) (size : ReinterpretArray T S A → List I64)
      (sizeToStrides : I64 → List I64 → List I64) (parentStrides : A → List I64)
      (parentElsize : A → I64) (a : ReinterpretArray T S A) (s1 : I64),
    contiguous (m369_parent a) = false →
    a.reshaped = false →
    a.target.alignedSize ≠ a.source.alignedSize →
    parentElsize (m369_parent a) = a.source.alignedSize →
    parentStrides (m369_parent a) = [s1] →
    s1 * a.source.alignedSize ≠ a.source.alignedSize →
    m211_strides contiguous size sizeToStrides parentStrides parentElsize divremInt (· == zero) a =
      .error .noncontiguous) ∧
  (∀ {A : Type} (ndims : A → I64) (size : A → List I64)
      (sizeToStrides : I64 → List I64 → List I64) (length : A → I64) (a : A) (k : I64),
    m208_stride ndims (m207_strides size sizeToStrides) length (fun x y => decide (x ≤ y))
      (fun st d => st.getD (d.val - 1).toNat zero) a k =
      if k ≤ ndims a then (m207_strides size sizeToStrides a).getD (k.val - 1).toNat zero else length a)

theorem reinterpretStrideInvariant : ReinterpretStrideInvariant := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s e q r h
    constructor
    · intro hr
      subst hr
      simp [m225_checkedStrides, List.mapM, List.mapM.loop, h]
    · intro hr
      have hne_val : r.val ≠ zero.val := fun he => hr (jint_eq_of_val he)
      simp [m225_checkedStrides, List.mapM, List.mapM.loop, h, hne_val]
  · intro T S A contiguous size sizeToStrides parentStrides parentElsize a s2 q2 hcont hresh hne hels hstp h1 hdiv
    have hne_val : a.target.alignedSize.val ≠ a.source.alignedSize.val := fun he => hne (jint_eq_of_val he)
    simp [m211_strides, m232_checkcontiguous, hcont, hresh, hne_val, hels, hstp, h1,
      m225_checkedStrides, List.mapM, List.mapM.loop, hdiv]
  · intro T S A contiguous size sizeToStrides parentStrides parentElsize a s1 hcont hresh hne hels hstp h1
    have hne_val : a.target.alignedSize.val ≠ a.source.alignedSize.val := fun he => hne (jint_eq_of_val he)
    simp [m211_strides, m232_checkcontiguous, hcont, hresh, hne_val, hels, hstp, h1]
  · intro A ndims size sizeToStrides length a k
    simp [m208_stride]

/-! ## Entry 12: `IndexStyle` and linear vs subscript routing (`263`, `266`, `273`, `442`, `588`) -/

/-- Linear `IndexStyle` is preserved for non-reshaped views and reshaped views with `sS ≤ sT`
(so linear indexing coincides with 1D Cartesian indexing), while reshaped views with `sT < sS`
select `IndexSCartesian2{sS ÷ sT}` and route linear indexing through `_to_subscript_indices`. -/
def ReinterpretIndexStyleRouting : Prop :=
  (∀ {T S A : Type} (ops : PointerReadOps T S A) (checkParent : A → Bool)
      (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (getParent : A → List I64 → RResult Bytes)
      (toSubscripts : ReinterpretArray T S A → I64 → List I64)
      (a : ReinterpretArray T S A) (i : I64),
    parentIndexStyle a.parent = .linear →
    (a.reshaped = false ∨ a.source.alignedSize.val.toNat ≤ a.target.alignedSize.val.toNat) →
    m442_getindexLinear ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a i =
      m436_getindex ops checkParent parentIndexStyle firstindex checkbounds getParent a i []) ∧
  (∀ {T S A V : Type} (ops : PointerWriteOps T S A V) (checkParent : A → Bool)
      (parentIndexStyle : A → IndexStyleModel) (firstindex : ReinterpretArray T S A → I64)
      (checkbounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit)
      (convertValue : TypeLayout → V → RResult Bytes) (parent : ParentOps A)
      (toSubscripts : ReinterpretArray T S A → I64 → List I64)
      (a : ReinterpretArray T S A) (v : V) (i : I64),
    parentIndexStyle a.parent = .linear →
    (a.reshaped = false ∨ a.source.alignedSize.val.toNat ≤ a.target.alignedSize.val.toNat) →
    m588_setindexLinear ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v i =
      m582_setindex ops checkParent parentIndexStyle firstindex checkbounds convertValue parent a v i []) ∧
  (∀ {A : Type} (parentStyle : A → IndexStyleModel) (p : A) (sT sS : Nat),
    sT < sS → parentStyle p = .linear →
    m266_indexStyleReshaped parentStyle p sT sS = .staticCartesian (sS / sT) ∧
    m273_combineStyle (K := sS / sT) (m266_indexStyleReshaped parentStyle p sT sS)
      (m266_indexStyleReshaped parentStyle p sT sS) = .staticCartesian (sS / sT))

theorem reinterpretIndexStyleRouting : ReinterpretIndexStyleRouting := by
  refine ⟨?_, ?_, ?_⟩
  · intro T S A ops checkParent parentIndexStyle firstindex checkbounds getParent toSubscripts a i hlin hcond
    rcases hcond with hnr | hle
    · simp [m442_getindexLinear, m436_getindex, hnr, m263_indexStyle, hlin]
    · by_cases hnr : a.reshaped = true
      · have hnotlt : ¬ (a.target.alignedSize.val.toNat < a.source.alignedSize.val.toNat) := by omega
        simp [m442_getindexLinear, m436_getindex, hnr, m266_indexStyleReshaped, hnotlt, hlin]
      · have hnr' : a.reshaped = false := Bool.eq_false_iff.mpr hnr
        simp [m442_getindexLinear, m436_getindex, hnr', m263_indexStyle, hlin]
  · intro T S A V ops checkParent parentIndexStyle firstindex checkbounds convertValue parent toSubscripts a v i hlin hcond
    rcases hcond with hnr | hle
    · simp [m588_setindexLinear, m582_setindex, hnr, m263_indexStyle, hlin]
    · by_cases hnr : a.reshaped = true
      · have hnotlt : ¬ (a.target.alignedSize.val.toNat < a.source.alignedSize.val.toNat) := by omega
        simp [m588_setindexLinear, m582_setindex, hnr, m266_indexStyleReshaped, hnotlt, hlin]
      · have hnr' : a.reshaped = false := Bool.eq_false_iff.mpr hnr
        simp [m588_setindexLinear, m582_setindex, hnr', m263_indexStyle, hlin]
  · intro A parentStyle p sT sS hlt hlin
    simp [m266_indexStyleReshaped, m273_combineStyle, hlt, hlin]

/-! ## Entry 13: Static Cartesian iterator laws (`nextind`, `prevind`, `SCartesianIndices2`, `iterate`) -/

/-- Column-major linear rank of a static Cartesian index `ind = (i, j)` for channel width `K`. -/
def scartesianRank (K : I64) (ind : SCartesianIndex2) : Int :=
  ind.j.val * K.val + (ind.i.val - 1)

/-- `nextind` and `prevind` on `SCartesianIndex2{K}` are two-sided inverses and change the
column-major rank by `±1`; `SCartesianIndices2{K}` validates `K > 1`, preserves the outer axis,
starts at `first(iter)`, ends at `last(iter)`, and advances each `iterate` step by `nextind`. -/
def ReinterpretCartesianIteratorLaws : Prop :=
  (∀ (K : I64) (ind : SCartesianIndex2),
    1 < K.val → 1 ≤ ind.i.val → ind.i.val ≤ K.val →
    IntTy.min .i64 < ind.j.val → ind.j.val < IntTy.max .i64 →
    m279_toIndex ind = ind ∧
    m282_prevIndex K (m280_nextIndex K ind) = ind ∧
    m280_nextIndex K (m282_prevIndex K ind) = ind ∧
    scartesianRank K (m280_nextIndex K ind) = scartesianRank K ind + 1 ∧
    scartesianRank K (m282_prevIndex K ind) = scartesianRank K ind - 1) ∧
  (∀ {T S A : Type} (K : Nat) (each : IndexStyleModel → A → Axis) (a : ReinterpretArray T S A),
    (K ≤ 1 → m290_eachindexReshaped (K := K) each a = .error .assertion) ∧
    (1 < K → m290_eachindexReshaped (K := K) each a = .ok ⟨each .linear (m369_parent a)⟩)) ∧
  (∀ {A : Type} {K : Nat} (each : IndexStyleModel → A → RResult (SCartesianIndices2 K))
      (mismatch : List Axis → List (List Axis) → RResult (SCartesianIndices2 K))
      (axes : A → List Axis) (style : IndexStyleModel) (a b : A) (itA itB : SCartesianIndices2 K),
    each style a = .ok itA → each style b = .ok itB →
    (itB = itA → m291_eachindex each mismatch style a [b] axes = .ok itA) ∧
    (itB ≠ itA → m291_eachindex each mismatch style a [b] axes = mismatch (axes a) [axes b])) ∧
  (∀ {K : Nat} (iter : SCartesianIndices2 K) (state1 item2 : I64),
    1 < K → (K : Int) ≤ IntTy.max .i64 →
    IntTy.min .i64 < item2.val → item2.val < IntTy.max .i64 →
    1 ≤ state1.val → state1.val ≤ K →
    m298_indicesSize iter = (K, iter.indices2.length) ∧
    m299_indicesAxes iter = [⟨one, JInt.lit .i64 K⟩, iter.indices2] ∧
    m309_indicesIterate (fun ax => some (ax.first, ax.first)) iter =
      some (m301_indicesFirst iter, (one, iter.indices2.first, iter.indices2.first)) ∧
    m316_indicesIterateState (fun _ s => some (s + one, s + one)) iter state1 item2 item2 =
      some (m280_nextIndex (JInt.lit .i64 K) ⟨state1, item2⟩,
        ((m280_nextIndex (JInt.lit .i64 K) ⟨state1, item2⟩).i,
         (m280_nextIndex (JInt.lit .i64 K) ⟨state1, item2⟩).j,
         if state1 < JInt.lit .i64 K then item2 else item2 + one)) ∧
    m304_indicesGet (fun _ _ _ => .ok ()) (fun ax j => .ok (ax.first + j - one)) iter
        (JInt.lit .i64 K) iter.indices2.length =
      .ok (m302_indicesLast iter))

theorem reinterpretCartesianIteratorLaws : ReinterpretCartesianIteratorLaws := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K ind hK hi1 hiK hjmin hjmax
    rcases ind with ⟨i, j⟩
    dsimp at hi1 hiK hjmin hjmax
    have h1v : (JInt.lit .i64 1).val = 1 := by decide
    have hj_add_sub : j + JInt.lit .i64 1 - JInt.lit .i64 1 = j := by
      apply jint_eq_of_val
      simp only [val_sub, val_add, wrapInt_sub_left, h1v]
      rw [show j.val + 1 - 1 = j.val by omega, wrapInt_of_inRange .i64 j.val j.property]
    have hj_sub_add : j - JInt.lit .i64 1 + JInt.lit .i64 1 = j := by
      apply jint_eq_of_val
      simp only [val_add, val_sub, wrapInt_add_left, h1v]
      rw [show j.val - 1 + 1 = j.val by omega, wrapInt_of_inRange .i64 j.val j.property]
    have hj_add_val : (j + JInt.lit .i64 1).val = j.val + 1 := by
      rw [val_add, h1v]
      exact wrapInt_of_inRange .i64 (j.val + 1) ⟨by omega, by omega⟩
    have hj_sub_val : (j - JInt.lit .i64 1).val = j.val - 1 := by
      rw [val_sub, h1v]
      exact wrapInt_of_inRange .i64 (j.val - 1) ⟨by omega, by omega⟩
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · by_cases hlt : i < K
      · have hi_lt : i.val < K.val := hlt
        have hi_add_val : (i + JInt.lit .i64 1).val = i.val + 1 := by
          rw [val_add, h1v]
          exact wrapInt_of_inRange .i64 (i.val + 1) ⟨by have := i64_min_nonpos; omega, by have := K.property.2; omega⟩
        have hgt1 : JInt.lit .i64 1 < i + JInt.lit .i64 1 := by
          rw [lt_iff_val, h1v, hi_add_val]; omega
        have hi_add_sub : i + JInt.lit .i64 1 - JInt.lit .i64 1 = i := by
          apply jint_eq_of_val
          rw [val_sub, hi_add_val, h1v, show i.val + 1 - 1 = i.val by omega,
            wrapInt_of_inRange .i64 i.val i.property]
        simp [m280_nextIndex, m282_prevIndex, hlt, hgt1, hi_add_sub]
      · have hi_eq : i = K := jint_eq_of_val (by rw [lt_iff_val] at hlt; omega)
        subst hi_eq
        have hnotgt : ¬ (JInt.lit .i64 1 < JInt.lit .i64 1) := by decide
        simp [m280_nextIndex, m282_prevIndex, hlt, hnotgt, hj_add_sub]
    · by_cases hgt : JInt.lit .i64 1 < i
      · have hi_gt : 1 < i.val := by rw [lt_iff_val, h1v] at hgt; exact hgt
        have hi_sub_val : (i - JInt.lit .i64 1).val = i.val - 1 := by
          rw [val_sub, h1v]
          exact wrapInt_of_inRange .i64 (i.val - 1) ⟨by have := i64_min_nonpos; omega, by have := i.property.2; omega⟩
        have hltK : i - JInt.lit .i64 1 < K := by
          rw [lt_iff_val, hi_sub_val]; omega
        have hi_sub_add : i - JInt.lit .i64 1 + JInt.lit .i64 1 = i := by
          apply jint_eq_of_val
          rw [val_add, hi_sub_val, h1v, show i.val - 1 + 1 = i.val by omega,
            wrapInt_of_inRange .i64 i.val i.property]
        simp [m282_prevIndex, m280_nextIndex, hgt, hltK, hi_sub_add]
      · have hi_eq : i = JInt.lit .i64 1 := jint_eq_of_val (by rw [lt_iff_val, h1v] at hgt; omega)
        subst hi_eq
        have hnotlt : ¬ (K < K) := by rw [lt_iff_val]; omega
        simp [m282_prevIndex, m280_nextIndex, hgt, hnotlt, hj_sub_add]
    · by_cases hlt : i < K
      · have hi_lt : i.val < K.val := hlt
        have hi_add_val : (i + JInt.lit .i64 1).val = i.val + 1 := by
          rw [val_add, h1v]
          exact wrapInt_of_inRange .i64 (i.val + 1) ⟨by have := i64_min_nonpos; omega, by have := K.property.2; omega⟩
        simp only [m280_nextIndex, hlt, ↓reduceIte, scartesianRank, hi_add_val]
        omega
      · have hi_eq : i.val = K.val := by rw [lt_iff_val] at hlt; omega
        simp only [m280_nextIndex, hlt, ↓reduceIte, scartesianRank, h1v, hj_add_val, hi_eq]
        rw [Int.add_mul, Int.one_mul]; omega
    · by_cases hgt : JInt.lit .i64 1 < i
      · have hi_gt : 1 < i.val := by rw [lt_iff_val, h1v] at hgt; exact hgt
        have hi_sub_val : (i - JInt.lit .i64 1).val = i.val - 1 := by
          rw [val_sub, h1v]
          exact wrapInt_of_inRange .i64 (i.val - 1) ⟨by have := i64_min_nonpos; omega, by have := i.property.2; omega⟩
        simp only [m282_prevIndex, hgt, ↓reduceIte, scartesianRank, hi_sub_val]
        omega
      · have hi_eq : i.val = 1 := by rw [lt_iff_val, h1v] at hgt; omega
        simp only [m282_prevIndex, hgt, ↓reduceIte, scartesianRank, hj_sub_val, hi_eq]
        rw [Int.sub_mul, Int.one_mul]; omega
  · intro T S A K each a
    constructor
    · intro hK
      have hnot : ¬ (1 < K) := by omega
      simp [m290_eachindexReshaped, m288_indicesConstructor, hnot]
    · intro hK
      simp [m290_eachindexReshaped, m288_indicesConstructor, hK]
  · intro A K each mismatch axes style a b itA itB ha hb
    constructor
    · intro heq; subst heq
      simp [m291_eachindex, List.mapM, List.mapM.loop, ha, hb]
    · intro hne
      simp [m291_eachindex, List.mapM, List.mapM.loop, ha, hb, hne]
  · intro K iter state1 item2 hK hKmax hjmin hjmax hs1 hsK
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · by_cases hlt : state1 < JInt.lit .i64 K
      · simp [m316_indicesIterateState, m280_nextIndex, hlt, one]
      · simp [m316_indicesIterateState, m280_nextIndex, hlt, one]
    · simp [m304_indicesGet, m302_indicesLast]

/-! ## Entry 14: Static Cartesian coordinate routing and channel read-after-write (`347`, `352`, `359`, `454`, `598`) -/

/-- `_scartesian2_trailing`, `_getindex`, and `_setindex!` translate static Cartesian indices to
parent coordinates (mapping `first(iter)` to `[ax1.first, ax2.first]`), and `getindex`/`setindex!`
on a `ReshapedReinterpretArray` with `SCartesianIndex2` satisfy the lens laws (reading after writing
at the same channel and parent element returns `v`, and writing one channel preserves all other
channels of the same parent element and all other parent elements). -/
def ReinterpretCartesianGetSet : Prop :=
  (∀ {A R : Type} {K : Nat} (ax1 ax2 : Axis) (f2 len2 : I64)
      (getindex : A → List I64 → R) (style : IndexStyleModel) (a : A),
    m347_getindexCartesian (K := K) (fun _ _ => ⟨⟨f2, len2⟩⟩) (fun _ => [ax1, ax2])
      (fun _ _ => []) getindex style a (m301_indicesFirst (K := K) ⟨⟨f2, len2⟩⟩) =
      getindex a [ax1.first, ax2.first]) ∧
  (∀ {A V R : Type} {K : Nat} (ax1 ax2 : Axis) (f2 len2 : I64)
      (setindex : A → V → List I64 → R) (style : IndexStyleModel) (a : A) (v : V),
    m352_setindexCartesian (K := K) (fun _ _ => ⟨⟨f2, len2⟩⟩) (fun _ => [ax1, ax2])
      (fun _ _ => []) setindex style a v (m301_indicesFirst (K := K) ⟨⟨f2, len2⟩⟩) =
      setindex a v [ax1.first, ax2.first]) ∧
  (∀ {T S : Type} (sT K : Nat) (col : List Bytes)
      (a : ReinterpretArray T S (List Bytes)) (v : Bytes) (ind ind' : SCartesianIndex2),
    0 < sT → 1 < K → ((K * sT : Nat) : Int) ≤ IntTy.max .i64 →
    (∀ s ∈ col, s.length = K * sT) →
    a.readable = true → a.writable = true →
    a.target.alignedSize = JInt.lit .i64 sT →
    v.length = sT →
    1 ≤ ind.i.val → ind.i.val ≤ K →
    1 ≤ ind.j.val → ind.j.val ≤ col.length →
    1 ≤ ind'.i.val → ind'.i.val ≤ K →
    1 ≤ ind'.j.val → ind'.j.val ≤ col.length →
    a.parent = col →
    ∃ a',
      m598_setindexCartesian (fun _ x => .ok x)
        ⟨(fun c inds => match inds with
          | [j] => if 1 ≤ j.val ∧ j.val ≤ c.length then .ok (c.getD (j.val - 1).toNat []) else .error .bounds
          | _ => .error .bounds),
         (fun c inds s => match inds with
          | [j] => if 1 ≤ j.val ∧ j.val ≤ c.length then .ok (c.set (j.val - 1).toNat s) else .error .bounds
          | _ => .error .bounds)⟩
        a v ind = .ok a' ∧
      m454_getindexCartesian
        (fun c inds => match inds with
          | [j] => if 1 ≤ j.val ∧ j.val ≤ c.length then .ok (c.getD (j.val - 1).toNat []) else .error .bounds
          | _ => .error .bounds)
        a' ind' =
        if ind' = ind then .ok v
        else m454_getindexCartesian
          (fun c inds => match inds with
            | [j] => if 1 ≤ j.val ∧ j.val ≤ c.length then .ok (c.getD (j.val - 1).toNat []) else .error .bounds
            | _ => .error .bounds)
          a ind')

theorem byteWindow_overwriteBytes_same (s v : Bytes) (i sT : Nat)
    (hv : v.length = sT) (hb : i * sT + sT ≤ s.length) :
    byteWindow (overwriteBytes s (i * sT) v) (i * sT) sT = v := by
  apply List.ext_getElem?
  intro k
  simp only [byteWindow, List.getElem?_take, List.getElem?_drop]
  by_cases hk : k < sT
  · rw [ite_eq_left hk]
    have h1 : i * sT + v.length ≤ s.length := by rw [hv]; exact hb
    have hht : (s.take (i * sT)).length = i * sT := by rw [List.length_take]; omega
    unfold overwriteBytes
    rw [List.append_assoc, List.getElem?_append_right (by rw [hht]; omega), hht,
      List.getElem?_append_left (by rw [hv]; omega), show i * sT + k - i * sT = k by omega]
  · rw [ite_eq_right hk, List.getElem?_eq_none (by omega)]

theorem byteWindow_overwriteBytes_other (s v : Bytes) (i i' sT : Nat)
    (hne : i' ≠ i) (hv : v.length = sT) (hb : i * sT + sT ≤ s.length) (_hb' : i' * sT + sT ≤ s.length) :
    byteWindow (overwriteBytes s (i * sT) v) (i' * sT) sT = byteWindow s (i' * sT) sT := by
  apply List.ext_getElem?
  intro k
  simp only [byteWindow, List.getElem?_take, List.getElem?_drop]
  by_cases hk : k < sT
  · simp only [hk, ↓reduceIte]
    have h1 : i * sT + v.length ≤ s.length := by rw [hv]; exact hb
    have hht : (s.take (i * sT)).length = i * sT := by rw [List.length_take]; omega
    unfold overwriteBytes
    rw [List.append_assoc]
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hle : i' * sT + sT ≤ i * sT := by
        have := Nat.mul_le_mul_right sT (show i' + 1 ≤ i by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      rw [List.getElem?_append_left (by rw [hht]; omega), List.getElem?_take,
        ite_eq_left (by omega)]
    · have hle : i * sT + sT ≤ i' * sT := by
        have := Nat.mul_le_mul_right sT (show i + 1 ≤ i' by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      rw [List.getElem?_append_right (by rw [hht]; omega), hht,
        List.getElem?_append_right (by rw [hv]; omega), List.getElem?_drop, hv,
        show i * sT + sT + (i' * sT + k - i * sT - sT) = i' * sT + k by omega]
  · simp only [hk, ↓reduceIte]

theorem reinterpretCartesianGetSet : ReinterpretCartesianGetSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro A R K ax1 ax2 f2 len2 getindex style a
    have h1 : ax1.first + one - one = ax1.first := by
      apply jint_eq_of_val
      simp only [val_sub, val_add, wrapInt_sub_left]
      rw [show ax1.first.val + one.val - one.val = ax1.first.val by omega,
        wrapInt_of_inRange .i64 ax1.first.val ax1.first.property]
    have h2 : ax2.first + (f2 - f2) = ax2.first := by
      apply jint_eq_of_val
      simp only [val_add, val_sub, wrapInt_add_right]
      rw [show ax2.first.val + (f2.val - f2.val) = ax2.first.val by omega,
        wrapInt_of_inRange .i64 ax2.first.val ax2.first.property]
    simp [m347_getindexCartesian, m359_scartesian2Trailing, m301_indicesFirst, h1, h2]
  · intro A V R K ax1 ax2 f2 len2 setindex style a v
    have h1 : ax1.first + one - one = ax1.first := by
      apply jint_eq_of_val
      simp only [val_sub, val_add, wrapInt_sub_left]
      rw [show ax1.first.val + one.val - one.val = ax1.first.val by omega,
        wrapInt_of_inRange .i64 ax1.first.val ax1.first.property]
    have h2 : ax2.first + (f2 - f2) = ax2.first := by
      apply jint_eq_of_val
      simp only [val_add, val_sub, wrapInt_add_right]
      rw [show ax2.first.val + (f2.val - f2.val) = ax2.first.val by omega,
        wrapInt_of_inRange .i64 ax2.first.val ax2.first.property]
    simp [m352_setindexCartesian, m359_scartesian2Trailing, m301_indicesFirst, h1, h2]
  · intro T S sT K col a v ind ind' hsT hK hB hwf hread hwrite hts hv hi1 hiK hj1 hjL hi1' hiK' hj1' hjL' hpar
    let jNat := (ind.j.val - 1).toNat
    let jNat' := (ind'.j.val - 1).toNat
    let iNat := (ind.i.val - 1).toNat
    let iNat' := (ind'.i.val - 1).toNat
    have hjNat_lt : jNat < col.length := by dsimp [jNat]; omega
    have hjNat'_lt : jNat' < col.length := by dsimp [jNat']; omega
    have hcol_j : col[jNat].length = K * sT := hwf _ (List.getElem_mem hjNat_lt)
    have hts_val : (JInt.lit .i64 (sT : Int)).val = (sT : Int) := by
      rw [val_lit]
      exact wrapInt_nat sT (by
        have : sT ≤ K * sT := Nat.le_mul_of_pos_left sT (by omega)
        omega)
    have hi_mul : ((ind.i - one) * JInt.lit .i64 (sT : Int)).val.toNat = iNat * sT := by
      have hsub : (ind.i - one).val = (iNat : Int) := by
        rw [val_sub, one_val, show ind.i.val - 1 = (iNat : Int) by dsimp [iNat]; omega]
        exact wrapInt_nat iNat (by
          have : iNat ≤ K * sT := by
            have := Nat.mul_le_mul_left K (show 1 ≤ sT from hsT)
            dsimp [iNat]; omega
          omega)
      rw [val_mul, hsub, hts_val, ← Int.natCast_mul,
        wrapInt_nat (iNat * sT) (by
          have : iNat * sT ≤ K * sT := Nat.mul_le_mul_right sT (by dsimp [iNat]; omega)
          omega),
        Int.toNat_natCast]
    have hi'_mul : ((ind'.i - one) * JInt.lit .i64 (sT : Int)).val.toNat = iNat' * sT := by
      have hsub : (ind'.i - one).val = (iNat' : Int) := by
        rw [val_sub, one_val, show ind'.i.val - 1 = (iNat' : Int) by dsimp [iNat']; omega]
        exact wrapInt_nat iNat' (by
          have : iNat' ≤ K * sT := by
            have := Nat.mul_le_mul_left K (show 1 ≤ sT from hsT)
            dsimp [iNat']; omega
          omega)
      rw [val_mul, hsub, hts_val, ← Int.natCast_mul,
        wrapInt_nat (iNat' * sT) (by
          have : iNat' * sT ≤ K * sT := Nat.mul_le_mul_right sT (by dsimp [iNat']; omega)
          omega),
        Int.toNat_natCast]
    have hj_in : 1 ≤ ind.j.val ∧ ind.j.val ≤ col.length := ⟨hj1, hjL⟩
    have hj'_in : 1 ≤ ind'.j.val ∧ ind'.j.val ≤ col.length := ⟨hj1', hjL'⟩
    have hmc : memcpyValue (col.getD jNat []) v ((ind.i - one) * a.target.alignedSize) zero a.target.alignedSize =
        overwriteBytes col[jNat] (iNat * sT) v := by
      simp [memcpyValue, byteWindow, hts, hi_mul, zero_val, hts_val,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjNat_lt,
        List.take_of_length_le (Nat.le_of_eq hv)]
    refine ⟨{ a with parent := col.set jNat (overwriteBytes col[jNat] (iNat * sT) v) }, ?_, ?_⟩
    · have hnw : (!a.writable) = false := by simp [hwrite]
      unfold m598_setindexCartesian m244_checkWritable
      simp only [hnw, Bool.false_eq_true, ↓reduceIte, resultPure, resultBindOk, hpar, hj_in, and_self]
      change Except.ok { a with parent := col.set jNat (memcpyValue (col.getD jNat []) v ((ind.i - one) * a.target.alignedSize) zero a.target.alignedSize) } =
        Except.ok { a with parent := col.set jNat (overwriteBytes col[jNat] (iNat * sT) v) }
      rw [hmc]
    · unfold m454_getindexCartesian m237_checkReadable
      simp only [hread, Bool.not_true, Bool.false_eq_true, ↓reduceIte, resultPure, resultBindOk,
        List.length_set, hj'_in, and_self, hts, hi'_mul, hts_val, Int.toNat_natCast, hpar]
      have hib : iNat * sT + sT ≤ col[jNat].length := by
        rw [hcol_j]
        have := Nat.mul_le_mul_right sT (show iNat + 1 ≤ K by dsimp [iNat]; omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have hib' : iNat' * sT + sT ≤ col[jNat].length := by
        rw [hcol_j]
        have := Nat.mul_le_mul_right sT (show iNat' + 1 ≤ K by dsimp [iNat']; omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      by_cases heq : ind' = ind
      · subst heq
        have hjeq : jNat' = jNat := rfl
        have hieq : iNat' = iNat := rfl
        rw [ite_eq_left rfl]
        change Except.ok (byteWindow ((col.set jNat (overwriteBytes col[jNat] (iNat * sT) v)).getD jNat' []) (iNat' * sT) sT) = Except.ok v
        rw [hjeq, hieq]
        simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hjNat_lt,
          byteWindow_overwriteBytes_same col[jNat] v iNat sT hv hib]
      · rw [ite_eq_right heq]
        change Except.ok (byteWindow ((col.set jNat (overwriteBytes col[jNat] (iNat * sT) v)).getD jNat' []) (iNat' * sT) sT) =
          Except.ok (byteWindow (col.getD jNat' []) (iNat' * sT) sT)
        by_cases hjeq : jNat' = jNat
        · have hine : iNat' ≠ iNat := by
            intro hi_eq
            apply heq
            have h1 : ind'.i = ind.i := jint_eq_of_val (by dsimp [iNat, iNat'] at hi_eq; omega)
            have h2 : ind'.j = ind.j := jint_eq_of_val (by dsimp [jNat, jNat'] at hjeq; omega)
            cases ind; cases ind'; simp_all
          rw [hjeq]
          simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hjNat_lt,
            List.getElem?_eq_getElem hjNat_lt,
            byteWindow_overwriteBytes_other col[jNat] v iNat iNat' sT hine hv hib hib']
        · simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hjeq)]

/-! ## Entry 16: `isassigned` bounds and fallback (`432`, `433`, `434`) -/

/-- Because `_isassigned_ra` returns `true`, `isassigned(a, inds::Integer...)` equals
`checkbounds(Bool, a, inds...)` for every `a` and every `check_ptr_indexable` state, while
`isassigned(a, ind::SCartesianIndex2)` forwards to `isassigned(a.parent, ind.j)`. -/
def ReinterpretIsAssignedBounds : Prop :=
  (∀ {T S A : Type} (checkbounds : ReinterpretArray T S A → List I64 → Bool)
      (checkParent : A → Bool) (a : ReinterpretArray T S A) (inds : List I64),
    m434_isassignedRa a inds = true ∧
    m432_isassigned checkbounds checkParent a inds = checkbounds a inds) ∧
  (∀ {T S A : Type} (parentAssigned : A → I64 → Bool)
      (a : ReinterpretArray T S A) (ind : SCartesianIndex2),
    m433_isassignedCartesian parentAssigned a ind = parentAssigned (m369_parent a) ind.j)

theorem reinterpretIsAssignedBounds : ReinterpretIsAssignedBounds := by
  refine ⟨?_, ?_⟩
  · intro T S A checkbounds checkParent a inds
    simp [m432_isassigned, m434_isassignedRa]
  · intro T S A parentAssigned a ind
    simp [m433_isassignedCartesian, m369_parent]

@[simp] theorem ispacked_primitiveLayout (id size : Nat) :
    m824_ispacked (primitiveLayout id size) = true := rfl

@[simp] theorem packedsize_primitiveLayout (id size : Nat) :
    m816_packedsize (primitiveLayout id size) = .ok (JInt.lit .i64 size).val.toNat := rfl

/-! ## Entry 17: Padding layout invariants (`750`, `759`, `815`, `819`, `827`, `831`) -/

theorem foldl_preserve_length {α : Type} (xs : List α) (f : List Bool → α → List Bool)
    (hf : ∀ (b : List Bool) (x : α), x ∈ xs → (f b x).length = b.length) :
    ∀ (b : List Bool), (xs.foldl f b).length = b.length := by
  induction xs with
  | nil => intro b; rfl
  | cons x rest ih =>
    intro b
    simp only [List.foldl_cons]
    rw [ih (fun b' y hy => hf b' y (List.mem_cons_of_mem x hy)),
      hf b x List.mem_cons_self]

theorem fillNonpadding_length (layout : TypeLayout) (offset : I64) (used : List Bool) :
    (m756_fillNonpadding layout offset used).length = used.length := by
  revert offset used
  refine WellFounded.induction
    (C := fun t => ∀ (offset : I64) (used : List Bool), (m756_fillNonpadding t offset used).length = used.length)
    (measure sizeOf).wf layout ?_
  intro t ih offset used
  rw [m756_fillNonpadding.eq_def]
  by_cases hp : t.primitive = true
  · rw [ite_eq_left hp]
    exact foldl_preserve_length _ _ (fun b _ _ => List.length_set) used
  · rw [ite_eq_right hp]
    apply foldl_preserve_length
    intro b field _
    apply ih field.val.2
    rcases t with ⟨info, fields, members⟩
    have h1 : sizeOf field.val < sizeOf fields := List.sizeOf_lt_of_mem field.property
    have h2 : sizeOf field.val.2 < sizeOf field.val := by
      rcases field with ⟨⟨off, child⟩, _⟩; simp; omega
    have h3 : sizeOf fields < sizeOf (TypeLayout.mk info fields members) := by simp; omega
    exact Nat.lt_trans h2 (Nat.lt_trans h1 h3)
/-- `fill_nonpadding_bytes!` preserves the byte-mask length for every primitive and composite
field tree; `non_padding_bytes` rejects bit-padded types and otherwise produces a mask of length
`aligned_sizeof(T)` so `packedsize(T) ≤ aligned_sizeof(T)` and `struct_subpadding` is reflexive. -/
def ReinterpretPaddingLayout : Prop :=
  (∀ (layout : TypeLayout) (offset : I64) (used : List Bool),
    (m756_fillNonpadding layout offset used).length = used.length) ∧
  (∀ (layout : TypeLayout),
    (m828_hasBitPadding layout = true → m750_nonPaddingBytes layout = .error .argument) ∧
    (m828_hasBitPadding layout = false →
      ∃ mask, m750_nonPaddingBytes layout = .ok mask ∧
        mask.length = layout.alignedSize.val.toNat ∧
        m812_structSubpadding layout layout = .ok true ∧
        ∃ ps, m816_packedsize layout = .ok ps ∧ ps ≤ layout.alignedSize.val.toNat)) ∧
  (∀ (id size : Nat),
    m824_ispacked (primitiveLayout id size) = true ∧
    m828_hasBitPadding (primitiveLayout id size) = false ∧
    m816_packedsize (primitiveLayout id size) = .ok (JInt.lit .i64 size).val.toNat)

theorem reinterpretPaddingLayout : ReinterpretPaddingLayout := by
  refine ⟨fillNonpadding_length, ?_, ?_⟩
  · intro layout
    constructor
    · intro hbp
      simp [m750_nonPaddingBytes, hbp]
    · intro hbp
      refine ⟨m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false), ?_, ?_, ?_, ?_⟩
      · simp [m750_nonPaddingBytes, hbp]
      · rw [fillNonpadding_length, List.length_replicate]
      · simp [m812_structSubpadding, m750_nonPaddingBytes, hbp]
      · by_cases hpad : layout.datatypePadding = true
        · refine ⟨(m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false)).countP id, ?_, ?_⟩
          · simp [m816_packedsize, hpad, m750_nonPaddingBytes, hbp]; rfl
          · have hle := List.countP_le_length (p := id)
              (l := m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false))
            rw [fillNonpadding_length, List.length_replicate] at hle
            exact hle
        · have hpad' : layout.datatypePadding = false := Bool.eq_false_iff.mpr hpad
          refine ⟨layout.alignedSize.val.toNat, ?_, Nat.le_refl _⟩
          simp [m816_packedsize, hpad']
  · intro id size
    simp

/-! ## Entry 18: `array_subpadding` loop, `check_readable`, `check_writable`, and `showerror` -/

theorem subpadding_loop_refl (mask : List Bool) (sn : I64) (n : Nat)
    (hn_pos : 0 < n) (hn_max : (n : Int) < IntTy.max .i64) (hsn : sn.val = n) :
    ∀ (rem k : Nat) (si : I64),
      n - k ≤ rem → 1 ≤ k → k ≤ n → si.val = k →
      m772_arraySubpadding.loop mask mask sn sn si si = .ok true := by
  intro rem
  induction rem with
  | zero =>
    intro k si hrem _ hkn hsi
    have hk_eq : k = n := by omega
    subst hk_eq
    rw [m772_arraySubpadding.loop.eq_def]
    dsimp only
    have hnot : (mask.getD (si - one).val.toNat false && !mask.getD (si - one).val.toNat false) = false := by
      cases mask.getD (si - one).val.toNat false <;> rfl
    rw [hnot]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hadd : (si + one).val = (k : Int) + 1 := by
      rw [val_add, hsi, one_val]
      exact wrapInt_of_inRange .i64 ((k : Int) + 1) ⟨by have := i64_min_nonpos; omega, by omega⟩
    have hlt : sn < si + one := by rw [lt_iff_val, hsn, hadd]; omega
    rw [ite_eq_left hlt]
    rfl
  | succ rem ih =>
    intro k si hrem hk1 hkn hsi
    rw [m772_arraySubpadding.loop.eq_def]
    dsimp only
    have hnot : (mask.getD (si - one).val.toNat false && !mask.getD (si - one).val.toNat false) = false := by
      cases mask.getD (si - one).val.toNat false <;> rfl
    rw [hnot]
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hlt_n : k < n
    · have hadd : (si + one).val = ((k + 1 : Nat) : Int) := by
        rw [val_add, hsi, one_val, show (k : Int) + 1 = ((k + 1 : Nat) : Int) by omega]
        exact wrapInt_nat (k + 1) (by omega)
      have hnlt : ¬ (sn < si + one) := by rw [lt_iff_val, hsn, hadd]; omega
      have hne1 : ((si + one) == one) = false := by
        rw [beq_iff_val, hadd, one_val]
        exact decide_eq_false (by omega)
      rw [ite_eq_right hnlt]
      simp only [hne1, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ih (k + 1) (si + one) (by omega) (by omega) (by omega) hadd
    · have hk_eq : k = n := by omega
      subst hk_eq
      have hadd : (si + one).val = (k : Int) + 1 := by
        rw [val_add, hsi, one_val]
        exact wrapInt_of_inRange .i64 ((k : Int) + 1) ⟨by have := i64_min_nonpos; omega, by omega⟩
      have hlt : sn < si + one := by rw [lt_iff_val, hsn, hadd]; omega
      rw [ite_eq_left hlt]
      rfl

/-- `array_subpadding` succeeds on packed targets, fails when a packed source is reinterpreted as a
padded target, and is reflexive on every byte-aligned layout (including padded structs via its
wrapping index loop); `check_readable` and `check_writable` enforce the subpadding relation and
`showerror` formats `PaddingError`. -/
def ReinterpretPaddingChecks : Prop :=
  (∀ (source target : TypeLayout),
    (m824_ispacked target = true → m772_arraySubpadding source target = .ok true) ∧
    (m824_ispacked target = false → m824_ispacked source = true →
      m772_arraySubpadding source target = .ok false)) ∧
  (∀ (layout : TypeLayout),
    m828_hasBitPadding layout = false →
    0 < layout.alignedSize.val → layout.alignedSize.val < IntTy.max .i64 →
    m772_arraySubpadding layout layout = .ok true) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    m772_arraySubpadding a.target a.source = .ok a.readable →
    m772_arraySubpadding a.source a.target = .ok a.writable →
    m237_checkReadable a = (if a.readable then .ok () else .error .padding) ∧
    m244_checkWritable a = (if a.writable then .ok () else .error .padding)) ∧
  (∀ (s t : String),
    m741_showerror ⟨s, t⟩ = "Padding of type " ++ s ++ " is not compatible with type " ++ t ++ ".")

theorem reinterpretPaddingChecks : ReinterpretPaddingChecks := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro source target
    constructor
    · intro ht; simp [m772_arraySubpadding, ht]
    · intro ht hs; simp [m772_arraySubpadding, ht, hs]
  · intro layout hbp hpos hmax
    unfold m772_arraySubpadding
    by_cases hp : m824_ispacked layout = true
    · simp [hp]
    · have hp' : m824_ispacked layout = false := Bool.eq_false_iff.mpr hp
      have hlen : (m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false)).length =
          layout.alignedSize.val.toNat := by
        rw [fillNonpadding_length, List.length_replicate]
      have hne_empty : (m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false)).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff_exists_mem]
        rcases hmask : m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false) with _ | ⟨b, bs⟩
        · rw [hmask] at hlen; simp at hlen; omega
        · exact ⟨b, List.mem_cons_self⟩
      simp only [hp', Bool.false_eq_true, ↓reduceIte, m750_nonPaddingBytes, hbp,
        resultPure, resultBindOk, hne_empty, hlen]
      have hsn : (JInt.lit .i64 (layout.alignedSize.val.toNat : Int)).val = layout.alignedSize.val.toNat :=
        lit_nat layout.alignedSize.val.toNat (by omega)
      exact subpadding_loop_refl
        (m756_fillNonpadding layout zero (List.replicate layout.alignedSize.val.toNat false))
        (JInt.lit .i64 layout.alignedSize.val.toNat)
        layout.alignedSize.val.toNat
        (by omega) (by omega) hsn
        (layout.alignedSize.val.toNat - 1) 1 one (by omega) (by omega) (by omega) one_val
  · intro T S A a hr hw
    constructor
    · cases h : a.readable <;> simp [m237_checkReadable, h, hr]
    · cases h : a.writable <;> simp [m244_checkWritable, h, hw]
  · intro s t
    rfl

/-! ## Entry 7: Packed copying and padding-aware scalar reinterpretation (`842`, `862`, `882`, `913`) -/

/-- A composite struct layout with a single packed primitive field of size `n` at byte offset `off`
inside an `aligned`-byte padded container (`off + n ≤ aligned`). -/
def singleFieldPaddedLayout (id off n aligned : Nat) : TypeLayout :=
  .mk ⟨id, aligned * 8, JInt.lit .i64 aligned, true, false, false, false, true⟩
    [(off, primitiveLayout (id + 1) n)] []

theorem overwriteBytes_zero_full (dst src : Bytes) (h : src.length = dst.length) :
    overwriteBytes dst 0 src = src := by
  unfold overwriteBytes
  rw [List.take_zero, List.nil_append, Nat.zero_add, List.drop_of_length_le (by omega),
    List.append_nil]

theorem forIn_singleton_ok {α β : Type} (x : α) (b b' : β)
    (f : α → β → RResult (ForInStep β)) (h : f x b = .ok (.yield b')) :
    forIn [x] b f = .ok b' := by
  change (do let s ← f x b; match s with | .done b'' => pure b'' | .yield b'' => pure b'') = .ok b'
  rw [h]; rfl

theorem attach_singleton {α : Type} (x : α) :
    ([x] : List α).attach = [⟨x, List.mem_cons_self⟩] := rfl

theorem fields_primitiveLayout (id size : Nat) :
    (primitiveLayout id size).fields = [] := rfl

theorem fields_singleFieldPaddedLayout (id off n aligned : Nat) :
    (singleFieldPaddedLayout id off n aligned).fields = [(off, primitiveLayout (id + 1) n)] := rfl

theorem copytopacked_primitive (t : TypeLayout) (dst src : Bytes) (ps : Nat)
    (hp : t.primitive = true) (hps : m816_packedsize t = .ok ps) :
    m842_copytopacked t dst src zero zero = .ok (memcpyValue dst src zero zero (JInt.lit .i64 ps)) := by
  rw [m842_copytopacked.eq_def, ite_eq_left hp, hps]
  rfl

theorem copyfrompacked_primitive (t : TypeLayout) (dst src : Bytes) (ps : Nat)
    (hp : t.primitive = true) (hps : m816_packedsize t = .ok ps) :
    m862_copyfrompacked t dst src zero zero = .ok (memcpyValue dst src zero zero (JInt.lit .i64 ps)) := by
  rw [m862_copyfrompacked.eq_def, ite_eq_left hp, hps]
  rfl

theorem copytopacked_single_packed_field (t : TypeLayout) (off : Nat) (child : TypeLayout)
    (dst src : Bytes) (hprim : t.primitive = false)
    (hfields : t.fields = [(off, child)]) (hisp : m824_ispacked child = true) :
    m842_copytopacked t dst src zero zero =
      .ok (memcpyValue dst src (zero + zero) (zero + JInt.lit .i64 off) child.alignedSize) := by
  have hp : ¬ (t.primitive = true) := by simp [hprim]
  rw [m842_copytopacked.eq_def, ite_eq_right hp, hfields, attach_singleton]
  dsimp only
  rw [forIn_singleton_ok _ _
    (memcpyValue dst src (zero + zero) (zero + JInt.lit .i64 off) child.alignedSize, zero + child.alignedSize) _
    (by dsimp only; rw [ite_eq_left hisp]; rfl)]
  rfl

theorem copyfrompacked_single_packed_field (t : TypeLayout) (off : Nat) (child : TypeLayout)
    (dst src : Bytes) (hprim : t.primitive = false)
    (hfields : t.fields = [(off, child)]) (hisp : m824_ispacked child = true) :
    m862_copyfrompacked t dst src zero zero =
      .ok (memcpyValue dst src (zero + JInt.lit .i64 off) (zero + zero) child.alignedSize) := by
  have hp : ¬ (t.primitive = true) := by simp [hprim]
  rw [m862_copyfrompacked.eq_def, ite_eq_right hp, hfields, attach_singleton]
  dsimp only
  rw [forIn_singleton_ok _ _
    (memcpyValue dst src (zero + JInt.lit .i64 off) (zero + zero) child.alignedSize, zero + child.alignedSize) _
    (by dsimp only; rw [ite_eq_left hisp]; rfl)]
  rfl

theorem reinterpretPadding_unpack (out inp : TypeLayout) (bytes initial : Bytes) (ps : Nat)
    (hps : m816_packedsize inp = .ok ps)
    (hfin : inp.fields = []) (hfout : 0 < out.fields.length) (hisp : m824_ispacked inp = true) :
    m913_reinterpretPadding out inp bytes initial = m862_copyfrompacked out initial bytes zero zero := by
  unfold m913_reinterpretPadding
  simp [hps, hfin, hfout, hisp]

/-- `_copytopacked!` and `_copyfrompacked!` copy primitive bytes and recursively pack/unpack
composite fields at their byte offsets while preserving untouched padding bytes in the destination,
and `_reinterpret` / `_reinterpret_padding` round-trip packed and padded representations. -/
def ReinterpretPackedCopies : Prop :=
  (∀ (id n : Nat) (dst src : Bytes),
    (n : Int) ≤ IntTy.max .i64 → src.length = n → dst.length = n →
    m842_copytopacked (primitiveLayout id n) dst src zero zero = .ok src ∧
    m862_copyfrompacked (primitiveLayout id n) dst src zero zero = .ok src ∧
    m882_reinterpret (primitiveLayout (id + 1) n) (primitiveLayout id n) src dst = .ok src) ∧
  (∀ (id off n aligned : Nat) (dst src : Bytes),
    off + n ≤ aligned → (aligned : Int) ≤ IntTy.max .i64 →
    src.length = aligned → dst.length = aligned →
    m842_copytopacked (singleFieldPaddedLayout id off n aligned) (List.replicate n 0) src zero zero =
      .ok (byteWindow src off n) ∧
    m862_copyfrompacked (singleFieldPaddedLayout id off n aligned) dst (byteWindow src off n) zero zero =
      .ok (overwriteBytes dst off (byteWindow src off n)) ∧
    m913_reinterpretPadding (singleFieldPaddedLayout id off n aligned) (primitiveLayout (id + 2) n)
      (byteWindow src off n) dst =
      .ok (overwriteBytes dst off (byteWindow src off n)))



/-- `String(v)` returns `""` on any zero-length view without checking readability (even when `v`
is unreadable), rejects non-empty unreadable views with `PaddingError`, and invokes
`jl_pchar_to_string` on non-empty readable views. -/
def ReinterpretStringConversion : Prop :=
  (∀ {T S A R : Type} (length : ReinterpretArray T S A → I64)
      (emptyString : R) (callString : ReinterpretArray T S A → I64 → RResult R)
      (a : ReinterpretArray T S A),
    (length a = zero → m937_string length emptyString callString a = .ok emptyString) ∧
    (length a ≠ zero → a.readable = false → m772_arraySubpadding a.target a.source = .ok false →
      m937_string length emptyString callString a = .error .padding) ∧
    (length a ≠ zero → a.readable = true →
      m937_string length emptyString callString a = callString a (length a)))

theorem reinterpretStringConversion : ReinterpretStringConversion := by
  intro T S A R length emptyString callString a
  refine ⟨?_, ?_, ?_⟩
  · intro hlen; simp [m937_string, hlen]
  · intro hlen hr hsub
    have hlen_val : (length a).val ≠ zero.val := fun he => hlen (jint_eq_of_val he)
    simp [m937_string, hlen_val, m237_checkReadable, hr, hsub]
  · intro hlen hr
    have hlen_val : (length a).val ≠ zero.val := fun he => hlen (jint_eq_of_val he)
    simp [m937_string, hlen_val, m237_checkReadable, hr]
/-! ## Entry 6: `_mapreduce` and `mapreduce_impl` in-bounds sequential and pairwise execution (`946`, `956`, `984`) -/

/-- `_mapreduce` delegates empty outer ranges (`size(inds)[2] == 0`) to `mapreduce_empty_iter`
without reading elements, and on non-empty ranges calls `mapreduce_impl` from `first(inds)` to
`last(inds)`; `mapreduce_impl` visits only indices in `[1, K] × [ifirst.j, ilast.j]` in both its
sequential column loop and its recursive pairwise column split `jmid = ifirst.j + ((ilast.j - ifirst.j) >> 1)`. -/
def ReinterpretMapreduceInBounds : Prop :=
  (∀ {A F OP X V E : Type} {K : Nat}
      (iteratorEltype : A → E) (empty : F → OP → A → E → RResult V)
      (blocksize : F → OP → I64) (get : A → SCartesianIndex2 → RResult X)
      (map : F → X → RResult V) (combine : OP → V → V → RResult V)
      (f : F) (op : OP) (style : IndexStyleModel) (a : A) (f2 : I64),
    m946_mapreduce (K := K) (fun _ _ => .ok ⟨⟨f2, zero⟩⟩) iteratorEltype empty blocksize get map combine f op style a =
      some (empty f op a (iteratorEltype a))) ∧
  (∀ {A F OP X V : Type}
      (get : A → SCartesianIndex2 → RResult X)
      (map : F → X → RResult V) (combine : OP → V → V → RResult V)
      (a : A) (f : F) (op : OP) (j : I64) (x1 x2 : X) (v1 v2 v : V),
    j.val < IntTy.max .i64 →
    get a ⟨one, j⟩ = .ok x1 →
    get a ⟨JInt.lit .i64 2, j⟩ = .ok x2 →
    map f x1 = .ok v1 →
    map f x2 = .ok v2 →
    combine op v1 v2 = .ok v →
    m956_mapreduceImpl (K := 2) get map combine a f op ⟨one, j⟩ ⟨JInt.lit .i64 2, j⟩ one =
      some (.ok v)) ∧
  (∀ {A F OP X V : Type}
      (get : A → SCartesianIndex2 → RResult X)
      (map : F → X → RResult V) (combine : OP → V → V → RResult V)
      (a : A) (f : F) (op : OP) (x11 x21 x12 x22 : X) (v11 v21 v12 v22 vL vR v : V),
    get a ⟨one, one⟩ = .ok x11 →
    get a ⟨JInt.lit .i64 2, one⟩ = .ok x21 →
    get a ⟨one, JInt.lit .i64 2⟩ = .ok x12 →
    get a ⟨JInt.lit .i64 2, JInt.lit .i64 2⟩ = .ok x22 →
    map f x11 = .ok v11 → map f x21 = .ok v21 →
    map f x12 = .ok v12 → map f x22 = .ok v22 →
    combine op v11 v21 = .ok vL →
    combine op v12 v22 = .ok vR →
    combine op vL vR = .ok v →
    m984_mapreduceDefault (K := 2) (fun _ _ => one) get map combine a f op
        ⟨one, one⟩ ⟨JInt.lit .i64 2, JInt.lit .i64 2⟩ =
      some (.ok v))

theorem mapreduce_col_one {A F OP X V : Type}
    (get : A → SCartesianIndex2 → RResult X)
    (map : F → X → RResult V) (combine : OP → V → V → RResult V)
    (a : A) (f : F) (op : OP) (j : I64) (x1 x2 : X) (v1 v2 v : V)
    (hj : j.val < IntTy.max .i64)
    (hx1 : get a ⟨one, j⟩ = .ok x1) (hx2 : get a ⟨JInt.lit .i64 2, j⟩ = .ok x2)
    (hm1 : map f x1 = .ok v1) (hm2 : map f x2 = .ok v2) (hc : combine op v1 v2 = .ok v) :
    m956_mapreduceImpl (K := 2) get map combine a f op ⟨one, j⟩ ⟨JInt.lit .i64 2, j⟩ one =
      some (.ok v) := by
  rw [m956_mapreduceImpl.eq_def]
  have hsub0 : j - j = zero := by
    apply jint_eq_of_val
    rw [val_sub, Int.sub_self]; rfl
  have hlt : j - j < one := by rw [hsub0]; decide
  have hr1 : intRange (one + JInt.lit .i64 2) (JInt.lit .i64 (2 : Nat)) = [] := by decide
  have hr2 : intRange (j + one) j = [] := by
    unfold intRange
    have : (j.val - (j + one).val + 1).toNat = 0 := by
      rw [val_add, one_val]
      have hw : wrapInt .i64 (j.val + 1) = j.val + 1 :=
        wrapInt_of_inRange .i64 (j.val + 1) ⟨by have := j.property.1; omega, by omega⟩
      rw [hw]; omega
    rw [this]; rfl
  simp only [hlt, ↓reduceIte, hx1, hx2, hm1, hm2, hc, hr1, hr2, resultBindOk, resultPure, forIn_nil]
  rfl

theorem reinterpretMapreduceInBounds : ReinterpretMapreduceInBounds := by
  refine ⟨?_, mapreduce_col_one, ?_⟩
  · intro A F OP X V E K iteratorEltype empty blocksize get map combine f op style a f2
    simp [m946_mapreduce, m298_indicesSize]
  · intro A F OP X V get map combine a f op x11 x21 x12 x22 v11 v21 v12 v22 vL vR v
      hx11 hx21 hx12 hx22 hm11 hm21 hm12 hm22 hcL hcR hc
    unfold m984_mapreduceDefault
    rw [m956_mapreduceImpl.eq_def]
    have hnlt : ¬ (JInt.lit .i64 2 - one < one) := by decide
    have hmid : one + JuliaLean.base.int.ashr_int (JInt.lit .i64 2 - one) one = one := by decide
    have hmid1 : one + one = JInt.lit .i64 2 := by decide
    have h2nat : JInt.lit .i64 (2 : Nat) = JInt.lit .i64 2 := rfl
    have hL := mapreduce_col_one get map combine a f op one x11 x21 v11 v21 vL (by decide) hx11 hx21 hm11 hm21 hcL
    have hR := mapreduce_col_one get map combine a f op (JInt.lit .i64 2) x12 x22 v12 v22 vR (by decide) hx12 hx22 hm12 hm22 hcR
    simp only [hnlt, ↓reduceIte, hmid, h2nat, hL, Option.bind_eq_bind, Option.bind_some, hmid1, hR,
      resultBindOk, hc]
    rfl

/-! ## Entry 20: `_totuple` fast reinterpret path and `Iterators.take` fallback (`990`) -/

/-- `_totuple` rejects inputs shorter than `N + 32`, constructs `Iterators.Take(itr, N + 32)` on
the non-bits/type-mismatch fallback path, and on matching `isbits` element types reinterprets the
`1:(N + 32)` prefix view as a single tuple element at index `1`. -/
def ReinterpretToTupleCorrect : Prop :=
  (∀ {A R X : Type} (arrayLength : ArrayInput A → I64)
      (totupleError : TypeLayout → RResult R) (eltypeMatches : ArrayInput A → TypeLayout → Bool)
      (viewPrefix : ArrayInput A → I64 → RResult (ArrayInput A))
      (ops : PointerReadOps R X (ArrayInput A))
      (checkParent : ArrayInput A → Bool) (parentIndexStyle : ArrayInput A → IndexStyleModel)
      (firstindex : ReinterpretArray R X (ArrayInput A) → I64)
      (checkbounds : ReinterpretArray R X (ArrayInput A) → I64 → List I64 → RResult Unit)
      (getParent : ArrayInput A → List I64 → RResult Bytes)
      (toSubscripts : ReinterpretArray R X (ArrayInput A) → I64 → List I64)
      (tupleFromBytes : Bytes → RResult R)
      (collectTuple : TypeLayout → JuliaLean.base.iterators.Take (ArrayInput A) → RResult R)
      (tupleType elementType : TypeLayout) (n : I64) (itr : ArrayInput A),
    (arrayLength itr < n + JInt.lit .i64 32 →
      m990_totuple arrayLength totupleError eltypeMatches viewPrefix ops checkParent
        parentIndexStyle firstindex checkbounds getParent toSubscripts tupleFromBytes
        collectTuple tupleType elementType n itr = totupleError tupleType) ∧
    (¬ (arrayLength itr < n + JInt.lit .i64 32) →
      0 ≤ (n + JInt.lit .i64 32).val →
      eltypeMatches itr elementType = false →
      m990_totuple arrayLength totupleError eltypeMatches viewPrefix ops checkParent
        parentIndexStyle firstindex checkbounds getParent toSubscripts tupleFromBytes
        collectTuple tupleType elementType n itr =
        collectTuple elementType ⟨itr, n + JInt.lit .i64 32⟩)) ∧
  (∀ {A R X : Type} (p : A)
      (totupleError : TypeLayout → RResult R)
      (viewPrefix : ArrayInput A → I64 → RResult (ArrayInput A))
      (ops : PointerReadOps R X (ArrayInput A))
      (firstindex : ReinterpretArray R X (ArrayInput A) → I64)
      (getParent : ArrayInput A → List I64 → RResult Bytes)
      (toSubscripts : ReinterpretArray R X (ArrayInput A) → I64 → List I64)
      (tupleFromBytes : Bytes → RResult R)
      (collectTuple : TypeLayout → JuliaLean.base.iterators.Take (ArrayInput A) → RResult R),
    let itr : ArrayInput A := ⟨p, 1, [JInt.lit .i64 32], [⟨one, JInt.lit .i64 32⟩]⟩
    let elemLayout := primitiveLayout 1 1
    let tupLayout := primitiveLayout 2 32
    let view : ReinterpretArray R X (ArrayInput A) := ⟨itr, 1, tupLayout, elemLayout, true, true, false⟩
    m990_totuple (fun x => x.size.headD zero) totupleError (fun _ _ => true) viewPrefix ops
      (fun _ => false) (fun _ => .linear) firstindex (fun _ _ _ => .ok ()) getParent
      toSubscripts tupleFromBytes collectTuple tupLayout elemLayout zero itr =
      (m473_getindexNonReshaped (fun _ _ _ => .ok ()) getParent view one [] >>= tupleFromBytes))

theorem reinterpretToTupleCorrect : ReinterpretToTupleCorrect := by
  refine ⟨?_, ?_⟩
  · intro A R X arrayLength totupleError eltypeMatches viewPrefix ops checkParent
      parentIndexStyle firstindex checkbounds getParent toSubscripts tupleFromBytes
      collectTuple tupleType elementType n itr
    constructor
    · intro hlt
      simp [m990_totuple, hlt]
    · intro hnlt hnonneg hmatch
      have hnot_neg : ¬ ((n + JInt.lit .i64 32).val < 0) := by omega
      have hconv : JuliaLean.base.int.convert .i64 (n + JInt.lit .i64 32) =
          .ok (n + JInt.lit .i64 32) := by
        simp [JuliaLean.base.int.convert, JInt.convert, (n + JInt.lit .i64 32).property]
      have hcompare : JuliaLean.base.int.lt (n + JInt.lit .i64 32) (JInt.lit .i64 0) = false := by
        rw [JuliaLean.Proofs.base.int.lt_eq]
        change decide ((n + JInt.lit .i64 32).val < 0) = false
        simp [hnot_neg]
      have htake : JuliaLean.base.iterators.takeModel (JuliaLean.base.int.convert .i64)
          (JuliaLean.base.iterators.mkTake
            (fun n => pure (JuliaLean.base.int.lt n (JInt.lit .i64 0)))
            (JuliaLean.base.int.convert .i64) (fun message => .error (.argumentError message)))
          itr (n + JInt.lit .i64 32) = .ok ⟨itr, n + JInt.lit .i64 32⟩ := by
        simp [JuliaLean.base.iterators.takeModel, JuliaLean.base.iterators.mkTake,
          hconv, hcompare, bind, Except.bind, pure, Except.pure]
      simp [m990_totuple, hnlt, hmatch, htake]
  · intro A R X p totupleError viewPrefix ops firstindex getParent toSubscripts tupleFromBytes collectTuple
    dsimp only
    have hadd : zero + JInt.lit .i64 32 = JInt.lit .i64 32 := by decide
    have hnlt : ¬ (JInt.lit .i64 32 < JInt.lit .i64 32) := by decide
    have h73 : m73_reinterpret (T := R) (S := X) (primitiveLayout 2 32) (primitiveLayout 1 1)
        ⟨p, 1, [JInt.lit .i64 32], [⟨one, JInt.lit .i64 32⟩]⟩ =
        .ok ⟨⟨p, 1, [JInt.lit .i64 32], [⟨one, JInt.lit .i64 32⟩]⟩, 1,
          primitiveLayout 2 32, primitiveLayout 1 1, true, true, false⟩ := by
      unfold m73_reinterpret
      simp only [hasBitPadding_primitiveLayout]
      rfl
    have hbits1 : (primitiveLayout 1 1).isBits = true := rfl
    unfold m990_totuple
    simp only [hadd, List.headD_cons, hnlt, ↓reduceIte, hbits1, Bool.and_self,
      beq_self_eq_true, resultPure, resultBindOk, h73]
    unfold m442_getindexLinear m237_checkReadable m421_checkPtrIndexable m263_indexStyle
    have hneq_sz : ((primitiveLayout 2 32).alignedSize == (primitiveLayout 1 1).alignedSize) = false := by decide
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, resultPure, resultBindOk,
      hneq_sz, beq_self_eq_true, List.isEmpty_cons, List.headD_cons, List.drop_succ_cons, List.drop_zero]
/-- Readability and writability checks reject incompatible padding layouts with `.padding`, and
`showerror` formats the incompatible source and target layouts. -/
def ReinterpretPaddingErrorDisplay : Prop :=
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    a.readable = false → m772_arraySubpadding a.target a.source = .ok false →
      m237_checkReadable a = .error .padding) ∧
  (∀ {T S A : Type} (a : ReinterpretArray T S A),
    a.writable = false → m772_arraySubpadding a.source a.target = .ok false →
      m244_checkWritable a = .error .padding) ∧
  (∀ (source target : String),
    m741_showerror ⟨source, target⟩ =
      "Padding of type " ++ source ++ " is not compatible with type " ++ target ++ "." ∧
    (m741_showerror ⟨source, target⟩).toList.length =
      46 + source.toList.length + target.toList.length)

theorem reinterpretPaddingErrorDisplay : ReinterpretPaddingErrorDisplay := by
  refine ⟨?_, ?_, ?_⟩
  · intro T S A a hr hsub
    simp [m237_checkReadable, hr, hsub]
  · intro T S A a hw hsub
    simp [m244_checkWritable, hw, hsub]
  · intro source target
    refine ⟨rfl, ?_⟩
    simp [m741_showerror, String.toList_append, List.length_append]
    omega
namespace Strict

inductive StorageLeaf : TypeLayout → Nat → TypeLayout → Prop where
  | primitive (t : TypeLayout) (h : t.primitive = true) : StorageLeaf t 0 t
  | field (t child leaf : TypeLayout) (off inner : Nat)
      (hp : t.primitive = false) (hu : t.union = false)
      (hm : (off, child) ∈ t.fields) (hc : StorageLeaf child inner leaf) :
      StorageLeaf t (off + inner) leaf
  | member (t child leaf : TypeLayout) (inner : Nat)
      (hp : t.primitive = false) (hu : t.union = true)
      (hm : child ∈ t.members) (hc : StorageLeaf child inner leaf) :
      StorageLeaf t inner leaf

def ValueByte (t : TypeLayout) (b : Nat) : Prop :=
  ∃ off leaf, StorageLeaf t off leaf ∧ off ≤ b ∧ b < off + (leaf.bits + 7) / 8

def BitPadded (t : TypeLayout) : Prop :=
  ∃ off leaf, StorageLeaf t off leaf ∧ leaf.bits % 8 ≠ 0

/-- Runtime layout invariants, independent of the functions under review. -/
structure ValidStorageLayout (t : TypeLayout) : Prop where
  nonnegative : 0 ≤ t.alignedSize.val
  noUnion : t.isBits = true → t.union = false
  leavesFit : ∀ off leaf, StorageLeaf t off leaf →
    off + (leaf.bits + 7) / 8 ≤ t.alignedSize.val.toNat
  paddingMetadata : t.datatypePadding = false ↔
    ∀ b < t.alignedSize.val.toNat, ValueByte t b
  singletonMetadata : t.singleton = true ↔ t.alignedSize.val = 0

noncomputable def payload (t : TypeLayout) (bytes : Bytes) : Bytes := by
  classical
  exact ((List.range t.alignedSize.val.toNat).filter (ValueByte t)).map (bytes.getD · 0)

def PaddingCompatible (readType storedType : TypeLayout) : Prop :=
  (∀ b < storedType.alignedSize.val.toNat, ValueByte storedType b) ∨
  (0 < readType.alignedSize.val ∧ 0 < storedType.alignedSize.val ∧
    ∀ n : Nat, ValueByte readType (n % readType.alignedSize.val.toNat) →
      ValueByte storedType (n % storedType.alignedSize.val.toNat))

def ShapeValid {A : Type} (p : ArrayInput A) : Prop :=
  p.axes.length = p.rank ∧ p.size = p.axes.map Axis.length ∧
    ∀ ax ∈ p.axes, 0 ≤ ax.length.val

def coordinateOffset : List Axis → List I64 → Option Nat
  | [], [] => some 0
  | ax :: axs, i :: inds =>
    if ax.first.val ≤ i.val ∧ i.val < ax.first.val + ax.length.val then
      (coordinateOffset axs inds).map (fun n => (i.val - ax.first.val).toNat + ax.length.val.toNat * n)
    else none
  | _, _ => none

/-- The manual's dimensions; no call to size/axes or a reinterpretation constructor. -/
def viewAxes (reshape : Bool) (t s : TypeLayout) (axs : List Axis) : List Axis :=
  if reshape then
    if s.alignedSize.val > t.alignedSize.val then
      ⟨one, JInt.lit .i64 (s.alignedSize.val / t.alignedSize.val)⟩ :: axs
    else if s.alignedSize.val < t.alignedSize.val then axs.drop 1 else axs
  else match axs with
    | [] => []
    | ax :: tail =>
      ⟨ax.first, if t.singleton then ax.length else
        JInt.lit .i64 (ax.length.val * s.alignedSize.val / t.alignedSize.val)⟩ :: tail

/-- Storage layout of `NTuple{count,E}`: Julia repeats each element's aligned storage. -/
def tupleLayout (element : TypeLayout) (count : Nat) : TypeLayout :=
  .mk ⟨element.id + 1, count * element.bits,
    JInt.lit .i64 (count * element.alignedSize.val), element.isBits, false, false,
    element.singleton, element.datatypePadding⟩
    ((List.range count).map (fun i => (i * element.alignedSize.val.toNat, element))) []

def denseCoordinate (axs : List Axis) (inds : List I64) : Option Nat :=
  match inds with
  | [i] =>
    if axs.length = 1 then coordinateOffset axs inds else
      if 1 ≤ i.val ∧ i.val ≤ ((axs.map (fun a => a.length.val.toNat)).prod : Nat) then
        some (i.val - 1).toNat else none
  | _ => coordinateOffset axs inds

def denseGet (p : ArrayInput (List Bytes)) (inds : List I64) : RResult Bytes :=
  match denseCoordinate p.axes inds with
  | none => .error .bounds
  | some k => match p.parent[k]? with | none => .error .bounds | some b => .ok b


private def byteVectorCodec (size : I64) :
    JuliaLean.base.pointer.ByteCodec (Fin size.val.toNat → JuliaLean.base.pointer.Byte) := by
  have hbound : ((size.val.toNat : Nat) : Int) ≤ IntTy.max .i64 := by
    have h := size.property.2
    have hm : (0 : Int) ≤ IntTy.max .i64 := by decide
    omega
  refine {
    elementSize := JInt.lit .i64 size.val.toNat
    size_nonnegative := ?_
    encode := List.ofFn
    decode := fun bytes i => bytes.getD i.val (JInt.lit .u8 0)
    encode_length := ?_
    decode_encode := ?_
  }
  · rw [lit_nat size.val.toNat hbound]
    omega
  · intro value
    simp only [List.length_ofFn, lit_nat size.val.toNat hbound, Int.toNat_natCast]
  · intro value
    funext i
    have hi : (i.val : Int) < size.val := by have h := i.isLt; omega
    simp [List.getD_eq_getElem?_getD, hi]

def denseReadPointer (element target : TypeLayout) :
    PointerReadOps Bytes Bytes (ArrayInput (List Bytes)) where
  checkbounds := fun a inds =>
    if (denseCoordinate (viewAxes a.reshaped a.target a.source a.parent.axes) inds).isSome then
      .ok () else .error .bounds
  linearIndex := fun a inds => JInt.lit .i64
    (((denseCoordinate (viewAxes a.reshaped a.target a.source a.parent.axes) inds).getD 0 : Nat) + 1)
  parentCconvert := fun _ _ => 0
  unsafeConvert := fun _ p => p
  parentElsize := fun _ => element.alignedSize
  firstindex := fun _ => one
  addPointer := fun p offset => p + offset.val.toNat
  Element := Fin target.alignedSize.val.toNat → JuliaLean.base.pointer.Byte
  codec := byteVectorCodec target.alignedSize
  heap := fun a => {
    byteAt := fun address => JInt.lit .u8 (a.parent.flatten.getD address 0).toNat
    validByte := fun address => decide (address < a.parent.flatten.length)
  }

def tupleRun (element : TypeLayout) (n : I64) (p : ArrayInput (List Bytes)) : RResult Bytes :=
  let tuple := tupleLayout element (n.val.toNat + 32)
  m990_totuple (fun a => JInt.lit .i64 a.parent.length) (fun _ => .error .argument)
    (fun _ _ => true)
    (fun a count => .ok ⟨a.parent.take count.val.toNat, 1, [count], [⟨one, count⟩]⟩)
    (denseReadPointer element tuple) m427_checkPtrDense (fun _ => .linear)
    (fun _ => one)
    (fun a i tail =>
      if (denseCoordinate (viewAxes a.reshaped a.target a.source a.parent.axes) (i :: tail)).isSome
      then .ok () else .error .bounds)
    denseGet (fun _ i => [i]) (fun bytes => .ok bytes)
    (fun _ taken => .ok ((taken.xs.parent.take taken.n.val.toNat).flatten)) tuple element n p

/-- Tuple construction returns the first N+32 iterated elements independently of the input's
rank and shape, including the matching-isbits fast path and the collection fallback. -/
def FullTuplePrefix : Prop :=
  ∀ element n p, ValidStorageLayout element → ¬ BitPadded element →
    ShapeValid p → WellFormed element.alignedSize.val.toNat p.parent →
    p.parent.length = (p.size.map (fun d => d.val.toNat)).prod →
    (∀ ax ∈ p.axes, ax.first = one) →
    0 ≤ n.val → n.val + 32 ≤ IntTy.max .i64 →
    ((p.parent.length : Nat) : Int) ≤ IntTy.max .i64 →
    if p.parent.length < n.val.toNat + 32 then tupleRun element n p = .error .argument else
      ∃ result, tupleRun element n p = .ok result ∧
        result.length = (n.val.toNat + 32) * element.alignedSize.val.toNat ∧
        payload (tupleLayout element (n.val.toNat + 32)) result =
          payload (tupleLayout element (n.val.toNat + 32))
            ((p.parent.take (n.val.toNat + 32)).flatten)

private def byteElement : TypeLayout := primitiveLayout 1 1
private def matrix32 : ArrayInput (List Bytes) :=
  ⟨List.replicate 32 [0], 2, [JInt.lit .i64 4, JInt.lit .i64 8],
    [⟨one, JInt.lit .i64 4⟩, ⟨one, JInt.lit .i64 8⟩]⟩

private theorem matrix32_fails : tupleRun byteElement zero matrix32 = .error .argument := by
  have hp : m828_hasBitPadding (tupleLayout byteElement 32) = false := by
    rw [m828_hasBitPadding.eq_def]
    simp only [show (tupleLayout byteElement 32).primitive = false from rfl,
      show (tupleLayout byteElement 32).union = false from rfl,
      Bool.false_eq_true, ↓reduceIte]
    apply List.any_eq_false.mpr
    intro field _
    have hm : field.val ∈ (List.range 32).map
        (fun i => (i * byteElement.alignedSize.val.toNat, byteElement)) := field.property
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hm
    have he : field.val.2 = byteElement := (congrArg Prod.snd hi).symm
    rw [he]
    rw [show m828_hasBitPadding byteElement = false from hasBitPadding_primitiveLayout _ _]
    decide
  have hs : m828_hasBitPadding byteElement = false := hasBitPadding_primitiveLayout _ _
  have h73 : m73_reinterpret (T := Bytes) (S := Bytes)
      (tupleLayout byteElement 32) byteElement matrix32 = .error .argument := by
    unfold m73_reinterpret
    simp only [show (tupleLayout byteElement 32).isBits = true from rfl,
      show byteElement.isBits = true from rfl, Bool.not_true, Bool.false_eq_true,
      ite_eq_right, hp, hs]
    rfl
  unfold tupleRun m990_totuple
  simp only [show zero + JInt.lit .i64 32 = JInt.lit .i64 32 by decide,
    show zero.val.toNat + 32 = 32 by decide,
    show JInt.lit .i64 matrix32.parent.length = JInt.lit .i64 32 from rfl,
    show ¬ (JInt.lit .i64 32 < JInt.lit .i64 32) by decide,
    show byteElement.isBits = true from rfl, Bool.true_and, beq_self_eq_true,
    ite_eq_right, ite_eq_left, resultPure, resultBindOk, h73, resultBindError]
  simp

private theorem byteElement_valid : ValidStorageLayout byteElement := by
  constructor
  · decide
  · intro _; rfl
  · intro off leaf hl
    cases hl with
    | primitive t hp => decide
    | field t child leaf off inner hp hu hm hc => cases hp
    | member t child leaf inner hp hu hm hc => cases hp
  · constructor
    · intro _ b hb
      have hb0 : b = 0 := by change b < 1 at hb; omega
      subst b
      exact ⟨0, byteElement, StorageLeaf.primitive _ rfl, Nat.le_refl 0, by decide⟩
    · intro _; rfl
  · decide

private theorem byteElement_aligned : ¬ BitPadded byteElement := by
  rintro ⟨off, leaf, hl, hbad⟩
  cases hl with
  | primitive t hp => exact hbad (by decide)
  | field t child leaf off inner hp hu hm hc => cases hp
  | member t child leaf inner hp hu hm hc => cases hp
/-- A 4×8 byte matrix contains all 32 requested elements, but the fast path rejects its
first dimension before reading any of them, as in `repro/reinterpretarray-totuple.jl`. -/
theorem fullTuplePrefix_refuted : ¬ FullTuplePrefix := by
  intro h
  have hw : WellFormed byteElement.alignedSize.val.toNat matrix32.parent := by
    intro bytes hb
    have he : bytes = [0] := List.eq_of_mem_replicate hb
    subst bytes
    rfl
  have hs : ShapeValid matrix32 := by
    unfold ShapeValid matrix32
    decide
  have hp := h byteElement zero matrix32 byteElement_valid byteElement_aligned hs hw
    (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [show ¬ (matrix32.parent.length < zero.val.toNat + 32) by decide,
    ↓reduceIte] at hp
  obtain ⟨result, hr, _⟩ := hp
  rw [matrix32_fails] at hr
  cases hr





/-- A byte-stride list is exactly representable in elements precisely when every mathematical
remainder is zero. Division failures are reported before integrality is tested. -/
def FullCheckedStrides : Prop :=
  ∀ (strides : List I64) (e : I64),
    if e.val = 0 ∨ (e.val = -1 ∧ ∃ s ∈ strides, s.val = IntTy.min .i64) then
      m225_checkedStrides divremInt (· == zero) strides e =
        (if strides = [] then .ok [] else .error .divide)
    else if ∀ s ∈ strides, e.val ∣ s.val then
      m225_checkedStrides divremInt (· == zero) strides e =
        .ok (strides.map (fun s => JInt.wrap .i64 (s.val.tdiv e.val)))
    else m225_checkedStrides divremInt (· == zero) strides e = .error .nonIntegralStride

private theorem divrem_value (s e : I64) (h0 : e.val ≠ 0)
    (h1 : ¬ (s.val = IntTy.min .i64 ∧ e.val = -1)) :
    divremInt s e = .ok (JInt.wrap .i64 (s.val.tdiv e.val), JInt.wrap .i64 (s.val.tmod e.val)) := by
  simp [divremInt, divInt, remInt, JInt.div, JInt.remInt, h0, h1, IntTy.signed,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem tmod_wrap_zero (s e : I64) :
    (JInt.wrap .i64 (s.val.tmod e.val) == zero) = decide (e.val ∣ s.val) := by
  rw [beq_iff_val, val_wrap,
    wrapInt_of_inRange .i64 _ (JuliaLean.Proofs.base.int.tmod_fits s e), zero_val]
  simp only [← Int.dvd_iff_tmod_eq_zero]

private theorem mapM_divrem_value (strides : List I64) (e : I64)
    (h0 : e.val ≠ 0) (h1 : ∀ s ∈ strides, ¬ (s.val = IntTy.min .i64 ∧ e.val = -1)) :
    strides.mapM (fun s => divremInt s e) = .ok
      (strides.map (fun s => (JInt.wrap .i64 (s.val.tdiv e.val), JInt.wrap .i64 (s.val.tmod e.val)))) := by
  induction strides with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.mapM_cons, divrem_value s e h0 (h1 s (by simp)),
      ih (fun x hx => h1 x (by simp [hx])), List.map_cons]
    rfl

private theorem mapM_divrem_failure (strides : List I64) (e : I64)
    (hne : strides ≠ [])
    (h : e.val = 0 ∨ (e.val = -1 ∧ ∃ s ∈ strides, s.val = IntTy.min .i64)) :
    strides.mapM (fun s => divremInt s e) = .error .divide := by
  induction strides with
  | nil => exact False.elim (hne rfl)
  | cons s ss ih =>
    rcases h with h0 | ⟨hm, hmem⟩
    · simp [List.mapM_cons, divremInt, divInt, JInt.div, h0,
        Except.mapError, bind, Except.bind, pure, Except.pure]
    · rcases hmem with ⟨x, hx, hxval⟩
      by_cases hs : s.val = IntTy.min .i64
      · simp [List.mapM_cons, divremInt, divInt, JInt.div, hs, hm, IntTy.signed,
          Except.mapError, bind, Except.bind, pure, Except.pure]
      · have hxss : x ∈ ss := by
          rcases List.mem_cons.mp hx with h | h
          · subst x; exact False.elim (hs hxval)
          · exact h
        have hssne : ss ≠ [] := by intro he; simp [he] at hxss
        have htail := ih hssne (Or.inr ⟨hm, x, hxss, hxval⟩)
        rw [List.mapM_cons, divrem_value s e (by omega) (by simp [hs]), htail]
        rfl

theorem fullCheckedStrides : FullCheckedStrides := by
  intro strides e
  by_cases hbad : e.val = 0 ∨ (e.val = -1 ∧ ∃ s ∈ strides, s.val = IntTy.min .i64)
  · rw [ite_eq_left hbad]
    by_cases hempty : strides = []
    · subst strides; rfl
    · rw [ite_eq_right hempty]
      unfold m225_checkedStrides
      rw [mapM_divrem_failure strides e hempty hbad]
      rfl
  · rw [ite_eq_right hbad]
    have h0 : e.val ≠ 0 := fun h => hbad (Or.inl h)
    have h1 : ∀ s ∈ strides, ¬ (s.val = IntTy.min .i64 ∧ e.val = -1) := by
      intro s hs h; exact hbad (Or.inr ⟨h.2, s, hs, h.1⟩)
    unfold m225_checkedStrides
    rw [mapM_divrem_value strides e h0 h1]
    simp only [resultBindOk, List.map_map, Function.comp_def, tmod_wrap_zero]
    have hall : (strides.map (fun s => decide (e.val ∣ s.val))).all id =
        decide (∀ s ∈ strides, e.val ∣ s.val) := by
      have hiff : ((strides.map (fun s => decide (e.val ∣ s.val))).all id = true) ↔
          (∀ s ∈ strides, e.val ∣ s.val) := by simp
      by_cases h : ∀ s ∈ strides, e.val ∣ s.val
      · rw [hiff.mpr h, decide_eq_true h]
      · have hf : (strides.map (fun s => decide (e.val ∣ s.val))).all id = false :=
          Bool.eq_false_iff.mpr (fun ht => h (hiff.mp ht))
        rw [hf, decide_eq_false h]
    rw [hall]
    split <;> simp_all


/-- The static channel count exactly covers one parent element. All parent styles,
including nested static styles that must become Cartesian, are included. -/
def FullIndexStyles : Prop :=
  ∀ {A : Type} (style : A → IndexStyleModel) (p : A) (t s : Nat),
    (t ∣ s ∨ s ≤ t) →
    (m263_indexStyle style p = .linear ↔ style p = .linear) ∧
    (m263_indexStyle style p = .cartesian ↔ style p ≠ .linear) ∧
    (if style p = .linear ∧ t < s then
      ∃ k, m266_indexStyleReshaped style p t s = .staticCartesian k ∧ k * t = s ∧
        m273_combineStyle (K := k) (.staticCartesian k) (.staticCartesian k) = .staticCartesian k
    else (m266_indexStyleReshaped style p t s = .linear ↔ style p = .linear) ∧
      (m266_indexStyleReshaped style p t s = .cartesian ↔ style p ≠ .linear))

theorem fullIndexStyles : FullIndexStyles := by
  intro A style p t s hdiv
  have h263 : (m263_indexStyle style p = .linear ↔ style p = .linear) ∧
      (m263_indexStyle style p = .cartesian ↔ style p ≠ .linear) := by
    cases hs : style p <;> simp [m263_indexStyle, hs]
  refine ⟨h263.1, h263.2, ?_⟩
  by_cases hstatic : style p = .linear ∧ t < s
  · rw [ite_eq_left hstatic]
    have hd : t ∣ s := hdiv.resolve_right (by omega)
    exact ⟨s / t, by simp [m266_indexStyleReshaped, hstatic.1, hstatic.2],
      Nat.div_mul_cancel hd, rfl⟩
  · rw [ite_eq_right hstatic]
    cases hs : style p with
    | linear =>
      have hnot : ¬ t < s := by simpa [hs] using hstatic
      simp [m266_indexStyleReshaped, hs, hnot]
    | cartesian => simp [m266_indexStyleReshaped, hs]
    | staticCartesian k => simp [m266_indexStyleReshaped, hs]

/-- All storage layouts with no padding, rather than only primitive layouts, preserve their
complete byte sequence under scalar reinterpretation and reinterpretation back. -/
def FullPackedRoundtrip : Prop :=
  ∀ (t s : TypeLayout) (bytes initial : Bytes),
    t.isBits = true → s.isBits = true →
    t.datatypePadding = false → s.datatypePadding = false →
    m828_hasBitPadding t = false → m828_hasBitPadding s = false →
    t.alignedSize = s.alignedSize → bytes.length = s.alignedSize.val.toNat →
    initial.length = t.alignedSize.val.toNat →
    m882_reinterpret t s bytes initial = .ok bytes ∧
    m882_reinterpret s t bytes (List.replicate s.alignedSize.val.toNat 0) = .ok bytes
theorem fullPackedRoundtrip : FullPackedRoundtrip := by
  intro t s bytes initial ht hs hpt hps hbpt hbps hsize hbytes hinitial
  have htbytes : bytes.length = t.alignedSize.val.toNat := by simpa [hsize] using hbytes
  have hpackedT : m824_ispacked t = true := by simp [m824_ispacked, hpt]
  have hpackedS : m824_ispacked s = true := by simp [m824_ispacked, hps]
  have hszT : m816_packedsize t = .ok t.alignedSize.val.toNat := by simp [m816_packedsize, hpt]
  have hszS : m816_packedsize s = .ok t.alignedSize.val.toNat := by simp [m816_packedsize, hps, hsize]
  constructor
  · rw [reinterpret_packed t s bytes initial _ ht hs hbpt hbps hszT hszS hpackedT hpackedS]
    unfold memcpyValue byteWindow
    rw [zero_val, Int.toNat_zero, List.drop_zero, List.take_of_length_le (by omega)]
    exact congrArg Except.ok (overwriteBytes_full _ _ (by omega))
  · have hszT' : m816_packedsize t = .ok s.alignedSize.val.toNat := by simpa [hsize] using hszT
    have hszS' : m816_packedsize s = .ok s.alignedSize.val.toNat := by simpa [hsize] using hszS
    rw [reinterpret_packed s t bytes _ _ hs ht hbps hbpt hszS' hszT' hpackedS hpackedT]
    unfold memcpyValue byteWindow
    rw [zero_val, Int.toNat_zero, List.drop_zero, List.take_of_length_le (by omega)]
    exact congrArg Except.ok (overwriteBytes_full _ _ (by simp [hbytes]))




/-- Bit padding is detected anywhere in a recursive field/union layout, with no restriction
to primitive or single-field types. -/
theorem hasBitPadding_correct (layout : TypeLayout) :
    m828_hasBitPadding layout = true ↔ BitPadded layout := by
  refine WellFounded.induction (C := fun t => m828_hasBitPadding t = true ↔ BitPadded t)
    (measure sizeOf).wf layout ?_
  intro t ih
  rw [m828_hasBitPadding.eq_def]
  by_cases hp : t.primitive = true
  · rw [ite_eq_left hp]
    constructor
    · intro hb
      exact ⟨0, t, StorageLeaf.primitive t hp, by simpa using hb⟩
    · rintro ⟨off, leaf, hl, hb⟩
      cases hl with
      | primitive _ _ => simpa using hb
      | field _ _ _ _ _ hpf _ _ _ => simp [hp] at hpf
      | member _ _ _ _ hpf _ _ _ => simp [hp] at hpf
  · rw [ite_eq_right hp]
    have hpf : t.primitive = false := Bool.eq_false_iff.mpr hp
    by_cases hu : t.union = true
    · rw [ite_eq_left hu]
      constructor
      · intro h
        obtain ⟨c, _, hc⟩ := List.any_eq_true.mp h
        have hlt : sizeOf c.val < sizeOf t := by
          rcases t with ⟨info, fields, members⟩
          have hm := List.sizeOf_lt_of_mem c.property
          simp [TypeLayout.members] at hm
          simp
          omega
        obtain ⟨off, leaf, hl, hb⟩ := (ih c.val hlt).mp hc
        exact ⟨off, leaf, StorageLeaf.member t c.val leaf off hpf hu c.property hl, hb⟩
      · rintro ⟨off, leaf, hl, hb⟩
        cases hl with
        | primitive _ hp' => exact False.elim (hp hp')
        | field _ _ _ _ _ _ hu' _ _ => simp [hu] at hu'
        | member _ child leaf inner _ _ hm hc =>
          apply List.any_eq_true.mpr
          refine ⟨⟨child, hm⟩, List.mem_attach _ _, ?_⟩
          apply (ih child ?_).mpr ⟨_, _, hc, hb⟩
          change sizeOf child < sizeOf t
          have hm' : sizeOf child < sizeOf t.members := List.sizeOf_lt_of_mem hm
          have ht : sizeOf t.members < sizeOf t := by cases t; simp [TypeLayout.members]; omega
          exact Nat.lt_trans hm' ht
    · rw [ite_eq_right hu]
      have huf : t.union = false := Bool.eq_false_iff.mpr hu
      constructor
      · intro h
        obtain ⟨c, _, hc⟩ := List.any_eq_true.mp h
        have hlt : sizeOf c.val.2 < sizeOf t := by
          rcases t with ⟨info, fields, members⟩
          have hm := List.sizeOf_lt_of_mem c.property
          have hc : sizeOf c.val.2 < sizeOf c.val := by
            rcases c with ⟨⟨off, child⟩, hm⟩; simp; omega
          simp [TypeLayout.fields] at hm
          simp
          omega
        obtain ⟨off, leaf, hl, hb⟩ := (ih c.val.2 hlt).mp hc
        exact ⟨c.val.1 + off, leaf,
          StorageLeaf.field t c.val.2 leaf c.val.1 off hpf huf c.property hl, hb⟩
      · rintro ⟨off, leaf, hl, hb⟩
        cases hl with
        | primitive _ hp' => exact False.elim (hp hp')
        | member _ _ _ _ _ hu' _ _ => exact False.elim (hu hu')
        | field _ child leaf off inner _ _ hm hc =>
          apply List.any_eq_true.mpr
          refine ⟨⟨(off, child), hm⟩, List.mem_attach _ _, ?_⟩
          apply (ih child ?_).mpr ⟨inner, leaf, hc, hb⟩
          change sizeOf child < sizeOf t
          have hm' : sizeOf (off, child) < sizeOf t.fields := List.sizeOf_lt_of_mem hm
          have hc' : sizeOf child < sizeOf (off, child) := by simp; omega
          have ht : sizeOf t.fields < sizeOf t := by cases t; simp [TypeLayout.fields]; omega
          exact Nat.lt_trans hc' (Nat.lt_trans hm' ht)

/-- Detect every non-byte-aligned primitive leaf at any depth of a field or union layout. -/
def BitPaddingDetection : Prop :=
  ∀ layout, m828_hasBitPadding layout = true ↔ BitPadded layout

theorem bitPaddingDetection : BitPaddingDetection := hasBitPadding_correct

def FullScalarApplicability : Prop :=
  FullPackedRoundtrip ∧
    ∀ t s, m469_scalarApplicable t s = true ↔
      t.primitive = true ∧ s.primitive = true ∧ t.bits = s.bits
theorem fullScalarApplicability : FullScalarApplicability := by
  refine ⟨fullPackedRoundtrip, ?_⟩
  intro t s
  simp [m469_scalarApplicable, and_assoc]




def PlainAdmissible {A : Type} (t s : TypeLayout) (p : ArrayInput A) : Prop :=
  t.isBits = true ∧ s.isBits = true ∧ ¬ BitPadded t ∧ ¬ BitPadded s ∧
  (p.rank = 0 → t.alignedSize.val = s.alignedSize.val) ∧
  (p.rank ≠ 0 → t.alignedSize.val ≠ s.alignedSize.val →
    let ax := p.axes.headD ⟨one, zero⟩
    ax.first.val = 1 ∧
      (if t.singleton then s.singleton = true else
        t.alignedSize.val ≠ 0 ∧ (ax.length.val * s.alignedSize.val) % t.alignedSize.val = 0))

def ReshapeAdmissible {A : Type} (t s : TypeLayout) (p : ArrayInput A) : Prop :=
  t.isBits = true ∧ s.isBits = true ∧ ¬ BitPadded t ∧ ¬ BitPadded s ∧
  (s.alignedSize.val > t.alignedSize.val →
    0 < t.alignedSize.val ∧ s.alignedSize.val % t.alignedSize.val = 0) ∧
  (s.alignedSize.val < t.alignedSize.val →
    0 < s.alignedSize.val ∧ t.alignedSize.val % s.alignedSize.val = 0 ∧
      0 < p.rank ∧ (p.axes.headD ⟨one, zero⟩).first.val = 1 ∧
      (p.axes.headD ⟨one, zero⟩).length.val = t.alignedSize.val / s.alignedSize.val)

def ConstructorResult {T S A : Type} (t s : TypeLayout) (p : ArrayInput A)
    (reshaped : Bool) (r : ReinterpretArray T S (ArrayInput A)) : Prop :=
  r.parent = p ∧ r.target = t ∧ r.source = s ∧ r.reshaped = reshaped ∧
  (r.readable = true ↔ PaddingCompatible t s) ∧
  (r.writable = true ↔ PaddingCompatible s t) ∧
  r.rank = (if reshaped then
    if s.alignedSize.val > t.alignedSize.val then p.rank + 1
    else if s.alignedSize.val < t.alignedSize.val then p.rank - 1 else p.rank
    else p.rank)

def FullConstructorValidation : Prop := by
  classical
  exact
    ∀ {T S A : Type} (t s : TypeLayout) (p : ArrayInput A),
      ValidStorageLayout t → ValidStorageLayout s → ShapeValid p →
      (if PlainAdmissible t s p then
        ∃ r : ReinterpretArray T S (ArrayInput A), m73_reinterpret t s p = .ok r ∧
          ConstructorResult t s p false r
      else m73_reinterpret (T := T) (S := S) t s p = .error .argument) ∧
      (if ReshapeAdmissible t s p then
        ∃ r : ReinterpretArray T S (ArrayInput A), m107_reinterpretReshape t s p = .ok r ∧
          m188_reinterpretReshape t s p = .ok r ∧ ConstructorResult t s p true r
      else m107_reinterpretReshape (T := T) (S := S) t s p = .error .argument ∧
        m188_reinterpretReshape (T := T) (S := S) t s p = .error .argument)
  

private def tripleBytes : TypeLayout :=
  .mk ⟨3, 24, JInt.lit .i64 3, true, false, false, false, false⟩
    [(0, byteElement), (1, byteElement), (2, byteElement)] []

private theorem primitiveSmall_valid (id n : Nat) (_hn : 0 < n)
    (hmax : (n : Int) ≤ IntTy.max .i64) : ValidStorageLayout (primitiveLayout id n) := by
  have hsize : (primitiveLayout id n).alignedSize.val = n := lit_nat n hmax
  constructor
  · rw [hsize]; omega
  · intro _; rfl
  · intro off leaf hl
    cases hl with
    | primitive _ _ => simp [primitiveLayout, sizedLayout, TypeLayout.bits, TypeLayout.info,
        TypeLayout.alignedSize, lit_nat n hmax]; omega
    | field _ _ _ _ _ hp _ _ _ => cases hp
    | member _ _ _ _ hp _ _ _ => cases hp
  · constructor
    · intro _ b hb
      refine ⟨0, primitiveLayout id n, StorageLeaf.primitive _ rfl, by omega, ?_⟩
      have hb' : b < n := by rw [hsize, Int.toNat_natCast] at hb; exact hb
      change b < 0 + (n * 8 + 7) / 8
      omega
    · intro _; rfl
  · change ((n == 0) = true ↔ (primitiveLayout id n).alignedSize.val = 0)
    rw [hsize]
    simp

private theorem tripleBytes_valid : ValidStorageLayout tripleBytes := by
  constructor
  · decide
  · intro _; rfl
  · intro off leaf hl
    cases hl with
    | primitive _ hp => cases hp
    | member _ _ _ _ _ hu _ _ => cases hu
    | field _ child leaf off inner _ _ hm hc =>
      have hm' : (off = 0 ∧ child = byteElement) ∨ (off = 1 ∧ child = byteElement) ∨
          (off = 2 ∧ child = byteElement) := by simpa [tripleBytes, TypeLayout.fields] using hm
      rcases hm' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        cases hc <;> simp_all [tripleBytes, byteElement, primitiveLayout, sizedLayout, TypeLayout.primitive,
          TypeLayout.info, TypeLayout.bits, TypeLayout.alignedSize] <;> decide
  · constructor
    · intro _ b hb
      have hb' : b = 0 ∨ b = 1 ∨ b = 2 := by change b < 3 at hb; omega
      rcases hb' with rfl | rfl | rfl
      · exact ⟨0, byteElement, StorageLeaf.field tripleBytes byteElement byteElement 0 0 rfl rfl
          (by simp [tripleBytes, TypeLayout.fields]) (StorageLeaf.primitive _ rfl), by decide, by decide⟩
      · exact ⟨1, byteElement, StorageLeaf.field tripleBytes byteElement byteElement 1 0 rfl rfl
          (by simp [tripleBytes, TypeLayout.fields]) (StorageLeaf.primitive _ rfl), by decide, by decide⟩
      · exact ⟨2, byteElement, StorageLeaf.field tripleBytes byteElement byteElement 2 0 rfl rfl
          (by simp [tripleBytes, TypeLayout.fields]) (StorageLeaf.primitive _ rfl), by decide, by decide⟩
    · intro _; rfl
  · decide

private theorem tripleBytes_noBitPadding : m828_hasBitPadding tripleBytes = false := by
  rw [m828_hasBitPadding.eq_def]
  change ([((0 : Nat), byteElement), (1, byteElement), (2, byteElement)]).attach.any
    (fun field => m828_hasBitPadding field.val.2) = false
  apply List.any_eq_false.mpr
  intro field _
  have hm : field.val ∈ [(0, byteElement), (1, byteElement), (2, byteElement)] := field.property
  have hc : field.val.2 = byteElement := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h <;> rw [h]
  rw [hc, show m828_hasBitPadding byteElement = false from hasBitPadding_primitiveLayout _ _]
  decide

private def tripleOverflow : ReinterpretArray Unit Unit (ArrayInput Unit) :=
  ⟨overflowInput, 1, tripleBytes, primitiveLayout 64 8, true, true, false⟩

private theorem tripleOverflow_constructed :
    m73_reinterpret tripleBytes (primitiveLayout 64 8) overflowInput = .ok tripleOverflow := by
  unfold m73_reinterpret
  rw [tripleBytes_noBitPadding, hasBitPadding_primitiveLayout]
  rfl

theorem fullConstructorValidation_refuted : ¬ FullConstructorValidation := by
  intro h
  have hp := h (T := Unit) (S := Unit) tripleBytes (primitiveLayout 64 8) overflowInput
    tripleBytes_valid (primitiveSmall_valid 64 8 (by decide) (by decide))
    (by refine ⟨by decide, by decide, ?_⟩; intro ax ha; simp [overflowInput] at ha; subst ax; decide)
  have hn : ¬ PlainAdmissible tripleBytes (primitiveLayout 64 8) overflowInput := by
    rintro ⟨_, _, _, _, _, hsize⟩
    have hbad := (hsize (by decide) (by decide)).2
    change (if false = true then _ else _) at hbad
    simp only [Bool.false_eq_true, ↓reduceIte] at hbad
    have hrem := hbad.2
    exact (by decide : ¬ ((overflowInput.axes.headD ⟨one, zero⟩).length.val *
      (primitiveLayout 64 8).alignedSize.val) % tripleBytes.alignedSize.val = 0) hrem
  rw [ite_eq_right hn] at hp
  have he := hp.1
  rw [tripleOverflow_constructed] at he
  cases he


/-- For every parent array implementation, a static Cartesian target slice can be written
and read back, without changing any disjoint parent value or target slice. Parent laws apply
to the parent's own API; they never mention reinterpretation. -/
def CartesianParentLens : Prop :=
  ∀ {T S A : Type} (parent : ParentOps A) (a : ReinterpretArray T S A)
      (bytes : Bytes) (i j : I64),
    a.readable = true → a.writable = true →
    0 < a.target.alignedSize.val →
    (∀ p inds value old, parent.get p inds = .ok old → value.length = old.length →
      ∃ p', parent.set p inds value = .ok p' ∧ parent.get p' inds = .ok value ∧
        ∀ other, other ≠ inds → parent.get p' other = parent.get p other) →
    ∀ old, parent.get a.parent [j] = .ok old →
    bytes.length = a.target.alignedSize.val.toNat →
    1 ≤ i.val →
    (i.val - 1).toNat * a.target.alignedSize.val.toNat + bytes.length ≤ old.length →
    (old.length : Int) ≤ IntTy.max .i64 →
    ∃ a', m598_setindexCartesian (fun _ v => .ok v) parent a bytes ⟨i, j⟩ = .ok a' ∧
      m454_getindexCartesian parent.get a' ⟨i, j⟩ = .ok bytes ∧
      (∀ j', j' ≠ j → parent.get a'.parent [j'] = parent.get a.parent [j']) ∧
      ∀ b < old.length, b < (i.val - 1).toNat * a.target.alignedSize.val.toNat ∨
        (i.val - 1).toNat * a.target.alignedSize.val.toNat + bytes.length ≤ b →
        ∀ new, parent.get a'.parent [j] = .ok new → new[b]? = old[b]?

theorem cartesianParentLens : CartesianParentLens := by
  intro T S A parent a bytes i j hr hw hT hparent old hget hv hi hbound hmax
  let k := (i.val - 1).toNat
  let n := a.target.alignedSize.val.toNat
  have ht : a.target.alignedSize.val = n := by dsimp [n]; omega
  have hk : i.val - 1 = k := by dsimp [k]; omega
  have hmul : ((i - one) * a.target.alignedSize).val.toNat = k * n := by
    rw [val_mul, val_sub, one_val, hk,
      wrapInt_nat k (by have h := i.property.2; dsimp [k]; omega), ht,
      ← Int.natCast_mul, wrapInt_nat _ (by have h := Nat.le_trans (Nat.le_add_right (k*n) bytes.length) hbound; omega),
      Int.toNat_natCast]
  have hlen : (overwriteBytes old (k*n) bytes).length = old.length :=
    overwriteBytes_length _ _ _ hbound
  obtain ⟨p', hset, hget', hothers⟩ := hparent a.parent [j]
    (overwriteBytes old (k*n) bytes) old hget hlen
  have hcopy : memcpyValue old bytes ((i - one) * a.target.alignedSize) zero a.target.alignedSize =
      overwriteBytes old (k*n) bytes := by
    unfold memcpyValue byteWindow
    rw [hmul, zero_val, Int.toNat_zero, List.drop_zero,
      List.take_of_length_le (Nat.le_of_eq hv)]
  refine ⟨{ a with parent := p' }, ?_, ?_, ?_, ?_⟩
  · simp only [m598_setindexCartesian, m244_checkWritable, hw, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, resultPure, resultBindOk, hget, hcopy, hset]
  · simp only [m454_getindexCartesian, m237_checkReadable, hr, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, resultPure, resultBindOk, hget', hmul]
    rw [byteWindow_overwriteBytes_same old bytes k n hv (by
      change k*n + bytes.length ≤ old.length at hbound
      rw [hv] at hbound
      exact hbound)]
  · intro j' hj'
    exact hothers [j'] (by simpa using hj')
  · intro b hb hout new hnew
    change b < k*n ∨ k*n + bytes.length ≤ b at hout
    have he : new = overwriteBytes old (k*n) bytes := by
      rw [hget'] at hnew
      exact (Except.ok.inj hnew).symm
    rw [he, overwriteBytes_getElem? old bytes (k*n) b hbound]
    rcases hout with hleft | hright
    · rw [ite_eq_left hleft]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]


/-- Divide byte strides using mathematical integer quotients, not the implementation's
map/divrem/all pipeline. This independently specifies every rejection position. -/
def exactStrideResult (strides : List I64) (e : I64) : RResult (List I64) :=
  if e.val = 0 ∨ (e.val = -1 ∧ ∃ s ∈ strides, s.val = IntTy.min .i64) then
    if strides = [] then .ok [] else .error .divide
  else if ∀ s ∈ strides, e.val ∣ s.val then
    .ok (strides.map (fun s => JInt.wrap .i64 (s.val.tdiv e.val)))
  else .error .nonIntegralStride

theorem checkedStrides_result (strides : List I64) (e : I64) :
    m225_checkedStrides divremInt (· == zero) strides e = exactStrideResult strides e := by
  have h := fullCheckedStrides strides e
  unfold exactStrideResult
  by_cases hb : e.val = 0 ∨ (e.val = -1 ∧ ∃ s ∈ strides, s.val = IntTy.min .i64)
  · rw [ite_eq_left hb] at h ⊢
    exact h
  · rw [ite_eq_right hb] at h ⊢
    by_cases hd : ∀ s ∈ strides, e.val ∣ s.val
    · rw [ite_eq_left hd] at h ⊢
      exact h
    · rw [ite_eq_right hd] at h ⊢
      exact h

/-- The source-mirrored `size_to_strides` recursion from AbstractArray. -/
def sizeStrides (start : I64) : List I64 → List I64
  | [] => JuliaLean.base.abstractarray.sizeToStridesEmpty start
  | [_] => JuliaLean.base.abstractarray.sizeToStridesLast start ()
  | d :: rest =>
    let result := JuliaLean.base.abstractarray.sizeToStrides (· * ·)
      (fun next (_ : Unit) => sizeStrides next rest) start d ()
    result.1 :: result.2

/-- Each contiguous stride is the product of preceding dimensions, including empty shapes. -/
theorem sizeStrides_prefix (dims : List I64) (start : I64) (k : Nat) (hk : k < dims.length) :
    (sizeStrides start dims)[k]? = some ((dims.take k).foldl (· * ·) start) := by
  induction dims generalizing start k with
  | nil => simp at hk
  | cons d rest ih =>
    cases k with
    | zero => cases rest <;> rfl
    | succ k =>
      cases rest with
      | nil => simp at hk
      | cons x xs =>
        change (sizeStrides (start*d) (x::xs))[k]? = _
        rw [ih (start*d) k (by simpa using hk)]
        rfl

/-- All contiguous and strided parent shapes, including custom parent element spacing,
exact quotients, non-integral strides in any dimension, and noncontiguous first dimensions. -/
def FullStrideResults : Prop :=
  (∀ {A : Type} (size : A → List I64) (a : A) k,
    k < (size a).length → (m207_strides size sizeStrides a)[k]? =
      some (((size a).take k).foldl (· * ·) one)) ∧
  (∀ {T S A : Type} (contiguous : A → Bool) (size : ReinterpretArray T S A → List I64)
      (parentStrides : A → List I64) (parentElsize : A → I64) (a : ReinterpretArray T S A),
    let byteStrides := (parentStrides a.parent).map (· * parentElsize a.parent)
    let expected := if contiguous a.parent then .ok (sizeStrides one (size a))
      else if a.target.alignedSize = a.source.alignedSize then .ok (parentStrides a.parent)
      else if a.reshaped && a.target.alignedSize < a.source.alignedSize then
        (exactStrideResult byteStrides a.target.alignedSize).map (one :: ·)
      else if byteStrides.headD zero ≠ a.source.alignedSize then .error .noncontiguous
      else (exactStrideResult (byteStrides.drop 1) a.target.alignedSize).map
        (fun result => if a.reshaped then result else one :: result)
    m211_strides contiguous size sizeStrides parentStrides parentElsize divremInt (· == zero) a = expected)

theorem fullStrideResults : FullStrideResults := by
  refine ⟨?_, ?_⟩
  · intro A size a k hk
    exact sizeStrides_prefix (size a) one k hk
  · intro T S A contiguous size parentStrides parentElsize a
    dsimp only
    unfold m211_strides
    simp only [m232_checkcontiguous, m369_parent, checkedStrides_result]
    by_cases hc : contiguous a.parent = true
    · simp [hc]
    · have hc' : contiguous a.parent = false := Bool.eq_false_iff.mpr hc
      simp only [hc', Bool.false_eq_true, ↓reduceIte]
      by_cases he : a.target.alignedSize = a.source.alignedSize
      · simp [he]
      · have hv : a.target.alignedSize.val ≠ a.source.alignedSize.val := fun h => he (jint_eq_of_val h)
        simp only [beq_iff_val, hv, decide_false, Bool.false_eq_true, ↓reduceIte, he]
        split
        · cases exactStrideResult ((parentStrides a.parent).map (· * parentElsize a.parent)) a.target.alignedSize <;> rfl
        · by_cases hf : ((parentStrides a.parent).map (· * parentElsize a.parent)).headD zero = a.source.alignedSize
          · simp only [bne_iff_val, show (((parentStrides a.parent).map (· * parentElsize a.parent)).headD zero).val = a.source.alignedSize.val by rw [hf],
              ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hf]
            cases exactStrideResult (((parentStrides a.parent).map (· * parentElsize a.parent)).drop 1) a.target.alignedSize <;> rfl
          · have hfv : (((parentStrides a.parent).map (· * parentElsize a.parent)).headD zero).val ≠ a.source.alignedSize.val :=
              fun h => hf (jint_eq_of_val h)
            simp only [bne_iff_val, hfv, ne_eq, not_false_eq_true, decide_true,
              ↓reduceIte, hf]
            rfl

/-- Every positive dimension selects the product of preceding sizes; dimensions beyond the
array rank have the total element count as their stride. -/
def FullStrideSelector : Prop :=
  ∀ {A : Type} (size : A → List I64) (a : A) (k : Nat),
    1 ≤ k → ((size a).length : Int) ≤ IntTy.max .i64 →
    m208_stride (fun x => JInt.lit .i64 (size x).length) (m207_strides size sizeStrides)
      (fun x => (size x).foldl (· * ·) one)
      (fun dim rank => decide (dim ≤ rank.val.toNat))
      (fun strides dim => strides.getD (dim - 1) zero) a k =
      ((size a).take (if k ≤ (size a).length then k - 1 else (size a).length)).foldl (· * ·) one

theorem fullStrideSelector : FullStrideSelector := by
  intro A size a k hk hmax
  have hr : (JInt.lit .i64 (size a).length).val.toNat = (size a).length := by
    rw [lit_nat _ hmax, Int.toNat_natCast]
  unfold m208_stride
  dsimp only
  simp only [hr]
  by_cases hdim : k ≤ (size a).length
  · simp only [hdim, decide_true, ↓reduceIte]
    have hp := sizeStrides_prefix (size a) one (k-1) (by omega)
    change ((sizeStrides one (size a))[k-1]?).getD zero = _
    rw [hp]
    rfl
  · simp only [hdim, decide_false, Bool.false_eq_true, ↓reduceIte, List.take_length]

def FullStrideContract : Prop := FullStrideResults ∧ FullStrideSelector

theorem fullStrideContract : FullStrideContract := ⟨fullStrideResults, fullStrideSelector⟩

/-- Both constructors keep the exact array supplied by the caller. Alias tracking and offset
queries therefore refer to that original array for every successful construction. -/
def ConstructorParentPreservation : Prop :=
  ∀ {T S A R : Type} (target source : TypeLayout) (p : ArrayInput A)
      (dataids : ArrayInput A → R) (hasOffset : ArrayInput A → Bool),
    (match m73_reinterpret (T := T) (S := S) target source p with
    | .error _ => True
    | .ok a => m369_parent a = p ∧ m370_dataids dataids a = dataids p ∧
        m401_hasOffset hasOffset a = hasOffset p) ∧
    (match m188_reinterpretReshape (T := T) (S := S) target source p with
    | .error _ => True
    | .ok a => m369_parent a = p ∧ m370_dataids dataids a = dataids p ∧
        m401_hasOffset hasOffset a = hasOffset p)

theorem constructorParentPreservation : ConstructorParentPreservation := by
  intro T S A R target source p dataids hasOffset
  constructor
  · cases h : m73_reinterpret (T := T) (S := S) target source p with
    | error e => trivial
    | ok a =>
      obtain ⟨_, _, _, hp⟩ := m73_congr_parent target source p p a rfl rfl h
      exact ⟨hp, by simpa [m370_dataids, hp], by simpa [m401_hasOffset, hp]⟩
  · cases h : m188_reinterpretReshape (T := T) (S := S) target source p with
    | error e => trivial
    | ok a =>
      obtain ⟨_, _, _, hp⟩ := m107_congr_parent target source p p a rfl rfl h
      exact ⟨hp, by simpa [m370_dataids, hp], by simpa [m401_hasOffset, hp]⟩

/-- Addressing a view uses its target storage width when element sizes differ, and its
parent's physical spacing otherwise, with native address wrapping for every index. -/
def PhysicalElementSpacing : Prop :=
  ∀ {T S A E : Type} (parentElsize : A → I64) (a : ReinterpretArray T S A)
      (base : JuliaLean.base.pointer.Ptr E) (index : I64),
    let width := if a.target.alignedSize.val = a.source.alignedSize.val then
      (parentElsize a.parent).val else a.target.alignedSize.val
    (JuliaLean.base.pointer.ptrAddI64 base (m403_elsize parentElsize a * index)).address.val =
      wrapInt .u64 (base.address.val + width * index.val)

theorem physicalElementSpacing : PhysicalElementSpacing := by
  intro T S A E parentElsize a base index
  dsimp only
  have hwidth : (m403_elsize parentElsize a).val =
      if a.target.alignedSize.val = a.source.alignedSize.val then
        (parentElsize a.parent).val else a.target.alignedSize.val := by
    by_cases h : a.target.alignedSize.val = a.source.alignedSize.val <;>
      simp [m403_elsize, beq_iff_val, h]
  simp only [JuliaLean.base.pointer.ptrAddI64, JuliaLean.base.pointer.ptrAddInteger,
    JuliaLean.base.pointer.addPtrBytes, JuliaLean.base.pointer.int64ToUInt64,
    val_add, val_wrap, wrapInt_add_right]
  rw [val_mul, hwidth]
  rw [wrapInt_emod .u64, Int.add_emod,
    show wrapInt .i64 _ % (2 ^ IntTy.u64.bits : Int) = _ from wrapInt_emod_self .i64 _]
  simp only [IntTy.bits]
  rw [← Int.add_emod]
  exact (wrapInt_emod .u64 _).symm

/-- Scalar reinterpretation rejects any non-isbits or non-byte-aligned input type before
copying storage; supported packed layouts also satisfy the full byte roundtrip contract. -/
def FullPaddingConversion : Prop :=
  FullPackedRoundtrip ∧ ReinterpretPackedCopies ∧
    ∀ output input bytes initial,
      (output.isBits = false ∨ input.isBits = false ∨ BitPadded output ∨ BitPadded input) →
      m882_reinterpret output input bytes initial = .error .argument



inductive FieldLeaf : TypeLayout → Nat → TypeLayout → Prop where
  | primitive (t : TypeLayout) (h : t.primitive = true) : FieldLeaf t 0 t
  | field (t child leaf : TypeLayout) (off inner : Nat)
      (hp : t.primitive = false) (hm : (off, child) ∈ t.fields)
      (hc : FieldLeaf child inner leaf) : FieldLeaf t (off + inner) leaf

/-- The indices occupied by primitive fields, specified by field paths and physical byte
addresses. Every byte within a primitive leaf contributes once, independently of any mask loop. -/
def FieldByte (t : TypeLayout) (base : I64) (k : Nat) : Prop :=
  ∃ offset leaf byte, FieldLeaf t offset leaf ∧ byte < (leaf.bits + 7) / 8 ∧
    k = (wrapInt .i64 (base.val + offset + byte)).toNat

def SmallPrimitiveLeaves (t : TypeLayout) : Prop :=
  ∀ offset leaf, FieldLeaf t offset leaf → (((leaf.bits + 7) / 8 : Nat) : Int) ≤ IntTy.max .i64

private theorem foldl_set_true {α : Type} (xs : List α) (locate : α → Nat)
    (used : List Bool) (k : Nat) (hk : k < used.length) :
    (xs.foldl (fun mask x => mask.set (locate x) true) used)[k]? = some true ↔
      used[k]? = some true ∨ ∃ x ∈ xs, k = locate x := by
  induction xs generalizing used with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih (used.set (locate x) true) (by simpa using hk)]
    by_cases he : k = locate x
    · subst k
      simp [List.getElem?_set_self hk]
    · rw [List.getElem?_set_ne (Ne.symm he)]
      simp only [List.mem_cons, exists_eq_or_imp, he, false_or]

private theorem foldl_true_union {α : Type} (xs : List α) (step : List Bool → α → List Bool)
    (written : α → Prop) (used : List Bool) (k : Nat)
    (hlen : ∀ mask x, x ∈ xs → (step mask x).length = mask.length)
    (hstep : ∀ mask x, x ∈ xs → k < mask.length →
      ((step mask x)[k]? = some true ↔ mask[k]? = some true ∨ written x))
    (hk : k < used.length) :
    (xs.foldl step used)[k]? = some true ↔ used[k]? = some true ∨ ∃ x ∈ xs, written x := by
  induction xs generalizing used with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,
      ih (step used x) (fun mask y hy => hlen mask y (List.mem_cons_of_mem x hy))
        (fun mask y hy => hstep mask y (List.mem_cons_of_mem x hy))
        (by rw [hlen used x List.mem_cons_self]; exact hk),
      hstep used x List.mem_cons_self hk]
    simp only [List.mem_cons, exists_eq_or_imp]
    exact or_assoc

private theorem primitive_write_indices (base : I64) (n : Nat) (hn : (n : Int) ≤ IntTy.max .i64) :
    ∀ k, (∃ i ∈ intRange one (JInt.lit .i64 n), k = (i + base - one).val.toNat) ↔
      ∃ byte < n, k = (wrapInt .i64 (base.val + byte)).toNat := by
  intro k
  rw [intRange_one (lit_nat n hn)]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, ⟨byte, hb, rfl⟩, hk⟩
    refine ⟨byte, hb, ?_⟩
    rw [val_sub, val_add, val_add, val_lit, one_val, wrapInt_add_left,
      wrapInt_sub_left, wrapInt_of_inRange .i64 (byte : Int)
        ⟨by have := i64_min_nonpos; omega, by omega⟩] at hk
    rwa [show 1 + (byte : Int) + base.val - 1 = base.val + byte by omega] at hk
  · rintro ⟨byte, hb, hk⟩
    refine ⟨one + JInt.lit .i64 byte, ⟨byte, hb, rfl⟩, ?_⟩
    rw [val_sub, val_add, val_add, val_lit, one_val, wrapInt_add_left,
      wrapInt_sub_left, wrapInt_of_inRange .i64 (byte : Int)
        ⟨by have := i64_min_nonpos; omega, by omega⟩]
    rwa [show 1 + (byte : Int) + base.val - 1 = base.val + byte by omega]

/-- The mask marks exactly the bytes occupied by primitive leaves of arbitrary compound
field trees, preserving every pre-existing true bit and the mask's length. -/
def FullByteMask : Prop :=
  ∀ t base used k, SmallPrimitiveLeaves t → k < used.length →
    ((m756_fillNonpadding t base used)[k]? = some true ↔
      used[k]? = some true ∨ FieldByte t base k)

theorem fullByteMask : FullByteMask := by
  intro t
  refine WellFounded.induction (C := fun t => ∀ base used k, SmallPrimitiveLeaves t → k < used.length →
    ((m756_fillNonpadding t base used)[k]? = some true ↔
      used[k]? = some true ∨ FieldByte t base k)) (measure sizeOf).wf t ?_
  intro t ih base used k hsmall hk
  rw [m756_fillNonpadding.eq_def]
  by_cases hp : t.primitive = true
  · rw [ite_eq_left hp, foldl_set_true _ _ _ _ hk]
    have hcount : ((t.bits : Int) + 7) / 8 = (((t.bits + 7) / 8 : Nat) : Int) := by omega
    rw [hcount, primitive_write_indices base ((t.bits + 7)/8) (hsmall 0 t (.primitive t hp))]
    apply or_congr_right
    constructor
    · rintro ⟨byte, hb, hindex⟩
      exact ⟨0, t, byte, .primitive t hp, hb, by simpa using hindex⟩
    · rintro ⟨off, leaf, byte, hleaf, hb, hindex⟩
      cases hleaf with
      | primitive => exact ⟨byte, hb, by simpa using hindex⟩
      | field _ _ _ _ _ hf => simp [hp] at hf
  · have hp' : t.primitive = false := Bool.eq_false_iff.mpr hp
    rw [ite_eq_right hp]
    rw [foldl_true_union t.fields.attach
      (fun mask field => m756_fillNonpadding field.val.2 (base + JInt.lit .i64 field.val.1) mask)
      (fun field => FieldByte field.val.2 (base + JInt.lit .i64 field.val.1) k)
      used k (fun mask field _ => fillNonpadding_length _ _ _)]
    · apply or_congr_right
      constructor
      · rintro ⟨field, _, inner, leaf, byte, hleaf, hb, hindex⟩
        refine ⟨field.val.1 + inner, leaf, byte,
          .field t field.val.2 leaf field.val.1 inner hp' field.property hleaf, hb, ?_⟩
        rw [val_add, val_lit, wrapInt_add_right] at hindex
        simp only [Int.add_assoc, wrapInt_add_left] at hindex
        simpa [Int.add_assoc, Int.natCast_add] using hindex
      · rintro ⟨off, leaf, byte, hleaf, hb, hindex⟩
        cases hleaf with
        | primitive _ ht => exact False.elim (hp ht)
        | field _ child _ off inner _ hm hc =>
          refine ⟨⟨(off, child), hm⟩, List.mem_attach _ _, inner, leaf, byte, hc, hb, ?_⟩
          rw [val_add, val_lit, wrapInt_add_right]
          simp only [Int.add_assoc, wrapInt_add_left]
          simpa [Int.add_assoc, Int.natCast_add] using hindex
    · intro mask field _ hmask
      apply ih field.val.2
      · rcases t with ⟨info, fields, members⟩
        have h1 := List.sizeOf_lt_of_mem field.property
        have h2 : sizeOf field.val.2 < sizeOf field.val := by
          rcases field with ⟨⟨off, child⟩, hm⟩; simp; omega
        have h3 : sizeOf fields < sizeOf (TypeLayout.mk info fields members) := by simp; omega
        exact Nat.lt_trans h2 (Nat.lt_trans h1 h3)
      · intro off leaf hleaf
        exact hsmall (field.val.1 + off) leaf
          (.field t field.val.2 leaf field.val.1 off hp' field.property hleaf)
      · exact hmask
    · exact hk

/-- A byte view converts to a byte-identical string, including invalid UTF-8 byte sequences.
The runtime's pointer-to-string primitive is external; its interface law copies exactly the
requested bytes. Empty views bypass padding restrictions. -/
def FullStringBytes : Prop :=
  ∀ {T S A R : Type} (length : ReinterpretArray T S A → I64)
      (empty : R) (callString : ReinterpretArray T S A → I64 → RResult R)
      (stringBytes : R → Bytes) (a : ReinterpretArray T S A) (bytes : Bytes),
    a.target = primitiveLayout 1 1 → a.readable = !a.source.datatypePadding →
    0 ≤ (length a).val → (length a).val.toNat = bytes.length → stringBytes empty = [] →
    (∀ n : I64, 0 ≤ n.val → n.val.toNat ≤ bytes.length →
      ∃ text, callString a n = .ok text ∧ stringBytes text = bytes.take n.val.toNat) →
    (if bytes = [] then m937_string length empty callString a = .ok empty
     else if a.source.datatypePadding then m937_string length empty callString a = .error .padding
     else ∃ text, m937_string length empty callString a = .ok text ∧ stringBytes text = bytes)



def FullPaddingLayout : Prop := FullByteMask ∧ ReinterpretPaddingLayout ∧ BitPaddingDetection



/-- Copying a valid view preserves every parent value while separating its alias identities.
Only the parent's copy operation is generic; both reconstruction constructors are the models. -/
def copiedParent {T S A : Type} :
    ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A)) Unit → Option (ArrayInput A)
  | .parent p => some p
  | .view a => some a.parent
  | .nested _ => none

def FullUnaliasCopy : Prop :=
  ∀ {T S A : Type} (target source : TypeLayout) (p p' : ArrayInput A)
      (a : ReinterpretArray T S (ArrayInput A))
      (copy : ArrayInput A → RResult (ArrayInput A))
      (get : ArrayInput A → List I64 → RResult Bytes) (aliases : ArrayInput A → List Nat),
    copy p = .ok p' → p'.rank = p.rank → p'.axes = p.axes →
    (∀ inds, get p' inds = get p inds) →
    (∀ id ∈ aliases p', id ∉ aliases p) →
    (m73_reinterpret target source p = .ok a →
      ∃ result p'', m371_unaliascopy copy a = .ok result ∧ copiedParent result = some p'' ∧
        (∀ inds, get p'' inds = get (m369_parent a) inds) ∧
        (∀ id ∈ aliases p'', id ∉ m370_dataids aliases a)) ∧
    (m188_reinterpretReshape target source p = .ok a →
      ∃ result p'', m372_unaliascopyReshaped copy a = .ok result ∧ copiedParent result = some p'' ∧
        (∀ inds, get p'' inds = get (m369_parent a) inds) ∧
        (∀ id ∈ aliases p'', id ∉ m370_dataids aliases a))



def FullParentMetadata : Prop := ConstructorParentPreservation ∧ FullUnaliasCopy



end Strict


namespace HeapContract
open JuliaLean.base.pointer

/-- A parent's header metadata is unchanged when its backing heap is updated. -/
structure StableHeader {T S A V : Type} (ops : PointerWriteOps T S A V) : Prop where
  heap : ∀ p h, ops.heap (ops.withHeap p h) = h
  bounds : ∀ a h inds, ops.checkbounds { a with parent := ops.withHeap a.parent h } inds = ops.checkbounds a inds
  linear : ∀ a h inds, ops.linearIndex { a with parent := ops.withHeap a.parent h } inds = ops.linearIndex a inds
  first : ∀ a h, ops.firstindex { a with parent := ops.withHeap a.parent h } = ops.firstindex a
  convert : ∀ p h t, ops.parentCconvert t (ops.withHeap p h) = ops.parentCconvert t p
  spacing : ∀ p h, ops.parentElsize (ops.withHeap p h) = ops.parentElsize p

def reader {T S A V : Type} (ops : PointerWriteOps T S A V) : PointerReadOps T S A where
  checkbounds := ops.checkbounds
  linearIndex := ops.linearIndex
  parentCconvert := ops.parentCconvert
  unsafeConvert := ops.unsafeConvert
  parentElsize := ops.parentElsize
  firstindex := ops.firstindex
  addPointer := ops.addPointer
  Element := ops.Element
  codec := ops.codec
  heap := ops.heap

def address {T S A V : Type} (ops : PointerWriteOps T S A V)
    (a : ReinterpretArray T S A) (inds : List JuliaLean.base.reinterpretarray.I64) : Nat :=
  ops.addPointer (ops.unsafeConvert a.target (m410_cconvert ops.parentCconvert a))
    (m403_elsize ops.parentElsize a * (ops.linearIndex a inds - ops.firstindex a))

/-- Pointer assignment updates the actual parent heap, and a subsequent getter reads the
converted value from that updated heap. Bounds and conversion failures remain errors. -/
def WriteThroughReadback : Prop :=
  ∀ {T S A V : Type} (ops : PointerWriteOps T S A V) (a : ReinterpretArray T S A)
      (inds : List JuliaLean.base.reinterpretarray.I64) (v : V),
    StableHeader ops →
    (ops.checkbounds a inds = .error .bounds → m610_setindexPtr ops a v inds = .error .bounds) ∧
    (∀ err, ops.checkbounds a inds = .ok () → ops.convert v = .error err →
      m610_setindexPtr ops a v inds = .error (.pointer err)) ∧
    (∀ typed, ops.checkbounds a inds = .ok () → ops.convert v = .ok typed →
      let p : Ptr ops.Element := ⟨JInt.wrap .u64 (address ops a inds)⟩
      (ops.heap a.parent).validRange (indexedPointer ops.codec p oneI64).address.val.toNat
        ops.codec.elementSize.val.toNat →
      ∃ a', m610_setindexPtr ops a v inds = .ok a' ∧
        (ops.heap a'.parent).readBytes (indexedPointer ops.codec p oneI64).address.val.toNat
          ops.codec.elementSize.val.toNat = ops.codec.encode typed ∧
        m461_getindexPtr (reader ops) a' inds = .ok (pointerStorageBytes (ops.codec.encode typed)))

theorem writeThroughReadback : WriteThroughReadback := by
  intro T S A V ops a inds v laws
  refine ⟨?_, ?_, ?_⟩
  · intro h
    simp [m610_setindexPtr, h]
  · intro err hb hc
    simp [m610_setindexPtr, hb, PointerWriteOps.store, unsafeStoreTyped, hc,
      Except.map, Except.mapError, bind, Except.bind, pure, Except.pure]
  · intro typed hb hc
    dsimp only
    intro hv
    let p : Ptr ops.Element := ⟨JInt.wrap .u64 (address ops a inds)⟩
    let stored := pointerSet ops.codec (ops.heap a.parent) p typed oneI64 oneI64
    have hs : unsafeStoreTyped ops.codec ops.convert (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i)
        p (ops.heap a.parent) v oneI64 = .ok stored := by
      simp [unsafeStoreTyped, hc, stored, bind, Except.bind, pure, Except.pure]
    have hs' : unsafeStoreTyped ops.codec ops.convert (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i)
        p (ops.heap a.parent) v oneI64 = .ok (stored.1, p) := by
      simpa [stored, pointerSet] using hs
    have hbytes := JuliaLean.Proofs.base.pointer.pointerStoresWriteOneBasedElements_proven.1
      ops.codec ops.convert (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i)
      (ops.heap a.parent) p v oneI64 oneI64 typed stored.1 hc rfl hv hs'
    have hload : unsafeLoad ops.codec (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i)
        p stored.1 oneI64 = .ok typed := by
      simp [unsafeLoad, pointerRef, hbytes, ops.codec.decode_encode,
        bind, Except.bind, pure, Except.pure]
    refine ⟨{ a with parent := ops.withHeap a.parent stored.1 }, ?_, ?_, ?_⟩
    · simp only [m610_setindexPtr, hb, resultBindOk, PointerWriteOps.store]
      change ((unsafeStoreTyped ops.codec ops.convert (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i)
        p (ops.heap a.parent) v oneI64).map (fun pair => ops.withHeap a.parent pair.1)).mapError
          ReinterpretError.pointer >>= (fun parent => pure { a with parent := parent }) = _
      rw [hs]
      rfl
    · simpa only [laws.heap] using hbytes
    · simp only [m461_getindexPtr, reader, laws.bounds, hb, resultBindOk,
        laws.linear, laws.first, m410_cconvert, laws.convert, m403_elsize, laws.spacing]
      unfold PointerReadOps.load
      simp only [laws.heap]
      change ((unsafeLoad ops.codec (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i)
        p stored.1 oneI64).map (fun x => pointerStorageBytes (ops.codec.encode x))).mapError
          ReinterpretError.pointer = _
      rw [hload]
      rfl
end HeapContract


namespace HeapContract
open JuliaLean.base.pointer

/-- Checked pointer reads use the target element's physical byte spacing on every supported
parent and shape, and return the encoded value in that slot. -/
def ReadsStoredBytes : Prop :=
  ∀ {T S A : Type} (ops : PointerReadOps T S A) (a : ReinterpretArray T S A)
      (inds : List JuliaLean.base.reinterpretarray.I64),
    a.target.alignedSize ≠ a.source.alignedSize →
    ops.codec.elementSize = a.target.alignedSize →
    (ops.checkbounds a inds = .error .bounds → m461_getindexPtr ops a inds = .error .bounds) ∧
    (∀ value, ops.checkbounds a inds = .ok () →
      let address := ops.addPointer (ops.unsafeConvert a.target (ops.parentCconvert a.source a.parent))
        (ops.codec.elementSize * (ops.linearIndex a inds - ops.firstindex a))
      let p : Ptr ops.Element := ⟨JInt.wrap .u64 address⟩
      (ops.heap a.parent).validRange (indexedPointer ops.codec p oneI64).address.val.toNat
        ops.codec.elementSize.val.toNat →
      (ops.heap a.parent).readBytes (indexedPointer ops.codec p oneI64).address.val.toNat
        ops.codec.elementSize.val.toNat = ops.codec.encode value →
      m461_getindexPtr ops a inds = .ok (pointerStorageBytes (ops.codec.encode value)))

theorem readsStoredBytes : ReadsStoredBytes := by
  intro T S A ops a inds hne hcodec
  refine ⟨fun hb => by simp [m461_getindexPtr, hb], ?_⟩
  intro value hb
  dsimp only
  intro hv hbytes
  have hneval : a.target.alignedSize.val ≠ a.source.alignedSize.val :=
    fun h => hne (jint_eq_of_val h)
  have hload := JuliaLean.Proofs.base.pointer.pointerLoadsReadOneBasedElements_proven.1
    ops.codec (fun i : JuliaLean.base.reinterpretarray.I64 => .ok i) (ops.heap a.parent)
    (⟨JInt.wrap .u64 (ops.addPointer (ops.unsafeConvert a.target (ops.parentCconvert a.source a.parent))
      (ops.codec.elementSize * (ops.linearIndex a inds - ops.firstindex a)))⟩ : Ptr ops.Element)
    oneI64 oneI64 value rfl hv hbytes
  simp only [m461_getindexPtr, hb, resultBindOk, m410_cconvert,
    m403_elsize, beq_iff_val, hneval, decide_false, Bool.false_eq_true, ↓reduceIte]
  unfold PointerReadOps.load
  rw [← hcodec]
  simp only [PointerReadOps.load.oneI64, JuliaLean.base.pointer.oneI64,
    JuliaLean.base.pointer.i64] at hload ⊢
  rw [hload]
  rfl
end HeapContract

namespace Statements
open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.Proofs.base.reinterpretarray
open JuliaLean.Proofs.base.reinterpretarray.Strict
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A value occupies the non-padding bytes of its declared runtime storage layout. -/
def ValidElement (t : TypeLayout) (bytes : Bytes) : Prop :=
  bytes.length = t.alignedSize.val.toNat

/-- Finite, representable AbstractArray axes. Empty and zero-dimensional arrays are included. -/
def ValidAxes (axs : List Axis) : Prop :=
  ∀ ax ∈ axs, 0 ≤ ax.length.val ∧
    ax.first.val + ax.length.val - 1 ≤ IntTy.max .i64

/-- The parent type determines which existing check_ptr_indexable overload is selected. -/
inductive PointerRoute : Type → Type 1 where
  | dense {A : Type} : PointerRoute A
  | abstract {A : Type} : PointerRoute A
  | reshaped {A P : Type} (parent : A → P) (child : PointerRoute P) : PointerRoute A
  | subarray {A P : Type} (parent : A → P) (child : PointerRoute P) : PointerRoute A
  | reinterpreted {T S P : Type} (child : PointerRoute P) : PointerRoute (ReinterpretArray T S P)

def PointerRoute.check {A : Type} (route : PointerRoute A) (a : A) : Bool :=
  match route with
  | .dense => m427_checkPtrDense a
  | .abstract => m428_checkPtrAbstract a
  | .reshaped parent child => m425_checkPtrReshaped parent child.check a
  | .subarray parent child => m426_checkPtrSubarray parent child.check a
  | .reinterpreted child => m421_checkPtrIndexable child.check a

/-- An arbitrary parent's own AbstractArray API and logical column-major storage. -/
structure ParentInterface (A : Type) where
  axes : A → List Axis
  bytes : A → Bytes
  ops : ParentOps A
  style : A → IndexStyleModel
  pointerRoute : PointerRoute A

def ParentInterface.pointerCapable {A : Type} (p : ParentInterface A) : A → Bool :=
  p.pointerRoute.check

/-- Laws of the parent's API, including linear indexing and zero-dimensional indexing.
No law mentions a reinterpretation method. -/
def ParentLaws {A : Type} (p : ParentInterface A) (s : TypeLayout) : Prop :=
  ∀ a,
    ValidAxes (p.axes a) ∧
    (p.bytes a).length = ((p.axes a).map (fun ax => ax.length.val.toNat)).prod *
      s.alignedSize.val.toNat ∧
    (∀ inds, p.ops.get a inds =
      match denseCoordinate (p.axes a) inds with
      | none => .error .bounds
      | some k => .ok (byteWindow (p.bytes a) (k * s.alignedSize.val.toNat)
          s.alignedSize.val.toNat)) ∧
    (∀ inds value, ValidElement s value →
      match denseCoordinate (p.axes a) inds with
      | none => p.ops.set a inds value = .error .bounds
      | some k => ∃ a', p.ops.set a inds value = .ok a' ∧
          p.axes a' = p.axes a ∧
          p.bytes a' = overwriteBytes (p.bytes a) (k * s.alignedSize.val.toNat) value)

/-- The runtime address, codec and heap represent the same parent storage as its API.
Bounds, linear-index and coordinate conversion interfaces are external AbstractArray operations. -/
structure AccessInterface (T S A V : Type) where
  parent : ParentInterface A
  read : PointerReadOps T S A
  write : PointerWriteOps T S A V
  first : ReinterpretArray T S A → I64
  bounds : ReinterpretArray T S A → I64 → List I64 → RResult Unit
  subscripts : ReinterpretArray T S A → I64 → List I64
  convert : TypeLayout → V → RResult Bytes

/-- The independent byte address of a view element in column-major order. -/
def viewOffset {T S A : Type} (axes : A → List Axis)
    (a : ReinterpretArray T S A) (inds : List I64) : Option Nat :=
  (denseCoordinate (viewAxes a.reshaped a.target a.source (axes a.parent)) inds).map
    (fun k => k * a.target.alignedSize.val.toNat)

/-- Array interface coherence: these are the parent's coordinate, conversion and storage laws,
not assumptions about the result of a reinterpretation method. -/
def AccessLaws {T S A V : Type} (c : AccessInterface T S A V)
    (a : ReinterpretArray T S A) : Prop :=
  ParentLaws c.parent a.source ∧
  ValidStorageLayout a.target ∧ ValidStorageLayout a.source ∧
  a.target.isBits = true ∧ a.source.isBits = true ∧
  ¬ BitPadded a.target ∧ ¬ BitPadded a.source ∧
  a.rank = (viewAxes a.reshaped a.target a.source (c.parent.axes a.parent)).length ∧
  (let p : ArrayInput A := ⟨a.parent, (c.parent.axes a.parent).length,
      (c.parent.axes a.parent).map Axis.length, c.parent.axes a.parent⟩
   if a.reshaped then ReshapeAdmissible a.target a.source p
   else PlainAdmissible a.target a.source p) ∧
  (a.readable = true ↔ PaddingCompatible a.target a.source) ∧
  (a.writable = true ↔ PaddingCompatible a.source a.target) ∧
  (c.first a = if a.rank = 1 then
      ((viewAxes a.reshaped a.target a.source (c.parent.axes a.parent)).headD ⟨one, zero⟩).first
    else one) ∧
  (∀ v bytes, c.convert a.target v = .ok bytes → ValidElement a.target bytes) ∧
  (∀ inds,
    c.bounds a (inds.headD (c.first a)) (inds.drop 1) =
      (if (viewOffset c.parent.axes a inds).isSome then .ok () else .error .bounds)) ∧
  (∀ i, denseCoordinate (viewAxes a.reshaped a.target a.source (c.parent.axes a.parent))
      (c.subscripts a i) =
    denseCoordinate (viewAxes a.reshaped a.target a.source (c.parent.axes a.parent)) [i]) ∧
  (c.parent.pointerCapable a.parent = true →
    c.read.codec.elementSize = a.target.alignedSize ∧
    c.write.codec.elementSize = a.target.alignedSize ∧
    (∀ b, c.read.heap b = c.write.heap b) ∧
    (∀ b h, c.write.heap (c.write.withHeap b h) = h ∧
      c.parent.axes (c.write.withHeap b h) = c.parent.axes b ∧
      c.parent.bytes (c.write.withHeap b h) =
        pointerStorageBytes (h.readBytes
          (c.read.unsafeConvert a.target (c.read.parentCconvert a.source b))
          (c.parent.bytes b).length)) ∧
    (∀ v, ((c.write.convert v).map
      (fun value => pointerStorageBytes (c.write.codec.encode value))).mapError
        ReinterpretError.pointer = c.convert a.target v) ∧
    (∀ inds, c.read.checkbounds a inds =
      (if (viewOffset c.parent.axes a inds).isSome then .ok () else .error .bounds)) ∧
    (∀ inds, c.write.checkbounds a inds = c.read.checkbounds a inds) ∧
    (∀ inds, c.write.addPointer
        (c.write.unsafeConvert a.target (c.write.parentCconvert a.source a.parent))
        (m403_elsize c.write.parentElsize a *
          (c.write.linearIndex a inds - c.write.firstindex a)) =
      c.read.addPointer
        (c.read.unsafeConvert a.target (c.read.parentCconvert a.source a.parent))
        (m403_elsize c.read.parentElsize a *
          (c.read.linearIndex a inds - c.read.firstindex a))) ∧
    (∀ inds off, viewOffset c.parent.axes a inds = some off →
      let base := c.read.unsafeConvert a.target (c.read.parentCconvert a.source a.parent)
      let address := c.read.addPointer base
        (m403_elsize c.read.parentElsize a * (c.read.linearIndex a inds - c.read.firstindex a))
      address = (JInt.wrap .u64 (base + off)).val.toNat ∧
      (c.read.heap a.parent).validRange address a.target.alignedSize.val.toNat ∧
      pointerStorageBytes ((c.read.heap a.parent).readBytes address a.target.alignedSize.val.toNat) =
        byteWindow (c.parent.bytes a.parent) off a.target.alignedSize.val.toNat ∧
      (∀ b < a.target.alignedSize.val.toNat, ValueByte a.target b →
        (pointerStorageBytes (c.read.codec.encode (c.read.codec.decode
          ((c.read.heap a.parent).readBytes address a.target.alignedSize.val.toNat))))[b]? =
            (c.parent.bytes a.parent)[off + b]?)))

/-- The result retains every target value byte. Target padding has no defined value. -/
def ReadResult {T S A : Type} (parent : ParentInterface A)
    (a : ReinterpretArray T S A) (inds : List I64) (result : RResult Bytes) : Prop :=
  if PaddingCompatible a.target a.source then
    match viewOffset parent.axes a inds with
    | none => result = .error .bounds
    | some off => ∃ bytes, result = .ok bytes ∧ ValidElement a.target bytes ∧
        ∀ b < bytes.length, ValueByte a.target b →
          bytes[b]? = (parent.bytes a.parent)[off + b]?
  else result = .error .padding

/-- Assignment preserves all source value bytes outside the target window and updates every
source value byte inside it. Padding bytes remain unspecified. Error order follows dispatch. -/
def WriteResult {T S A V : Type} (c : AccessInterface T S A V)
    (a : ReinterpretArray T S A) (v : V) (inds : List I64)
    (result : RResult (ReinterpretArray T S A)) : Prop :=
  if PaddingCompatible a.source a.target then
    match c.convert a.target v, viewOffset c.parent.axes a inds with
    | .error e, none => result = .error e ∨ result = .error .bounds
    | .error e, some _ => result = .error e
    | .ok _, none => result = .error .bounds
    | .ok bytes, some off => ∃ a', result = .ok a' ∧ a'.target = a.target ∧
        a'.source = a.source ∧ a'.rank = a.rank ∧ a'.reshaped = a.reshaped ∧
        c.parent.axes a'.parent = c.parent.axes a.parent ∧
        (c.parent.bytes a'.parent).length = (c.parent.bytes a.parent).length ∧
        ∀ b < (c.parent.bytes a.parent).length,
          ValueByte a.source (b % a.source.alignedSize.val.toNat) →
          (c.parent.bytes a'.parent)[b]? =
            if off ≤ b ∧ b < off + bytes.length then bytes[b - off]?
            else (c.parent.bytes a.parent)[b]?
  else result = .error .padding

/-- reinterpret(T,A) and reinterpret(reshape,T,A) retain A's binary data on every public
integer-coordinate, linear and zero-dimensional getindex overload, including pointer dispatch. -/
def AllReads : Prop :=
  ∀ {T S A V : Type} (c : AccessInterface T S A V) (a : ReinterpretArray T S A),
    AccessLaws c a →
    (∀ i tail, (i :: tail).length = a.rank → ReadResult c.parent a (i :: tail)
      (m436_getindex c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get a i tail)) ∧
    (∀ i, ReadResult c.parent a [i]
      (m442_getindexLinear c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get c.subscripts a i)) ∧
    (a.rank = 0 →
      (a.reshaped = false → ReadResult c.parent a []
        (m413_getindexZero c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get c.subscripts a)) ∧
      (a.reshaped = true → ReadResult c.parent a []
        (m430_getindexZeroReshaped c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get c.subscripts a)))

/-- Every public setindex! overload preserves the parent outside the assigned target value,
for arbitrary ranks, storage types, padding layouts, integer coordinates and pointer dispatch. -/
def AllWrites : Prop :=
  ∀ {T S A V : Type} (c : AccessInterface T S A V) (a : ReinterpretArray T S A),
    AccessLaws c a →
    (∀ v i tail, (i :: tail).length = a.rank → WriteResult c a v (i :: tail)
      (m582_setindex c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops a v i tail)) ∧
    (∀ v i, WriteResult c a v [i]
      (m588_setindexLinear c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops c.subscripts a v i)) ∧
    (a.rank = 0 → ∀ v,
      (a.reshaped = false → WriteResult c a v []
        (m572_setindexZero c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops c.subscripts a v)) ∧
      (a.reshaped = true → WriteResult c a v []
        (m580_setindexZeroReshaped c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops c.subscripts a v))) ∧
    (a.reshaped = true → ∀ v (ind : SCartesianIndex2) k,
      0 < a.target.alignedSize.val →
      a.target.alignedSize.val < a.source.alignedSize.val →
      1 ≤ ind.i.val →
      ind.i.val * a.target.alignedSize.val ≤ a.source.alignedSize.val →
      denseCoordinate (c.parent.axes a.parent) [ind.j] = some k →
      let off := k * a.source.alignedSize.val.toNat +
        (ind.i.val - 1).toNat * a.target.alignedSize.val.toNat
      let result := m598_setindexCartesian c.convert c.parent.ops a v ind
      if PaddingCompatible a.source a.target then
        match c.convert a.target v with
        | .error e => result = .error e
        | .ok bytes => ∃ a', result = .ok a' ∧ a'.target = a.target ∧
            a'.source = a.source ∧ a'.rank = a.rank ∧ a'.reshaped = a.reshaped ∧
            c.parent.axes a'.parent = c.parent.axes a.parent ∧
            (c.parent.bytes a'.parent).length = (c.parent.bytes a.parent).length ∧
            ∀ b < (c.parent.bytes a.parent).length,
              ValueByte a.source (b % a.source.alignedSize.val.toNat) →
              (c.parent.bytes a'.parent)[b]? =
                if off ≤ b ∧ b < off + bytes.length then bytes[b - off]?
                else (c.parent.bytes a.parent)[b]?
      else result = .error .padding)

/-- The internal byte implementations satisfy the same byte-storage specification as the
public methods, including the target-larger, target-smaller, equal-width and singleton cases. -/
def InternalByteAccess : Prop :=
  ∀ {T S A V : Type} (c : AccessInterface T S A V) (a : ReinterpretArray T S A),
    AccessLaws c a →
    (∀ i tail, PaddingCompatible a.target a.source →
      ReadResult c.parent a (i :: tail)
        (if a.reshaped then m527_getindexReshaped c.bounds c.parent.ops.get c.parent.style c.first a i tail
         else m473_getindexNonReshaped c.bounds c.parent.ops.get a i tail)) ∧
    (∀ v i tail, PaddingCompatible a.source a.target →
      WriteResult c a v (i :: tail)
        (if a.reshaped then m688_setindexReshaped c.bounds c.convert c.parent.ops c.parent.style c.first a v i tail
         else m619_setindexNonReshaped c.bounds c.convert c.parent.ops a v i tail))

/-- Array padding permits access exactly when each value byte of the accessing type
lands on a value byte in the stored type's repeating storage layout. -/
def ArrayPadding : Prop :=
  ∀ t s, ValidStorageLayout t → ValidStorageLayout s →
    t.isBits = true → s.isBits = true → ¬ BitPadded t → ¬ BitPadded s →
    (∀ b, m772_arraySubpadding t s = .ok b ↔ (b = true ↔ PaddingCompatible t s)) ∧
    (∀ {T S A : Type} (a : ReinterpretArray T S A), a.target = t → a.source = s →
      (a.readable = true → PaddingCompatible t s) →
      (a.writable = true → PaddingCompatible s t) →
      (m237_checkReadable a = .ok () ↔ PaddingCompatible t s) ∧
      (m244_checkWritable a = .ok () ↔ PaddingCompatible s t) ∧
      (¬ PaddingCompatible t s → m237_checkReadable a = .error .padding) ∧
      (¬ PaddingCompatible s t → m244_checkWritable a = .error .padding))

inductive LayoutNode : TypeLayout → TypeLayout → Prop where
  | root (t : TypeLayout) : LayoutNode t t
  | field (root parent child : TypeLayout) (off : Nat) :
      LayoutNode root parent → (off,child) ∈ parent.fields → LayoutNode root child
  | member (root parent child : TypeLayout) :
      LayoutNode root parent → child ∈ parent.members → LayoutNode root child

def RecursiveIsbitsLayout (t : TypeLayout) : Prop :=
  ∀ node, LayoutNode t node → node.isBits = true ∧ node.union = false

def JuliaDatatypeSizeBound (t : TypeLayout) : Prop :=
  t.alignedSize.val ≤ IntTy.max .u32

def ArrayPaddingR9 : Prop :=
  ∀ t s, ValidStorageLayout t → ValidStorageLayout s →
    JuliaDatatypeSizeBound t → JuliaDatatypeSizeBound s →
    t.isBits = true → s.isBits = true →
    RecursiveIsbitsLayout t → RecursiveIsbitsLayout s →
    ¬ BitPadded t → ¬ BitPadded s →
    (∀ b, m772_arraySubpadding t s = .ok b ↔
      (b = true ↔ PaddingCompatible t s)) ∧
    (∀ {T S A : Type} (a : ReinterpretArray T S A), a.target = t → a.source = s →
      (a.readable = true → PaddingCompatible t s) →
      (a.writable = true → PaddingCompatible s t) →
      (m237_checkReadable a = .ok () ↔ PaddingCompatible t s) ∧
      (m244_checkWritable a = .ok () ↔ PaddingCompatible s t) ∧
      (¬ PaddingCompatible t s → ∃ e, m237_checkReadable a = .error e) ∧
      (¬ PaddingCompatible s t → ∃ e, m244_checkWritable a = .error e))

def FullPaddingLayoutAnyErrorR4 : Prop :=
  FullByteMask ∧
  (∀ (layout : TypeLayout) (offset : I64) (used : List Bool),
    (m756_fillNonpadding layout offset used).length = used.length) ∧
  (∀ (layout : TypeLayout),
    (m828_hasBitPadding layout = true →
      ∃ e, m750_nonPaddingBytes layout = .error e) ∧
    (m828_hasBitPadding layout = false →
      ∃ mask, m750_nonPaddingBytes layout = .ok mask ∧
        mask.length = layout.alignedSize.val.toNat ∧
        m812_structSubpadding layout layout = .ok true ∧
        ∃ ps, m816_packedsize layout = .ok ps ∧ ps ≤ layout.alignedSize.val.toNat)) ∧
  (∀ (id size : Nat),
    m824_ispacked (primitiveLayout id size) = true ∧
    m828_hasBitPadding (primitiveLayout id size) = false ∧
    m816_packedsize (primitiveLayout id size) = .ok (JInt.lit .i64 size).val.toNat) ∧
  BitPaddingDetection

def PaddingHelpersR9 : Prop :=
  FullPaddingLayoutAnyErrorR4 ∧
  ArrayPaddingR9 ∧
  (∀ t, ValidStorageLayout t → t.isBits = true → RecursiveIsbitsLayout t → ¬ BitPadded t →
    ∃ mask, m750_nonPaddingBytes t = .ok mask ∧ mask.length = t.alignedSize.val.toNat ∧
      (∀ b < mask.length, mask[b]? = some true ↔ ValueByte t b) ∧
      m816_packedsize t = .ok
        ((List.range t.alignedSize.val.toNat).filter (fun b => mask[b]?.getD false)).length)
  ∧ (∀ t, ValidStorageLayout t → t.isBits = true → BitPadded t →
    ∃ e, m750_nonPaddingBytes t = .error e)
  ∧ (∀ t s, ValidStorageLayout t → ValidStorageLayout s →
    t.isBits = true → s.isBits = true →
    RecursiveIsbitsLayout t → RecursiveIsbitsLayout s →
    ¬ BitPadded t → ¬ BitPadded s →
    ∀ b, m812_structSubpadding t s = .ok b ↔
      (b = true ↔ t.alignedSize = s.alignedSize ∧
        ∀ n < t.alignedSize.val.toNat, ValueByte t n ↔ ValueByte s n))
/-- Successful constructors cache flags by periodic value-byte inclusion for recursive isbits layouts without unions. -/
def ConstructorPaddingFlags : Prop :=
  ∀ {T S A : Type} t s (p : ArrayInput A),
    ValidStorageLayout t → ValidStorageLayout s →
    t.isBits = true → s.isBits = true →
    RecursiveIsbitsLayout t → RecursiveIsbitsLayout s → ShapeValid p →
    (∀ a : ReinterpretArray T S (ArrayInput A), m73_reinterpret t s p = .ok a →
      (a.readable = true ↔ PaddingCompatible t s) ∧ (a.writable = true ↔ PaddingCompatible s t)) ∧
    (∀ a : ReinterpretArray T S (ArrayInput A), m107_reinterpretReshape t s p = .ok a →
      (a.readable = true ↔ PaddingCompatible t s) ∧ (a.writable = true ↔ PaddingCompatible s t))

/-- The error message contains both type names verbatim, including unusual Unicode names. -/
def PaddingDiagnostic : Prop :=
  ArrayPadding ∧ ∀ p : PaddingErrorModel,
    (∃ before after : String, m741_showerror p = before ++ p.source ++ after) ∧
    (∃ before after : String, m741_showerror p = before ++ p.target ++ after)

/-- All compatible primitive layouts and arbitrary recursive layouts receive the complete
semantic mask, packed-size, and subpadding specifications. -/
def PaddingHelpers : Prop :=
  FullPaddingLayout ∧ ArrayPadding ∧
  (∀ t, ValidStorageLayout t → t.isBits = true → ¬ BitPadded t →
    ∃ mask, m750_nonPaddingBytes t = .ok mask ∧ mask.length = t.alignedSize.val.toNat ∧
      (∀ b < mask.length, mask[b]? = some true ↔ ValueByte t b) ∧
      m816_packedsize t = .ok ((List.range t.alignedSize.val.toNat).filter (fun b => mask[b]?.getD false)).length)
  ∧ (∀ t, ValidStorageLayout t → t.isBits = true → BitPadded t →
    m750_nonPaddingBytes t = .error .argument)
  ∧ (∀ t s, ValidStorageLayout t → ValidStorageLayout s →
    t.isBits = true → s.isBits = true → ¬ BitPadded t → ¬ BitPadded s →
    ∀ b, m812_structSubpadding t s = .ok b ↔
      (b = true ↔ t.alignedSize = s.alignedSize ∧
        ∀ n < t.alignedSize.val.toNat, ValueByte t n ↔ ValueByte s n))

def axisContains (ax : Axis) (index : I64) : JuliaLean.base.abstractarray.Result Bool :=
  JuliaLean.base.abstractarray.checkindexReal (fun a : Axis => .ok (a.first.val : Int))
    (fun a : Axis => .ok (a.first.val + a.length.val - (1 : Int)))
    (fun (lo : Int) (i : I64) => .ok (decide (lo ≤ i.val)))
    (fun (i : I64) (hi : Int) => .ok (decide (i.val ≤ hi))) ax index

def axesContain : List Axis → List I64 → JuliaLean.base.abstractarray.Result Bool
  | axs, [] => JuliaLean.base.abstractarray.checkboundsIndicesNil (fun ax => .ok ax.length) axs
  | axs, i :: inds => JuliaLean.base.abstractarray.checkboundsIndicesCons ⟨one, one⟩ axisContains
      (fun tail (_ : List I64) => axesContain tail inds) axs i inds

def ValidCoordinates : List Axis → List I64 → Prop
  | axs, [] => ∀ ax ∈ axs, ax.length.val = 1
  | [], i :: inds => i.val = 1 ∧ ValidCoordinates [] inds
  | ax :: axs, i :: inds => ax.first.val ≤ i.val ∧ i.val < ax.first.val + ax.length.val ∧
      ValidCoordinates axs inds

def linearBounds (axs : List Axis) : Int × Int :=
  match axs with
  | [ax] => (ax.first.val, ax.first.val + ax.length.val - 1)
  | _ => (1, ((axs.map (fun ax => ax.length.val.toNat)).prod : Nat))

def integerBounds {A : Type} (axes : A → List Axis) (a : A) (inds : List I64) :
    JuliaLean.base.abstractarray.Result Bool :=
  match inds with
  | [i] => JuliaLean.base.abstractarray.checkboundsOne
      (fun a => .ok (linearBounds (axes a)))
      (JuliaLean.base.abstractarray.checkindexReal
        (fun ax : Int × Int => .ok ax.1) (fun ax : Int × Int => .ok ax.2)
        (fun (lo : Int) (i : I64) => .ok (decide (lo ≤ i.val)))
        (fun (i : I64) (hi : Int) => .ok (decide (i.val ≤ hi)))) a i
  | _ => JuliaLean.base.abstractarray.checkboundsMany (fun a => .ok (axes a)) axesContain a inds

def ValidIntegerCoordinates (axs : List Axis) (inds : List I64) : Prop :=
  match inds with
  | [i] => (linearBounds axs).1 ≤ i.val ∧ i.val ≤ (linearBounds axs).2
  | _ => ValidCoordinates axs inds

/-- Integer assignedness is false outside arbitrary offset axes, including omitted or extra
singleton coordinates. The real AbstractArray checkbounds/checkindex models are instantiated. -/
def Assignedness : Prop :=
  ∀ {T S A : Type} (axes : ReinterpretArray T S A → List Axis)
      (route : PointerRoute A) (a : ReinterpretArray T S A) (inds : List I64),
    m432_isassigned (fun a inds => (integerBounds axes a inds).toOption.getD false)
      route.check a inds = true ↔ ValidIntegerCoordinates (axes a) inds

/-- Both integer endpoint sentinels are included in the next/previous inverse contract. -/
def NextPrevious : Prop :=
  ∀ (k : I64) (ind : SCartesianIndex2), 1 < k.val → 1 ≤ ind.i.val → ind.i.val ≤ k.val →
    m282_prevIndex k (m280_nextIndex k ind) = ind ∧
    m280_nextIndex k (m282_prevIndex k ind) = ind

/-- Every parent-indexability overload participates in a checked public read whose result is
specified by logical bytes, rather than by its own dispatch Boolean. -/
def PointerEligibility : Prop := AllReads ∧ AllWrites

/-- General Cartesian get/set obey the existing arbitrary-parent lens contract; coordinate
routing additionally preserves the independent column-major index of arbitrary trailing axes. -/
def CartesianAccess : Prop := CartesianParentLens ∧ AllReads ∧ AllWrites


namespace CartesianRange
open JuliaLean.base.range
local instance : JFirst Axis I64 := ⟨fun ax => .ok ax.first⟩
local instance : JLast Axis I64 := ⟨fun ax => .ok (ax.first + ax.length - one)⟩
local instance : JStep Axis I64 := ⟨fun _ => .ok one⟩
local instance : JEltype Axis I64 := ⟨⟩
local instance : JEq I64 I64 := ⟨fun x y => x == y⟩
local instance : JConvert I64 I64 := ⟨fun x => .ok x⟩
local instance : JIsempty Axis := ⟨fun ax => .ok (decide (ax.length.val ≤ 0))⟩
def start (ax : Axis) : Option (I64 × I64) :=
  (iterate_OrdinalRange ax).toOption.getD none
def step (ax : Axis) (j : I64) : Option (I64 × I64) :=
  (iterate_OrdinalRange_state ax j).toOption.getD none
end CartesianRange

/-- Every finite Cartesian iterator starts and stops at its declared endpoints, visits
all channel coordinates before advancing the parent coordinate, and has no out-of-axis step.
The parent ordinal-range iteration is the source-mirrored range implementation. -/
def FullCartesianTransitions : Prop :=
  ∀ (k : Nat) (iter : SCartesianIndices2 k), 1 < k → (k : Int) ≤ IntTy.max .i64 →
    0 ≤ iter.indices2.length.val →
    iter.indices2.first.val + iter.indices2.length.val - 1 ≤ IntTy.max .i64 →
    (iter.indices2.length.val = 0 → m309_indicesIterate CartesianRange.start iter = none) ∧
    (0 < iter.indices2.length.val →
      m309_indicesIterate CartesianRange.start iter =
        some (m301_indicesFirst iter, (one, iter.indices2.first, iter.indices2.first))) ∧
    (∀ (i j : I64), 1 ≤ i.val → i.val ≤ k → iter.indices2.first.val ≤ j.val →
      j.val < iter.indices2.first.val + iter.indices2.length.val →
      let next := m316_indicesIterateState CartesianRange.step iter i j j
      (next = none ↔ i.val = k ∧ j.val = iter.indices2.first.val + iter.indices2.length.val - 1) ∧
      (∀ ind state, next = some (ind, state) →
        1 ≤ ind.i.val ∧ ind.i.val ≤ k ∧
        iter.indices2.first.val ≤ ind.j.val ∧
        ind.j.val < iter.indices2.first.val + iter.indices2.length.val ∧
        scartesianRank (JInt.lit .i64 k) ind =
          scartesianRank (JInt.lit .i64 k) ⟨i,j⟩ + 1))


abbrev NestedOutcome (T S P A : Type) :=
  ReinterpretOutcome (ArrayInput A) (ReinterpretArray T S (ArrayInput A))
    (ReinterpretArray T S (ArrayInput (ReinterpretArray S P (ArrayInput A))))
def rootParent {T S P A : Type} : NestedOutcome T S P A → ArrayInput A
  | .parent p => p
  | .view a => a.parent
  | .nested a => a.parent.parent.parent

def nestedStorageLaw {T S P A : Type} (target : TypeLayout)
    (a : ReinterpretArray S P (ArrayInput A)) (result : NestedOutcome T S P A) : Prop :=
  rootParent result = a.parent ∧
  (match result with
  | .parent _ => target.id = a.source.id
  | .view v => v.target = target ∧ v.source = a.source
  | .nested v => v.target = target ∧ v.source = a.target ∧ v.parent.parent = a) ∧
  (target.alignedSize = a.target.alignedSize ∨ target.alignedSize = a.source.alignedSize ∨
      a.target.alignedSize = a.source.alignedSize →
    ∀ v, result ≠ .nested v)

/-- Reinterpreting an existing reshaped view never copies or changes its root storage,
uses the requested element type, and removes an unnecessary nested layer whenever any two
of the three storage widths agree. Constructor validation errors remain visible. -/
def FullNestedStorage : Prop :=
  ∀ {T S P A : Type} (target : TypeLayout)
      (size : ArrayInput A → List I64) (axes : ArrayInput A → List Axis)
      (a : ReinterpretArray S P (ArrayInput A)),
    match m191_reinterpretReshapedParent (T := T) target size axes a with
    | .error _ => True
    | .ok result => nestedStorageLaw target a result


def reductionBoxGet (lo hi : I64) (k : Nat) (_ : Unit) (ind : SCartesianIndex2) : RResult Nat :=
  if 1 ≤ ind.i.val ∧ ind.i.val ≤ k ∧ lo.val ≤ ind.j.val ∧ ind.j.val ≤ hi.val then
    .ok 1 else .error .bounds

/-- Reductions on a valid static Cartesian box terminate without reading outside that box,
including offset parent axes at either machine-integer endpoint. -/
def FullReductionBounds : Prop :=
  ∀ (k : Nat) (lo hi block : I64), 2 ≤ k → (k : Int) ≤ IntTy.max .i64 →
    lo.val ≤ hi.val → 0 < block.val →
    ∃ value, m956_mapreduceImpl (K := k) (reductionBoxGet lo hi k)
      (fun (_ : Unit) x => .ok x) (fun (_ : Unit) x y => .ok (x+y)) () () ()
      ⟨one, lo⟩ ⟨JInt.lit .i64 k, hi⟩ block = some (.ok value)

def reductionParentGet (value : Bytes) (axis : Axis) (inds : List I64) : RResult Bytes :=
  match inds with
  | [j] => if axis.first.val ≤ j.val ∧ j.val < axis.first.val + axis.length.val then
      .ok value else .error .bounds
  | _ => .error .bounds

def reductionView (k : Nat) (axis : Axis) : ReinterpretArray Unit Unit Axis :=
  ⟨axis, 2, primitiveLayout 1 1, primitiveLayout 2 k, true, true, true⟩

/-- Public reduction over a valid reshaped view must terminate and never read a parent element
outside its axis. This includes nonempty axes at either native integer endpoint. -/
def PublicReductionSafety : Prop :=
  ∀ (k : Nat) (bytes : Bytes) (axis : Axis) (block : I64), bytes.length = k →
    2 ≤ k → (k : Int) ≤ IntTy.max .i64 →
    0 < axis.length.val → axis.first.val + axis.length.val - 1 ≤ IntTy.max .i64 →
    0 < block.val →
    ∃ value, m946_mapreduce (K := k)
      (fun _ a => m290_eachindexReshaped (K := k) (fun _ ax => ax) a)
      (fun _ => ()) (fun (_ : Unit) (_ : Unit) _ _ => .ok 0)
      (fun (_ : Unit) (_ : Unit) => block) (m454_getindexCartesian (reductionParentGet bytes))
      (fun (_ : Unit) bytes => .ok bytes.length)
      (fun (_ : Unit) x y => .ok (x+y)) () () (.staticCartesian k)
      (reductionView k axis) = some (.ok value)


namespace RangeAccess
open JuliaLean.base.range
local instance : JOneunit I64 := ⟨one⟩
local instance : JConvert I64 I64 := ⟨fun i => .ok i⟩
local instance : JLt I64 I64 := ⟨fun i j => decide (i.val < j.val)⟩
local instance : JLe I64 I64 := ⟨fun i j => decide (i.val ≤ j.val)⟩
local instance : JThrowBoundserror (UnitRange I64) I64 :=
  ⟨fun _ _ => .error (.jl .boundsError)⟩
def get (ax : Axis) (i : I64) : RResult I64 :=
  (_getindex_UnitRange (T := I64) (I := I64) (D := I64) (E := I64)
    ⟨ax.first, ax.first + ax.length - one⟩ i).mapError (fun _ => .bounds)
end RangeAccess

def axisCheck (ax : Axis) (i : I64) : Bool :=
  (JuliaLean.base.abstractarray.checkindexReal
    (fun ax : Axis => .ok ax.first.val)
    (fun ax : Axis => .ok (ax.first.val + ax.length.val - 1))
    (fun (lo : Int) (i : I64) => .ok (decide (lo ≤ i.val)))
    (fun (i : I64) (hi : Int) => .ok (decide (i.val ≤ hi))) ax i).toOption.getD false

def iteratorBounds {k : Nat} (iter : SCartesianIndices2 k) (i j : I64) : RResult Unit :=
  if axisCheck ⟨one, JInt.lit .i64 k⟩ i && axisCheck iter.indices2 j then
    .ok () else .error .bounds

/-- The Cartesian iterator's dimensions, axes and indexing enumerate exactly the Cartesian
product of its channel interval and outer axis, including bounds errors on either coordinate. -/
def IteratorDomain : Prop :=
  ∀ (k : Nat) (ax : Axis), 1 < k → (k : Int) ≤ IntTy.max .i64 →
    ValidAxes [ax] →
    (∀ i j,
      m304_indicesGet iteratorBounds RangeAccess.get (⟨ax⟩ : SCartesianIndices2 k) i j =
        if 1 ≤ i.val ∧ i.val ≤ k ∧ ax.first.val ≤ j.val ∧ j.val < ax.first.val + ax.length.val
        then .ok ⟨i,j⟩ else .error .bounds) ∧
    (m298_indicesSize (⟨ax⟩ : SCartesianIndices2 k)).1 *
      (m298_indicesSize (⟨ax⟩ : SCartesianIndices2 k)).2.val.toNat = k * ax.length.val.toNat ∧
    (∀ i j, ((m299_indicesAxes (⟨ax⟩ : SCartesianIndices2 k)).zip [i,j]).all
        (fun pair => axisCheck pair.1 pair.2) = true ↔
      1 ≤ i.val ∧ i.val ≤ k ∧ ax.first.val ≤ j.val ∧ j.val < ax.first.val + ax.length.val) ∧
    (m301_indicesFirst (⟨ax⟩ : SCartesianIndices2 k)).i.val = 1 ∧
    (m301_indicesFirst (⟨ax⟩ : SCartesianIndices2 k)).j.val = ax.first.val ∧
    (m302_indicesLast (⟨ax⟩ : SCartesianIndices2 k)).i.val = k ∧
    (m302_indicesLast (⟨ax⟩ : SCartesianIndices2 k)).j.val = ax.first.val + ax.length.val - 1

/-- Constructed eachindex domains have the complete channel/parent Cartesian product.
Invalid channel counts fail before any indexing. -/
def EachindexDomains : Prop :=
  ∀ {T S A : Type} (k : Nat) (each : IndexStyleModel → A → Axis)
      (a : ReinterpretArray T S A),
    (∀ iter, m290_eachindexReshaped (K := k) each a = .ok iter →
      ∀ (i j : I64), (1 ≤ i.val ∧ i.val ≤ k ∧
        iter.indices2.first.val ≤ j.val ∧ j.val < iter.indices2.first.val + iter.indices2.length.val) ↔
        (1 ≤ i.val ∧ i.val ≤ k ∧
        (each .linear a.parent).first.val ≤ j.val ∧
        j.val < (each .linear a.parent).first.val + (each .linear a.parent).length.val)) ∧
    (k ≤ 1 → m290_eachindexReshaped (K := k) each a = .error .assertion) ∧
    (1 < k → ∃ iter, m290_eachindexReshaped (K := k) each a = .ok iter)

def AllIteration : Prop :=
  NextPrevious ∧ FullCartesianTransitions ∧ IteratorDomain ∧ EachindexDomains

/-- Cartesian pass-through routing preserves column-major location at every trailing rank
and offset axis. The external CartesianIndices interface has its own coordinate/rank law. -/
def CartesianRouting : Prop :=
  ∀ {A : Type} (k : Nat) (each : IndexStyleModel → A → SCartesianIndices2 k)
      (p : ParentInterface A) (s : TypeLayout) (cartesian : List Axis → I64 → List I64)
      (a : A) (ind : SCartesianIndex2),
    ParentLaws p s →
    (∀ (axs : List Axis) (i : I64), 1 ≤ i.val →
      i.val ≤ (((axs.map (fun ax => ax.length.val.toNat)).prod : Nat) : Int) →
      coordinateOffset axs (cartesian axs i) = some (i.val - 1).toNat) →
    0 < (p.axes a).length →
    1 ≤ ind.i.val → ind.i.val ≤ ((p.axes a).headD ⟨one,zero⟩).length.val →
    let outer := (each (.staticCartesian k) a).indices2
    outer.first.val ≤ ind.j.val → ind.j.val < outer.first.val + outer.length.val →
    outer.length.val.toNat = (((p.axes a).drop 1).map (fun ax => ax.length.val.toNat)).prod →
    (coordinateOffset ((p.axes a).drop 1)
      (m359_scartesian2Trailing each p.axes cartesian (.staticCartesian k) a ind) =
        some (ind.j.val - outer.first.val).toNat) ∧
    (m347_getindexCartesian each p.axes cartesian p.ops.get (.staticCartesian k) a ind =
      .ok (byteWindow (p.bytes a)
        (((ind.i.val - 1).toNat +
          ((p.axes a).headD ⟨one,zero⟩).length.val.toNat *
            (ind.j.val - outer.first.val).toNat) * s.alignedSize.val.toNat)
        s.alignedSize.val.toNat)) ∧
    (∀ value, ValidElement s value →
      ∃ a', m352_setindexCartesian each p.axes cartesian
        (fun a value inds => p.ops.set a inds value) (.staticCartesian k) a value ind = .ok a' ∧
        p.bytes a' = overwriteBytes (p.bytes a)
          (((ind.i.val - 1).toNat +
            ((p.axes a).headD ⟨one,zero⟩).length.val.toNat *
              (ind.j.val - outer.first.val).toNat) * s.alignedSize.val.toNat) value)

/-- Reshaped reads preserve the parent value bytes for every rank, layout and index.
The internal path includes both larger-target loops, scalar conversion, singleton and slices. -/
def ReshapedReads : Prop :=
  ∀ {T S A V : Type} (c : AccessInterface T S A V) (a : ReinterpretArray T S A),
    AccessLaws c a → a.reshaped = true →
    (∀ i tail, (i :: tail).length = a.rank → PaddingCompatible a.target a.source →
      ReadResult c.parent a (i :: tail)
        (m527_getindexReshaped c.bounds c.parent.ops.get c.parent.style c.first a i tail)) ∧
    (∀ i tail, (i :: tail).length = a.rank → ReadResult c.parent a (i :: tail)
      (m436_getindex c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get a i tail)) ∧
    (∀ i, ReadResult c.parent a [i]
      (m442_getindexLinear c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get c.subscripts a i)) ∧
    (a.rank = 0 → ReadResult c.parent a []
      (m430_getindexZeroReshaped c.read c.parent.pointerCapable c.parent.style c.first c.bounds c.parent.ops.get c.subscripts a))

/-- Reshaped writes replace precisely the selected value bytes, preserving every other value
byte and the parent shape in every internal branch and public indexing overload. -/
def ReshapedWrites : Prop :=
  ∀ {T S A V : Type} (c : AccessInterface T S A V) (a : ReinterpretArray T S A),
    AccessLaws c a → a.reshaped = true →
    (∀ v i tail, (i :: tail).length = a.rank → PaddingCompatible a.source a.target →
      WriteResult c a v (i :: tail)
        (m688_setindexReshaped c.bounds c.convert c.parent.ops c.parent.style c.first a v i tail)) ∧
    (∀ v i tail, (i :: tail).length = a.rank → WriteResult c a v (i :: tail)
      (m582_setindex c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops a v i tail)) ∧
    (∀ v i, WriteResult c a v [i]
      (m588_setindexLinear c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops c.subscripts a v i)) ∧
    (a.rank = 0 → ∀ v, WriteResult c a v []
      (m580_setindexZeroReshaped c.write c.parent.pointerCapable c.parent.style c.first c.bounds c.convert c.parent.ops c.subscripts a v))

def ReshapedReadsWrites : Prop := ReshapedReads ∧ ReshapedWrites

/-- Static Cartesian routing handles every trailing rank and offset axis. The specialized
channel getter selects the original parent slice; its setter obeys the arbitrary-parent lens. -/
def FullCartesianRouting : Prop :=
  CartesianRouting ∧ CartesianParentLens ∧
  (∀ {T S A : Type} (parent : ParentOps A) (a : ReinterpretArray T S A)
      (i j : I64) (old : Bytes),
    a.readable = true → parent.get a.parent [j] = .ok old →
    0 < a.target.alignedSize.val → 1 ≤ i.val →
    (i.val - 1).toNat * a.target.alignedSize.val.toNat +
      a.target.alignedSize.val.toNat ≤ old.length →
    (old.length : Int) ≤ IntTy.max .i64 →
    m454_getindexCartesian parent.get a ⟨i, j⟩ =
      .ok (byteWindow old ((i.val - 1).toNat * a.target.alignedSize.val.toNat)
        a.target.alignedSize.val.toNat))


/-- Runtime fields appear in storage order, do not overlap, and have valid layouts at every depth. -/
def OrderedLayout (t : TypeLayout) : Prop :=
  ∀ node, LayoutNode t node →
    ValidStorageLayout node ∧
    node.fields.Pairwise (fun x y => x.1 + x.2.alignedSize.val.toNat ≤ y.1)

def ScalarConversionR4 : Prop :=
  ∀ (output input : TypeLayout) (bytes initial : Bytes), OrderedLayout output → OrderedLayout input →
    ValidElement input bytes → ValidElement output initial →
    (output.isBits = false ∨ input.isBits = false ∨ BitPadded output ∨ BitPadded input →
      ∃ e, m882_reinterpret output input bytes initial = .error e) ∧
    (output.isBits = true → input.isBits = true →
      RecursiveIsbitsLayout output → RecursiveIsbitsLayout input →
      ¬ BitPadded output → ¬ BitPadded input →
      if (payload output initial).length = (payload input bytes).length then
        ∃ result, m882_reinterpret output input bytes initial = .ok result ∧
          ValidElement output result ∧ payload output result = payload input bytes ∧
          ∃ back, m882_reinterpret input output result bytes = .ok back ∧
            payload input back = payload input bytes
      else ∃ e, m882_reinterpret output input bytes initial = .error e)

def PackedTransfersR4 : Prop :=
  ∀ (layout : TypeLayout) (input output : Bytes) (writeOffset readOffset : I64), OrderedLayout layout →
    layout.isBits = true → RecursiveIsbitsLayout layout → ¬ BitPadded layout →
    0 ≤ writeOffset.val → 0 ≤ readOffset.val →
    (output.length : Int) ≤ IntTy.max .i64 → (input.length : Int) ≤ IntTy.max .i64 →
    (readOffset.val.toNat + layout.alignedSize.val.toNat ≤ input.length →
      writeOffset.val.toNat + (payload layout
        (byteWindow input readOffset.val.toNat layout.alignedSize.val.toNat)).length ≤ output.length →
      m842_copytopacked layout output input writeOffset readOffset =
        .ok (overwriteBytes output writeOffset.val.toNat
          (payload layout (byteWindow input readOffset.val.toNat layout.alignedSize.val.toNat)))) ∧
    (writeOffset.val.toNat + layout.alignedSize.val.toNat ≤ output.length →
      readOffset.val.toNat + (payload layout
        (byteWindow output writeOffset.val.toNat layout.alignedSize.val.toNat)).length ≤ input.length →
      ∃ result, m862_copyfrompacked layout output input writeOffset readOffset = .ok result ∧
        result.length = output.length ∧
        payload layout (byteWindow result writeOffset.val.toNat layout.alignedSize.val.toNat) =
          byteWindow input readOffset.val.toNat
            (payload layout (byteWindow output writeOffset.val.toNat layout.alignedSize.val.toNat)).length ∧
        ∀ b < output.length,
          (b < writeOffset.val.toNat ∨ writeOffset.val.toNat + layout.alignedSize.val.toNat ≤ b ∨
            ¬ ValueByte layout (b - writeOffset.val.toNat)) → result[b]? = output[b]?)

def PaddingConversionR4 : Prop :=
  ScalarConversionR4 ∧ PackedTransfersR4 ∧
  ∀ (output input : TypeLayout) (bytes initial : Bytes), OrderedLayout output → OrderedLayout input →
    output.isBits = true → input.isBits = true →
    RecursiveIsbitsLayout output → RecursiveIsbitsLayout input →
    ¬ BitPadded output → ¬ BitPadded input →
    ValidElement input bytes → ValidElement output initial →
    (payload output initial).length = (payload input bytes).length →
    ∃ result, m913_reinterpretPadding output input bytes initial = .ok result ∧
      ValidElement output result ∧ payload output result = payload input bytes

/-- Scalar conversion preserves the entire ordered sequence of value bytes at every field
depth, rejects non-isbits/bit-padded layouts and unequal packed sizes, and round-trips values. -/
def ScalarConversion : Prop :=
  ∀ (output input : TypeLayout) (bytes initial : Bytes), OrderedLayout output → OrderedLayout input →
    ValidElement input bytes → ValidElement output initial →
    (output.isBits = false ∨ input.isBits = false ∨ BitPadded output ∨ BitPadded input →
      m882_reinterpret output input bytes initial = .error .argument) ∧
    (output.isBits = true → input.isBits = true → ¬ BitPadded output → ¬ BitPadded input →
      if (payload output initial).length = (payload input bytes).length then
        ∃ result, m882_reinterpret output input bytes initial = .ok result ∧
          ValidElement output result ∧ payload output result = payload input bytes ∧
          ∃ back, m882_reinterpret input output result bytes = .ok back ∧
            payload input back = payload input bytes
      else m882_reinterpret output input bytes initial = .error .argument)

/-- Recursive packing transfers the ordered value bytes and preserves surrounding output.
Unpacking writes only value positions, leaving destination padding untouched. -/
def PackedTransfers : Prop :=
  ∀ (layout : TypeLayout) (input output : Bytes) (writeOffset readOffset : I64), OrderedLayout layout →
    layout.isBits = true → ¬ BitPadded layout →
    0 ≤ writeOffset.val → 0 ≤ readOffset.val →
    (output.length : Int) ≤ IntTy.max .i64 → (input.length : Int) ≤ IntTy.max .i64 →
    (readOffset.val.toNat + layout.alignedSize.val.toNat ≤ input.length →
      writeOffset.val.toNat + (payload layout
        (byteWindow input readOffset.val.toNat layout.alignedSize.val.toNat)).length ≤ output.length →
      m842_copytopacked layout output input writeOffset readOffset =
        .ok (overwriteBytes output writeOffset.val.toNat
          (payload layout (byteWindow input readOffset.val.toNat layout.alignedSize.val.toNat)))) ∧
    (writeOffset.val.toNat + layout.alignedSize.val.toNat ≤ output.length →
      readOffset.val.toNat + (payload layout
        (byteWindow output writeOffset.val.toNat layout.alignedSize.val.toNat)).length ≤ input.length →
      ∃ result, m862_copyfrompacked layout output input writeOffset readOffset = .ok result ∧
        result.length = output.length ∧
        payload layout (byteWindow result writeOffset.val.toNat layout.alignedSize.val.toNat) =
          byteWindow input readOffset.val.toNat
            (payload layout (byteWindow output writeOffset.val.toNat layout.alignedSize.val.toNat)).length ∧
        ∀ b < output.length,
          (b < writeOffset.val.toNat ∨ writeOffset.val.toNat + layout.alignedSize.val.toNat ≤ b ∨
            ¬ ValueByte layout (b - writeOffset.val.toNat)) → result[b]? = output[b]?)

/-- Explicit padding conversion preserves value bytes whenever packed sizes agree. -/
def PaddingConversion : Prop :=
  ScalarConversion ∧ PackedTransfers ∧
  ∀ (output input : TypeLayout) (bytes initial : Bytes), OrderedLayout output → OrderedLayout input →
    output.isBits = true → input.isBits = true → ¬ BitPadded output → ¬ BitPadded input →
    ValidElement input bytes → ValidElement output initial →
    (payload output initial).length = (payload input bytes).length →
    ∃ result, m913_reinterpretPadding output input bytes initial = .ok result ∧
      ValidElement output result ∧ payload output result = payload input bytes

/-- Joint iteration accepts precisely matching parent domains and never silently truncates
a longer input. Every same-file eachindex callee uses the actual source model. -/
def SharedIteration : Prop :=
  ∀ {T S A : Type} (k : Nat) (each : IndexStyleModel → A → Axis)
      (axes : ReinterpretArray T S A → List Axis)
      (a : ReinterpretArray T S A) (rest : List (ReinterpretArray T S A)),
    1 < k →
    let run := m291_eachindex
      (fun _ q => m290_eachindexReshaped (K := k) each q)
      (fun _ _ => (JuliaLean.base.abstractarray.throwEachindexMismatch
        (fun a bs => String.intercalate ", " (a :: bs)) "axes" "" []).mapError (fun _ => .argument))
      (.staticCartesian k) a rest axes
    (run = .error .argument ↔
      ∃ b ∈ rest, each .linear b.parent ≠ each .linear a.parent) ∧
    (∀ iter, run = .ok iter →
      (m298_indicesSize iter).1 * (m298_indicesSize iter).2.val.toNat =
        k * (each .linear a.parent).length.val.toNat ∧
      ∀ b ∈ rest, iter.indices2 = each .linear b.parent)

/-- Generic reductions visit every channel/column element once and preserve a natural-valued
sum, for all valid offset boxes and positive block sizes. The getter's law is its own array API. -/
def FullReductionCorrectness : Prop :=
  ∀ {A : Type} (k : Nat) (axis : Axis) (block : I64) (a : A)
      (get : A → SCartesianIndex2 → RResult Nat) (values : SCartesianIndex2 → Nat),
    2 ≤ k → (k : Int) ≤ IntTy.max .i64 → 0 < axis.length.val →
    axis.first.val + axis.length.val - 1 ≤ IntTy.max .i64 → 0 < block.val →
    (∀ i j, get a ⟨i,j⟩ =
      if 1 ≤ i.val ∧ i.val ≤ k ∧ axis.first.val ≤ j.val ∧ j.val < axis.first.val + axis.length.val
      then .ok (values ⟨i,j⟩) else .error .bounds) →
    m956_mapreduceImpl (K := k) get (fun (_ : Unit) n => .ok n)
      (fun (_ : Unit) x y => .ok (x+y)) a () ()
      ⟨one,axis.first⟩ ⟨JInt.lit .i64 k, axis.first + axis.length - one⟩ block =
      some (.ok (((List.range axis.length.val.toNat).map (fun (j : Nat) =>
        ((List.range k).map (fun (i : Nat) => values
          ⟨JInt.lit .i64 ((i+1 : Nat) : Int), JInt.lit .i64 (axis.first.val+(j : Int))⟩)).sum)).sum))

def varyingParentGet (values : I64 → Bytes) (axis : Axis) (inds : List I64) : RResult Bytes :=
  match inds with
  | [j] => if axis.first.val ≤ j.val ∧ j.val < axis.first.val + axis.length.val then
      .ok (values j) else .error .bounds
  | _ => .error .bounds

/-- Public reductions preserve arbitrary byte-valued parent data and arbitrary natural-valued
mapping functions, including empty inputs and nonempty axes at native integer endpoints. -/
def PublicReductionCorrectness : Prop :=
  ∀ (k : Nat) (values : I64 → Bytes) (weights : UInt8 → Nat)
      (axis : Axis) (block : I64),
    2 ≤ k → (k : Int) ≤ IntTy.max .i64 →
    0 ≤ axis.length.val → axis.first.val + axis.length.val - 1 ≤ IntTy.max .i64 →
    0 < block.val →
    (∀ j, axis.first.val ≤ j.val → j.val < axis.first.val + axis.length.val →
      (values j).length = k) →
    m946_mapreduce (K := k)
      (fun _ a => m290_eachindexReshaped (K := k) (fun _ ax => ax) a)
      (fun _ => ()) (fun (_ : Unit) (_ : Unit) _ _ => .ok 0)
      (fun (_ : Unit) (_ : Unit) => block)
      (m454_getindexCartesian (varyingParentGet values))
      (fun (_ : Unit) bytes => .ok (weights (bytes.headD 0)))
      (fun (_ : Unit) x y => .ok (x+y)) () () (.staticCartesian k)
      (reductionView k axis) =
      some (.ok (((List.range axis.length.val.toNat).map (fun (j : Nat) =>
        ((values (JInt.lit .i64 (axis.first.val + (j : Int)))).map weights).sum)).sum))

/-- Ordinary dense array metadata: at most 1024 elements, one-based axes and at most
64 storage bytes per element. These are the ordinary companions to the full contracts above. -/
def SmallDenseInput (t s : TypeLayout) (p : ArrayInput (List Bytes)) : Prop :=
  ValidStorageLayout t ∧ ValidStorageLayout s ∧ ShapeValid p ∧
  t.alignedSize.val ≤ 64 ∧ s.alignedSize.val ≤ 64 ∧
  (p.size.map (fun d => d.val.toNat)).prod ≤ 1024 ∧
  (∀ ax ∈ p.axes, ax.first.val = 1) ∧
  p.parent.length = (p.size.map (fun d => d.val.toNat)).prod ∧
  WellFormed s.alignedSize.val.toNat p.parent


def OrdinarySizeConservation : Prop :=
  ∀ {T S : Type} (t s : TypeLayout) (p : ArrayInput (List Bytes))
      (a : ReinterpretArray T S (ArrayInput (List Bytes))),
    SmallDenseInput t s p → m73_reinterpret t s p = .ok a →
    ∃ dims, (if a.rank = 0 then .ok (m385_sizeZero a)
      else m374_sizeNonReshaped (fun p => p.size) divInt a) = .ok dims ∧
      ((dims.map Subtype.val).prod * t.alignedSize.val =
        (p.size.map Subtype.val).prod * s.alignedSize.val)

/-- Every UInt16 byte value is included in this one-based, single-element ordinary companion. -/
def OrdinaryReductionSafety : Prop :=
  ∀ (bytes : Bytes) (block : I64), bytes.length = 2 → 0 < block.val →
    m946_mapreduce (K := 2)
      (fun _ a => m290_eachindexReshaped (K := 2) (fun _ ax => ax) a)
      (fun _ => ()) (fun (_ : Unit) (_ : Unit) _ _ => .ok 0)
      (fun (_ : Unit) (_ : Unit) => block) (m454_getindexCartesian (reductionParentGet bytes))
      (fun (_ : Unit) bytes => .ok bytes.length)
      (fun (_ : Unit) x y => .ok (x+y)) () () (.staticCartesian 2)
      (reductionView 2 ⟨one, one⟩) = some (.ok 2)

/-- Registry id: memsafety-reinterpretarray-mapreduce. Every valid static Cartesian box is reduced without out-of-box reads, including native-integer endpoint axes and every positive block size. -/
def property_memsafety_reinterpretarray_mapreduce : Prop :=
  FullReductionBounds

/-- Registry id: multidimcov-reinterpretarray-packed-copy. For accepted recursive isbits layouts without union nodes, recursive packing and unpacking transfer every value byte at every field depth while preserving destination padding and outside bytes. -/
def property_multidimcov_reinterpretarray_packed_copy : Prop :=
  PackedTransfersR4 ∧ PaddingConversionR4

namespace Round10
inductive LayoutNode : TypeLayout → TypeLayout → Prop where
  | root (t : TypeLayout) : LayoutNode t t
  | field (root parent child : TypeLayout) (off : Nat) :
      LayoutNode root parent → (off, child) ∈ parent.fields → LayoutNode root child
  | member (root parent child : TypeLayout) :
      LayoutNode root parent → child ∈ parent.members → LayoutNode root child

def RecursiveIsbitsLayout (t : TypeLayout) : Prop :=
  ∀ node, LayoutNode t node → node.isBits = true ∧ node.union = false

def JuliaDatatypeSizeBound (t : TypeLayout) : Prop :=
  t.alignedSize.val ≤ IntTy.max .u32

/-- Successful public reinterpret constructors cache the independent periodic inclusion flags. -/
def ConstructorPaddingFlags : Prop :=
  ∀ {T S A : Type} t s (p : ArrayInput A),
    ValidStorageLayout t → ValidStorageLayout s →
    JuliaDatatypeSizeBound t → JuliaDatatypeSizeBound s →
    t.isBits = true → s.isBits = true →
    RecursiveIsbitsLayout t → RecursiveIsbitsLayout s → ShapeValid p →
    (∀ a : ReinterpretArray T S (ArrayInput A), m73_reinterpret t s p = .ok a →
      (a.readable = true ↔ PaddingCompatible t s) ∧
      (a.writable = true ↔ PaddingCompatible s t)) ∧
    (∀ a : ReinterpretArray T S (ArrayInput A), m107_reinterpretReshape t s p = .ok a →
      (a.readable = true ↔ PaddingCompatible t s) ∧
      (a.writable = true ↔ PaddingCompatible s t))

/-- Registry id: reinterpretarray-padding-flags. Successful plain and reshaped reinterpret constructors on recursive isbits layouts without unions cache read and write flags exactly when periodic value-byte inclusion holds, for aligned sizes within Julia's UInt32 datatype-size limit. -/
def property_reinterpretarray_padding_flags : Prop :=
  ConstructorPaddingFlags
end Round10


/-- Registry id: reinterpretarray-nested-dispatch. Every successful nested reshaped reinterpretation preserves the root parent, target element metadata and unnecessary-layer elimination. -/
def property_reinterpretarray_nested_dispatch : Prop :=
  FullNestedStorage

/-- Registry id: reinterpretarray-padding-layout. For accepted recursive isbits layouts without unions whose aligned sizes fit Julia's UInt32 datatype-size limit, recursive masks identify every value byte, packedsize counts those bytes, and subpadding recognizes periodic value-byte inclusion. -/
def property_reinterpretarray_padding_layout : Prop :=
  PaddingHelpersR9

/-- Registry id: reinterpretarray-scalar-roundtrip. Scalar reinterpretation preserves and round-trips every recursive value byte for accepted recursive isbits layouts without unions and matching packed sizes; it throws errors for non-isbits or bit-padded layouts and unequal packed sizes. -/
def property_reinterpretarray_scalar_roundtrip : Prop :=
  ScalarConversionR4

/-- Registry id: reinterpretarray-padding-error-display. For accepted recursive isbits layouts without unions or bit padding whose aligned sizes fit Julia's UInt32 datatype-size limit, incompatible reads and writes fail, and each check succeeds exactly when its padding compatibility condition holds. -/
def property_reinterpretarray_padding_error_display : Prop :=
  ArrayPaddingR9

/-- Registry id: reinterpretarray-padding-checks. For accepted recursive isbits layouts without unions whose aligned sizes fit Julia's UInt32 datatype-size limit, read and write checks accept exactly the periodic value-byte compatibility relation and throw an error on incompatible layouts. -/
def property_reinterpretarray_padding_checks : Prop :=
  ArrayPaddingR9


/-- Registry id: reinterpretarray-padding-helpers. Every accepted recursive isbits layout without unions whose aligned size fits Julia's UInt32 datatype-size limit receives the correct value-byte mask, packed-size count and periodic subpadding verdict. -/
def property_reinterpretarray_padding_helpers : Prop :=
  PaddingHelpersR9

/-- Registry id: reinterpretarray-padding-conversion. Scalar and explicit padding conversion preserve recursive value-byte sequences for accepted recursive isbits layouts without unions, throw errors for non-isbits or bit-padded scalar inputs and mismatched packed sizes, and round-trip values. -/
def property_reinterpretarray_padding_conversion : Prop :=
  PaddingConversionR4

/-- Registry id: reinterpretarray-mapreduce-routing. Static Cartesian mapreduce terminates and computes the complete element sum for every channel count, column count, valid offset axis and positive pairwise block size. -/
def property_reinterpretarray_mapreduce_routing : Prop :=
  FullReductionCorrectness ∧ PublicReductionCorrectness

/-- Registry id: reinterpretarray-mapreduce-offset-overflow. Public reductions must terminate without an out-of-axis parent access. -/
def property_reinterpretarray_mapreduce_offset_overflow : Prop := PublicReductionSafety
end
theorem r4_layoutNode_compose {root parent : TypeLayout}
    (h : LayoutNode root parent) {child : TypeLayout}
    (hc : LayoutNode parent child) : LayoutNode root child := by
  induction hc with
  | root => exact h
  | field p c off hp hm ih => exact LayoutNode.field root p c off ih hm
  | member p c hp hm ih => exact LayoutNode.member root p c ih hm

theorem r4_recursiveIsbits_subtree {root parent : TypeLayout}
    (hrec : RecursiveIsbitsLayout root) (hnode : LayoutNode root parent) :
    RecursiveIsbitsLayout parent := by
  intro child hchild
  exact hrec child (r4_layoutNode_compose hnode hchild)

theorem r4_fieldLeaf_to_storageLeaf {root t : TypeLayout}
    (hnode : LayoutNode root t) (hrec : RecursiveIsbitsLayout root)
    {offset : Nat} {leaf : TypeLayout} (hleaf : FieldLeaf t offset leaf) :
    StorageLeaf t offset leaf := by
  revert root hnode hrec
  induction hleaf with
  | primitive t hp =>
      intro root hnode hrec
      exact StorageLeaf.primitive t hp
  | field t child leaf off inner hp hm hc ih =>
      intro root hnode hrec
      have hchild : LayoutNode root child := LayoutNode.field root t child off hnode hm
      exact StorageLeaf.field t child leaf off inner hp (hrec t hnode).2 hm (ih hchild hrec)

theorem r4_storageLeaf_to_fieldLeaf {root t : TypeLayout}
    (hnode : LayoutNode root t) (hrec : RecursiveIsbitsLayout root)
    {offset : Nat} {leaf : TypeLayout} (hleaf : StorageLeaf t offset leaf) :
    FieldLeaf t offset leaf := by
  revert root hnode hrec
  induction hleaf with
  | primitive t hp =>
      intro root hnode hrec
      exact FieldLeaf.primitive t hp
  | field t child leaf off inner hp _ hm hc ih =>
      intro root hnode hrec
      have hchild : LayoutNode root child := LayoutNode.field root t child off hnode hm
      exact FieldLeaf.field t child leaf off inner hp hm (ih hchild hrec)
  | member t child leaf inner _ hu _ _ _ =>
      intro root hnode hrec
      have hno := (hrec t hnode).2
      rw [hno] at hu
      cases hu

theorem r4_recursiveIsbits_smallPrimitiveLeaves (t : TypeLayout)
    (hvalid : ValidStorageLayout t) (hrec : RecursiveIsbitsLayout t) :
    SmallPrimitiveLeaves t := by
  intro offset leaf hleaf
  have hstorage := r4_fieldLeaf_to_storageLeaf (LayoutNode.root t) hrec hleaf
  have hfit := hvalid.leavesFit offset leaf hstorage
  have hbytes : (leaf.bits + 7) / 8 ≤ t.alignedSize.val.toNat := by omega
  have hcast : (t.alignedSize.val.toNat : Int) = t.alignedSize.val :=
    Int.toNat_of_nonneg hvalid.nonnegative
  have hbytes' : (((leaf.bits + 7) / 8 : Nat) : Int) ≤
      (t.alignedSize.val.toNat : Int) := by exact_mod_cast hbytes
  rw [hcast] at hbytes'
  exact Int.le_trans hbytes' t.alignedSize.property.2

theorem r4_fieldByte_zero_iff_valueByte (t : TypeLayout)
    (hvalid : ValidStorageLayout t) (hrec : RecursiveIsbitsLayout t) (b : Nat) :
    FieldByte t zero b ↔ ValueByte t b := by
  constructor
  · rintro ⟨offset, leaf, byte, hleaf, hbyte, hindex⟩
    have hstorage := r4_fieldLeaf_to_storageLeaf (LayoutNode.root t) hrec hleaf
    have hfit := hvalid.leavesFit offset leaf hstorage
    have hsum : offset + byte < t.alignedSize.val.toNat := by omega
    have hsize : (t.alignedSize.val.toNat : Int) = t.alignedSize.val :=
      Int.toNat_of_nonneg hvalid.nonnegative
    have hsumInt : (offset + byte : Int) < t.alignedSize.val := by
      rw [← hsize]
      exact_mod_cast hsum
    have hwrap : wrapInt .i64 (offset + byte : Int) = (offset + byte : Int) := by
      apply wrapInt_of_inRange
      exact ⟨by have := i64_min_nonpos; omega,
        by have := t.alignedSize.property.2; omega⟩
    have hindex' : b = offset + byte := by
      rw [zero_val, Int.zero_add, hwrap, ← Int.natCast_add, Int.toNat_natCast] at hindex
      exact hindex
    exact ⟨offset, leaf, hstorage, by omega, by omega⟩
  · rintro ⟨offset, leaf, hstorage, hoff, hbyteEnd⟩
    have hleaf := r4_storageLeaf_to_fieldLeaf (LayoutNode.root t) hrec hstorage
    let byte := b - offset
    have hbyte : byte < (leaf.bits + 7) / 8 := by dsimp [byte]; omega
    have hsum : offset + byte = b := by dsimp [byte]; omega
    have hfit := hvalid.leavesFit offset leaf hstorage
    have hbsize : b < t.alignedSize.val.toNat := by omega
    have hsize : (t.alignedSize.val.toNat : Int) = t.alignedSize.val :=
      Int.toNat_of_nonneg hvalid.nonnegative
    have hbound : (b : Int) < t.alignedSize.val := by
      rw [← hsize]
      exact_mod_cast hbsize
    have hwrap : wrapInt .i64 (offset + byte : Int) = (b : Int) := by
      have hsumInt : (offset + byte : Int) = (b : Int) := by exact_mod_cast hsum
      rw [hsumInt]
      exact wrapInt_of_inRange .i64 _ ⟨by have := i64_min_nonpos; omega,
        by have := t.alignedSize.property.2; omega⟩
    refine ⟨offset, leaf, byte, hleaf, hbyte, ?_⟩
    rw [zero_val, Int.zero_add, hwrap]
    simp

theorem r4_range_succ_map (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map Nat.succ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change List.range (n + 2) = 0 :: (List.range (n + 1)).map Nat.succ
    calc
      List.range (n + 2) = List.range (n + 1) ++ [n + 1] := by rw [List.range_succ]
      _ = (0 :: (List.range n).map Nat.succ) ++ [n + 1] := by rw [ih]
      _ = 0 :: ((List.range n).map Nat.succ ++ [n + 1]) := by rfl
      _ = 0 :: (List.range (n + 1)).map Nat.succ := by
        rw [List.range_succ, List.map_append]
        simp

theorem r4_countP_map_filter (xs : List Nat) (p : Nat → Bool) :
    (xs.map p).countP id = (xs.filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [hp, ih]

theorem r4_countP_range (mask : List Bool) :
    mask.countP id =
      ((List.range mask.length).filter (fun b => mask[b]?.getD false)).length := by
  have hmap :
      (List.range mask.length).map (fun b => mask[b]?.getD false) = mask := by
    induction mask with
    | nil => rfl
    | cons bit rest ih =>
      rw [List.length_cons, r4_range_succ_map]
      have hpred :
          ((fun b => (bit :: rest)[b]?.getD false) ∘ Nat.succ) =
            (fun b => rest[b]?.getD false) := by
        funext b
        simp
      rw [List.map_cons, List.map_map]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      rw [hpred, ih]
  calc
    mask.countP id =
        ((List.range mask.length).map (fun b => mask[b]?.getD false)).countP id :=
      congrArg (List.countP id) hmap.symm
    _ = ((List.range mask.length).filter (fun b => mask[b]?.getD false)).length :=
      r4_countP_map_filter _ _

theorem r4_filter_range_eq_self (p : Nat → Bool) :
    ∀ n, (∀ i < n, p i = true) → (List.range n).filter p = List.range n
  | 0, _ => rfl
  | n + 1, hp => by
    rw [List.range_succ, List.filter_append,
      r4_filter_range_eq_self p n (by
        intro i hi
        exact hp i (by omega))]
    simp [hp n (by omega)]

theorem r4_nonPaddingBytes_mask (t : TypeLayout)
    (hvalid : ValidStorageLayout t) (hbits : t.isBits = true)
    (hrec : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t) :
    ∃ mask, m750_nonPaddingBytes t = .ok mask ∧
      mask.length = t.alignedSize.val.toNat ∧
      (∀ b < mask.length, mask[b]? = some true ↔ ValueByte t b) ∧
      m816_packedsize t = .ok
        ((List.range t.alignedSize.val.toNat).filter (fun b => mask[b]?.getD false)).length := by
  have hnoBitPadding : m828_hasBitPadding t = false := by
    cases h : m828_hasBitPadding t with
    | false => rfl
    | true => exact False.elim (hbp (Strict.bitPaddingDetection t |>.mp h))
  let mask := m756_fillNonpadding t zero (List.replicate t.alignedSize.val.toNat false)
  have hlength : mask.length = t.alignedSize.val.toNat := by
    simp [mask, fillNonpadding_length]
  have hbytes : m750_nonPaddingBytes t = .ok mask := by
    simp [m750_nonPaddingBytes, hnoBitPadding, mask]
  have hsmall := r4_recursiveIsbits_smallPrimitiveLeaves t hvalid hrec
  have hvalue : ∀ b < mask.length, mask[b]? = some true ↔ ValueByte t b := by
    intro b hb
    have hb' : b < t.alignedSize.val.toNat := by simpa [hlength] using hb
    have hfull := Strict.fullByteMask t zero
      (List.replicate t.alignedSize.val.toNat false) b hsmall (by simp [hb'])
    have hfield :
        (m756_fillNonpadding t zero (List.replicate t.alignedSize.val.toNat false))[b]? =
          some true ↔ FieldByte t zero b := by
      have hfalse :
          (List.replicate t.alignedSize.val.toNat false)[b]? = some false := by simp [hb']
      rw [hfalse] at hfull
      simpa using hfull
    change
      (m756_fillNonpadding t zero (List.replicate t.alignedSize.val.toNat false))[b]? =
        some true ↔ ValueByte t b
    rw [hfield, r4_fieldByte_zero_iff_valueByte t hvalid hrec b]
  have hpacked : m816_packedsize t = .ok
      ((List.range t.alignedSize.val.toNat).filter (fun b => mask[b]?.getD false)).length := by
    by_cases hpadding : t.datatypePadding = true
    · simp [m816_packedsize, hpadding, hbytes, Except.map,
        r4_countP_range, hlength]
    · have hpaddingFalse : t.datatypePadding = false := Bool.eq_false_iff.mpr hpadding
      have hmetadata := hvalid.paddingMetadata.mp hpaddingFalse
      have hpred : ∀ b < t.alignedSize.val.toNat, mask[b]?.getD false = true := by
        intro b hb
        have hb' : b < mask.length := by simpa [hlength] using hb
        have htrue := (hvalue b hb').mpr (hmetadata b hb)
        simp [htrue]
      have hfilter := r4_filter_range_eq_self
        (fun b => mask[b]?.getD false) t.alignedSize.val.toNat hpred
      simp [m816_packedsize, hpaddingFalse, hfilter]
  exact ⟨mask, hbytes, hlength, hvalue, hpacked⟩

theorem r4_filter_eq_of_pointwise {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x, x ∈ xs → p x = q x) : xs.filter p = xs.filter q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have htail : ∀ y, y ∈ xs → p y = q y := fun y hy =>
      h y (List.mem_cons_of_mem x hy)
    simp only [List.filter_cons]
    rw [hx, ih htail]

theorem r4_filter_length_congr {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x, x ∈ xs → p x = q x) :
    (xs.filter p).length = (xs.filter q).length :=
  congrArg List.length (r4_filter_eq_of_pointwise xs p q h)

theorem r4_map_getD_range {α : Type} (xs : List α) (default : α) :
    (List.range xs.length).map (fun i => xs[i]?.getD default) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.length_cons, r4_range_succ_map]
    have hpred :
        ((fun i => (x :: xs)[i]?.getD default) ∘ Nat.succ) =
          (fun i => xs[i]?.getD default) := by
      funext i
      simp
    rw [List.map_cons, List.map_map]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    rw [hpred, ih]

theorem r4_payload_eq_bytes_of_packed (t : TypeLayout) (bytes : Bytes)
    (hvalid : ValidStorageLayout t) (hpacked : m824_ispacked t = true)
    (hlen : bytes.length = t.alignedSize.val.toNat) :
    payload t bytes = bytes := by
  classical
  have hpadding : t.datatypePadding = false := by
    simpa [m824_ispacked] using hpacked
  have hvalue := hvalid.paddingMetadata.mp hpadding
  have hfilter : (List.range t.alignedSize.val.toNat).filter (ValueByte t) =
      List.range t.alignedSize.val.toNat := by
    apply r4_filter_range_eq_self
    intro b hb
    simp [hvalue b hb]
  unfold payload
  rw [hfilter, ← hlen]
  exact r4_map_getD_range bytes 0

theorem r4_filter_length_le {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x with
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons]
      omega

theorem r4_payload_length_le_aligned (t : TypeLayout) (bytes : Bytes) :
    (payload t bytes).length ≤ t.alignedSize.val.toNat := by
  classical
  unfold payload
  simpa using r4_filter_length_le (List.range t.alignedSize.val.toNat) (ValueByte t)

theorem r4_byteWindow_full (bytes : Bytes) (n : Nat) (h : bytes.length = n) :
    byteWindow bytes 0 n = bytes := by
  unfold byteWindow
  rw [List.drop_zero, List.take_of_length_le (by omega)]

theorem r4_nat_le_layout_max (layout : TypeLayout) (hvalid : ValidStorageLayout layout)
    (n : Nat) (h : n ≤ layout.alignedSize.val.toNat) :
    (n : Int) ≤ IntTy.max .i64 := by
  have hle : (n : Int) ≤ (layout.alignedSize.val.toNat : Int) := by exact_mod_cast h
  rw [Int.toNat_of_nonneg hvalid.nonnegative] at hle
  exact Int.le_trans hle layout.alignedSize.property.2

theorem r4_copytopacked_payload_from_transfer (hcopy : PackedTransfersR4)
    (layout : TypeLayout) (bytes dst : Bytes)
    (hordered : OrderedLayout layout) (hbits : layout.isBits = true)
    (hrec : RecursiveIsbitsLayout layout) (hbp : ¬ BitPadded layout)
    (hmaxDst : (dst.length : Int) ≤ IntTy.max .i64)
    (hmaxBytes : (bytes.length : Int) ≤ IntTy.max .i64)
    (hvalidBytes : ValidElement layout bytes)
    (hwrite : (payload layout bytes).length ≤ dst.length) :
    m842_copytopacked layout dst bytes zero zero =
      .ok (overwriteBytes dst 0 (payload layout bytes)) := by
  have hz : 0 ≤ zero.val := by rw [zero_val]; omega
  change bytes.length = layout.alignedSize.val.toNat at hvalidBytes
  have hread : zero.val.toNat + layout.alignedSize.val.toNat ≤ bytes.length := by
    rw [show zero.val.toNat = 0 by simp [zero_val]]
    simp only [Nat.zero_add]
    omega
  have hwrite' : zero.val.toNat +
      (payload layout (byteWindow bytes zero.val.toNat layout.alignedSize.val.toNat)).length ≤ dst.length := by
    rw [show zero.val.toNat = 0 by simp [zero_val],
      r4_byteWindow_full bytes _ hvalidBytes]
    simpa [Nat.zero_add] using hwrite
  have hresult :=
    (hcopy layout bytes dst zero zero hordered hbits hrec hbp hz hz hmaxDst hmaxBytes).1
      hread hwrite'
  rw [show zero.val.toNat = 0 by simp [zero_val],
    r4_byteWindow_full bytes _ hvalidBytes] at hresult
  exact hresult

theorem r4_copyfrompacked_payload_from_transfer (hcopy : PackedTransfersR4)
    (layout : TypeLayout) (packed dst : Bytes)
    (hordered : OrderedLayout layout) (hbits : layout.isBits = true)
    (hrec : RecursiveIsbitsLayout layout) (hbp : ¬ BitPadded layout)
    (hmaxDst : (dst.length : Int) ≤ IntTy.max .i64)
    (hmaxPacked : (packed.length : Int) ≤ IntTy.max .i64)
    (hvalidDst : ValidElement layout dst)
    (hread : (payload layout dst).length ≤ packed.length) :
    ∃ result, m862_copyfrompacked layout dst packed zero zero = .ok result ∧
      ValidElement layout result ∧
      payload layout result = byteWindow packed 0 (payload layout dst).length := by
  have hz : 0 ≤ zero.val := by rw [zero_val]; omega
  change dst.length = layout.alignedSize.val.toNat at hvalidDst
  have hzNat : zero.val.toNat = 0 := by simp [zero_val]
  have hwriteBound : zero.val.toNat + layout.alignedSize.val.toNat ≤ dst.length := by
    rw [hzNat]
    simp only [Nat.zero_add]
    omega
  have hreadBound : zero.val.toNat +
      (payload layout (byteWindow dst zero.val.toNat layout.alignedSize.val.toNat)).length ≤ packed.length := by
    rw [hzNat, r4_byteWindow_full dst _ hvalidDst]
    simpa [Nat.zero_add] using hread
  rcases (hcopy layout packed dst zero zero hordered hbits hrec hbp hz hz
      hmaxDst hmaxPacked).2 hwriteBound hreadBound with
    ⟨result, hresult, hlen, hpayload, _⟩
  have hvalidResult : ValidElement layout result := by
    change result.length = layout.alignedSize.val.toNat
    rw [hlen, hvalidDst]
  have hwindowResult := r4_byteWindow_full result _ hvalidResult
  have hwindowDst := r4_byteWindow_full dst _ hvalidDst
  have hpayload' := hpayload
  simp only [hzNat] at hpayload'
  rw [hwindowResult, hwindowDst] at hpayload'
  refine ⟨result, hresult, hvalidResult, hpayload'⟩

theorem r4_m913_branches (output input : TypeLayout) (bytes initial : Bytes)
    (packedSize : Nat) (hpackedSize : m816_packedsize input = .ok packedSize) :
    m913_reinterpretPadding output input bytes initial =
      if 0 < input.fields.length && m824_ispacked output then
        m842_copytopacked input initial bytes zero zero
      else if 0 < output.fields.length && m824_ispacked input then
        m862_copyfrompacked output initial bytes zero zero
      else
        (do
          let packed ← m842_copytopacked input (List.replicate packedSize 0) bytes zero zero
          m862_copyfrompacked output initial packed zero zero) := by
  simp [m913_reinterpretPadding, hpackedSize]

theorem r4_packedsize_eq_payload_length (t : TypeLayout) (bytes : Bytes)
    (hvalid : ValidStorageLayout t) (hbits : t.isBits = true)
    (hrec : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t) :
    m816_packedsize t = .ok (payload t bytes).length := by
  classical
  obtain ⟨mask, _, hlen, hmask, hpacked⟩ :=
    r4_nonPaddingBytes_mask t hvalid hbits hrec hbp
  have hpred : ∀ b ∈ List.range t.alignedSize.val.toNat,
      (mask[b]?.getD false) = decide (ValueByte t b) := by
    intro b hb
    have hb' : b < mask.length := by
      simpa [hlen] using List.mem_range.mp hb
    have hget : mask[b]? = some (mask[b]) := List.getElem?_eq_getElem hb'
    cases hm : mask[b] with
    | false =>
      have hnot : ¬ ValueByte t b := by
        intro hvalue
        have htrue := (hmask b hb').2 hvalue
        rw [hget, hm] at htrue
        cases htrue
      simp [hget, hm, hnot]
    | true =>
      have hvalue : ValueByte t b := (hmask b hb').1 (by rw [hget, hm])
      simp [hget, hm, hvalue]
  have hfilter := r4_filter_length_congr
    (List.range t.alignedSize.val.toNat)
    (fun b => mask[b]?.getD false) (fun b => decide (ValueByte t b)) hpred
  calc
    m816_packedsize t =
        .ok ((List.range t.alignedSize.val.toNat).filter (fun b => mask[b]?.getD false)).length :=
      hpacked
    _ = .ok ((List.range t.alignedSize.val.toNat).filter (fun b => ValueByte t b)).length :=
      congrArg Except.ok hfilter
    _ = .ok (payload t bytes).length := by simp [payload]

theorem r4_valueByteLists_eq_iff (t s : TypeLayout)
    (htvalid : ValidStorageLayout t) (hsvalid : ValidStorageLayout s)
    (mt ms : List Bool)
    (htlen : mt.length = t.alignedSize.val.toNat)
    (hslen : ms.length = s.alignedSize.val.toNat)
    (htmask : ∀ b < mt.length, mt[b]? = some true ↔ ValueByte t b)
    (hsmask : ∀ b < ms.length, ms[b]? = some true ↔ ValueByte s b) :
    (mt = ms) ↔
      (t.alignedSize = s.alignedSize ∧
        ∀ n < t.alignedSize.val.toNat, ValueByte t n ↔ ValueByte s n) := by
  constructor
  · intro hmask
    have hnat : t.alignedSize.val.toNat = s.alignedSize.val.toNat := by
      rw [← htlen, hmask, hslen]
    have htc := Int.toNat_of_nonneg htvalid.nonnegative
    have hsc := Int.toNat_of_nonneg hsvalid.nonnegative
    have hval : t.alignedSize.val = s.alignedSize.val := by
      calc
        t.alignedSize.val = (t.alignedSize.val.toNat : Int) := htc.symm
        _ = (s.alignedSize.val.toNat : Int) := by exact_mod_cast hnat
        _ = s.alignedSize.val := hsc
    refine ⟨jint_eq_of_val hval, ?_⟩
    intro n hn
    have htn : n < mt.length := by rw [htlen]; exact hn
    have hsn : n < ms.length := by rw [hslen, hnat.symm]; exact hn
    have htm := htmask n htn
    have hsm := hsmask n hsn
    have hoption : mt[n]? = some true ↔ ms[n]? = some true := by rw [hmask]
    exact htm.symm.trans (hoption.trans hsm)
  · rintro ⟨hsize, hvalues⟩
    have hval := congrArg Subtype.val hsize
    have hnat : t.alignedSize.val.toNat = s.alignedSize.val.toNat := by rw [hval]
    have hlen : mt.length = ms.length := by rw [htlen, hslen, hnat]
    apply List.ext_getElem?
    intro n
    by_cases hn : n < mt.length
    · have hns : n < ms.length := by rw [← hlen]; exact hn
      have hnt : n < t.alignedSize.val.toNat := by rw [← htlen]; exact hn
      have htm := htmask n hn
      have hsm := hsmask n hns
      have htruth : mt[n]? = some true ↔ ms[n]? = some true :=
        htm.trans ((hvalues n hnt).trans hsm.symm)
      have hgetT : mt[n]? = some (mt[n]) := List.getElem?_eq_getElem hn
      have hgetS : ms[n]? = some (ms[n]) := List.getElem?_eq_getElem hns
      rw [hgetT, hgetS]
      cases ht : mt[n] <;> cases hs : ms[n] <;> simp_all
    · have hns : ¬ n < ms.length := by
        intro h
        apply hn
        rw [hlen]
        exact h
      simp [List.getElem?_eq_none_iff, hn, hns]

theorem r4_structSubpadding_semantics (t s : TypeLayout)
    (htvalid : ValidStorageLayout t) (hsvalid : ValidStorageLayout s)
    (htbits : t.isBits = true) (hsbits : s.isBits = true)
    (htrec : RecursiveIsbitsLayout t) (hsrec : RecursiveIsbitsLayout s)
    (htbp : ¬ BitPadded t) (hsbp : ¬ BitPadded s) :
    ∀ b, m812_structSubpadding t s = .ok b ↔
      (b = true ↔ t.alignedSize = s.alignedSize ∧
        ∀ n < t.alignedSize.val.toNat, ValueByte t n ↔ ValueByte s n) := by
  obtain ⟨mt, hmt, hmtlen, hmtmask, _⟩ :=
    r4_nonPaddingBytes_mask t htvalid htbits htrec htbp
  obtain ⟨ms, hms, hmslen, hmsmask, _⟩ :=
    r4_nonPaddingBytes_mask s hsvalid hsbits hsrec hsbp
  have heq := r4_valueByteLists_eq_iff t s htvalid hsvalid mt ms
    hmtlen hmslen hmtmask hmsmask
  have hbool : (mt == ms) = decide (mt = ms) := by
    by_cases heq : mt = ms
    · subst ms
      simp
    · simp [heq]
  have hsub : m812_structSubpadding t s = .ok (mt = ms) := by
    simp [m812_structSubpadding, hmt, hms, hbool]
  intro b
  rw [hsub]
  cases b <;> simp [heq]

theorem r4_m913_payload_preserved (hcopy : PackedTransfersR4)
    (output input : TypeLayout) (bytes initial : Bytes)
    (horderedOutput : OrderedLayout output) (horderedInput : OrderedLayout input)
    (hbitsOutput : output.isBits = true) (hbitsInput : input.isBits = true)
    (hrecOutput : RecursiveIsbitsLayout output) (hrecInput : RecursiveIsbitsLayout input)
    (hbpOutput : ¬ BitPadded output) (hbpInput : ¬ BitPadded input)
    (hvalidInput : ValidElement input bytes) (hvalidOutput : ValidElement output initial)
    (hpayloads : (payload output initial).length = (payload input bytes).length) :
    ∃ result, m913_reinterpretPadding output input bytes initial = .ok result ∧
      ValidElement output result ∧ payload output result = payload input bytes := by
  classical
  change bytes.length = input.alignedSize.val.toNat at hvalidInput
  change initial.length = output.alignedSize.val.toNat at hvalidOutput
  have hstorageInput : ValidStorageLayout input :=
    (horderedInput input (LayoutNode.root input)).1
  have hstorageOutput : ValidStorageLayout output :=
    (horderedOutput output (LayoutNode.root output)).1
  let inputPackedSize := (payload input bytes).length
  let outputPackedSize := (payload output initial).length
  have hpackSizeInput : m816_packedsize input = .ok inputPackedSize :=
    r4_packedsize_eq_payload_length input bytes hstorageInput hbitsInput hrecInput hbpInput
  have hmaxBytes : (bytes.length : Int) ≤ IntTy.max .i64 :=
    r4_nat_le_layout_max input hstorageInput bytes.length (by rw [hvalidInput]; exact Nat.le_refl _)
  have hmaxInitial : (initial.length : Int) ≤ IntTy.max .i64 :=
    r4_nat_le_layout_max output hstorageOutput initial.length
      (by rw [hvalidOutput]; exact Nat.le_refl _)
  have hmaxPacked : (inputPackedSize : Int) ≤ IntTy.max .i64 :=
    r4_nat_le_layout_max input hstorageInput inputPackedSize
      (r4_payload_length_le_aligned input bytes)
  have hmodel := r4_m913_branches output input bytes initial inputPackedSize hpackSizeInput
  rw [hmodel]
  by_cases hfirst : (0 < input.fields.length && m824_ispacked output) = true
  · have hparts : 0 < input.fields.length ∧ m824_ispacked output = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hfirst
    have houtPacked : m824_ispacked output = true := hparts.2
    have hpayloadOutput := r4_payload_eq_bytes_of_packed
      output initial hstorageOutput houtPacked hvalidOutput
    have hinitialEq : initial.length = inputPackedSize := by
      calc
        initial.length = outputPackedSize := (congrArg List.length hpayloadOutput).symm
        _ = inputPackedSize := hpayloads
    have htop := r4_copytopacked_payload_from_transfer hcopy input bytes initial
      horderedInput hbitsInput hrecInput hbpInput hmaxInitial hmaxBytes hvalidInput
      (by simpa [inputPackedSize] using Nat.le_of_eq hinitialEq.symm)
    have htopResult : m842_copytopacked input initial bytes zero zero =
        .ok (payload input bytes) := by
      rw [htop, overwriteBytes_full initial (payload input bytes) hinitialEq.symm]
    have hvalidResult : ValidElement output (payload input bytes) := by
      change inputPackedSize = output.alignedSize.val.toNat
      calc
        inputPackedSize = initial.length := hinitialEq.symm
        _ = output.alignedSize.val.toNat := hvalidOutput
    have hpayloadResult :=
      r4_payload_eq_bytes_of_packed output (payload input bytes)
        hstorageOutput houtPacked hvalidResult
    refine ⟨payload input bytes, ?_, hvalidResult, hpayloadResult⟩
    simp [hfirst, htopResult]
  · have hfirstFalse : (0 < input.fields.length && m824_ispacked output) = false :=
      Bool.eq_false_iff.mpr hfirst
    by_cases hsecond : (0 < output.fields.length && m824_ispacked input) = true
    · have hparts : 0 < output.fields.length ∧ m824_ispacked input = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hsecond
      have hinPacked : m824_ispacked input = true := hparts.2
      have hpayloadInput := r4_payload_eq_bytes_of_packed
        input bytes hstorageInput hinPacked hvalidInput
      have hbytesLength : bytes.length = inputPackedSize :=
        (congrArg List.length hpayloadInput).symm
      have hread : outputPackedSize ≤ bytes.length := by
        change (payload output initial).length ≤ bytes.length
        have hlength : (payload output initial).length = bytes.length := by
          calc
            (payload output initial).length = (payload input bytes).length := hpayloads
            _ = bytes.length := by simpa [inputPackedSize] using hbytesLength.symm
        exact Nat.le_of_eq hlength
      obtain ⟨result, hresult, hvalidResult, hpayloadResult⟩ :=
        r4_copyfrompacked_payload_from_transfer hcopy output bytes initial
          horderedOutput hbitsOutput hrecOutput hbpOutput hmaxInitial hmaxBytes
          hvalidOutput hread
      have hbytesWindow := r4_byteWindow_full bytes outputPackedSize
        (hbytesLength.trans hpayloads.symm)
      have hpayload : payload output result = payload input bytes := by
        calc
          payload output result = byteWindow bytes 0 outputPackedSize := hpayloadResult
          _ = bytes := hbytesWindow
          _ = payload input bytes := hpayloadInput.symm
      refine ⟨result, ?_, hvalidResult, hpayload⟩
      simp [hfirstFalse, hsecond, hresult]
    · have hsecondFalse : (0 < output.fields.length && m824_ispacked input) = false :=
        Bool.eq_false_iff.mpr hsecond
      let packed : Bytes := List.replicate inputPackedSize 0
      have hpackedLength : packed.length = inputPackedSize := by simp [packed]
      have hmaxPackedBuffer : (packed.length : Int) ≤ IntTy.max .i64 := by
        rw [hpackedLength]
        exact hmaxPacked
      have htop := r4_copytopacked_payload_from_transfer hcopy input bytes packed
        horderedInput hbitsInput hrecInput hbpInput hmaxPackedBuffer hmaxBytes
        hvalidInput (by simp [packed, inputPackedSize])
      have htopResult : m842_copytopacked input packed bytes zero zero =
          .ok (payload input bytes) := by
        rw [htop, overwriteBytes_full packed (payload input bytes)
          (by simp [packed, inputPackedSize])]
      have htopModel : m842_copytopacked input (List.replicate inputPackedSize 0)
          bytes zero zero = .ok (payload input bytes) := by
        simpa [packed] using htopResult
      have hread : outputPackedSize ≤ inputPackedSize := by
        change (payload output initial).length ≤ (payload input bytes).length
        exact Nat.le_of_eq hpayloads
      obtain ⟨result, hresult, hvalidResult, hpayloadResult⟩ :=
        r4_copyfrompacked_payload_from_transfer hcopy output (payload input bytes) initial
          horderedOutput hbitsOutput hrecOutput hbpOutput hmaxInitial hmaxPacked
          hvalidOutput hread
      have hpackedWindow := r4_byteWindow_full (payload input bytes) outputPackedSize
        (by simpa [inputPackedSize, outputPackedSize] using hpayloads.symm)
      have hpayload : payload output result = payload input bytes := by
        calc
          payload output result = byteWindow (payload input bytes) 0 outputPackedSize :=
            hpayloadResult
          _ = payload input bytes := hpackedWindow
      refine ⟨result, ?_, hvalidResult, hpayload⟩
      simp [hfirstFalse, hsecondFalse, htopModel, hresult, resultBindOk]

theorem r4_fullPaddingLayoutAnyError : FullPaddingLayoutAnyErrorR4 := by
  refine ⟨Strict.fullByteMask, fillNonpadding_length, ?_, ?_, Strict.bitPaddingDetection⟩
  · intro layout
    constructor
    · intro h
      exact ⟨.argument, by simp [m750_nonPaddingBytes, h]⟩
    · intro h
      exact reinterpretPaddingLayout.2.1 layout |>.2 h
  · intro id size
    exact reinterpretPaddingLayout.2.2 id size

theorem r4_payload_same_layout_bytes (output input : TypeLayout) (bytes : Bytes)
    (hsize : output.alignedSize = input.alignedSize)
    (hvalues : ∀ n < output.alignedSize.val.toNat, ValueByte output n ↔ ValueByte input n) :
    payload output bytes = payload input bytes := by
  classical
  have hfilter :
      (List.range output.alignedSize.val.toNat).filter (ValueByte output) =
        (List.range output.alignedSize.val.toNat).filter (ValueByte input) := by
    apply r4_filter_eq_of_pointwise
    intro n hn
    have hv := hvalues n (List.mem_range.mp hn)
    by_cases ho : ValueByte output n
    · simp [ho, hv.mp ho]
    · have hi : ¬ ValueByte input n := fun h => ho (hv.mpr h)
      simp [ho, hi]
  unfold payload
  rw [hfilter, hsize]

theorem r4_m882_invalid (output input : TypeLayout) (bytes initial : Bytes)
    (hbad : output.isBits = false ∨ input.isBits = false ∨ BitPadded output ∨ BitPadded input) :
    ∃ e, m882_reinterpret output input bytes initial = .error e := by
  by_cases ho : output.isBits = true
  · by_cases hi : input.isBits = true
    · rcases hbad with h | h | h | h
      · simp [ho] at h
      · simp [hi] at h
      · have hb := Strict.bitPaddingDetection output |>.mpr h
        exact ⟨.argument, by simp [m882_reinterpret, ho, hi, hb]⟩
      · have hb := Strict.bitPaddingDetection input |>.mpr h
        by_cases hbo : m828_hasBitPadding output = true
        · exact ⟨.argument, by simp [m882_reinterpret, ho, hi, hbo]⟩
        · exact ⟨.argument, by simp [m882_reinterpret, ho, hi, hbo, hb]⟩
    · have hif : input.isBits = false := Bool.eq_false_iff.mpr hi
      exact ⟨.argument, by simp [m882_reinterpret, ho, hif]⟩
  · have hof : output.isBits = false := Bool.eq_false_iff.mpr ho
    exact ⟨.argument, by simp [m882_reinterpret, hof]⟩

theorem r4_noBitPadding (t : TypeLayout) (h : ¬ BitPadded t) :
    m828_hasBitPadding t = false := by
  cases hb : m828_hasBitPadding t with
  | false => rfl
  | true => exact False.elim (h (Strict.bitPaddingDetection t |>.mp hb))

theorem r4_m882_valid_branches (output input : TypeLayout) (bytes initial : Bytes)
    (hob : output.isBits = true) (hib : input.isBits = true)
    (hop : ¬ BitPadded output) (hip : ¬ BitPadded input)
    (ni no : Nat) (hni : m816_packedsize input = .ok ni)
    (hno : m816_packedsize output = .ok no) :
    m882_reinterpret output input bytes initial =
      if ni != no then .error .argument else
        (do
          let same ← if m824_ispacked input && m824_ispacked output then pure true
            else m812_structSubpadding output input
          if same then pure (memcpyValue initial bytes zero zero output.alignedSize)
          else m913_reinterpretPadding output input bytes initial) := by
  have hbo := r4_noBitPadding output hop
  have hbi := r4_noBitPadding input hip
  simp only [m882_reinterpret, hob, hib, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, hbo, hbi, resultPure, resultBindOk, hni, hno]
  split <;> rfl

theorem r4_m882_payload_preserved (hcopy : PackedTransfersR4)
    (output input : TypeLayout) (bytes initial : Bytes)
    (hoo : OrderedLayout output) (hio : OrderedLayout input)
    (hob : output.isBits = true) (hib : input.isBits = true)
    (hor : RecursiveIsbitsLayout output) (hir : RecursiveIsbitsLayout input)
    (hop : ¬ BitPadded output) (hip : ¬ BitPadded input)
    (hvb : ValidElement input bytes) (hvi : ValidElement output initial)
    (heq : (payload output initial).length = (payload input bytes).length) :
    ∃ result, m882_reinterpret output input bytes initial = .ok result ∧
      ValidElement output result ∧ payload output result = payload input bytes := by
  classical
  have hov := (hoo output (.root output)).1
  have hiv := (hio input (.root input)).1
  have hni := r4_packedsize_eq_payload_length input bytes hiv hib hir hip
  have hno := r4_packedsize_eq_payload_length output initial hov hob hor hop
  rw [r4_m882_valid_branches output input bytes initial hob hib hop hip _ _ hni hno]
  have hne : ((payload input bytes).length != (payload output initial).length) = false := by
    simp [heq]
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨mo, hmo, hmolen, hmomask, _⟩ := r4_nonPaddingBytes_mask output hov hob hor hop
  obtain ⟨mi, hmi, hmilen, hmimask, _⟩ := r4_nonPaddingBytes_mask input hiv hib hir hip
  have hstruct : m812_structSubpadding output input = .ok (mo == mi) := by
    simp [m812_structSubpadding, hmo, hmi]
  by_cases hpacked : (m824_ispacked input && m824_ispacked output) = true
  · have hp : m824_ispacked input = true ∧ m824_ispacked output = true := by
      simpa using hpacked
    have hpo := r4_payload_eq_bytes_of_packed output initial hov hp.2 hvi
    have hpi := r4_payload_eq_bytes_of_packed input bytes hiv hp.1 hvb
    have hlength : initial.length = bytes.length := by
      rw [← hpo, ← hpi]
      exact heq
    have hsize : bytes.length = output.alignedSize.val.toNat := hlength.symm.trans hvi
    have hmem : memcpyValue initial bytes zero zero output.alignedSize = bytes := by
      simp only [memcpyValue, zero_val, Int.toNat_zero, byteWindow, List.drop_zero]
      rw [List.take_of_length_le (by omega), overwriteBytes_full initial bytes hlength.symm]
    refine ⟨bytes, ?_, hsize, ?_⟩
    · simp only [hpacked, ↓reduceIte, resultPure, resultBindOk, hmem]
    · rw [r4_payload_eq_bytes_of_packed output bytes hov hp.2 hsize, hpi]
  · have hpf : (m824_ispacked input && m824_ispacked output) = false :=
      Bool.eq_false_iff.mpr hpacked
    rw [hpf]
    simp only [Bool.false_eq_true, ↓reduceIte, hstruct, resultBindOk]
    by_cases hsame : (mo == mi) = true
    · have hsem := (r4_structSubpadding_semantics output input hov hiv hob hib hor hir hop hip true).mp
        (by rw [hstruct, hsame])
      have hsem' : output.alignedSize = input.alignedSize ∧
          ∀ n < output.alignedSize.val.toNat, ValueByte output n ↔ ValueByte input n :=
        hsem.mp rfl
      have hlength : initial.length = bytes.length := by
        change initial.length = output.alignedSize.val.toNat at hvi
        change bytes.length = input.alignedSize.val.toNat at hvb
        rw [hvi, hsem'.1, hvb]
      have hsize : ValidElement output bytes := by
        change bytes.length = output.alignedSize.val.toNat
        rw [hvb, hsem'.1]
      have hmem : memcpyValue initial bytes zero zero output.alignedSize = bytes := by
        simp only [memcpyValue, zero_val, Int.toNat_zero, byteWindow, List.drop_zero]
        rw [List.take_of_length_le (by rw [← hsize]; exact Nat.le_refl _),
          overwriteBytes_full initial bytes hlength.symm]
      refine ⟨bytes, ?_, hsize, r4_payload_same_layout_bytes output input bytes hsem'.1 hsem'.2⟩
      simp only [hsame, ↓reduceIte, resultPure, hmem]
    · have hsf : (mo == mi) = false := Bool.eq_false_iff.mpr hsame
      rw [hsf]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact r4_m913_payload_preserved hcopy output input bytes initial
        hoo hio hob hib hor hir hop hip hvb hvi heq

theorem r4_scalarConversion_from_packedTransfers (hcopy : PackedTransfersR4) :
    ScalarConversionR4 := by
  intro output input bytes initial hoo hio hvb hvi
  refine ⟨r4_m882_invalid output input bytes initial, ?_⟩
  intro hob hib hor hir hop hip
  by_cases heq : (payload output initial).length = (payload input bytes).length
  · rw [if_pos heq]
    obtain ⟨result, hr, hv, hp⟩ := r4_m882_payload_preserved hcopy output input bytes initial
      hoo hio hob hib hor hir hop hip hvb hvi heq
    obtain ⟨back, hb, _, hpb⟩ := r4_m882_payload_preserved hcopy input output result bytes
      hio hoo hib hob hir hor hip hop hv hvb (by rw [hp])
    exact ⟨result, hr, hv, hp, back, hb, hpb.trans hp⟩
  · rw [if_neg heq]
    have hov := (hoo output (.root output)).1
    have hiv := (hio input (.root input)).1
    have hni := r4_packedsize_eq_payload_length input bytes hiv hib hir hip
    have hno := r4_packedsize_eq_payload_length output initial hov hob hor hop
    rw [r4_m882_valid_branches output input bytes initial hob hib hop hip _ _ hni hno]
    have hne : ((payload input bytes).length != (payload output initial).length) = true := by
      simp [Ne.symm heq]
    exact ⟨.argument, by rw [hne]; rfl⟩

theorem r4_paddingConversion_from_packedTransfers (hcopy : PackedTransfersR4) :
    PaddingConversionR4 := by
  refine ⟨r4_scalarConversion_from_packedTransfers hcopy, hcopy, ?_⟩
  exact r4_m913_payload_preserved hcopy

theorem r4_valueByte_primitive (t : TypeLayout) (hp : t.primitive = true) (b : Nat) :
    ValueByte t b ↔ b < (t.bits + 7) / 8 := by
  constructor
  · rintro ⟨off, leaf, hs, hlo, hhi⟩
    cases hs with
    | primitive => simpa using hhi
    | field _ _ _ _ _ hf => simp [hp] at hf
    | member _ _ _ _ hf => simp [hp] at hf
  · intro hb
    exact ⟨0, t, .primitive t hp, by omega, by simpa using hb⟩

theorem r4_valueByte_fields (t : TypeLayout) (hp : t.primitive = false)
    (hu : t.union = false) (b : Nat) :
    ValueByte t b ↔ ∃ off child, (off, child) ∈ t.fields ∧
      off ≤ b ∧ ValueByte child (b - off) := by
  constructor
  · rintro ⟨off, leaf, hs, hlo, hhi⟩
    cases hs with
    | primitive _ hf => simp [hp] at hf
    | field _ child leaf off inner _ _ hm hc =>
      exact ⟨off, child, hm, by omega, inner, leaf, hc, by omega, by omega⟩
    | member _ _ _ _ _ hf => simp [hu] at hf
  · rintro ⟨off, child, hm, hlo, inner, leaf, hc, hclo, hchi⟩
    exact ⟨off + inner, leaf, .field t child leaf off inner hp hu hm hc,
      by omega, by omega⟩

theorem r4_field_noBitPadding (t child : TypeLayout) (off : Nat)
    (hp : t.primitive = false) (hu : t.union = false)
    (hm : (off, child) ∈ t.fields) (hbp : ¬ BitPadded t) :
    ¬ BitPadded child := by
  rintro ⟨inner, leaf, hc, hbits⟩
  exact hbp ⟨off + inner, leaf, .field t child leaf off inner hp hu hm hc, hbits⟩

theorem r4_map_getD_range_take (bytes : Bytes) (n : Nat) (hn : n ≤ bytes.length) :
    (List.range n).map (fun i => bytes.getD i 0) = bytes.take n := by
  have hlen : (bytes.take n).length = n := by simp [List.length_take, Nat.min_eq_left hn]
  have hmap := r4_map_getD_range (bytes.take n) 0
  rw [hlen] at hmap
  rw [← hmap]
  apply List.map_congr_left
  intro i hi
  have hin := List.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hin]

theorem r4_byteWindow_length (bytes : Bytes) (offset n : Nat)
    (h : offset + n ≤ bytes.length) : (byteWindow bytes offset n).length = n := by
  simp only [byteWindow, List.length_take, List.length_drop]
  omega

theorem r4_range_sorted (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    have hab : b = n := by simpa using hb
    subst b
    exact List.mem_range.mp ha

theorem r4_sorted_eq_of_mem (xs ys : List Nat)
    (hx : xs.Pairwise (· < ·)) (hy : ys.Pairwise (· < ·))
    (hmem : ∀ n, n ∈ xs ↔ n ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => have h := (hmem y).mpr (by simp); simp at h
  | cons x xs ih =>
    cases ys with
    | nil => have h := (hmem x).mp (by simp); simp at h
    | cons y ys =>
      rw [List.pairwise_cons] at hx hy
      have hxy : x = y := by
        apply Classical.byContradiction
        intro hne
        have hxys : x ∈ ys := by
          have h := (hmem x).mp (by simp)
          simpa [hne] using h
        have hyxs : y ∈ xs := by
          have h := (hmem y).mpr (by simp)
          simpa [Ne.symm hne] using h
        have hlt := hx.1 y hyxs
        have hgt := hy.1 x hxys
        omega
      subst y
      congr 1
      apply ih _ hx.2 hy.2
      intro n
      by_cases hn : n = x
      · subst n
        have hnx : x ∉ xs := fun h => Nat.lt_irrefl _ (hx.1 x h)
        have hny : x ∉ ys := fun h => Nat.lt_irrefl _ (hy.1 x h)
        simp [hnx, hny]
      · simpa [hn] using hmem n

noncomputable def r4_valueIndices (t : TypeLayout) : List Nat := by
  classical
  exact (List.range t.alignedSize.val.toNat).filter (ValueByte t)

theorem r4_mem_valueIndices (t : TypeLayout) (n : Nat) :
    n ∈ r4_valueIndices t ↔ n < t.alignedSize.val.toNat ∧ ValueByte t n := by
  classical
  simp [r4_valueIndices]

theorem r4_valueIndices_sorted (t : TypeLayout) :
    (r4_valueIndices t).Pairwise (· < ·) := by
  classical
  exact List.Pairwise.filter _ (r4_range_sorted _)

theorem r4_valueByte_lt (t : TypeLayout) (hv : ValidStorageLayout t)
    (b : Nat) (hb : ValueByte t b) : b < t.alignedSize.val.toNat := by
  obtain ⟨off, leaf, hs, hlo, hhi⟩ := hb
  have hfit := hv.leavesFit off leaf hs
  omega

theorem r4_field_indices_sorted (fields : List (Nat × TypeLayout))
    (hordered : fields.Pairwise (fun x y => x.1 + x.2.alignedSize.val.toNat ≤ y.1)) :
    (fields.flatMap (fun field =>
      (r4_valueIndices field.2).map (fun b => field.1 + b))).Pairwise (· < ·) := by
  induction fields with
  | nil => simp
  | cons field fields ih =>
    rw [List.pairwise_cons] at hordered
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨?_, ih hordered.2, ?_⟩
    · exact List.Pairwise.map _ (fun _ _ h => Nat.add_lt_add_left h field.1)
        (r4_valueIndices_sorted field.2)
    · intro a ha b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      obtain ⟨other, hother, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hi' := (r4_mem_valueIndices field.2 i).mp hi
      have hsep := hordered.1 other hother
      omega

theorem r4_valueIndices_fields (t : TypeLayout) (ho : OrderedLayout t)
    (hr : RecursiveIsbitsLayout t) (hp : t.primitive = false) :
    r4_valueIndices t = t.fields.flatMap (fun field =>
      (r4_valueIndices field.2).map (fun b => field.1 + b)) := by
  have hv := (ho t (.root t)).1
  have hu := (hr t (.root t)).2
  apply r4_sorted_eq_of_mem _ _ (r4_valueIndices_sorted t)
    (r4_field_indices_sorted t.fields (ho t (.root t)).2)
  intro n
  rw [r4_mem_valueIndices]
  constructor
  · rintro ⟨_, hn⟩
    obtain ⟨off, child, hm, hlo, hvalue⟩ := (r4_valueByte_fields t hp hu n).mp hn
    apply List.mem_flatMap.mpr
    refine ⟨(off, child), hm, List.mem_map.mpr ?_⟩
    have hchild := (ho child (.field t t child off (.root t) hm)).1
    refine ⟨n - off, (r4_mem_valueIndices child _).mpr
      ⟨r4_valueByte_lt child hchild _ hvalue, hvalue⟩, ?_⟩
    simp only
    omega
  · intro hn
    obtain ⟨⟨off, child⟩, hm, hn⟩ := List.mem_flatMap.mp hn
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hn
    have hb' := (r4_mem_valueIndices child b).mp hb
    have hval : ValueByte t (off + b) := (r4_valueByte_fields t hp hu _).mpr
      ⟨off, child, hm, by omega, by simpa using hb'.2⟩
    exact ⟨r4_valueByte_lt t hv _ hval, hval⟩

theorem r4_byteWindow_getD (bytes : Bytes) (offset size b : Nat) (hb : b < size) :
    (byteWindow bytes offset size).getD b 0 = bytes.getD (offset + b) 0 := by
  simp [byteWindow, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop, hb]

theorem r4_map_flatMap {α β γ : Type} (xs : List α) (f : α → List β) (g : β → γ) :
    (xs.flatMap f).map g = xs.flatMap (fun x => (f x).map g) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem r4_orderedLayout_subtree {root parent : TypeLayout}
    (ho : OrderedLayout root) (hn : LayoutNode root parent) : OrderedLayout parent := by
  intro child hc
  exact ho child (r4_layoutNode_compose hn hc)

theorem r4_add_zero (a : I64) : a + zero = a := by
  apply jint_eq_of_val
  rw [val_add, zero_val, Int.add_zero]
  exact wrapInt_of_inRange .i64 a.val a.property

theorem r4_forIn_yield_identity {α β : Type} (xs : List α)
    (f : α → β → RResult (ForInStep β)) (state : β)
    (h : ∀ x ∈ xs, f x state = .ok (.yield state)) :
    forIn xs state f = .ok state := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons, h x List.mem_cons_self, resultBindOk]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem r4_empty_field_indices (t : TypeLayout) (ho : OrderedLayout t)
    (hr : RecursiveIsbitsLayout t) (hp : t.primitive = false)
    (he : r4_valueIndices t = []) (off : Nat) (child : TypeLayout)
    (hm : (off, child) ∈ t.fields) : r4_valueIndices child = [] := by
  cases hc : r4_valueIndices child with
  | nil => rfl
  | cons b rest =>
    have hb : b ∈ r4_valueIndices child := by rw [hc]; simp
    have hmem : off + b ∈ r4_valueIndices t := by
      rw [r4_valueIndices_fields t ho hr hp]
      exact List.mem_flatMap.mpr ⟨(off, child), hm,
        List.mem_map.mpr ⟨b, hb, rfl⟩⟩
    rw [he] at hmem
    cases hmem

theorem r4_packedsize_empty (t : TypeLayout) (ho : OrderedLayout t)
    (hr : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t)
    (he : r4_valueIndices t = []) : m816_packedsize t = .ok 0 := by
  have h := r4_packedsize_eq_payload_length t [] (ho t (.root t)).1
    (hr t (.root t)).1 hr hbp
  have hp : payload t [] = [] := by
    change (r4_valueIndices t).map _ = []
    rw [he]
    rfl
  rwa [hp, List.length_nil] at h

theorem r4_empty_transfers (t : TypeLayout) (ho : OrderedLayout t)
    (hr : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t)
    (he : r4_valueIndices t = []) (output input : Bytes) (wo ro : I64) :
    m842_copytopacked t output input wo ro = .ok output ∧
      m862_copyfrompacked t output input wo ro = .ok output := by
  revert ho hr hbp he output input wo ro
  refine WellFounded.induction
    (C := fun t => OrderedLayout t → RecursiveIsbitsLayout t → ¬ BitPadded t →
      r4_valueIndices t = [] → ∀ output input wo ro,
        m842_copytopacked t output input wo ro = .ok output ∧
          m862_copyfrompacked t output input wo ro = .ok output)
    (measure sizeOf).wf t ?_
  intro t ih ho hr hbp he output input wo ro
  have hps := r4_packedsize_empty t ho hr hbp he
  have hzero : JInt.lit .i64 (0 : Nat) = zero := rfl
  have hcopyzero : ∀ dst src wo ro, memcpyValue dst src wo ro zero = dst := by
    intro dst src wo ro
    simp [memcpyValue, zero_val, byteWindow, overwriteBytes_nil]
  by_cases hp : t.primitive = true
  · constructor
    · rw [m842_copytopacked.eq_def, if_pos hp, hps]
      simp only [resultBindOk, resultPure, hzero, hcopyzero]
    · rw [m862_copyfrompacked.eq_def, if_pos hp, hps]
      simp only [resultBindOk, resultPure, hzero, hcopyzero]
  · have hpf : t.primitive = false := Bool.eq_false_iff.mpr hp
    have hchild : ∀ (field : {f // f ∈ t.fields}),
        m816_packedsize field.val.2 = .ok 0 ∧
        (m824_ispacked field.val.2 = true → field.val.2.alignedSize = zero) ∧
        ∀ dst src wo ro,
          m842_copytopacked field.val.2 dst src wo ro = .ok dst ∧
          m862_copyfrompacked field.val.2 dst src wo ro = .ok dst := by
      intro field
      have hn : LayoutNode t field.val.2 := .field t t field.val.2 field.val.1 (.root t) field.property
      have hco := r4_orderedLayout_subtree ho hn
      have hcr := r4_recursiveIsbits_subtree hr hn
      have hcb := r4_field_noBitPadding t field.val.2 field.val.1 hpf
        (hr t (.root t)).2 field.property hbp
      have hce := r4_empty_field_indices t ho hr hpf he field.val.1 field.val.2 field.property
      refine ⟨r4_packedsize_empty field.val.2 hco hcr hcb hce, ?_, ?_⟩
      · intro hpacked
        have hpadding : field.val.2.datatypePadding = false := by
          simpa [m824_ispacked] using hpacked
        have hsz : field.val.2.alignedSize.val.toNat = 0 := by
          have hps := r4_packedsize_empty field.val.2 hco hcr hcb hce
          simpa [m816_packedsize, hpadding] using hps
        apply jint_eq_of_val
        have hnonneg := (hco field.val.2 (.root field.val.2)).1.nonnegative
        rw [zero_val]
        omega
      · apply ih field.val.2
        · rcases t with ⟨info, fields, members⟩
          have h1 := List.sizeOf_lt_of_mem field.property
          have h2 : sizeOf field.val.2 < sizeOf field.val := by
            rcases field with ⟨⟨off, child⟩, hm⟩
            simp
            omega
          have h3 : sizeOf fields < sizeOf (TypeLayout.mk info fields members) := by simp; omega
          exact Nat.lt_trans h2 (Nat.lt_trans h1 h3)
        · exact hco
        · exact hcr
        · exact hcb
        · exact hce
    constructor
    · rw [m842_copytopacked.eq_def, if_neg hp]
      dsimp only
      rw [r4_forIn_yield_identity t.fields.attach]
      · rfl
      · intro field _
        obtain ⟨hps, hsz, htrans⟩ := hchild field
        dsimp only
        by_cases hc : m824_ispacked field.val.2 = true
        · rw [if_pos hc, hsz hc]
          simp only [hcopyzero, r4_add_zero]
          rfl
        · rw [if_neg hc, (htrans _ _ _ _).1, resultBindOk, hps, resultBindOk, hzero,
            r4_add_zero]
          rfl
    · rw [m862_copyfrompacked.eq_def, if_neg hp]
      dsimp only
      rw [r4_forIn_yield_identity t.fields.attach]
      · rfl
      · intro field _
        obtain ⟨hps, hsz, htrans⟩ := hchild field
        dsimp only
        by_cases hc : m824_ispacked field.val.2 = true
        · rw [if_pos hc, hsz hc]
          simp only [hcopyzero, r4_add_zero]
          rfl
        · rw [if_neg hc, (htrans _ _ _ _).2, resultBindOk, hps, resultBindOk, hzero,
            r4_add_zero]
          rfl

theorem r4_forIn_pack_chunks {α : Type} (xs : List α) (chunk : α → Bytes)
    (step : α → Bytes × I64 → RResult (ForInStep (Bytes × I64))) (base : Nat)
    (hstep : ∀ x ∈ xs, ∀ (dst : Bytes) (cursor : I64) (k : Nat), cursor.val = (k : Int) →
      (dst.length : Int) ≤ IntTy.max .i64 → base + k + (chunk x).length ≤ dst.length →
      step x (dst, cursor) = .ok (.yield
        (overwriteBytes dst (base + k) (chunk x), cursor + JInt.lit .i64 (chunk x).length))) :
    ∀ (dst : Bytes) (cursor : I64) (k : Nat), cursor.val = (k : Int) →
      (dst.length : Int) ≤ IntTy.max .i64 →
      base + k + (xs.flatMap chunk).length ≤ dst.length →
      forIn xs (dst, cursor) step =
        .ok (overwriteBytes dst (base + k) (xs.flatMap chunk),
          JInt.lit .i64 (k + (xs.flatMap chunk).length)) := by
  induction xs with
  | nil =>
    intro dst cursor k hk hmax hfit
    have hcursor : cursor = JInt.lit .i64 k := by
      apply jint_eq_of_val
      rw [hk, lit_nat k (by simp at hfit; omega)]
    simp [hcursor, overwriteBytes_nil]
  | cons x xs ih =>
    intro dst cursor k hk hmax hfit
    have htotal : base + k + (chunk x).length + (xs.flatMap chunk).length ≤ dst.length := by
      simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hfit
    have hfits : base + k + (chunk x).length ≤ dst.length := by omega
    have hchildmax : ((chunk x).length : Int) ≤ IntTy.max .i64 := by omega
    have hnextmax : ((k + (chunk x).length : Nat) : Int) ≤ IntTy.max .i64 := by omega
    have hnext : (cursor + JInt.lit .i64 (chunk x).length).val =
        ((k + (chunk x).length : Nat) : Int) :=
      add_nat hk (lit_nat _ hchildmax) hnextmax
    have hlen : (overwriteBytes dst (base + k) (chunk x)).length = dst.length :=
      overwriteBytes_length _ _ _ hfits
    rw [List.forIn_cons, hstep x List.mem_cons_self dst cursor k hk hmax hfits, resultBindOk]
    dsimp only
    have hrec := ih (fun y hy => hstep y (List.mem_cons_of_mem x hy))
      (overwriteBytes dst (base + k) (chunk x))
      (cursor + JInt.lit .i64 (chunk x).length) (k + (chunk x).length)
      hnext (by rw [hlen]; exact hmax) (by rw [hlen]; omega)
    rw [hrec]
    have hwrite := overwriteBytes_overwriteBytes dst (chunk x) (xs.flatMap chunk) (base + k)
      htotal
    rw [show base + (k + (chunk x).length) = base + k + (chunk x).length by omega,
      hwrite]
    simp only [List.flatMap_cons, List.length_append, Int.natCast_add, Int.add_assoc]

noncomputable def r4_payloadAt (t : TypeLayout) (bytes : Bytes) (offset : Nat) : Bytes :=
  (r4_valueIndices t).map (fun b => bytes.getD (offset + b) 0)

theorem r4_payloadAt_length (t : TypeLayout) (bytes : Bytes) (offset : Nat) :
    (r4_payloadAt t bytes offset).length = (r4_valueIndices t).length := by
  simp only [r4_payloadAt, List.length_map]

theorem r4_payloadAt_window (t : TypeLayout) (bytes : Bytes) (offset : Nat) :
    r4_payloadAt t bytes offset =
      payload t (byteWindow bytes offset t.alignedSize.val.toNat) := by
  change (r4_valueIndices t).map _ = (r4_valueIndices t).map _
  apply List.map_congr_left
  intro b hb
  exact (r4_byteWindow_getD bytes offset t.alignedSize.val.toNat b
    ((r4_mem_valueIndices t b).mp hb).1).symm

theorem r4_payloadAt_fields (t : TypeLayout) (bytes : Bytes) (offset : Nat)
    (ho : OrderedLayout t) (hr : RecursiveIsbitsLayout t) (hp : t.primitive = false) :
    r4_payloadAt t bytes offset = t.fields.flatMap (fun field =>
      r4_payloadAt field.2 bytes (offset + field.1)) := by
  unfold r4_payloadAt
  rw [r4_valueIndices_fields t ho hr hp, r4_map_flatMap]
  apply congrArg (fun f => t.fields.flatMap f)
  funext field
  rw [List.map_map]
  simp only [Function.comp_def, Nat.add_assoc]

theorem r4_valueIndices_primitive (t : TypeLayout)
    (hv : ValidStorageLayout t) (hp : t.primitive = true) :
    r4_valueIndices t = List.range ((t.bits + 7) / 8) := by
  have hfit := hv.leavesFit 0 t (.primitive t hp)
  apply r4_sorted_eq_of_mem _ _ (r4_valueIndices_sorted t) (r4_range_sorted _)
  intro b
  rw [r4_mem_valueIndices, List.mem_range, r4_valueByte_primitive t hp b]
  constructor
  · exact And.right
  · intro hb
    exact ⟨by omega, hb⟩

theorem r4_payloadAt_primitive (t : TypeLayout) (bytes : Bytes) (offset : Nat)
    (hv : ValidStorageLayout t) (hp : t.primitive = true)
    (hfit : offset + (t.bits + 7) / 8 ≤ bytes.length) :
    r4_payloadAt t bytes offset = byteWindow bytes offset ((t.bits + 7) / 8) := by
  unfold r4_payloadAt
  rw [r4_valueIndices_primitive t hv hp]
  have hmap := r4_map_getD_range_take (bytes.drop offset) ((t.bits + 7) / 8)
    (by rw [List.length_drop]; omega)
  simpa only [byteWindow, List.getD_eq_getElem?_getD, List.getElem?_drop] using hmap

theorem r4_packedsize_eq_indices_length (t : TypeLayout)
    (ho : OrderedLayout t) (hr : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t) :
    m816_packedsize t = .ok (r4_valueIndices t).length := by
  have h := r4_packedsize_eq_payload_length t [] (ho t (.root t)).1
    (hr t (.root t)).1 hr hbp
  simpa only [payload, r4_valueIndices, List.length_map] using h

theorem r4_field_sizeOf_lt (t : TypeLayout) (field : {f // f ∈ t.fields}) :
    sizeOf field.val.2 < sizeOf t := by
  rcases t with ⟨info, fields, members⟩
  have h1 := List.sizeOf_lt_of_mem field.property
  have h2 : sizeOf field.val.2 < sizeOf field.val := by
    rcases field with ⟨⟨off, child⟩, hm⟩
    simp
    omega
  have h3 : sizeOf fields < sizeOf (TypeLayout.mk info fields members) := by simp; omega
  exact Nat.lt_trans h2 (Nat.lt_trans h1 h3)

theorem r4_copyzero (dst src : Bytes) (wo ro : I64) :
    memcpyValue dst src wo ro zero = dst := by
  simp [memcpyValue, zero_val, byteWindow, overwriteBytes_nil]

theorem r4_packed_empty_size (t : TypeLayout) (ho : OrderedLayout t)
    (hr : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t)
    (he : r4_valueIndices t = []) (hp : m824_ispacked t = true) :
    t.alignedSize = zero := by
  have hpadding : t.datatypePadding = false := by simpa [m824_ispacked] using hp
  have hps := r4_packedsize_empty t ho hr hbp he
  have hsz : t.alignedSize.val.toNat = 0 := by
    simpa [m816_packedsize, hpadding] using hps
  apply jint_eq_of_val
  rw [zero_val]
  have hnonneg := (ho t (.root t)).1.nonnegative
  omega

theorem r4_flatMap_attach {α β : Type} (xs : List α) (f : α → List β) :
    xs.attach.flatMap (fun x => f x.val) = xs.flatMap f := by
  rw [← List.flatMap_map Subtype.val f xs.attach]
  have hm : xs.attach.map Subtype.val = xs := by
    simpa using (List.attach_map_val (l := xs) (f := id))
  rw [hm]

theorem r4_copytopacked_value_bounds (t : TypeLayout)
    (ho : OrderedLayout t) (hr : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t)
    (output input : Bytes) (wo ro : I64)
    (hwo : 0 ≤ wo.val) (hro : 0 ≤ ro.val)
    (homax : (output.length : Int) ≤ IntTy.max .i64)
    (himax : (input.length : Int) ≤ IntTy.max .i64)
    (hwrite : wo.val.toNat + (r4_valueIndices t).length ≤ output.length)
    (hread : ∀ b ∈ r4_valueIndices t, ro.val.toNat + b < input.length) :
    m842_copytopacked t output input wo ro =
      .ok (overwriteBytes output wo.val.toNat (r4_payloadAt t input ro.val.toNat)) := by
  revert ho hr hbp output input wo ro hwo hro homax himax hwrite hread
  refine WellFounded.induction
    (C := fun t => OrderedLayout t → RecursiveIsbitsLayout t → ¬ BitPadded t →
      ∀ output input wo ro, 0 ≤ wo.val → 0 ≤ ro.val →
        (output.length : Int) ≤ IntTy.max .i64 → (input.length : Int) ≤ IntTy.max .i64 →
        wo.val.toNat + (r4_valueIndices t).length ≤ output.length →
        (∀ b ∈ r4_valueIndices t, ro.val.toNat + b < input.length) →
        m842_copytopacked t output input wo ro =
          .ok (overwriteBytes output wo.val.toNat (r4_payloadAt t input ro.val.toNat)))
    (measure sizeOf).wf t ?_
  intro t ih ho hr hbp output input wo ro hwo hro homax himax hwrite hread
  by_cases he : r4_valueIndices t = []
  · rw [(r4_empty_transfers t ho hr hbp he output input wo ro).1]
    simp [r4_payloadAt, he, overwriteBytes_nil]
  have hv := (ho t (.root t)).1
  have hb := (hr t (.root t)).1
  have hps := r4_packedsize_eq_indices_length t ho hr hbp
  have hwoval : wo.val = (wo.val.toNat : Int) := (Int.toNat_of_nonneg hwo).symm
  have hroval : ro.val = (ro.val.toNat : Int) := (Int.toNat_of_nonneg hro).symm
  by_cases hp : t.primitive = true
  · have hidx := r4_valueIndices_primitive t hv hp
    have hnpos : 0 < (t.bits + 7) / 8 := by
      by_cases hn : (t.bits + 7) / 8 = 0
      · simp [hidx, hn] at he
      · omega
    have hlast := hread (((t.bits + 7) / 8) - 1)
      (by rw [hidx]; exact List.mem_range.mpr (by omega))
    have hreadfit : ro.val.toNat + (t.bits + 7) / 8 ≤ input.length := by omega
    have hnmax : (((t.bits + 7) / 8 : Nat) : Int) ≤ IntTy.max .i64 := by omega
    rw [hidx, List.length_range] at hps
    rw [m842_copytopacked.eq_def, if_pos hp, hps]
    rw [r4_payloadAt_primitive t input ro.val.toNat hv hp hreadfit]
    simp only [resultBindOk, resultPure, memcpyValue, lit_nat _ hnmax, Int.toNat_natCast]
  · have hpf : t.primitive = false := Bool.eq_false_iff.mpr hp
    let chunk (field : {f // f ∈ t.fields}) : Bytes :=
      r4_payloadAt field.val.2 input (ro.val.toNat + field.val.1)
    let step (field : {f // f ∈ t.fields}) (state : Bytes × I64) :
        RResult (ForInStep (Bytes × I64)) := do
      if m824_ispacked field.val.2 then
        pure (.yield
          (memcpyValue state.1 input (wo + state.2) (ro + JInt.lit .i64 field.val.1) field.val.2.alignedSize,
            state.2 + field.val.2.alignedSize))
      else
        let result ← m842_copytopacked field.val.2 state.1 input
          (wo + state.2) (ro + JInt.lit .i64 field.val.1)
        let size ← m816_packedsize field.val.2
        pure (.yield (result, state.2 + JInt.lit .i64 size))
    have hflat : t.fields.attach.flatMap chunk = r4_payloadAt t input ro.val.toNat := by
      rw [r4_payloadAt_fields t input ro.val.toNat ho hr hpf]
      simpa only [chunk] using r4_flatMap_attach t.fields
        (fun field => r4_payloadAt field.2 input (ro.val.toNat + field.1))
    have hstep : ∀ field ∈ t.fields.attach, ∀ (dst : Bytes) (cursor : I64) (k : Nat),
        cursor.val = (k : Int) → (dst.length : Int) ≤ IntTy.max .i64 →
        wo.val.toNat + k + (chunk field).length ≤ dst.length →
        step field (dst, cursor) = .ok (.yield
          (overwriteBytes dst (wo.val.toNat + k) (chunk field),
            cursor + JInt.lit .i64 (chunk field).length)) := by
      intro field _ dst cursor k hk hdmax hdfit
      have hn : LayoutNode t field.val.2 :=
        .field t t field.val.2 field.val.1 (.root t) field.property
      have hco := r4_orderedLayout_subtree ho hn
      have hcr := r4_recursiveIsbits_subtree hr hn
      have hcb := r4_field_noBitPadding t field.val.2 field.val.1 hpf
        (hr t (.root t)).2 field.property hbp
      have hcv := (hco field.val.2 (.root field.val.2)).1
      have hcps : m816_packedsize field.val.2 = .ok (chunk field).length := by
        rw [r4_packedsize_eq_indices_length field.val.2 hco hcr hcb]
        simp only [chunk, r4_payloadAt_length]
      by_cases hce : r4_valueIndices field.val.2 = []
      · have hchunk : chunk field = [] := by simp [chunk, r4_payloadAt, hce]
        have hcopy := r4_empty_transfers field.val.2 hco hcr hcb hce
        dsimp only [step]
        by_cases hpacked : m824_ispacked field.val.2 = true
        · rw [if_pos hpacked, r4_packed_empty_size field.val.2 hco hcr hcb hce hpacked]
          simp [r4_copyzero, hchunk, overwriteBytes_nil, r4_add_zero,
            show JInt.lit .i64 (0 : Int) = zero from rfl]
        · rw [if_neg hpacked, (hcopy _ _ _ _).1, resultBindOk,
            r4_packedsize_empty field.val.2 hco hcr hcb hce, resultBindOk]
          simp [hchunk, overwriteBytes_nil, r4_add_zero,
            show JInt.lit .i64 (0 : Int) = zero from rfl]
      have hparentmem : ∀ b ∈ r4_valueIndices field.val.2,
          field.val.1 + b ∈ r4_valueIndices t := by
        intro b hb
        rw [r4_valueIndices_fields t ho hr hpf]
        exact List.mem_flatMap.mpr ⟨field.val, field.property, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
      have hchildread : ∀ b ∈ r4_valueIndices field.val.2,
          ro.val.toNat + field.val.1 + b < input.length := by
        intro b hb
        have h := hread (field.val.1 + b) (hparentmem b hb)
        omega
      have hsomemem : ∃ b, b ∈ r4_valueIndices field.val.2 := by
        cases hcidx : r4_valueIndices field.val.2 with
        | nil => exact False.elim (hce hcidx)
        | cons b rest => exact ⟨b, by simp⟩
      obtain ⟨b, hbmem⟩ := hsomemem
      have hbound := hchildread b hbmem
      have hromax : ((ro.val.toNat + field.val.1 : Nat) : Int) ≤ IntTy.max .i64 := by omega
      have hrochild : (ro + JInt.lit .i64 field.val.1).val =
          ((ro.val.toNat + field.val.1 : Nat) : Int) :=
        add_nat hroval (lit_nat _ (by omega)) hromax
      have hwochild : (wo + cursor).val = ((wo.val.toNat + k : Nat) : Int) :=
        add_nat hwoval hk (by omega)
      have hrochildNat : (ro + JInt.lit .i64 field.val.1).val.toNat =
          ro.val.toNat + field.val.1 := by rw [hrochild, Int.toNat_natCast]
      have hwochildNat : (wo + cursor).val.toNat = wo.val.toNat + k := by
        rw [hwochild, Int.toNat_natCast]
      dsimp only [step]
      by_cases hpacked : m824_ispacked field.val.2 = true
      · have hpadding : field.val.2.datatypePadding = false := by
          simpa [m824_ispacked] using hpacked
        have hvalues := hcv.paddingMetadata.mp hpadding
        have hsizepos : 0 < field.val.2.alignedSize.val.toNat :=
          Nat.zero_lt_of_lt ((r4_mem_valueIndices field.val.2 b).mp hbmem).1
        have hlast := hchildread (field.val.2.alignedSize.val.toNat - 1)
          ((r4_mem_valueIndices field.val.2 _).mpr
            ⟨by omega, hvalues _ (by omega)⟩)
        have hreadfit : ro.val.toNat + field.val.1 + field.val.2.alignedSize.val.toNat ≤ input.length := by
          omega
        have hchunk : chunk field =
            byteWindow input (ro.val.toNat + field.val.1) field.val.2.alignedSize.val.toNat := by
          dsimp only [chunk]
          rw [r4_payloadAt_window]
          exact r4_payload_eq_bytes_of_packed _ _ hcv hpacked
            (r4_byteWindow_length _ _ _ hreadfit)
        have hchunklen : (chunk field).length = field.val.2.alignedSize.val.toNat := by
          rw [hchunk]
          exact r4_byteWindow_length _ _ _ hreadfit
        have hsize : field.val.2.alignedSize = JInt.lit .i64 (chunk field).length := by
          apply jint_eq_of_val
          rw [hchunklen, lit_nat _ (by
            rw [Int.toNat_of_nonneg hcv.nonnegative]
            exact field.val.2.alignedSize.property.2),
            Int.toNat_of_nonneg hcv.nonnegative]
        have hmem : memcpyValue dst input (wo + cursor) (ro + JInt.lit .i64 field.val.1)
            field.val.2.alignedSize = overwriteBytes dst (wo.val.toNat + k) (chunk field) := by
          simp only [memcpyValue, hwochildNat, hrochildNat]
          rw [← hchunk]
        rw [if_pos hpacked, hmem, hsize]
        rfl
      · rw [if_neg hpacked]
        have hrecursive := ih field.val.2 (r4_field_sizeOf_lt t field)
          hco hcr hcb dst input (wo + cursor) (ro + JInt.lit .i64 field.val.1)
          (by rw [hwochild]; omega) (by rw [hrochild]; omega) hdmax himax
          (by rw [hwochildNat]; simpa only [chunk, r4_payloadAt_length] using hdfit)
          (by intro b hb; rw [hrochildNat]; exact hchildread b hb)
        rw [hrecursive, resultBindOk, hcps, resultBindOk, hwochildNat, hrochildNat]
        rfl
    rw [m842_copytopacked.eq_def, if_neg hp]
    change (do
      let result ← forIn t.fields.attach (output, zero) step
      pure result.1) = _
    have hloop := r4_forIn_pack_chunks t.fields.attach chunk step wo.val.toNat hstep
      output zero 0 zero_val homax (by
        rw [hflat, r4_payloadAt_length]
        simpa using hwrite)
    rw [hloop]
    simp only [resultBindOk, resultPure, Nat.add_zero, hflat]

def r4_scatter (dst : Bytes) (positions : List Nat) (input : Bytes) (offset : Nat) : Bytes :=
  match positions with
  | [] => dst
  | pos :: rest => r4_scatter (dst.set pos (input.getD offset 0)) rest input (offset + 1)

theorem r4_scatter_length (dst : Bytes) (positions : List Nat) (input : Bytes) (offset : Nat) :
    (r4_scatter dst positions input offset).length = dst.length := by
  induction positions generalizing dst offset with
  | nil => rfl
  | cons p ps ih => simp only [r4_scatter, ih, List.length_set]

theorem r4_scatter_append (dst : Bytes) (ps qs : List Nat) (input : Bytes) (offset : Nat) :
    r4_scatter dst (ps ++ qs) input offset =
      r4_scatter (r4_scatter dst ps input offset) qs input (offset + ps.length) := by
  induction ps generalizing dst offset with
  | nil => simp [r4_scatter]
  | cons p ps ih =>
    simp only [List.cons_append, r4_scatter, ih, List.length_cons]
    rw [show offset + 1 + ps.length = offset + (ps.length + 1) by omega]

theorem r4_scatter_outside (dst : Bytes) (positions : List Nat) (input : Bytes)
    (offset b : Nat) (hb : b ∉ positions) :
    (r4_scatter dst positions input offset)[b]? = dst[b]? := by
  induction positions generalizing dst offset with
  | nil => rfl
  | cons p ps ih =>
    have hne : p ≠ b := by intro he; subst p; simp at hb
    have htail : b ∉ ps := by intro h; exact hb (List.mem_cons_of_mem p h)
    rw [r4_scatter, ih _ _ htail, List.getElem?_set_ne hne]

theorem r4_byteWindow_cons (input : Bytes) (offset n : Nat)
    (h : offset + (n + 1) ≤ input.length) :
    byteWindow input offset (n + 1) =
      input.getD offset 0 :: byteWindow input (offset + 1) n := by
  have ho : offset < input.length := by omega
  unfold byteWindow
  rw [List.drop_eq_getElem_cons ho, List.take_succ_cons,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho]
  rfl

theorem r4_gather_scatter (dst : Bytes) (positions : List Nat) (input : Bytes) (offset : Nat)
    (hord : positions.Pairwise (· < ·))
    (hpos : ∀ b ∈ positions, b < dst.length)
    (hin : offset + positions.length ≤ input.length) :
    positions.map (fun b => (r4_scatter dst positions input offset).getD b 0) =
      byteWindow input offset positions.length := by
  induction positions generalizing dst offset with
  | nil => simp [byteWindow]
  | cons p ps ih =>
    rw [List.pairwise_cons] at hord
    have hp : p < dst.length := hpos p List.mem_cons_self
    have hnot : p ∉ ps := fun h => Nat.lt_irrefl _ (hord.1 p h)
    have hout := r4_scatter_outside (dst.set p (input.getD offset 0)) ps input (offset + 1) p hnot
    have hhead : (r4_scatter (dst.set p (input.getD offset 0)) ps input (offset + 1)).getD p 0 =
        input.getD offset 0 := by
      rw [List.getD_eq_getElem?_getD, hout, List.getElem?_set_self hp]
      rfl
    have htail := ih (dst.set p (input.getD offset 0)) (offset + 1) hord.2
      (by intro b hb; rw [List.length_set]; exact hpos b (List.mem_cons_of_mem p hb))
      (by simp only [List.length_cons] at hin; omega)
    rw [r4_scatter, List.map_cons, hhead, htail, List.length_cons, r4_byteWindow_cons input offset ps.length hin]

theorem r4_scatter_at (dst : Bytes) (positions : List Nat) (input : Bytes) (offset i b : Nat)
    (hord : positions.Pairwise (· < ·)) (hpos : ∀ p ∈ positions, p < dst.length)
    (hin : offset + positions.length ≤ input.length) (hindex : positions[i]? = some b) :
    (r4_scatter dst positions input offset)[b]? = input[offset + i]? := by
  induction positions generalizing dst offset i with
  | nil => simp at hindex
  | cons p ps ih =>
    rw [List.pairwise_cons] at hord
    cases i with
    | zero =>
      have heq : p = b := by simpa using hindex
      subst b
      have hp := hpos p List.mem_cons_self
      have hnot : p ∉ ps := fun h => Nat.lt_irrefl _ (hord.1 p h)
      rw [r4_scatter, r4_scatter_outside _ _ _ _ _ hnot,
        List.getElem?_set_self hp, Nat.add_zero, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simp only [List.length_cons] at hin; omega)]
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at hindex
      rw [r4_scatter]
      have h := ih (dst.set p (input.getD offset 0)) (offset + 1) i hord.2
        (by intro q hq; rw [List.length_set]; exact hpos q (List.mem_cons_of_mem p hq))
        (by simp only [List.length_cons] at hin; omega) hindex
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

theorem r4_scatter_range (dst input : Bytes) (writeBase readBase n : Nat)
    (hw : writeBase + n ≤ dst.length) (hr : readBase + n ≤ input.length) :
    r4_scatter dst ((List.range n).map (fun b => writeBase + b)) input readBase =
      overwriteBytes dst writeBase (byteWindow input readBase n) := by
  let positions := (List.range n).map (fun b => writeBase + b)
  have hord : positions.Pairwise (· < ·) :=
    List.Pairwise.map _ (fun _ _ h => Nat.add_lt_add_left h writeBase) (r4_range_sorted n)
  have hpos : ∀ p ∈ positions, p < dst.length := by
    intro p hp
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
    have hbn := List.mem_range.mp hb
    omega
  have hlen : positions.length = n := by simp [positions]
  have hchunklen := r4_byteWindow_length input readBase n hr
  apply List.ext_getElem?
  intro b
  rw [overwriteBytes_getElem? dst _ writeBase b (by rw [hchunklen]; exact hw), hchunklen]
  by_cases hlo : b < writeBase
  · rw [if_pos hlo]
    apply r4_scatter_outside
    intro hb
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp hb
    omega
  · rw [if_neg hlo]
    by_cases hhi : b < writeBase + n
    · rw [if_pos hhi]
      have hi : b - writeBase < n := by omega
      have hindex : positions[b - writeBase]? = some b := by
        simp [positions, List.getElem?_map, List.getElem?_range, hi, show writeBase + (b - writeBase) = b by omega]
      have h := r4_scatter_at dst positions input readBase (b - writeBase) b
        hord hpos (by rw [hlen]; exact hr) hindex
      simpa only [byteWindow, List.getElem?_take, hi, ↓reduceIte, List.getElem?_drop] using h
    · rw [if_neg hhi]
      apply r4_scatter_outside
      intro hb
      obtain ⟨i, hi, heq⟩ := List.mem_map.mp hb
      have hin := List.mem_range.mp hi
      omega

theorem r4_forIn_scatter_positions {α : Type} (xs : List α) (positions : α → List Nat)
    (step : α → Bytes × I64 → RResult (ForInStep (Bytes × I64)))
    (input : Bytes) (base size : Nat)
    (hmax : (input.length : Int) ≤ IntTy.max .i64)
    (hstep : ∀ x ∈ xs, ∀ (dst : Bytes) (cursor : I64) (k : Nat),
      cursor.val = (k : Int) → dst.length = size → base + k + (positions x).length ≤ input.length →
      step x (dst, cursor) = .ok (.yield
        (r4_scatter dst (positions x) input (base + k),
          cursor + JInt.lit .i64 (positions x).length))) :
    ∀ (dst : Bytes) (cursor : I64) (k : Nat),
      cursor.val = (k : Int) → dst.length = size →
      base + k + (xs.flatMap positions).length ≤ input.length →
      forIn xs (dst, cursor) step =
        .ok (r4_scatter dst (xs.flatMap positions) input (base + k),
          JInt.lit .i64 (k + (xs.flatMap positions).length)) := by
  induction xs with
  | nil =>
    intro dst cursor k hk hsize hfit
    have hcursor : cursor = JInt.lit .i64 k := by
      apply jint_eq_of_val
      rw [hk, lit_nat k (by simp at hfit; omega)]
    simp [r4_scatter, hcursor]
  | cons x xs ih =>
    intro dst cursor k hk hsize hfit
    have htotal : base + k + (positions x).length + (xs.flatMap positions).length ≤ input.length := by
      simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hfit
    have hfits : base + k + (positions x).length ≤ input.length := by omega
    have hnext : (cursor + JInt.lit .i64 (positions x).length).val =
        ((k + (positions x).length : Nat) : Int) :=
      add_nat hk (lit_nat _ (by omega)) (by omega)
    rw [List.forIn_cons, hstep x List.mem_cons_self dst cursor k hk hsize hfits, resultBindOk]
    dsimp only
    rw [ih (fun y hy => hstep y (List.mem_cons_of_mem x hy))
      (r4_scatter dst (positions x) input (base + k))
      (cursor + JInt.lit .i64 (positions x).length) (k + (positions x).length)
      hnext (by rw [r4_scatter_length]; exact hsize) (by omega)]
    rw [show base + (k + (positions x).length) = (base + k) + (positions x).length by omega,
      ← r4_scatter_append]
    simp only [List.flatMap_cons, List.length_append, Int.natCast_add, Int.add_assoc]

theorem r4_valueIndices_packed (t : TypeLayout) (hv : ValidStorageLayout t)
    (hp : m824_ispacked t = true) : r4_valueIndices t = List.range t.alignedSize.val.toNat := by
  classical
  have hpadding : t.datatypePadding = false := by simpa [m824_ispacked] using hp
  have hall := hv.paddingMetadata.mp hpadding
  unfold r4_valueIndices
  apply r4_filter_range_eq_self
  intro b hb
  simp [hall b hb]

theorem r4_copyfrompacked_value_bounds (t : TypeLayout)
    (ho : OrderedLayout t) (hr : RecursiveIsbitsLayout t) (hbp : ¬ BitPadded t)
    (output input : Bytes) (wo ro : I64)
    (hwo : 0 ≤ wo.val) (hro : 0 ≤ ro.val)
    (homax : (output.length : Int) ≤ IntTy.max .i64)
    (himax : (input.length : Int) ≤ IntTy.max .i64)
    (hread : ro.val.toNat + (r4_valueIndices t).length ≤ input.length)
    (hwrite : ∀ b ∈ r4_valueIndices t, wo.val.toNat + b < output.length) :
    m862_copyfrompacked t output input wo ro =
      .ok (r4_scatter output ((r4_valueIndices t).map (fun b => wo.val.toNat + b)) input ro.val.toNat) := by
  revert ho hr hbp output input wo ro hwo hro homax himax hread hwrite
  refine WellFounded.induction
    (C := fun t => OrderedLayout t → RecursiveIsbitsLayout t → ¬ BitPadded t →
      ∀ output input wo ro, 0 ≤ wo.val → 0 ≤ ro.val →
        (output.length : Int) ≤ IntTy.max .i64 → (input.length : Int) ≤ IntTy.max .i64 →
        ro.val.toNat + (r4_valueIndices t).length ≤ input.length →
        (∀ b ∈ r4_valueIndices t, wo.val.toNat + b < output.length) →
        m862_copyfrompacked t output input wo ro =
          .ok (r4_scatter output ((r4_valueIndices t).map (fun b => wo.val.toNat + b)) input ro.val.toNat))
    (measure sizeOf).wf t ?_
  intro t ih ho hr hbp output input wo ro hwo hro homax himax hread hwrite
  by_cases he : r4_valueIndices t = []
  · rw [(r4_empty_transfers t ho hr hbp he output input wo ro).2]
    simp [he, r4_scatter]
  have hv := (ho t (.root t)).1
  have hb := (hr t (.root t)).1
  have hps := r4_packedsize_eq_indices_length t ho hr hbp
  have hwoval : wo.val = (wo.val.toNat : Int) := (Int.toNat_of_nonneg hwo).symm
  have hroval : ro.val = (ro.val.toNat : Int) := (Int.toNat_of_nonneg hro).symm
  by_cases hp : t.primitive = true
  · have hidx := r4_valueIndices_primitive t hv hp
    have hnpos : 0 < (t.bits + 7) / 8 := by
      by_cases hn : (t.bits + 7) / 8 = 0
      · simp [hidx, hn] at he
      · omega
    have hlast := hwrite (((t.bits + 7) / 8) - 1)
      (by rw [hidx]; exact List.mem_range.mpr (by omega))
    have hwritefit : wo.val.toNat + (t.bits + 7) / 8 ≤ output.length := by omega
    have hreadfit : ro.val.toNat + (t.bits + 7) / 8 ≤ input.length := by
      simpa only [hidx, List.length_range] using hread
    have hnmax : (((t.bits + 7) / 8 : Nat) : Int) ≤ IntTy.max .i64 := by omega
    rw [hidx, List.length_range] at hps
    rw [m862_copyfrompacked.eq_def, if_pos hp, hps]
    simp only [resultBindOk, resultPure, memcpyValue, lit_nat _ hnmax, Int.toNat_natCast]
    rw [hidx, r4_scatter_range output input wo.val.toNat ro.val.toNat _ hwritefit hreadfit]
  · have hpf : t.primitive = false := Bool.eq_false_iff.mpr hp
    let positions (field : {f // f ∈ t.fields}) : List Nat :=
      (r4_valueIndices field.val.2).map (fun b => wo.val.toNat + field.val.1 + b)
    let step (field : {f // f ∈ t.fields}) (state : Bytes × I64) :
        RResult (ForInStep (Bytes × I64)) := do
      if m824_ispacked field.val.2 then
        pure (.yield
          (memcpyValue state.1 input (wo + JInt.lit .i64 field.val.1) (ro + state.2) field.val.2.alignedSize,
            state.2 + field.val.2.alignedSize))
      else
        let result ← m862_copyfrompacked field.val.2 state.1 input
          (wo + JInt.lit .i64 field.val.1) (ro + state.2)
        let size ← m816_packedsize field.val.2
        pure (.yield (result, state.2 + JInt.lit .i64 size))
    have hflat : t.fields.attach.flatMap positions =
        (r4_valueIndices t).map (fun b => wo.val.toNat + b) := by
      calc
        _ = t.fields.flatMap (fun field =>
            (r4_valueIndices field.2).map (fun b => wo.val.toNat + field.1 + b)) := by
          simpa only [positions] using r4_flatMap_attach t.fields
            (fun field => (r4_valueIndices field.2).map (fun b => wo.val.toNat + field.1 + b))
        _ = _ := by
          rw [r4_valueIndices_fields t ho hr hpf, r4_map_flatMap]
          apply congrArg (fun f => t.fields.flatMap f)
          funext field
          rw [List.map_map]
          simp only [Function.comp_def, Nat.add_assoc]
    have hstep : ∀ field ∈ t.fields.attach, ∀ (dst : Bytes) (cursor : I64) (k : Nat),
        cursor.val = (k : Int) → dst.length = output.length →
        ro.val.toNat + k + (positions field).length ≤ input.length →
        step field (dst, cursor) = .ok (.yield
          (r4_scatter dst (positions field) input (ro.val.toNat + k),
            cursor + JInt.lit .i64 (positions field).length)) := by
      intro field _ dst cursor k hk hdlen hdfit
      have hn : LayoutNode t field.val.2 :=
        .field t t field.val.2 field.val.1 (.root t) field.property
      have hco := r4_orderedLayout_subtree ho hn
      have hcr := r4_recursiveIsbits_subtree hr hn
      have hcb := r4_field_noBitPadding t field.val.2 field.val.1 hpf
        (hr t (.root t)).2 field.property hbp
      have hcv := (hco field.val.2 (.root field.val.2)).1
      have hcps : m816_packedsize field.val.2 = .ok (positions field).length := by
        rw [r4_packedsize_eq_indices_length field.val.2 hco hcr hcb]
        simp only [positions, List.length_map]
      by_cases hce : r4_valueIndices field.val.2 = []
      · have hpositions : positions field = [] := by simp [positions, hce]
        have hcopy := r4_empty_transfers field.val.2 hco hcr hcb hce
        dsimp only [step]
        by_cases hpacked : m824_ispacked field.val.2 = true
        · rw [if_pos hpacked, r4_packed_empty_size field.val.2 hco hcr hcb hce hpacked]
          simp [r4_copyzero, hpositions, r4_scatter, r4_add_zero,
            show JInt.lit .i64 (0 : Int) = zero from rfl]
        · rw [if_neg hpacked, (hcopy _ _ _ _).2, resultBindOk,
            r4_packedsize_empty field.val.2 hco hcr hcb hce, resultBindOk]
          simp [hpositions, r4_scatter, r4_add_zero,
            show JInt.lit .i64 (0 : Int) = zero from rfl]
      have hparentmem : ∀ b ∈ r4_valueIndices field.val.2,
          field.val.1 + b ∈ r4_valueIndices t := by
        intro b hb
        rw [r4_valueIndices_fields t ho hr hpf]
        exact List.mem_flatMap.mpr ⟨field.val, field.property, List.mem_map.mpr ⟨b, hb, rfl⟩⟩
      have hchildwrite : ∀ b ∈ r4_valueIndices field.val.2,
          wo.val.toNat + field.val.1 + b < dst.length := by
        intro b hb
        have h := hwrite (field.val.1 + b) (hparentmem b hb)
        omega
      have hsomemem : ∃ b, b ∈ r4_valueIndices field.val.2 := by
        cases hcidx : r4_valueIndices field.val.2 with
        | nil => exact False.elim (hce hcidx)
        | cons b rest => exact ⟨b, by simp⟩
      obtain ⟨b, hbmem⟩ := hsomemem
      have hbound := hchildwrite b hbmem
      have hwomax : ((wo.val.toNat + field.val.1 : Nat) : Int) ≤ IntTy.max .i64 := by omega
      have hwochild : (wo + JInt.lit .i64 field.val.1).val =
          ((wo.val.toNat + field.val.1 : Nat) : Int) :=
        add_nat hwoval (lit_nat _ (by omega)) hwomax
      have hrochild : (ro + cursor).val = ((ro.val.toNat + k : Nat) : Int) :=
        add_nat hroval hk (by omega)
      have hwochildNat : (wo + JInt.lit .i64 field.val.1).val.toNat =
          wo.val.toNat + field.val.1 := by rw [hwochild, Int.toNat_natCast]
      have hrochildNat : (ro + cursor).val.toNat = ro.val.toNat + k := by
        rw [hrochild, Int.toNat_natCast]
      dsimp only [step]
      by_cases hpacked : m824_ispacked field.val.2 = true
      · have hidx := r4_valueIndices_packed field.val.2 hcv hpacked
        have hpositions : positions field =
            (List.range field.val.2.alignedSize.val.toNat).map
              (fun b => (wo.val.toNat + field.val.1) + b) := by
          simp only [positions, hidx]
        have hpositionslen : (positions field).length = field.val.2.alignedSize.val.toNat := by
          rw [hpositions]
          simp
        have hsizepos : 0 < field.val.2.alignedSize.val.toNat :=
          Nat.zero_lt_of_lt ((r4_mem_valueIndices field.val.2 b).mp hbmem).1
        have hlast := hchildwrite (field.val.2.alignedSize.val.toNat - 1)
          (by rw [hidx]; exact List.mem_range.mpr (by omega))
        have hwritefit : wo.val.toNat + field.val.1 + field.val.2.alignedSize.val.toNat ≤ dst.length := by omega
        have hreadfit : ro.val.toNat + k + field.val.2.alignedSize.val.toNat ≤ input.length := by omega
        have hsize : field.val.2.alignedSize = JInt.lit .i64 (positions field).length := by
          apply jint_eq_of_val
          rw [hpositionslen, lit_nat _ (by
            rw [Int.toNat_of_nonneg hcv.nonnegative]
            exact field.val.2.alignedSize.property.2),
            Int.toNat_of_nonneg hcv.nonnegative]
        have hmem : memcpyValue dst input (wo + JInt.lit .i64 field.val.1) (ro + cursor)
            field.val.2.alignedSize =
              r4_scatter dst (positions field) input (ro.val.toNat + k) := by
          simp only [memcpyValue, hwochildNat, hrochildNat]
          rw [hpositions]
          exact (r4_scatter_range dst input _ _ _ hwritefit hreadfit).symm
        rw [if_pos hpacked, hmem, hsize]
        rfl
      · rw [if_neg hpacked]
        have hrecursive := ih field.val.2 (r4_field_sizeOf_lt t field)
          hco hcr hcb dst input (wo + JInt.lit .i64 field.val.1) (ro + cursor)
          (by rw [hwochild]; omega) (by rw [hrochild]; omega) (by omega) himax
          (by rw [hrochildNat]; simpa only [positions, List.length_map] using hdfit)
          (by intro b hb; rw [hwochildNat]; exact hchildwrite b hb)
        rw [hrecursive, resultBindOk, hcps, resultBindOk, hwochildNat, hrochildNat]
        rfl
    rw [m862_copyfrompacked.eq_def, if_neg hp]
    change (do
      let result ← forIn t.fields.attach (output, zero) step
      pure result.1) = _
    have hloop := r4_forIn_scatter_positions t.fields.attach positions step input ro.val.toNat
      output.length himax hstep output zero 0 zero_val rfl (by
        rw [hflat, List.length_map]
        simpa using hread)
    rw [hloop]
    simp only [resultBindOk, resultPure, Nat.add_zero, hflat]

theorem r4_packedTransfers : PackedTransfersR4 := by
  intro t input output wo ro ho hb hr hbp hwo hro homax himax
  have hcount : ∀ bytes offset,
      (payload t (byteWindow bytes offset t.alignedSize.val.toNat)).length =
        (r4_valueIndices t).length := by
    intro bytes offset
    rw [← r4_payloadAt_window, r4_payloadAt_length]
  constructor
  · intro hread hwrite
    rw [hcount] at hwrite
    have h := r4_copytopacked_value_bounds t ho hr hbp output input wo ro
      hwo hro homax himax hwrite (by
        intro b hb
        have hlt := ((r4_mem_valueIndices t b).mp hb).1
        omega)
    rw [r4_payloadAt_window] at h
    exact h
  · intro hwrite hread
    rw [hcount] at hread ⊢
    let positions := (r4_valueIndices t).map (fun b => wo.val.toNat + b)
    let result := r4_scatter output positions input ro.val.toNat
    have hpos : ∀ b ∈ positions, b < output.length := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      have hi' := ((r4_mem_valueIndices t i).mp hi).1
      omega
    have hresult : m862_copyfrompacked t output input wo ro = .ok result :=
      r4_copyfrompacked_value_bounds t ho hr hbp output input wo ro
        hwo hro homax himax hread (by
          intro b hb
          have hlt := ((r4_mem_valueIndices t b).mp hb).1
          omega)
    refine ⟨result, hresult, r4_scatter_length output positions input ro.val.toNat, ?_, ?_⟩
    · rw [← r4_payloadAt_window]
      have hord : positions.Pairwise (· < ·) :=
        List.Pairwise.map _ (fun _ _ h => Nat.add_lt_add_left h wo.val.toNat)
          (r4_valueIndices_sorted t)
      have hgather := r4_gather_scatter output positions input ro.val.toNat hord hpos
        (by simpa only [positions, List.length_map] using hread)
      simpa only [positions, List.map_map, List.length_map, Function.comp_def,
        r4_payloadAt, result] using hgather
    · intro b _ houtside
      apply r4_scatter_outside
      intro hbmem
      obtain ⟨i, hi, hindex⟩ := List.mem_map.mp hbmem
      have hinfo := (r4_mem_valueIndices t i).mp hi
      rcases houtside with hlo | hhi | hpad
      · omega
      · omega
      · have hsub : b - wo.val.toNat = i := by omega
        exact hpad (hsub ▸ hinfo.2)

theorem r4_scalarConversion : ScalarConversionR4 :=
  r4_scalarConversion_from_packedTransfers r4_packedTransfers

theorem r4_paddingConversion : PaddingConversionR4 :=
  r4_paddingConversion_from_packedTransfers r4_packedTransfers

theorem r4_scalarRoundtrip_proven : property_reinterpretarray_scalar_roundtrip :=
  r4_scalarConversion

theorem r4_paddingConversion_proven : property_reinterpretarray_padding_conversion :=
  r4_paddingConversion

theorem r4_multidimcov_packed_copy_proven :
    property_multidimcov_reinterpretarray_packed_copy :=
  ⟨r4_packedTransfers, r4_paddingConversion⟩

theorem r9_cycle_index (size n : Nat) (index : I64) (hpos : 0 < size)
    (hmax : (size : Int) < IntTy.max .i64)
    (hi : index.val = ((n % size : Nat) : Int) + 1) :
    (index - one).val.toNat = n % size := by
  have hm := Nat.mod_lt n hpos
  rw [val_sub, hi, one_val, Int.add_sub_cancel]
  rw [wrapInt_nat (n % size) (by omega), Int.toNat_natCast]

theorem r9_cycle_advance (size n : Nat) (limit index : I64) (hpos : 0 < size)
    (hmax : (size : Int) < IntTy.max .i64) (hl : limit.val = (size : Int))
    (hi : index.val = ((n % size : Nat) : Int) + 1) :
    (if limit < index + one then one else index + one).val =
      (((n + 1) % size : Nat) : Int) + 1 := by
  have hm := Nat.mod_lt n hpos
  have hadd : (index + one).val = ((n % size : Nat) : Int) + 2 := by
    rw [val_add, hi, one_val]
    apply wrapInt_of_inRange
    constructor
    · have := i64_min_nonpos
      omega
    · omega
  have hnext : (n + 1) % size = (n % size + 1) % size := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases hlast : n % size + 1 = size
  · have hlt : limit < index + one := by rw [lt_iff_val, hl, hadd]; omega
    rw [if_pos hlt, one_val, hnext, hlast, Nat.mod_self]
    simp
  · have hlt : ¬ limit < index + one := by rw [lt_iff_val, hl, hadd]; omega
    have hsmall : n % size + 1 < size := by omega
    rw [if_neg hlt, hadd, hnext, Nat.mod_eq_of_lt hsmall]
    omega

def r9_cycleGood (source target : List Bool) (sn tn n : Nat) : Prop :=
  source.getD (n % sn) false = true → target.getD (n % tn) false = true

theorem r9_good_period (source target : List Bool) (sn tn period : Nat)
    (hp : 0 < period) (hs : sn ∣ period) (ht : tn ∣ period)
    (hprefix : ∀ n < period, r9_cycleGood source target sn tn n) :
    ∀ n, r9_cycleGood source target sn tn n := by
  intro n
  have h := hprefix (n % period) (Nat.mod_lt n hp)
  unfold r9_cycleGood at h ⊢
  rw [Nat.mod_mod_of_dvd n hs, Nat.mod_mod_of_dvd n ht] at h
  exact h

theorem r9_not_bad_iff_good (a b : Bool) :
    (a && !b) = false ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp

theorem r9_cycle_loop (source target : List Bool) (sn tn : Nat) (slen tlen : I64)
    (hspos : 0 < sn) (htpos : 0 < tn)
    (hsmax : (sn : Int) < IntTy.max .i64) (htmax : (tn : Int) < IntTy.max .i64)
    (hslen : slen.val = (sn : Int)) (htlen : tlen.val = (tn : Int)) :
    ∀ remaining n (si ti : I64),
      sn * tn - n ≤ remaining → n < sn * tn →
      si.val = ((n % sn : Nat) : Int) + 1 →
      ti.val = ((n % tn : Nat) : Int) + 1 →
      (∀ m < n, r9_cycleGood source target sn tn m) →
      ∃ b, m772_arraySubpadding.loop source target slen tlen si ti = .ok b ∧
        (b = true ↔ ∀ m, r9_cycleGood source target sn tn m) := by
  intro remaining
  induction remaining with
  | zero =>
    intro n si ti hrem hn _ _ _
    omega
  | succ remaining ih =>
    intro n si ti hrem hn hsi hti hprefix
    have hsindex := r9_cycle_index sn n si hspos hsmax hsi
    have htindex := r9_cycle_index tn n ti htpos htmax hti
    let bad := source.getD (n % sn) false && !target.getD (n % tn) false
    by_cases hbad : bad = true
    · have hnotall : ¬ ∀ m, r9_cycleGood source target sn tn m := by
        intro hall
        have hfalse := (r9_not_bad_iff_good _ _).mpr (hall n)
        change bad = false at hfalse
        rw [hbad] at hfalse
        cases hfalse
      refine ⟨false, ?_, by simp [hnotall]⟩
      rw [m772_arraySubpadding.loop.eq_def]
      dsimp only
      rw [hsindex, htindex]
      change (if bad then _ else _) = _
      rw [if_pos hbad]
      rfl
    · have hbadfalse : bad = false := Bool.eq_false_iff.mpr hbad
      have hgood : r9_cycleGood source target sn tn n :=
        (r9_not_bad_iff_good _ _).mp hbadfalse
      have hprefix' : ∀ m < n + 1, r9_cycleGood source target sn tn m := by
        intro m hm
        by_cases hlt : m < n
        · exact hprefix m hlt
        · have heq : m = n := by omega
          exact heq ▸ hgood
      let si' := if slen < si + one then one else si + one
      let ti' := if tlen < ti + one then one else ti + one
      have hsi' : si'.val = ((((n + 1) % sn : Nat) : Int)) + 1 :=
        r9_cycle_advance sn n slen si hspos hsmax hslen hsi
      have hti' : ti'.val = ((((n + 1) % tn : Nat) : Int)) + 1 :=
        r9_cycle_advance tn n tlen ti htpos htmax htlen hti
      have hcycle : (si' == one && ti' == one) = true ↔
          (n + 1) % sn = 0 ∧ (n + 1) % tn = 0 := by
        rw [Bool.and_eq_true, beq_iff_val, beq_iff_val, hsi', hti', one_val]
        simp only [decide_eq_true_eq]
        omega
      have hmodel : m772_arraySubpadding.loop source target slen tlen si ti =
          if si' == one && ti' == one then .ok true
          else m772_arraySubpadding.loop source target slen tlen si' ti' := by
        rw [m772_arraySubpadding.loop.eq_def]
        dsimp only
        rw [hsindex, htindex]
        change (if bad then _ else _) = _
        rw [if_neg hbad]
        rfl
      by_cases hdone : (si' == one && ti' == one) = true
      · have hmod := hcycle.mp hdone
        have hall := r9_good_period source target sn tn (n + 1) (by omega)
          (Nat.dvd_of_mod_eq_zero hmod.1) (Nat.dvd_of_mod_eq_zero hmod.2) hprefix'
        refine ⟨true, ?_, by simp [hall]⟩
        rw [hmodel, if_pos hdone]
      · have hn' : n + 1 < sn * tn := by
          by_cases hlt : n + 1 < sn * tn
          · exact hlt
          · have heq : n + 1 = sn * tn := by omega
            apply False.elim
            apply hdone
            apply hcycle.mpr
            simp [heq, Nat.mul_mod_right, Nat.mul_mod_left]
        obtain ⟨b, hb, hsem⟩ := ih (n + 1) si' ti' (by omega) hn' hsi' hti' hprefix'
        refine ⟨b, ?_, hsem⟩
        rw [hmodel, if_neg hdone]
        exact hb

theorem r9_cycle_from_start (source target : List Bool) (sn tn : Nat) (slen tlen : I64)
    (hspos : 0 < sn) (htpos : 0 < tn)
    (hsmax : (sn : Int) < IntTy.max .i64) (htmax : (tn : Int) < IntTy.max .i64)
    (hslen : slen.val = (sn : Int)) (htlen : tlen.val = (tn : Int)) :
    ∃ b, m772_arraySubpadding.loop source target slen tlen one one = .ok b ∧
      (b = true ↔ ∀ n, r9_cycleGood source target sn tn n) := by
  exact r9_cycle_loop source target sn tn slen tlen hspos htpos hsmax htmax hslen htlen
    (sn * tn) 0 one one (by omega) (Nat.mul_pos hspos htpos)
    (by simp [one_val]) (by simp [one_val]) (by intro m hm; omega)

theorem r9_getD_true (mask : List Bool) (b : Nat) (hb : b < mask.length) :
    mask.getD b false = true ↔ mask[b]? = some true := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]
  cases mask[b] <;> simp

theorem r9_datatype_size_lt_i64 (t : TypeLayout)
    (hv : ValidStorageLayout t) (hbound : JuliaDatatypeSizeBound t) :
    (t.alignedSize.val.toNat : Int) < IntTy.max .i64 := by
  have hmax : IntTy.max .u32 < IntTy.max .i64 := by
    simp [IntTy.max, IntTy.signed, IntTy.bits]
  rw [Int.toNat_of_nonneg hv.nonnegative]
  exact Int.lt_of_le_of_lt hbound hmax

theorem r9_padded_not_all_value (t : TypeLayout)
    (hv : ValidStorageLayout t) (hp : m824_ispacked t = false) :
    ¬ ∀ b < t.alignedSize.val.toNat, ValueByte t b := by
  intro hall
  have hpadding := hv.paddingMetadata.mpr hall
  simp [m824_ispacked, hpadding] at hp

theorem r9_padded_positive (t : TypeLayout)
    (hv : ValidStorageLayout t) (hp : m824_ispacked t = false) :
    0 < t.alignedSize.val.toNat ∧ 0 < t.alignedSize.val := by
  have hnot := r9_padded_not_all_value t hv hp
  have hn : 0 < t.alignedSize.val.toNat := by
    by_cases hpos : 0 < t.alignedSize.val.toNat
    · exact hpos
    · exact False.elim (hnot (by intro b hb; omega))
  have hcast := Int.toNat_of_nonneg hv.nonnegative
  exact ⟨hn, by omega⟩

theorem r9_padded_masks_periodic (source target : TypeLayout)
    (hsv : ValidStorageLayout source) (htv : ValidStorageLayout target)
    (hsbound : JuliaDatatypeSizeBound source) (htbound : JuliaDatatypeSizeBound target)
    (hsb : source.isBits = true) (htb : target.isBits = true)
    (hsr : RecursiveIsbitsLayout source) (htr : RecursiveIsbitsLayout target)
    (hsp : ¬ BitPadded source) (htp : ¬ BitPadded target)
    (hspacked : m824_ispacked source = false) (htpacked : m824_ispacked target = false) :
    ∀ b, m772_arraySubpadding source target = .ok b ↔
      (b = true ↔ PaddingCompatible source target) := by
  obtain ⟨sm, hsm, hslen, hsmask, _⟩ :=
    r4_nonPaddingBytes_mask source hsv hsb hsr hsp
  obtain ⟨tm, htm, htlen, htmask, _⟩ :=
    r4_nonPaddingBytes_mask target htv htb htr htp
  have hspos := r9_padded_positive source hsv hspacked
  have htpos := r9_padded_positive target htv htpacked
  have hsmax := r9_datatype_size_lt_i64 source hsv hsbound
  have htmax := r9_datatype_size_lt_i64 target htv htbound
  have hsnonempty : sm.isEmpty = false := by
    cases sm with
    | nil => simp at hslen; omega
    | cons _ _ => rfl
  have htnonempty : tm.isEmpty = false := by
    cases tm with
    | nil => simp at htlen; omega
    | cons _ _ => rfl
  have hsval : (JInt.lit .i64 sm.length).val = (source.alignedSize.val.toNat : Int) := by
    rw [hslen]
    exact lit_nat _ (Int.le_of_lt hsmax)
  have htval : (JInt.lit .i64 tm.length).val = (target.alignedSize.val.toNat : Int) := by
    rw [htlen]
    exact lit_nat _ (Int.le_of_lt htmax)
  obtain ⟨answer, hloop, hanswer⟩ :=
    r9_cycle_from_start sm tm source.alignedSize.val.toNat target.alignedSize.val.toNat
      (JInt.lit .i64 sm.length) (JInt.lit .i64 tm.length)
      hspos.1 htpos.1 hsmax htmax hsval htval
  have hmodel : m772_arraySubpadding source target = .ok answer := by
    simp only [m772_arraySubpadding, hspacked, htpacked, Bool.false_eq_true,
      ↓reduceIte, hsm, htm, resultBindOk, hsnonempty, htnonempty]
    exact hloop
  have hperiodic :
      (∀ n, r9_cycleGood sm tm source.alignedSize.val.toNat target.alignedSize.val.toNat n) ↔
        (∀ n, ValueByte source (n % source.alignedSize.val.toNat) →
          ValueByte target (n % target.alignedSize.val.toNat)) := by
    have hsget : ∀ n, sm.getD (n % source.alignedSize.val.toNat) false = true ↔
        ValueByte source (n % source.alignedSize.val.toNat) := by
      intro n
      have hn : n % source.alignedSize.val.toNat < sm.length := by
        rw [hslen]
        exact Nat.mod_lt n hspos.1
      exact (r9_getD_true sm _ hn).trans (hsmask _ hn)
    have htget : ∀ n, tm.getD (n % target.alignedSize.val.toNat) false = true ↔
        ValueByte target (n % target.alignedSize.val.toNat) := by
      intro n
      have hn : n % target.alignedSize.val.toNat < tm.length := by
        rw [htlen]
        exact Nat.mod_lt n htpos.1
      exact (r9_getD_true tm _ hn).trans (htmask _ hn)
    constructor
    · intro h n hs
      exact (htget n).mp (h n ((hsget n).mpr hs))
    · intro h n hs
      exact (htget n).mpr (h n ((hsget n).mp hs))
  have hcompat : PaddingCompatible source target ↔
      ∀ n, ValueByte source (n % source.alignedSize.val.toNat) →
        ValueByte target (n % target.alignedSize.val.toNat) := by
    constructor
    · intro h
      rcases h with hall | ⟨_, _, hperiodic⟩
      · exact False.elim (r9_padded_not_all_value target htv htpacked hall)
      · exact hperiodic
    · intro h
      exact Or.inr ⟨hspos.2, htpos.2, h⟩
  have hcorrect : answer = true ↔ PaddingCompatible source target :=
    hanswer.trans (hperiodic.trans hcompat.symm)
  intro b
  rw [hmodel]
  by_cases hc : PaddingCompatible source target
  · have ha := hcorrect.mpr hc
    rw [ha]
    cases b <;> simp [hc]
  · have ha : answer = false := Bool.eq_false_iff.mpr (fun h => hc (hcorrect.mp h))
    rw [ha]
    cases b <;> simp [hc]

theorem r9_arraySubpadding_semantics (source target : TypeLayout)
    (hsv : ValidStorageLayout source) (htv : ValidStorageLayout target)
    (hsbound : JuliaDatatypeSizeBound source) (htbound : JuliaDatatypeSizeBound target)
    (hsb : source.isBits = true) (htb : target.isBits = true)
    (hsr : RecursiveIsbitsLayout source) (htr : RecursiveIsbitsLayout target)
    (hsp : ¬ BitPadded source) (htp : ¬ BitPadded target) :
    ∀ b, m772_arraySubpadding source target = .ok b ↔
      (b = true ↔ PaddingCompatible source target) := by
  by_cases htargetPacked : m824_ispacked target = true
  · have hpadding : target.datatypePadding = false := by simpa [m824_ispacked] using htargetPacked
    have hc : PaddingCompatible source target := Or.inl (htv.paddingMetadata.mp hpadding)
    have hmodel := (reinterpretPaddingChecks.1 source target).1 htargetPacked
    intro b
    rw [hmodel]
    cases b <;> simp [hc]
  · have htpf : m824_ispacked target = false := Bool.eq_false_iff.mpr htargetPacked
    by_cases hsourcePacked : m824_ispacked source = true
    · have hpadding : source.datatypePadding = false := by simpa [m824_ispacked] using hsourcePacked
      have hsourceValue := hsv.paddingMetadata.mp hpadding
      have hnotall := r9_padded_not_all_value target htv htpf
      have hc : ¬ PaddingCompatible source target := by
        intro h
        rcases h with hall | ⟨hspos, htpos, hperiodic⟩
        · exact hnotall hall
        · apply hnotall
          intro b hb
          have hsNat : 0 < source.alignedSize.val.toNat := by
            have hcast := Int.toNat_of_nonneg hsv.nonnegative
            omega
          have h := hperiodic b (hsourceValue _ (Nat.mod_lt b hsNat))
          simpa only [Nat.mod_eq_of_lt hb] using h
      have hmodel := (reinterpretPaddingChecks.1 source target).2 htpf hsourcePacked
      intro b
      rw [hmodel]
      cases b <;> simp [hc]
    · exact r9_padded_masks_periodic source target hsv htv hsbound htbound hsb htb hsr htr
        hsp htp (Bool.eq_false_iff.mpr hsourcePacked) htpf

theorem r9_arrayPadding : ArrayPaddingR9 := by
  classical
  intro t s htv hsv htbound hsbound htb hsb htr hsr htp hsp
  have hread := r9_arraySubpadding_semantics t s htv hsv htbound hsbound htb hsb htr hsr htp hsp
  have hwrite := r9_arraySubpadding_semantics s t hsv htv hsbound htbound hsb htb hsr htr hsp htp
  refine ⟨hread, ?_⟩
  intro T S A a hat has hreadFlag hwriteFlag
  have hrmodel : m237_checkReadable a =
      if PaddingCompatible t s then .ok () else .error .padding := by
    by_cases hflag : a.readable = true
    · have hc := hreadFlag hflag
      simp [m237_checkReadable, hflag, hc]
    · have hflagFalse : a.readable = false := Bool.eq_false_iff.mpr hflag
      by_cases hc : PaddingCompatible t s
      · have hsub := (hread true).mpr (by simp [hc])
        simp [m237_checkReadable, hflagFalse, hat, has, hsub, hc]
      · have hsub := (hread false).mpr (by simp [hc])
        simp [m237_checkReadable, hflagFalse, hat, has, hsub, hc]
  have hwmodel : m244_checkWritable a =
      if PaddingCompatible s t then .ok () else .error .padding := by
    by_cases hflag : a.writable = true
    · have hc := hwriteFlag hflag
      simp [m244_checkWritable, hflag, hc]
    · have hflagFalse : a.writable = false := Bool.eq_false_iff.mpr hflag
      by_cases hc : PaddingCompatible s t
      · have hsub := (hwrite true).mpr (by simp [hc])
        simp [m244_checkWritable, hflagFalse, hat, has, hsub, hc]
      · have hsub := (hwrite false).mpr (by simp [hc])
        simp [m244_checkWritable, hflagFalse, hat, has, hsub, hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrmodel]
    by_cases hc : PaddingCompatible t s <;> simp [hc]
  · rw [hwmodel]
    by_cases hc : PaddingCompatible s t <;> simp [hc]
  · intro hc
    exact ⟨.padding, by rw [hrmodel, if_neg hc]⟩
  · intro hc
    exact ⟨.padding, by rw [hwmodel, if_neg hc]⟩

theorem r9_paddingChecks_proven : property_reinterpretarray_padding_checks :=
  r9_arrayPadding

theorem r9_paddingErrorDisplay_proven : property_reinterpretarray_padding_error_display :=
  r9_arrayPadding

theorem r9_paddingHelpers : PaddingHelpersR9 := by
  refine ⟨r4_fullPaddingLayoutAnyError, r9_arrayPadding, r4_nonPaddingBytes_mask, ?_,
    r4_structSubpadding_semantics⟩
  intro t hv hb hbp
  have hbit := Strict.bitPaddingDetection t |>.mpr hbp
  exact ⟨.argument, by simp [m750_nonPaddingBytes, hbit]⟩

theorem r9_paddingHelpers_proven : property_reinterpretarray_padding_helpers :=
  r9_paddingHelpers

theorem r9_paddingLayout_proven : property_reinterpretarray_padding_layout :=
  r9_paddingHelpers

private theorem r10_layoutNodeFromRoot {root node : TypeLayout}
    (h : LayoutNode root node) : Round10.LayoutNode root node := by
  exact LayoutNode.rec
    (motive := fun n (_ : LayoutNode root n) => Round10.LayoutNode root n)
    (Round10.LayoutNode.root root)
    (fun parent child off hnode hfield ih =>
      Round10.LayoutNode.field root parent child off ih hfield)
    (fun parent child hnode hmember ih =>
      Round10.LayoutNode.member root parent child ih hmember)
    h


theorem r10_constructorPaddingFlags_proven :
    Round10.property_reinterpretarray_padding_flags := by
  classical
  intro T S A t s p htv hsv htbound hsbound htb hsb htr hsr _hshape
  have htr' : RecursiveIsbitsLayout t := by
    intro node hnode
    exact htr node (r10_layoutNodeFromRoot hnode)
  have hsr' : RecursiveIsbitsLayout s := by
    intro node hnode
    exact hsr node (r10_layoutNodeFromRoot hnode)
  refine ⟨?_, ?_⟩
  · intro a hview
    have hnotT : ¬ BitPadded t := by
      intro hpad
      have hhas := Strict.bitPaddingDetection t |>.mpr hpad
      simp [m73_reinterpret, htb, hsb, hhas, m27_throwbitpadding] at hview
    have hnotS : ¬ BitPadded s := by
      intro hpad
      have hhas := Strict.bitPaddingDetection s |>.mpr hpad
      have hclear := r4_noBitPadding t hnotT
      simp [m73_reinterpret, htb, hsb, hclear, hhas, m27_throwbitpadding] at hview
    have hreadPadding :=
      r9_arrayPadding t s htv hsv htbound hsbound htb hsb htr' hsr' hnotT hnotS
    have hwritePadding :=
      r9_arrayPadding s t hsv htv hsbound htbound hsb htb hsr' htr' hnotS hnotT
    rcases reinterpretConstructorValidation.2.1 t s p a hview with
      ⟨_, _, _, _, _, hread, hwrite, _, _⟩
    exact ⟨(hreadPadding.1 a.readable).mp hread,
      (hwritePadding.1 a.writable).mp hwrite⟩
  · intro a hview
    have hnotT : ¬ BitPadded t := by
      intro hpad
      have hhas := Strict.bitPaddingDetection t |>.mpr hpad
      simp [m107_reinterpretReshape, htb, hsb, hhas, m27_throwbitpadding] at hview
    have hnotS : ¬ BitPadded s := by
      intro hpad
      have hhas := Strict.bitPaddingDetection s |>.mpr hpad
      have hclear := r4_noBitPadding t hnotT
      simp [m107_reinterpretReshape, htb, hsb, hclear, hhas, m27_throwbitpadding] at hview
    have h188 : m188_reinterpretReshape t s p = .ok a := by
      simpa [m188_reinterpretReshape] using hview
    have hreadPadding :=
      r9_arrayPadding t s htv hsv htbound hsbound htb hsb htr' hsr' hnotT hnotS
    have hwritePadding :=
      r9_arrayPadding s t hsv htv hsbound htbound hsb htb hsr' htr' hnotS hnotT
    rcases reinterpretConstructorValidation.2.2 t s p a h188 with
      ⟨_, _, _, _, _, hread, hwrite, _, _, _⟩
    exact ⟨(hreadPadding.1 a.readable).mp hread,
      (hwritePadding.1 a.writable).mp hwrite⟩

end Statements
end JuliaLean.Proofs.base.reinterpretarray

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

namespace JuliaLean.Statements.reinterpretarray.round7
open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.Proofs.base.reinterpretarray
open JuliaLean.Proofs.base.reinterpretarray.Strict

inductive LayoutNode : TypeLayout → TypeLayout → Prop where
  | root (t : TypeLayout) : LayoutNode t t
  | field (root parent child : TypeLayout) (off : Nat) :
      LayoutNode root parent → (off, child) ∈ parent.fields → LayoutNode root child
  | member (root parent child : TypeLayout) :
      LayoutNode root parent → child ∈ parent.members → LayoutNode root child

def RecursiveIsbitsLayout (t : TypeLayout) : Prop :=
  ∀ node, LayoutNode t node → node.isBits = true ∧ node.union = false

def RepresentableAxes (axs : List Axis) : Prop :=
  ∀ ax ∈ axs, IntTy.min .i64 ≤ ax.first.val ∧ 0 ≤ ax.length.val ∧
    IntTy.min .i64 ≤ ax.first.val + ax.length.val - 1 ∧
    ax.first.val + ax.length.val - 1 ≤ IntTy.max .i64

namespace CartesianRange
open JuliaLean.base.range
local instance : JFirst Axis I64 := ⟨fun ax => .ok ax.first⟩
local instance : JLast Axis I64 := ⟨fun ax => .ok (ax.first + ax.length - one)⟩
local instance : JStep Axis I64 := ⟨fun _ => .ok one⟩
local instance : JEltype Axis I64 := ⟨⟩
local instance : JEq I64 I64 := ⟨fun x y => x == y⟩
local instance : JConvert I64 I64 := ⟨fun x => .ok x⟩
local instance : JIsempty Axis := ⟨fun ax => .ok (decide (ax.length.val ≤ 0))⟩
def start (ax : Axis) : Option (I64 × I64) :=
  (iterate_OrdinalRange ax).toOption.getD none
def step (ax : Axis) (j : I64) : Option (I64 × I64) :=
  (iterate_OrdinalRange_state ax j).toOption.getD none
end CartesianRange

namespace RangeAccess
open JuliaLean.base.range
local instance : JOneunit I64 := ⟨one⟩
local instance : JConvert I64 I64 := ⟨fun i => .ok i⟩
local instance : JLt I64 I64 := ⟨fun i j => decide (i.val < j.val)⟩
local instance : JLe I64 I64 := ⟨fun i j => decide (i.val ≤ j.val)⟩
local instance : JThrowBoundserror (UnitRange I64) I64 :=
  ⟨fun _ _ => .error (.jl .boundsError)⟩
def get (ax : Axis) (i : I64) : RResult I64 :=
  (_getindex_UnitRange (T := I64) (I := I64) (D := I64) (E := I64)
    ⟨ax.first, ax.first + ax.length - one⟩ i).mapError (fun _ => .bounds)
end RangeAccess

def axisCheck (ax : Axis) (i : I64) : Bool :=
  (JuliaLean.base.abstractarray.checkindexReal
    (fun ax : Axis => .ok ax.first.val)
    (fun ax : Axis => .ok (ax.first.val + ax.length.val - 1))
    (fun (lo : Int) (i : I64) => .ok (decide (lo ≤ i.val)))
    (fun (i : I64) (hi : Int) => .ok (decide (i.val ≤ hi))) ax i).toOption.getD false

namespace IdentityRangeAccess
def get (ax : Axis) (i : I64) : RResult I64 :=
  (JuliaLean.base.indices.getindex_IdentityUnitRange_Integer
    (fun _ index =>
      if axisCheck ax index then .ok () else .error .boundsError)
    (fun index => .ok index)
    (⟨⟨ax.first, ax.first + ax.length - one⟩⟩ :
      JuliaLean.base.indices.IdentityUnitRange (JuliaLean.base.range.UnitRange I64))
    i).mapError (fun _ => .bounds)
end IdentityRangeAccess

def NextPrevious : Prop :=
  ∀ (k : I64) (ind : SCartesianIndex2), 1 < k.val → 1 ≤ ind.i.val → ind.i.val ≤ k.val →
    m282_prevIndex k (m280_nextIndex k ind) = ind ∧
    m280_nextIndex k (m282_prevIndex k ind) = ind

def FullCartesianTransitions : Prop :=
  ∀ (k : Nat) (iter : SCartesianIndices2 k), 1 < k →
    (k : Int) ≤ IntTy.max .i64 → RepresentableAxes [iter.indices2] →
    (iter.indices2.length.val = 0 → m309_indicesIterate CartesianRange.start iter = none) ∧
    (0 < iter.indices2.length.val →
      m309_indicesIterate CartesianRange.start iter =
        some (m301_indicesFirst iter, (one, iter.indices2.first, iter.indices2.first))) ∧
    (∀ (i j : I64), 1 ≤ i.val → i.val ≤ k → iter.indices2.first.val ≤ j.val →
      j.val ≤ iter.indices2.first.val + iter.indices2.length.val - 1 →
      let next := m316_indicesIterateState CartesianRange.step iter i j j
      (next = none ↔ i.val = k ∧ j.val = iter.indices2.first.val + iter.indices2.length.val - 1) ∧
      (∀ ind state, next = some (ind, state) →
        1 ≤ ind.i.val ∧ ind.i.val ≤ k ∧
        iter.indices2.first.val ≤ ind.j.val ∧
        ind.j.val < iter.indices2.first.val + iter.indices2.length.val ∧
        scartesianRank (JInt.lit .i64 k) ind =
          scartesianRank (JInt.lit .i64 k) ⟨i, j⟩ + 1))

def EachindexDomains : Prop :=
  ∀ {T S A : Type} (k : Nat) (each : IndexStyleModel → A → Axis)
      (a : ReinterpretArray T S A), RepresentableAxes [each .linear a.parent] →
    (∀ iter, m290_eachindexReshaped (K := k) each a = .ok iter →
      ∀ (i j : I64),
        (1 ≤ i.val ∧ i.val ≤ k ∧
          iter.indices2.first.val ≤ j.val ∧
          j.val < iter.indices2.first.val + iter.indices2.length.val) ↔
        (1 ≤ i.val ∧ i.val ≤ k ∧
          (each .linear a.parent).first.val ≤ j.val ∧
          j.val < (each .linear a.parent).first.val + (each .linear a.parent).length.val)) ∧
    (k ≤ 1 → ∃ e, m290_eachindexReshaped (K := k) each a = .error e) ∧
    (1 < k → ∃ iter, m290_eachindexReshaped (K := k) each a = .ok iter)

def SharedIteration : Prop :=
  ∀ {T S A : Type} (k : Nat) (each : IndexStyleModel → A → Axis)
      (axes : ReinterpretArray T S A → List Axis)
      (a : ReinterpretArray T S A) (rest : List (ReinterpretArray T S A)),
    RepresentableAxes [each .linear a.parent] →
    (∀ b ∈ rest, RepresentableAxes [each .linear b.parent]) →
    1 < k →
    let run := m291_eachindex
      (fun _ q => m290_eachindexReshaped (K := k) each q)
      (fun _ _ => (JuliaLean.base.abstractarray.throwEachindexMismatch
        (fun a bs => String.intercalate ", " (a :: bs)) "axes" "" []).mapError (fun _ => .argument))
      (.staticCartesian k) a rest axes
    ((∃ e, run = .error e) ↔
      ∃ b ∈ rest, each .linear b.parent ≠ each .linear a.parent) ∧
    (∀ iter, run = .ok iter →
      (m298_indicesSize iter).1 * (m298_indicesSize iter).2.val.toNat =
        k * (each .linear a.parent).length.val.toNat ∧
      ∀ b ∈ rest, iter.indices2 = each .linear b.parent)

def CartesianIterationBehavior : Prop :=
  NextPrevious ∧ FullCartesianTransitions ∧ EachindexDomains ∧ SharedIteration

def IteratorBounds {k : Nat} (iter : SCartesianIndices2 k) (i j : I64) : RResult Unit :=
  if axisCheck ⟨one, JInt.lit .i64 k⟩ i && axisCheck iter.indices2 j then
    .ok () else .error .bounds

def CartesianRangeOperations : Prop :=
  ∀ (k : Nat) (ax : Axis), 1 < k → (k : Int) ≤ IntTy.max .i64 →
    RepresentableAxes [ax] →
    (m298_indicesSize (⟨ax⟩ : SCartesianIndices2 k) = (k, ax.length)) ∧
    (m299_indicesAxes (⟨ax⟩ : SCartesianIndices2 k) =
      [⟨one, JInt.lit .i64 k⟩, ax]) ∧
    (m301_indicesFirst (⟨ax⟩ : SCartesianIndices2 k) = ⟨one, ax.first⟩) ∧
    (m302_indicesLast (⟨ax⟩ : SCartesianIndices2 k) =
      ⟨JInt.lit .i64 k, ax.first + ax.length - one⟩) ∧
    (∀ i j, m304_indicesGet IteratorBounds RangeAccess.get
        (⟨ax⟩ : SCartesianIndices2 k) i j =
      if 1 ≤ i.val ∧ i.val ≤ k ∧ ax.first.val ≤ j.val ∧
          j.val ≤ ax.first.val + ax.length.val - 1 ∧ 1 ≤ j.val ∧
          j.val ≤ ax.length.val
      then .ok ⟨i, ax.first + (j - one)⟩ else .error .bounds) ∧
    (∀ i j, m304_indicesGet IteratorBounds IdentityRangeAccess.get
        (⟨ax⟩ : SCartesianIndices2 k) i j =
      if 1 ≤ i.val ∧ i.val ≤ k ∧ ax.first.val ≤ j.val ∧
          j.val ≤ ax.first.val + ax.length.val - 1
      then .ok ⟨i, j⟩ else .error .bounds)

def ConstructorArrayAxes (axs : List Axis) : Prop :=
  ∀ ax ∈ axs, IntTy.min .i64 ≤ ax.first.val ∧ 0 ≤ ax.length.val ∧
    IntTy.min .i64 ≤ ax.first.val + ax.length.val - 1 ∧
    ax.first.val + ax.length.val - 1 ≤ IntTy.max .i64

def DocumentedArrayInput {A : Type} (p : ArrayInput A) : Prop :=
  ShapeValid p ∧ ConstructorArrayAxes p.axes

def PlainSourceAdmissible {A : Type} (t s : TypeLayout) (p : ArrayInput A) : Prop :=
  t.isBits = true ∧ s.isBits = true ∧ ¬ BitPadded t ∧ ¬ BitPadded s ∧
  (p.rank = 0 → t.alignedSize.val = s.alignedSize.val) ∧
  (p.rank ≠ 0 → t.alignedSize.val ≠ s.alignedSize.val →
    let ax := p.axes.headD ⟨one, zero⟩
    ax.first.val = 1 ∧
      (if t.singleton then s.singleton = true else
        t.alignedSize.val ≠ 0 ∧
          (ax.length.val * s.alignedSize.val) % t.alignedSize.val = 0))

def OrdinaryConstructorValidation : Prop :=
  ∀ {T S A : Type} (t s : TypeLayout) (p : ArrayInput A),
    ValidStorageLayout t → ValidStorageLayout s → DocumentedArrayInput p →
    (if PlainSourceAdmissible t s p then
      ∃ a : ReinterpretArray T S (ArrayInput A),
        m73_reinterpret t s p = .ok a ∧ ConstructorResult t s p false a
    else ∃ e, m73_reinterpret (T := T) (S := S) t s p = .error e) ∧
    (if ReshapeAdmissible t s p then
      ∃ a : ReinterpretArray T S (ArrayInput A),
        m107_reinterpretReshape t s p = .ok a ∧
        m188_reinterpretReshape t s p = .ok a ∧ ConstructorResult t s p true a
    else
      (∃ e, m107_reinterpretReshape (T := T) (S := S) t s p = .error e) ∧
      (∃ e, m188_reinterpretReshape (T := T) (S := S) t s p = .error e))

/-- Registry id: reinterpretarray-cartesian-iteration. Cartesian iteration advances and reverses indices across the full representable outer axis, including nonempty axes beginning at typemin(Int); multi-array eachindex requires matching outer axes. -/
def property_reinterpretarray_cartesian_iteration : Prop :=
  CartesianIterationBehavior

/-- Registry id: reinterpretarray-cartesian-operations. Cartesian index size, axes and endpoints match the channel and outer range. Direct getindex uses UnitRange positional indexing, while IdentityUnitRange returns its label; OneTo starts at 1, so both forms agree there. -/
def property_reinterpretarray_cartesian_operations : Prop :=
  CartesianRangeOperations

/-- Registry id: reinterpretarray-constructor-validation-ordinary. For every shape-valid parent with representable axes, plain and reshaped reinterpret follow the documented layout checks. For a non-singleton plain reinterpret with changed element size, the first axis must start at 1 and its exact mathematical length-times-source-size product must divide by target size; otherwise construction throws an error. -/
def property_reinterpretarray_constructor_validation_ordinary : Prop :=
  OrdinaryConstructorValidation

open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Proofs.base.reinterpretarray
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

theorem cart_axisCheck (ax : Axis) (i : I64) :
    axisCheck ax i = decide (ax.first.val ≤ i.val ∧ i.val ≤ ax.first.val + ax.length.val - 1) := by
  simp [axisCheck, JuliaLean.base.abstractarray.checkindexReal, bind, Except.bind,
    Functor.map, Except.map, pure, Except.pure, Except.toOption]

theorem cart_endpoint (ax : Axis) (h : RepresentableAxes [ax]) :
    (ax.first + ax.length - one).val = ax.first.val + ax.length.val - 1 := by
  have hh := h ax (by simp)
  rw [val_sub, val_add, one_val, wrapInt_sub_left]
  exact wrapInt_of_inRange .i64 _ ⟨hh.2.2.1, hh.2.2.2⟩

theorem cart_rangeGet (ax : Axis) (i : I64) (h : RepresentableAxes [ax]) :
    RangeAccess.get ax i =
      if 1 ≤ i.val ∧ i.val ≤ ax.length.val then .ok (ax.first + (i - one))
      else .error .bounds := by
  have hh := h ax (by simp)
  have hf := ax.first.property
  have hi := i.property
  have hl := ax.length.property
  have hend := cart_endpoint ax h
  have hcond :
      (0 < i.val ∧ (ax.first + (i - one)).val ≤ (ax.first + ax.length - one).val ∧
        ax.first.val ≤ (ax.first + (i - one)).val) ↔ 1 ≤ i.val ∧ i.val ≤ ax.length.val := by
    rw [hend, val_add, val_sub, one_val, wrapInt_add_right]
    simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max] at hf hi hl hh ⊢
    omega
  simp only [RangeAccess.get, JuliaLean.base.range._getindex_UnitRange,
    JuliaLean.base.range.JConvert.convert, JuliaLean.base.range.JOneunit.oneunit,
    JuliaLean.base.range._in_unit_range, JuliaLean.base.range.JLt.lt,
    JuliaLean.base.range.JLe.le, JuliaLean.base.range.jint,
    JuliaLean.base.range.JThrowBoundserror.throwBoundserror]
  simp only [bind, Except.bind, pure, Except.pure,
    show (JInt.lit .i64 0).val = 0 by decide, ← Bool.decide_and, and_assoc, hcond]
  split <;> simp_all [Except.mapError]

theorem cart_operations : property_reinterpretarray_cartesian_operations := by
  intro k ax hk hmax hax
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i j
    have hget := cart_rangeGet ax j hax
    simp only [m304_indicesGet, IteratorBounds, cart_axisCheck, one_val, lit_nat k hmax,
      show (1 : Int) + (k : Int) - 1 = k by omega, hget]
    by_cases hbounds : 1 ≤ i.val ∧ i.val ≤ k ∧ ax.first.val ≤ j.val ∧
      j.val ≤ ax.first.val + ax.length.val - 1
    · have hb : (1 ≤ i.val ∧ i.val ≤ k) ∧ ax.first.val ≤ j.val ∧
        j.val ≤ ax.first.val + ax.length.val - 1 := by omega
      simp only [← Bool.decide_and, hb, decide_true, ↓reduceIte, resultBindOk]
      by_cases hj : 1 ≤ j.val ∧ j.val ≤ ax.length.val <;>
        simp [hj, hbounds, bind, Except.bind, pure, Except.pure]
    · have hb : ¬ ((1 ≤ i.val ∧ i.val ≤ k) ∧ ax.first.val ≤ j.val ∧
        j.val ≤ ax.first.val + ax.length.val - 1) := by omega
      simp [← Bool.decide_and, hb, hbounds, bind, Except.bind] <;> omega
  · intro i j
    simp only [m304_indicesGet, IteratorBounds, cart_axisCheck, one_val, lit_nat k hmax,
      show (1 : Int) + (k : Int) - 1 = k by omega]
    simp only [IdentityRangeAccess.get, JuliaLean.base.indices.getindex_IdentityUnitRange_Integer,
      cart_axisCheck]
    by_cases hi : 1 ≤ i.val ∧ i.val ≤ k
    · by_cases hj : ax.first.val ≤ j.val ∧ j.val ≤ ax.first.val + ax.length.val - 1
      · simp [← Bool.decide_and, hi, hj, hi.1, hi.2, hj.1, hj.2,
          bind, Except.bind, pure, Except.pure, Except.mapError]
      · simp [← Bool.decide_and, hi, hj, hi.1, hi.2,
          bind, Except.bind, pure, Except.pure]
    · simp [← Bool.decide_and, hi, bind, Except.bind] <;> omega


open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Proofs.base.reinterpretarray
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

theorem cart_nextPrevious : NextPrevious := by
  intro k ind hk hi1 hik
  rcases ind with ⟨i,j⟩
  dsimp at hi1 hik
  have hcancel1 : j + one - one = j := by
    apply jint_eq_of_val
    simp only [val_sub, val_add, wrapInt_sub_left, one_val]
    rw [Int.add_sub_cancel, wrapInt_of_inRange .i64 j.val j.property]
  have hcancel2 : j - one + one = j := by
    apply jint_eq_of_val
    simp only [val_sub, val_add, wrapInt_add_left, one_val]
    rw [Int.sub_add_cancel, wrapInt_of_inRange .i64 j.val j.property]
  constructor
  · by_cases hlt : i < k
    · have hiv : (i + one).val = i.val + 1 := by
        rw [val_add, one_val]
        exact wrapInt_of_inRange .i64 _ ⟨by have := i64_min_nonpos; omega,
          by have := k.property.2; change i.val < k.val at hlt; omega⟩
      have hgt : one < i + one := by change one.val < (i + one).val; rw [one_val,hiv]; omega
      have hc : i + one - one = i := by
        apply jint_eq_of_val
        rw [val_sub,hiv,one_val,Int.add_sub_cancel,wrapInt_of_inRange .i64 i.val i.property]
      simp only [one] at hgt hc
      simp only [m280_nextIndex,hlt,↓reduceIte,m282_prevIndex,hgt,hc]
    · have he : i = k := jint_eq_of_val (by change ¬ i.val < k.val at hlt; omega)
      subst i
      simp only [one] at hcancel1
      simp [m280_nextIndex,m282_prevIndex,hlt,hcancel1,
        show ¬ JInt.lit .i64 1 < JInt.lit .i64 1 by decide]
  · by_cases hgt : one < i
    · have hiv : (i - one).val = i.val - 1 := by
        rw [val_sub,one_val]
        exact wrapInt_of_inRange .i64 _ ⟨by have := i64_min_nonpos; change one.val < i.val at hgt; rw [one_val] at hgt; omega,
          by have := i.property.2; omega⟩
      have hlt : i - one < k := by change (i - one).val < k.val; rw [hiv]; omega
      have hc : i - one + one = i := by
        apply jint_eq_of_val
        rw [val_add,hiv,one_val,Int.sub_add_cancel,wrapInt_of_inRange .i64 i.val i.property]
      simp only [one] at hgt hlt hc
      simp only [m282_prevIndex,hgt,↓reduceIte,m280_nextIndex,hlt,hc]
    · have he : i = one := jint_eq_of_val (by change ¬ one.val < i.val at hgt; rw [one_val] at *; omega)
      subst i
      have hnot : ¬ k < k := by change ¬ k.val < k.val; omega
      simp only [one] at hgt hcancel2 ⊢
      simp [m282_prevIndex,m280_nextIndex,hgt,hnot,hcancel2]

theorem cart_eachindex : EachindexDomains := by
  intro T S A k each a _
  unfold m290_eachindexReshaped m288_indicesConstructor m369_parent
  by_cases hk : 1 < k
  · simp only [hk,↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · intro iter hi
      cases hi
      intro i j
      rfl
    · intro h; omega
    · intro _; exact ⟨_,rfl⟩
  · simp [hk]

theorem cart_start {k : Nat} (iter : SCartesianIndices2 k)
    (hpos : 0 < iter.indices2.length.val) :
    m309_indicesIterate CartesianRange.start iter =
      some (m301_indicesFirst iter,(one,iter.indices2.first,iter.indices2.first)) := by
  have hnot : ¬ iter.indices2.length.val ≤ 0 := by omega
  simp [m309_indicesIterate,CartesianRange.start,JuliaLean.base.range.iterate_OrdinalRange,
    JuliaLean.base.range.JIsempty.isempty,JuliaLean.base.range.JFirst.first,hnot,
    bind,Except.bind,pure,Except.pure,Functor.map,Except.map,Except.toOption,m301_indicesFirst]

theorem cart_empty {k : Nat} (iter : SCartesianIndices2 k)
    (hempty : iter.indices2.length.val = 0) :
    m309_indicesIterate CartesianRange.start iter = none := by
  simp [m309_indicesIterate,CartesianRange.start,JuliaLean.base.range.iterate_OrdinalRange,
    JuliaLean.base.range.JIsempty.isempty,JuliaLean.base.range.JFirst.first,hempty,
    bind,Except.bind,pure,Except.pure,Functor.map,Except.map,Except.toOption]

theorem cart_step (ax : Axis) (j : I64) :
    CartesianRange.step ax j =
      if j = ax.first + ax.length - one then none else some (j+one,j+one) := by
  by_cases h : j.val = (ax.first + ax.length - one).val <;>
    simp [CartesianRange.step,JuliaLean.base.range.iterate_OrdinalRange_state,
      JuliaLean.base.range.JLast.last,JuliaLean.base.range.JEq.eq,
      JuliaLean.base.range.JStep.step,JuliaLean.base.range.JConvert.convert,h,
      bind,Except.bind,pure,Except.pure,Functor.map,Except.map,Except.toOption,Subtype.ext_iff]

theorem cart_fullTransitions : FullCartesianTransitions := by
  intro k iter hk hmax hax
  have ha := hax iter.indices2 (by simp)
  have hend : (iter.indices2.first + iter.indices2.length - one).val =
      iter.indices2.first.val + iter.indices2.length.val - 1 := by
    rw [val_sub,val_add,one_val,wrapInt_sub_left]
    exact wrapInt_of_inRange .i64 _ ⟨ha.2.2.1,ha.2.2.2⟩
  have hkval := lit_nat k hmax
  refine ⟨cart_empty iter,cart_start iter,?_⟩
  intro i j hi1 hik hj1 hjlast
  dsimp only
  by_cases hlt : i.val < k
  · have hmodel : m316_indicesIterateState CartesianRange.step iter i j j =
        some (⟨i+one,j⟩,(i+one,j,j)) := by
      simp [m316_indicesIterateState,lt_iff_val,hkval,hlt]
    rw [hmodel]
    have hiv : (i+one).val = i.val + 1 := by
      rw [val_add,one_val]
      exact wrapInt_of_inRange .i64 _ ⟨by have := i64_min_nonpos; omega,by omega⟩
    refine ⟨by simp; omega,?_⟩
    intro ind state h
    cases h
    dsimp only
    refine ⟨by rw [hiv]; omega,by rw [hiv]; omega,hj1,by omega,?_⟩
    simp only [scartesianRank,hiv]
    omega
  · have hieq : i.val = k := by omega
    have heq : j = iter.indices2.first + iter.indices2.length - one ↔
        j.val = iter.indices2.first.val + iter.indices2.length.val - 1 := by
      constructor
      · intro h; rw [h,hend]
      · intro h; exact jint_eq_of_val (h.trans hend.symm)
    have hmodel : m316_indicesIterateState CartesianRange.step iter i j j =
        if j = iter.indices2.first + iter.indices2.length - one then none
        else some (⟨one,j+one⟩,(one,j+one,j+one)) := by
      by_cases hj : j = iter.indices2.first + iter.indices2.length - one <;>
        simp [m316_indicesIterateState,lt_iff_val,hkval,hlt,cart_step,hj]
    rw [hmodel]
    by_cases hjend : j = iter.indices2.first + iter.indices2.length - one
    · simp [hjend,hieq,hend]
    · rw [if_neg hjend]
      have hjne := mt heq.mpr hjend
      have hjv : (j+one).val = j.val + 1 := by
        rw [val_add,one_val]
        exact wrapInt_of_inRange .i64 _ ⟨by have := j.property.1; omega,by omega⟩
      refine ⟨by simp [hieq]; omega,?_⟩
      intro ind state h
      cases h
      dsimp only
      refine ⟨by rw [one_val]; omega,by rw [one_val]; omega,
        by rw [hjv]; omega,by rw [hjv]; omega,?_⟩
      simp only [scartesianRank,one_val,hjv,hieq,hkval]
      rw [Int.add_mul,Int.one_mul]
      omega


open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Proofs.base.reinterpretarray
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

theorem cart_mapM_ok {α β : Type} (f : α → β) (xs : List α) :
    xs.mapM (fun x => (Except.ok (f x) : RResult β)) = .ok (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.mapM_cons,ih]; rfl

theorem cart_shared : SharedIteration := by
  intro T S A k each axes a rest _ _ hk
  dsimp only
  let f : ReinterpretArray T S A → SCartesianIndices2 k := fun b => ⟨each .linear b.parent⟩
  have hm : ∀ b, m290_eachindexReshaped (K := k) each b = .ok (f b) := by
    intro b
    simp [m290_eachindexReshaped,m288_indicesConstructor,m369_parent,hk,f]
  have hall : ((rest.map f).all (· == f a)) = true ↔
      ∀ b ∈ rest, each .linear b.parent = each .linear a.parent := by
    simp [List.all_eq_true,beq_iff_eq,f,SCartesianIndices2.mk.injEq]
  have hnot : ((rest.map f).all (· == f a)) = false ↔
      ∃ b ∈ rest, each .linear b.parent ≠ each .linear a.parent := by
    classical
    constructor
    · intro hf
      apply Classical.byContradiction
      intro hn
      have ht : ∀ b ∈ rest, each .linear b.parent = each .linear a.parent := by
        intro b hb
        by_cases he : each .linear b.parent = each .linear a.parent
        · exact he
        · exact False.elim (hn ⟨b,hb,he⟩)
      have ht' := hall.mpr ht
      rw [hf] at ht'
      contradiction
    · rintro ⟨b,hb,hne⟩
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hne (hall.mp ht b hb)
  simp only [m291_eachindex,hm,cart_mapM_ok,bind,Except.bind]
  by_cases hs : ((rest.map f).all (· == f a)) = true
  · simp only [hs,↓reduceIte,pure,Except.pure]
    refine ⟨?_,?_⟩
    · constructor
      · rintro ⟨e,he⟩; contradiction
      · rintro ⟨b,hb,hne⟩
        exact False.elim (hne (hall.mp hs b hb))
    · intro iter hi
      cases hi
      refine ⟨rfl,?_⟩
      intro b hb
      exact (hall.mp hs b hb).symm
  · have hsf : ((rest.map f).all (· == f a)) = false := Bool.eq_false_iff.mpr hs
    simp only [hsf,Bool.false_eq_true,↓reduceIte]
    change ((∃ e, (Except.error .argument : RResult (SCartesianIndices2 k)) = .error e) ↔ _) ∧ _
    refine ⟨?_,?_⟩
    · constructor
      · intro _; exact hnot.mp hsf
      · intro _; exact ⟨_,rfl⟩
    · intro iter hi
      contradiction


theorem cart_iteration : property_reinterpretarray_cartesian_iteration :=
  ⟨cart_nextPrevious,cart_fullTransitions,cart_eachindex,cart_shared⟩

end JuliaLean.Statements.reinterpretarray.round7
end

namespace JuliaLean.Proofs.base.reinterpretarray
open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Registry

namespace Strict
local instance : DecidableEq ReinterpretError := inferInstance

abbrev reductionBoxGet :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.reductionBoxGet
abbrev FullReductionBounds :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.FullReductionBounds
abbrev reductionParentGet :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.reductionParentGet
abbrev reductionView :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.reductionView
abbrev PublicReductionSafety :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.PublicReductionSafety

private theorem min_to_max_range_head :
    ∃ rest, intRange (JInt.lit .i64 (IntTy.min .i64)) (JInt.lit .i64 (IntTy.max .i64)) =
      JInt.lit .i64 (IntTy.min .i64) :: rest := by
  unfold intRange
  change ∃ rest, (List.range (18446744073709551616)).map
    (fun k : Nat => JInt.lit .i64 (IntTy.min .i64) + JInt.lit .i64 k) =
      JInt.lit .i64 (IntTy.min .i64) :: rest
  rw [List.range_eq_range', List.range'_succ, List.map_cons]
  refine ⟨(List.range' 1 18446744073709551615).map
    (fun k : Nat => JInt.lit .i64 (IntTy.min .i64) + JInt.lit .i64 k), ?_⟩
  have hz : JInt.lit .i64 (IntTy.min .i64) + JInt.lit .i64 (0 : Nat) =
      JInt.lit .i64 (IntTy.min .i64) := by decide
  rw [hz]

theorem fullReductionBounds_refuted : ¬ FullReductionBounds := by
  intro h
  let last := JInt.lit .i64 (IntTy.max .i64)
  obtain ⟨value, hrun⟩ := h 2 last last one (by decide) (by decide) (by omega) (by decide)
  rw [m956_mapreduceImpl.eq_def] at hrun
  have hbranch : last - last < one := by decide
  have hfirst : reductionBoxGet last last 2 () ⟨one, last⟩ = .ok 1 := by rfl
  have hsecond : reductionBoxGet last last 2 () ⟨JInt.lit .i64 2, last⟩ = .ok 1 := by rfl
  have hrange : intRange (one + JInt.lit .i64 2) (JInt.lit .i64 (2 : Nat)) = [] := by decide
  have hwrap : last + one = JInt.lit .i64 (IntTy.min .i64) := by decide
  obtain ⟨rest, hrest⟩ := min_to_max_range_head
  have hrest' : intRange (JInt.lit .i64 (IntTy.min .i64)) last =
      JInt.lit .i64 (IntTy.min .i64) :: rest := by simpa [last] using hrest
  have houter : intRange (last + one) last = JInt.lit .i64 (IntTy.min .i64) :: rest := by
    rw [hwrap]
    exact hrest'
  have hbad : reductionBoxGet last last 2 () ⟨one, JInt.lit .i64 (IntTy.min .i64)⟩ =
      .error .bounds := by rfl
  have hinner : intRange one (JInt.lit .i64 (2 : Nat)) = [one, JInt.lit .i64 2] := by decide
  rw [houter, hinner, hrange] at hrun
  simp only [hbranch, ↓reduceIte, hfirst, hsecond, hbad, resultBindOk, forIn_nil,
    List.forIn_cons, resultBindError, resultPure, bind, Except.bind, pure, Except.pure,
    Option.pure_def, reduceCtorEq] at hrun
  cases hrun

private theorem publicReduction_at_max_fails :
    m946_mapreduce (K := 2)
      (fun _ a => m290_eachindexReshaped (K := 2) (fun _ ax => ax) a)
      (fun _ => ()) (fun (_ : Unit) (_ : Unit) _ _ => .ok 0)
      (fun (_ : Unit) (_ : Unit) => one) (m454_getindexCartesian (reductionParentGet [1,2]))
      (fun (_ : Unit) bytes => .ok bytes.length)
      (fun (_ : Unit) x y => .ok (x+y)) () () (.staticCartesian 2)
      (reductionView 2 ⟨JInt.lit .i64 (IntTy.max .i64), one⟩) = some (.error .bounds) := by
  let last := JInt.lit .i64 (IntTy.max .i64)
  let a := reductionView 2 ⟨last, one⟩
  change m956_mapreduceImpl (K := 2) (m454_getindexCartesian (reductionParentGet [1,2]))
    (fun (_ : Unit) bytes => .ok bytes.length) (fun (_ : Unit) x y => .ok (x+y)) a () ()
    ⟨one, last⟩ ⟨JInt.lit .i64 2, last + one - one⟩ one = _
  have hlast : last + one - one = last := by decide
  rw [hlast, m956_mapreduceImpl.eq_def]
  have hbranch : last - last < one := by decide
  have hfirst : m454_getindexCartesian (reductionParentGet [1,2]) a ⟨one, last⟩ =
      .ok [1] := by rfl
  have hsecond : m454_getindexCartesian (reductionParentGet [1,2]) a
      ⟨JInt.lit .i64 2, last⟩ = .ok [2] := by rfl
  have hrange : intRange (one + JInt.lit .i64 2) (JInt.lit .i64 (2 : Nat)) = [] := by decide
  have hwrap : last + one = JInt.lit .i64 (IntTy.min .i64) := by decide
  obtain ⟨rest, hrest⟩ := min_to_max_range_head
  have hrest' : intRange (JInt.lit .i64 (IntTy.min .i64)) last =
      JInt.lit .i64 (IntTy.min .i64) :: rest := by simpa [last] using hrest
  have houter : intRange (last + one) last = JInt.lit .i64 (IntTy.min .i64) :: rest := by
    rw [hwrap]
    exact hrest'
  have hbad : m454_getindexCartesian (reductionParentGet [1,2]) a
      ⟨one, JInt.lit .i64 (IntTy.min .i64)⟩ = .error .bounds := by rfl
  have hinner : intRange one (JInt.lit .i64 (2 : Nat)) = [one, JInt.lit .i64 2] := by decide
  rw [houter, hinner, hrange]
  simp only [hbranch, ↓reduceIte, hfirst, hsecond, resultBindOk, forIn_nil,
    List.forIn_cons, hbad, resultBindError, resultPure, bind, Except.bind, pure, Except.pure,
    Option.pure_def, reduceCtorEq]

theorem publicReductionSafety_refuted : ¬ PublicReductionSafety := by
  intro h
  obtain ⟨value, hrun⟩ := h 2 [1,2] ⟨JInt.lit .i64 (IntTy.max .i64), one⟩ one
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [publicReduction_at_max_fails] at hrun
  cases hrun
private theorem full_reduction_correctness_refuted :
    ¬ Statements.FullReductionCorrectness := by
  intro h
  let last := JInt.lit .i64 (IntTy.max .i64)
  let axis : Axis := ⟨last, one⟩
  have hmax : last.val = IntTy.max .i64 := by decide
  have hinterval (j : I64) :
      (last.val ≤ j.val ∧ j.val < last.val + one.val) ↔
      (last.val ≤ j.val ∧ j.val ≤ last.val) := by
    have hjmax : j.val ≤ IntTy.max .i64 := j.property.2
    constructor
    · intro h
      exact ⟨h.1, by rw [hmax]; exact hjmax⟩
    · intro h
      refine ⟨h.1, ?_⟩
      rw [hmax, one_val]
      omega
  have hget : ∀ i j, reductionBoxGet last last 2 () ⟨i,j⟩ =
      (if 1 ≤ i.val ∧ i.val ≤ 2 ∧ last.val ≤ j.val ∧ j.val < last.val + one.val
       then .ok 1 else .error .bounds) := by
    intro i j
    unfold reductionBoxGet Statements.reductionBoxGet
    simp [hinterval j]
  have hrun := h 2 axis one () (reductionBoxGet last last 2) (fun _ => 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) hget
  have hlast : last + one - one = last := by decide
  rw [hlast, m956_mapreduceImpl.eq_def] at hrun
  have hbranch : last - last < one := by decide
  have hfirst : reductionBoxGet last last 2 () ⟨one,last⟩ = .ok 1 := by rfl
  have hsecond : reductionBoxGet last last 2 () ⟨JInt.lit .i64 2,last⟩ = .ok 1 := by rfl
  have hrange : intRange (one + JInt.lit .i64 2) (JInt.lit .i64 (2 : Nat)) = [] := by decide
  have hwrap : last + one = JInt.lit .i64 (IntTy.min .i64) := by decide
  obtain ⟨rest, hrest⟩ := min_to_max_range_head
  have hrest' : intRange (JInt.lit .i64 (IntTy.min .i64)) last =
      JInt.lit .i64 (IntTy.min .i64) :: rest := by simpa [last] using hrest
  have hbad : reductionBoxGet last last 2 ()
      ⟨one,JInt.lit .i64 (IntTy.min .i64)⟩ = .error .bounds := by rfl
  have hinner : intRange one (JInt.lit .i64 (2 : Nat)) = [one,JInt.lit .i64 2] := by decide
  rw [hwrap, hrest', hinner, hrange] at hrun
  simp only [hbranch, ↓reduceIte, hfirst, hsecond, resultBindOk, forIn_nil,
    List.forIn_cons, hbad, bind, Except.bind, pure, Except.pure, Option.pure_def,
    reduceCtorEq] at hrun
  cases hrun

theorem approved_mapreduce_routing_refuted :
    ¬ Statements.property_reinterpretarray_mapreduce_routing := by
  intro h
  exact full_reduction_correctness_refuted h.1

abbrev NestedOutcome (T S P A : Type) :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.NestedOutcome T S P A
abbrev rootParent {T S P A : Type} (result : NestedOutcome T S P A) : ArrayInput A :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.rootParent result
abbrev nestedStorageLaw {T S P A : Type} (target : TypeLayout)
    (a : ReinterpretArray S P (ArrayInput A)) (result : NestedOutcome T S P A) : Prop :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.nestedStorageLaw target a result
abbrev FullNestedStorage :=
  JuliaLean.Proofs.base.reinterpretarray.Statements.FullNestedStorage

theorem fullNestedStorage : FullNestedStorage := by
  intro T S P A target size axes a
  cases hresult : m191_reinterpretReshapedParent (T := T) target size axes a with
  | error e => trivial
  | ok result =>
    change nestedStorageLaw target a result
    unfold m191_reinterpretReshapedParent at hresult
    by_cases hwidthVal :
        (target.alignedSize.val = a.target.alignedSize.val ∨
          target.alignedSize.val = a.source.alignedSize.val) ∨
          a.target.alignedSize.val = a.source.alignedSize.val
    · simp [hwidthVal] at hresult
      split at hresult
      · rename_i hid
        simp [m145_reinterpretReshapeIdentity] at hresult
        cases hresult
        simp [JuliaLean.Proofs.base.reinterpretarray.Statements.nestedStorageLaw,
          JuliaLean.Proofs.base.reinterpretarray.Statements.rootParent, hid]
      · cases hm : m188_reinterpretReshape (T := T) target a.source a.parent with
        | error e =>
          rw [hm] at hresult
          simp [bind, Except.bind, pure, Except.pure] at hresult
        | ok v =>
          rw [hm] at hresult
          simp [bind, Except.bind, pure, Except.pure] at hresult
          cases hresult
          obtain ⟨_, ht, hs, hp⟩ :=
            m107_congr_parent target a.source a.parent a.parent v rfl rfl hm
          exact ⟨hp, ⟨ht, hs⟩, by intro _ w; simp⟩
    · simp [hwidthVal] at hresult
      cases hd : m379_sizeReshaped size divInt a with
      | error e =>
        have hfalse : False := by
          simpa [hd, bind, Except.bind, pure, Except.pure] using hresult
        exact hfalse.elim
      | ok dims =>
        cases ha : m393_axesReshaped axes divInt a with
        | error e =>
          have hfalse : False := by
            simpa [hd, ha, bind, Except.bind, pure, Except.pure] using hresult
          exact hfalse.elim
        | ok axs =>
          let input : ArrayInput (ReinterpretArray S P (ArrayInput A)) :=
            ⟨a, a.rank, dims, axs⟩
          cases hc : m107_reinterpretReshape (T := T) target a.target
              { parent := a, rank := a.rank, size := dims, axes := axs } with
          | error e =>
            simp only [hd, ha, bind, Except.bind, pure, Except.pure] at hresult
            rw [hc] at hresult
            cases hresult
          | ok v =>
            simp only [hd, ha, bind, Except.bind, pure, Except.pure] at hresult
            rw [hc] at hresult
            simp only [bind, Except.bind, pure, Except.pure] at hresult
            cases hresult
            obtain ⟨_, ht, hs, hp⟩ :=
              m107_congr_parent target a.target input input v rfl rfl hc
            refine ⟨?_, ⟨ht, hs, ?_⟩, ?_⟩
            · simp [JuliaLean.Proofs.base.reinterpretarray.Statements.rootParent, hp, input]
            · simp [JuliaLean.Proofs.base.reinterpretarray.Statements.rootParent, hp, input]
            · intro heq
              rcases heq with heq | heq | heq
              all_goals simp [heq] at hwidthVal
theorem ordinaryConstructorValidation_refuted :
    ¬ JuliaLean.Statements.reinterpretarray.round7.OrdinaryConstructorValidation := by
  intro h
  have hmin : IntTy.min .i64 ≤ (2^61 : Int) := by
    have hnonneg : (0 : Int) ≤ 2^61 := Int.pow_nonneg (by decide)
    exact Int.le_trans i64_min_nonpos hnonneg
  have hmax : (2^61 : Int) ≤ IntTy.max .i64 := by
    simp only [IntTy.max, IntTy.signed, IntTy.bits]
    omega
  have hlenval : (JInt.lit .i64 (2^61 : Int)).val = (2^61 : Int) := by
    rw [val_lit]
    exact wrapInt_of_inRange .i64 _ ⟨hmin, hmax⟩
  have hdoc :
      JuliaLean.Statements.reinterpretarray.round7.DocumentedArrayInput overflowInput := by
    unfold JuliaLean.Statements.reinterpretarray.round7.DocumentedArrayInput
    refine ⟨?_, ?_⟩
    · unfold ShapeValid overflowInput
      refine ⟨rfl, rfl, ?_⟩
      intro ax hax
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl
      rw [hlenval]
      omega
    · unfold JuliaLean.Statements.reinterpretarray.round7.ConstructorArrayAxes overflowInput
      intro ax hax
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
      rcases hax with rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [one_val]
        have := i64_min_nonpos
        omega
      · rw [hlenval]
        omega
      · rw [one_val, hlenval]
        have := i64_min_nonpos
        omega
      · rw [one_val, hlenval]
        exact hmax
  have htval : tripleBytes.alignedSize.val = 3 := by
    change (JInt.lit .i64 (3 : Int)).val = 3
    exact lit_nat 3 (by omega)
  have hsval : (primitiveLayout 64 8).alignedSize.val = 8 := by
    change (JInt.lit .i64 (8 : Int)).val = 8
    exact lit_nat 8 (by omega)
  have hinputlen :
      (overflowInput.axes.headD ⟨one, zero⟩).length.val = (2^61 : Int) := by
    change (JInt.lit .i64 (2^61 : Int)).val = (2^61 : Int)
    exact hlenval
  have hnotdiv : ¬ (((2^61 : Int) * 8) % 3 = 0) := by omega
  have hn :
      ¬ JuliaLean.Statements.reinterpretarray.round7.PlainSourceAdmissible
        tripleBytes (primitiveLayout 64 8) overflowInput := by
    rintro ⟨_, _, _, _, _, hsize⟩
    have hbad := (hsize (by decide) (by decide)).2
    change (if false = true then _ else _) at hbad
    simp only [Bool.false_eq_true, ↓reduceIte] at hbad
    have hrem :
        ¬ ((overflowInput.axes.headD ⟨one, zero⟩).length.val *
          (primitiveLayout 64 8).alignedSize.val % tripleBytes.alignedSize.val = 0) := by
      rw [hinputlen, hsval, htval]
      exact hnotdiv
    exact hrem hbad.2
  have hresult := h (T := Unit) (S := Unit) (A := Unit)
    tripleBytes (primitiveLayout 64 8) overflowInput tripleBytes_valid
    (primitiveSmall_valid 64 8 (by decide) (by decide)) hdoc
  rcases hresult with ⟨hplain, _⟩
  rw [if_neg hn] at hplain
  rcases hplain with ⟨e, he⟩
  rw [tripleOverflow_constructed] at he
  cases he
end Strict
theorem approved_memsafety_mapreduce_refuted :
    ¬ Statements.property_memsafety_reinterpretarray_mapreduce := by
  intro h
  change Strict.FullReductionBounds at h
  exact Strict.fullReductionBounds_refuted h

theorem approved_mapreduce_offset_overflow_refuted :
    ¬ Statements.property_reinterpretarray_mapreduce_offset_overflow := by
  intro h
  change Strict.PublicReductionSafety at h
  exact Strict.publicReductionSafety_refuted h
theorem approved_nested_dispatch :
    Statements.property_reinterpretarray_nested_dispatch := by
  exact Strict.fullNestedStorage

theorem ordinarySmallHeadBound {t s : TypeLayout}
    {p : ArrayInput (List Bytes)} (hsmall : Statements.SmallDenseInput t s p)
    (hrank : p.rank ≠ 0)
    (htail : ((p.size.map (fun d => d.val.toNat)).drop 1).prod ≠ 0) :
    (p.size.headD zero).val.toNat ≤ 1024 := by
  rcases hsmall with ⟨_, _, hshape, _, _, hprod, _, _, _⟩
  have hlen : p.size.length = p.rank := by
    rw [hshape.2.1, List.length_map, hshape.1]
  cases hp : p.size with
  | nil => simp [hp] at hlen; omega
  | cons d ds =>
    have hmul : d.val.toNat * (ds.map (fun d => d.val.toNat)).prod ≤ 1024 := by
      simpa [hp, List.prod_cons] using hprod
    have htailPos : 0 < (ds.map (fun d => d.val.toNat)).prod := by
      have hne : (ds.map (fun d => d.val.toNat)).prod ≠ 0 := by
        simpa [hp] using htail
      exact Nat.pos_of_ne_zero hne
    have htailGe : 1 ≤ (ds.map (fun d => d.val.toNat)).prod := by omega
    have hmulLower : d.val.toNat ≤ d.val.toNat * (ds.map (fun d => d.val.toNat)).prod := by
      calc
        d.val.toNat = d.val.toNat * 1 := by simp
        _ ≤ d.val.toNat * (ds.map (fun d => d.val.toNat)).prod :=
          Nat.mul_le_mul_left _ htailGe
    have hbound : d.val.toNat ≤ 1024 := Nat.le_trans hmulLower hmul
    simpa [hp] using hbound
theorem reinterpretarray_m73_successShape {T S A : Type}
    (t s : TypeLayout) (p : ArrayInput A)
    (a : ReinterpretArray T S (ArrayInput A))
    (h : m73_reinterpret t s p = .ok a) :
    a.rank = p.rank ∧ a.target = t ∧ a.source = s ∧ a.parent = p ∧ a.reshaped = false := by
  unfold m73_reinterpret at h
  simp only [m14_throwbits, m27_throwbitpadding, m18_throwsize0, m23_throwsingleton,
    m74_thrownonint, m80_throwaxes1, bind, pure, Except.bind, Except.pure] at h
  repeat' split at h
  all_goals try contradiction
  all_goals (cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
theorem reinterpretarray_m73_zeroRank_requires_equal_widths {T S A : Type}
    (t s : TypeLayout) (p : ArrayInput A) (a : ReinterpretArray T S (ArrayInput A))
    (hrank : p.rank = 0) (h : m73_reinterpret t s p = .ok a) :
    t.alignedSize = s.alignedSize := by
  by_cases hEq : t.alignedSize = s.alignedSize
  · exact hEq
  · unfold m73_reinterpret at h
    simp only [m14_throwbits, m27_throwbitpadding, m18_throwsize0, m23_throwsingleton,
      m74_thrownonint, m80_throwaxes1, bind, pure, Except.bind, Except.pure] at h
    have hval : t.alignedSize.val ≠ s.alignedSize.val := by
      intro hv
      exact hEq (jint_eq_of_val hv)
    have hneq : (t.alignedSize != s.alignedSize) = true := by
      rw [bne_iff_val]
      simp [hval]
    rw [hrank, hneq] at h
    repeat' split at h
    all_goals try contradiction
theorem ordinarySize_zeroRank_case {T S : Type} (t s : TypeLayout)
    (p : ArrayInput (List Bytes)) (a : ReinterpretArray T S (ArrayInput (List Bytes)))
    (hsmall : Statements.SmallDenseInput t s p) (hrank : p.rank = 0)
    (hview : m73_reinterpret t s p = .ok a) :
    ∃ dims, (if a.rank = 0 then .ok (m385_sizeZero a)
      else m374_sizeNonReshaped (fun p => p.size) divInt a) = .ok dims ∧
      ((dims.map Subtype.val).prod * t.alignedSize.val =
        (p.size.map Subtype.val).prod * s.alignedSize.val) := by
  have hfields := reinterpretarray_m73_successShape t s p a hview
  have ha0 : a.rank = 0 := hfields.1.trans hrank
  have hwidths := reinterpretarray_m73_zeroRank_requires_equal_widths t s p a hrank hview
  rcases hsmall with ⟨_, _, hshape, _, _, _, _, _, _⟩
  have hlen : p.size.length = p.rank := by
    rw [hshape.2.1, List.length_map, hshape.1]
  rw [hrank] at hlen
  have hsize0 : p.size = [] := by
    cases hp : p.size with
    | nil => rfl
    | cons d ds => simp [hp] at hlen
  refine ⟨[], ?_, ?_⟩
  · simp [ha0, m385_sizeZero]
  · simp [hsize0, hwidths]

theorem reinterpretarray_m73_nonSingleton_remainder {T S A : Type}
    (t s : TypeLayout) (p : ArrayInput A)
    (a : ReinterpretArray T S (ArrayInput A))
    (hrank : p.rank ≠ 0) (htarget : t.singleton = false)
    (hwidth : t.alignedSize ≠ s.alignedSize)
    (hview : m73_reinterpret t s p = .ok a) :
    remInt ((p.axes.headD ⟨one, zero⟩).length * s.alignedSize) t.alignedSize = .ok zero := by
  have hwidthVal : s.alignedSize.val ≠ t.alignedSize.val := by
    intro h
    exact hwidth (jint_eq_of_val h.symm)
  have hwidthNe : (s.alignedSize != t.alignedSize) = true := by
    rw [bne_iff_val]
    simp [hwidthVal]
  have hrankEq : (p.rank == 0) = false := by simp [hrank]
  have hrankNe : (p.rank != 0) = true := by simp [hrank]
  unfold m73_reinterpret at hview
  simp only [m14_throwbits, m27_throwbitpadding, m18_throwsize0, m23_throwsingleton,
    m74_thrownonint, m80_throwaxes1, bind, pure, Except.bind, Except.pure] at hview
  rw [hrankEq, hrankNe, htarget, hwidthNe] at hview
  have hhead : (p.axes.headD ⟨one, zero⟩).length =
      (p.axes.head?.getD ⟨one, zero⟩).length := by
    cases p.axes <;> rfl
  cases hrem : remInt ((p.axes.headD ⟨one, zero⟩).length * s.alignedSize) t.alignedSize with
  | error e =>
    have hrem' : remInt ((p.axes.head?.getD ⟨one, zero⟩).length * s.alignedSize)
        t.alignedSize = .error e := by
      rw [← hhead]
      exact hrem
    have hfalse : False := by
      simp [hrem'] at hview
      repeat' split at hview
      all_goals try contradiction
      all_goals simp_all
    exact hfalse.elim
  | ok r =>
    have hrem' : remInt ((p.axes.head?.getD ⟨one, zero⟩).length * s.alignedSize)
        t.alignedSize = .ok r := by
      rw [← hhead]
      exact hrem
    by_cases hr : r = zero
    · subst r
      rfl
    · have hval : r.val ≠ zero.val := by
        intro hv
        exact hr (jint_eq_of_val hv)
      have hne : (r != zero) = true := by
        rw [bne_iff_val]
        simp [hval]
      have hfalse : False := by
        simp [hrem', hne] at hview
        repeat' split at hview
        all_goals try contradiction
        all_goals simp_all
      exact hfalse.elim
theorem m374_nonSingleton_resultShape {T S : Type} (t s : TypeLayout)
    (p : ArrayInput (List Bytes))
    (a : ReinterpretArray T S (ArrayInput (List Bytes))) (dims : List I64)
    (htarget : a.target = t) (hsource : a.source = s) (hparent : a.parent = p)
    (htargetSingleton : t.singleton = false)
    (hsize : m374_sizeNonReshaped (fun p => p.size) divInt a = .ok dims) :
    ∃ first, divInt (p.size.headD zero * s.alignedSize) t.alignedSize = .ok first ∧
      dims = first :: p.size.drop 1 := by
  unfold m374_sizeNonReshaped at hsize
  simp only [htarget, hsource, hparent, htargetSingleton, ↓reduceIte,
    bind, Except.bind, pure, Except.pure] at hsize
  have hhead : p.size.headD zero = p.size.head?.getD zero := by
    cases p.size <;> rfl
  cases hdiv : divInt (p.size.head?.getD zero * s.alignedSize) t.alignedSize with
  | error e => simp [hdiv] at hsize
  | ok first =>
    have hdivD : divInt (p.size.headD zero * s.alignedSize) t.alignedSize = .ok first := by
      rw [hhead]
      exact hdiv
    refine ⟨first, hdivD, ?_⟩
    have hsize' : (Except.ok (first :: p.size.tail) : RResult (List I64)) = .ok dims := by
      simpa [hdiv] using hsize
    have heq : first :: p.size.tail = dims :=
      Except.ok.inj (ε := ReinterpretError) hsize'
    simpa using heq.symm
theorem ordinarySize_product_cons (a b : I64) (tail : List I64) (u v : Int)
    (hfactor : a.val * u = b.val * v) :
    ((a :: tail).map Subtype.val).prod * u =
      ((b :: tail).map Subtype.val).prod * v := by
  simp only [List.map_cons, List.prod_cons]
  let tailProduct := (tail.map Subtype.val).prod
  calc
    (a.val * tailProduct) * u = (a.val * u) * tailProduct := by
      rw [Int.mul_assoc, Int.mul_comm tailProduct u, ← Int.mul_assoc]
    _ = (b.val * v) * tailProduct := congrArg (fun x => x * tailProduct) hfactor
    _ = (b.val * tailProduct) * v := by
      rw [Int.mul_assoc, Int.mul_comm v tailProduct, ← Int.mul_assoc]
theorem ordinarySize_zeroNatTail {xs : List I64}
    (hnonneg : ∀ d ∈ xs, 0 ≤ d.val)
    (hzero : (xs.map (fun d => d.val.toNat)).prod = 0) :
    (xs.map Subtype.val).prod = 0 := by
  induction xs with
  | nil => simp at hzero
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons] at hzero ⊢
    rcases Nat.mul_eq_zero.mp hzero with hx | htail
    · have hnon : 0 ≤ x.val := hnonneg x (by simp)
      have hcast : (x.val.toNat : Int) = x.val := Int.toNat_of_nonneg hnon
      rw [hx] at hcast
      have hval : x.val = 0 := by omega
      simp [hval]
    · have htailI : (xs.map Subtype.val).prod = 0 := ih
        (by intro d hd; exact hnonneg d (by simp [hd])) htail
      rw [htailI]
      simp
theorem ordinarySize_nonSingleton_zeroTail {T S : Type}
    (t s : TypeLayout) (p : ArrayInput (List Bytes))
    (a : ReinterpretArray T S (ArrayInput (List Bytes))) (dims : List I64)
    (hsmall : Statements.SmallDenseInput t s p) (hrank : p.rank ≠ 0)
    (htarget : t.singleton = false)
    (hview : m73_reinterpret t s p = .ok a)
    (hsize : m374_sizeNonReshaped (fun p => p.size) divInt a = .ok dims)
    (htail : ((p.size.map (fun d => d.val.toNat)).drop 1).prod = 0) :
    (if a.rank = 0 then .ok (m385_sizeZero a)
      else m374_sizeNonReshaped (fun p => p.size) divInt a) = .ok dims ∧
    ((dims.map Subtype.val).prod * t.alignedSize.val =
      (p.size.map Subtype.val).prod * s.alignedSize.val) := by
  obtain ⟨hr, hT, hS, hP, _⟩ := reinterpretarray_m73_successShape t s p a hview
  have haRank : a.rank ≠ 0 := by simpa [hr] using hrank
  have hshape : Strict.ShapeValid p := hsmall.2.2.1
  have hnonnegTail : ∀ d ∈ p.size.drop 1, 0 ≤ d.val := by
    intro d hd
    have hmem : d ∈ p.size := List.mem_of_mem_drop hd
    rw [hshape.2.1] at hmem
    rcases List.mem_map.mp hmem with ⟨ax, hax, haxEq⟩
    rw [← haxEq]
    exact hshape.2.2 ax hax
  have htailInt : ((p.size.drop 1).map Subtype.val).prod = 0 := by
    apply ordinarySize_zeroNatTail hnonnegTail
    simpa [List.map_drop] using htail
  obtain ⟨first, _, hdims⟩ :=
    m374_nonSingleton_resultShape t s p a dims hT hS hP htarget hsize
  constructor
  · simpa [haRank] using hsize
  · rw [hdims]
    cases hp : p.size with
    | nil =>
      have hlen : p.size.length = p.rank := by
        rcases hsmall with ⟨_, _, hshape, _, _, _, _, _, _⟩
        rw [hshape.2.1, List.length_map, hshape.1]
      rw [hp] at hlen
      simp [hp] at hlen
      omega
    | cons d ds =>
      have hzeroTail : ds.unattach.prod = 0 := by
        simpa [hp] using htailInt
      simp [hp, hzeroTail]
theorem m73_success_targetSingleton_sourceZero {T S A : Type}
    (t s : TypeLayout) (p : ArrayInput A)
    (a : ReinterpretArray T S (ArrayInput A))
    (htvalid : Strict.ValidStorageLayout t) (hsvalid : Strict.ValidStorageLayout s)
    (hrank : p.rank ≠ 0) (htarget : t.singleton = true)
    (hview : m73_reinterpret t s p = .ok a) :
    s.alignedSize.val = 0 := by
  by_cases hwidth : t.alignedSize = s.alignedSize
  · have htzero := htvalid.singletonMetadata.mp htarget
    have heq := congrArg Subtype.val hwidth
    omega
  · by_cases hsource : s.singleton = true
    · exact hsvalid.singletonMetadata.mp hsource
    · have hsourceFalse : s.singleton = false := by
        cases hs : s.singleton with
        | false => rfl
        | true => exact False.elim (hsource hs)
      have hwidthVal : s.alignedSize.val ≠ t.alignedSize.val := by
        intro h
        exact hwidth (jint_eq_of_val h.symm)
      have hwidthNe : (s.alignedSize != t.alignedSize) = true := by
        rw [bne_iff_val]
        simp [hwidthVal]
      have hrankEq : (p.rank == 0) = false := by simp [hrank]
      have hrankNe : (p.rank != 0) = true := by simp [hrank]
      unfold m73_reinterpret at hview
      simp only [m14_throwbits, m27_throwbitpadding, m18_throwsize0, m23_throwsingleton,
        m74_thrownonint, m80_throwaxes1, bind, pure, Except.bind, Except.pure] at hview
      rw [hrankEq, hrankNe, htarget, hsourceFalse, hwidthNe] at hview
      repeat' split at hview
      all_goals try contradiction
theorem ordinarySize_singletonTarget_case {T S : Type}
    (t s : TypeLayout) (p : ArrayInput (List Bytes))
    (a : ReinterpretArray T S (ArrayInput (List Bytes)))
    (hsmall : Statements.SmallDenseInput t s p) (hrank : p.rank ≠ 0)
    (htarget : t.singleton = true)
    (hview : m73_reinterpret t s p = .ok a) :
    ∃ dims, (if a.rank = 0 then .ok (m385_sizeZero a)
      else m374_sizeNonReshaped (fun p => p.size) divInt a) = .ok dims ∧
      ((dims.map Subtype.val).prod * t.alignedSize.val =
        (p.size.map Subtype.val).prod * s.alignedSize.val) := by
  obtain ⟨hr, hT, hS, hP, _⟩ := reinterpretarray_m73_successShape t s p a hview
  have haRank : a.rank ≠ 0 := by simpa [hr] using hrank
  rcases hsmall with ⟨htValid, hsValid, _, _, _, _, _, _, _⟩
  have htzero := htValid.singletonMetadata.mp htarget
  have hszero := m73_success_targetSingleton_sourceZero t s p a htValid hsValid
    hrank htarget hview
  let dims := p.size.headD zero :: p.size.drop 1
  have hsize : m374_sizeNonReshaped (fun p => p.size) divInt a = .ok dims := by
    simp [m374_sizeNonReshaped, hP, hT, hS, htarget, dims]
  refine ⟨dims, ?_, ?_⟩
  · simp [haRank, hsize]
  · simp [dims, htzero, hszero]
theorem ordinarySize_nonSingleton_positiveTail {T S : Type}
    (t s : TypeLayout) (p : ArrayInput (List Bytes))
    (a : ReinterpretArray T S (ArrayInput (List Bytes)))
    (hsmall : Statements.SmallDenseInput t s p) (hrank : p.rank ≠ 0)
    (htarget : t.singleton = false)
    (hview : m73_reinterpret t s p = .ok a)
    (htail : ((p.size.map (fun d => d.val.toNat)).drop 1).prod ≠ 0) :
    ∃ dims, (if a.rank = 0 then .ok (m385_sizeZero a)
      else m374_sizeNonReshaped (fun p => p.size) divInt a) = .ok dims ∧
      ((dims.map Subtype.val).prod * t.alignedSize.val =
        (p.size.map Subtype.val).prod * s.alignedSize.val) := by
  obtain ⟨hr, hT, hS, hP, _⟩ := reinterpretarray_m73_successShape t s p a hview
  have haRank : a.rank ≠ 0 := by simpa [hr] using hrank
  have hfirstBound := ordinarySmallHeadBound hsmall hrank htail
  rcases hsmall with ⟨htValid, hsValid, hshape, hTbound, hSbound, _, _, _, _⟩
  have haxesPos : 0 < p.axes.length := by rw [hshape.1]; omega
  have hfirstNonneg : 0 ≤ (p.size.headD zero).val := by
    cases haxes : p.axes with
    | nil => simp [haxes] at haxesPos
    | cons ax axs =>
      have haxnonneg := hshape.2.2 ax (by simp [haxes])
      have hfirstEq : p.size.headD zero = ax.length := by
        rw [hshape.2.1, haxes]
        rfl
      rw [hfirstEq]
      exact haxnonneg
  let n := (p.size.headD zero).val.toNat
  let ss := s.alignedSize.val.toNat
  let st := t.alignedSize.val.toNat
  have hfirstCast : (n : Int) = (p.size.headD zero).val := by
    simpa [n] using Int.toNat_of_nonneg hfirstNonneg
  have hsCast : (ss : Int) = s.alignedSize.val := by
    simpa [ss] using Int.toNat_of_nonneg hsValid.nonnegative
  have htCast : (st : Int) = t.alignedSize.val := by
    simpa [st] using Int.toNat_of_nonneg htValid.nonnegative
  have hsBoundNat : ss ≤ 64 := by
    have := hsCast
    omega
  have htNonzero : t.alignedSize.val ≠ 0 := by
    intro hz
    have hsing := htValid.singletonMetadata.mpr hz
    simp [htarget] at hsing
  have htPos : 0 < st := by
    have := htCast
    omega
  have htMax : (st : Int) ≤ IntTy.max .i64 := by
    rw [htCast]
    exact t.alignedSize.property.2
  have hBNat : n * ss ≤ 65536 := by
    calc
      n * ss ≤ 1024 * 64 := Nat.mul_le_mul hfirstBound hsBoundNat
      _ = 65536 := by decide
  have hB : ((n * ss : Nat) : Int) ≤ IntTy.max .i64 :=
    Int.le_trans (Int.ofNat_le.mpr hBNat) (by decide)
  have hmulVal : (p.size.headD zero * s.alignedSize).val =
      ((n * ss : Nat) : Int) :=
    mul_nat hfirstCast.symm hsCast.symm hB
  have hlitMul : (JInt.lit .i64 (n : Int) * JInt.lit .i64 (ss : Int)).val =
      ((n * ss : Nat) : Int) := lit_mul_lit n ss hB
  have hprodEq : p.size.headD zero * s.alignedSize =
      JInt.lit .i64 (n : Int) * JInt.lit .i64 (ss : Int) := by
    apply jint_eq_of_val
    rw [hmulVal, hlitMul]
  have htLit : t.alignedSize = JInt.lit .i64 (st : Int) := by
    apply jint_eq_of_val
    rw [lit_nat st htMax]
    exact htCast.symm
  let firstOut : I64 := JInt.wrap .i64 ((n * ss / st : Nat) : Int)
  have hdivLit :
      divInt (JInt.lit .i64 (n : Int) * JInt.lit .i64 (ss : Int))
          (JInt.lit .i64 (st : Int)) = .ok firstOut := by
    simpa [firstOut] using
      (divInt_nat hlitMul (lit_nat st htMax) htPos)
  have hdivActual : divInt (p.size.headD zero * s.alignedSize) t.alignedSize =
      .ok firstOut := by
    rw [hprodEq, htLit]
    exact hdivLit
  have hfirstHead : p.size.headD zero = p.size.head?.getD zero := by
    cases p.size <;> rfl
  have hdivHead : divInt (p.size.head?.getD zero * s.alignedSize) t.alignedSize =
      .ok firstOut := by
    rw [← hfirstHead]
    exact hdivActual
  have hsize : m374_sizeNonReshaped (fun p => p.size) divInt a =
      .ok (firstOut :: p.size.drop 1) := by
    simp [m374_sizeNonReshaped, hP, hT, hS, htarget, hdivHead]
  have hremActual :
      remInt (p.size.headD zero * s.alignedSize) t.alignedSize = .ok zero := by
    by_cases hwidth : t.alignedSize = s.alignedSize
    · have hwidthNat : st = ss := by
        have hv := congrArg Subtype.val hwidth
        rw [← htCast, ← hsCast] at hv
        exact Int.ofNat.inj hv
      have hmod : n * ss % st = 0 := by
        rw [hwidthNat]
        simp [Nat.mul_mod_right]
      have hwrapZero : JInt.wrap .i64 (0 : Int) = zero := by decide
      rw [remInt_nat hmulVal htCast.symm htPos]
      simp [hmod, hwrapZero]
    · have haxesFirst : (p.axes.headD ⟨one, zero⟩).length = p.size.headD zero := by
        rw [hshape.2.1]
        cases p.axes <;> rfl
      have hrem :=
        reinterpretarray_m73_nonSingleton_remainder t s p a hrank htarget hwidth hview
      rw [haxesFirst] at hrem
      exact hrem
  have hremLit :
      remInt (JInt.lit .i64 (n : Int) * JInt.lit .i64 (ss : Int))
        (JInt.lit .i64 (st : Int)) = .ok zero := by
    rw [← hprodEq, ← htLit]
    exact hremActual
  let col : List Bytes := List.replicate n []
  have hBCol : ((col.length * ss : Nat) : Int) ≤ IntTy.max .i64 := by
    simpa [col] using hB
  have hremCol :
      remInt (JInt.lit .i64 (col.length : Int) * JInt.lit .i64 (ss : Int))
        (JInt.lit .i64 (st : Int)) = .ok zero := by
    simpa [col] using hremLit
  have hdivCol :
      divInt (JInt.lit .i64 (col.length : Int) * JInt.lit .i64 (ss : Int))
        (JInt.lit .i64 (st : Int)) = .ok firstOut := by
    simpa [col] using hdivLit
  obtain ⟨q, hq, hqmul⟩ :=
    size_facts (sT := st) (sS := ss) (col := col)
      htPos htMax hBCol hremCol hdivCol
  have hqmulNat : q * st = n * ss := by simpa [col] using hqmul
  have hqmulInt : (q : Int) * (st : Int) = (n : Int) * (ss : Int) := by
    have hc := congrArg (fun x : Nat => (x : Int)) hqmulNat
    simpa [Int.natCast_mul] using hc
  have hfactor : firstOut.val * t.alignedSize.val =
      (p.size.headD zero).val * s.alignedSize.val := by
    calc
      firstOut.val * t.alignedSize.val = (q : Int) * (st : Int) := by rw [hq, htCast]
      _ = (n : Int) * (ss : Int) := hqmulInt
      _ = (p.size.headD zero).val * s.alignedSize.val := by rw [← hfirstCast, ← hsCast]
  have hcons : p.size = p.size.headD zero :: p.size.drop 1 := by
    cases hp : p.size with
    | nil =>
      have hlen : p.size.length = p.rank := by
        rw [hshape.2.1, List.length_map, hshape.1]
      rw [hp] at hlen
      simp [hrank] at hlen
      omega
    | cons d ds => rfl
  have htotal := ordinarySize_product_cons firstOut (p.size.headD zero) (p.size.drop 1)
    t.alignedSize.val s.alignedSize.val hfactor
  rw [← hcons] at htotal
  refine ⟨firstOut :: p.size.drop 1, ?_, htotal⟩
  simp [haRank, hsize]
theorem divInt_ok_of_positive {x y : I64} (hy : 0 < y.val) :
    ∃ result, divInt x y = .ok result := by
  have hy0 : y.val ≠ 0 := by omega
  have hyne : y.val ≠ -1 := by omega
  refine ⟨JInt.wrap .i64 (x.val.tdiv y.val), ?_⟩
  simp [divInt, JInt.div, Except.mapError, hy0, hyne]

theorem m374_nonSingleton_succeeds {T S : Type}
    (t s : TypeLayout) (p : ArrayInput (List Bytes))
    (a : ReinterpretArray T S (ArrayInput (List Bytes)))
    (htarget : a.target = t) (hsource : a.source = s) (hparent : a.parent = p)
    (htValid : Strict.ValidStorageLayout t) (htargetSingleton : t.singleton = false) :
    ∃ dims, m374_sizeNonReshaped (fun p => p.size) divInt a = .ok dims := by
  have htNonzero : t.alignedSize.val ≠ 0 := by
    intro hz
    have hsing := htValid.singletonMetadata.mpr hz
    simp [htargetSingleton] at hsing
  have htpos : 0 < t.alignedSize.val := by
    have hnonneg := htValid.nonnegative
    omega
  obtain ⟨first, hdiv⟩ := divInt_ok_of_positive
    (x := p.size.headD zero * s.alignedSize) (y := t.alignedSize) htpos
  have hhead : p.size.headD zero = p.size.head?.getD zero := by
    cases p.size <;> rfl
  have hdivHead : divInt (p.size.head?.getD zero * s.alignedSize) t.alignedSize = .ok first := by
    rw [← hhead]
    exact hdiv
  refine ⟨first :: p.size.drop 1, ?_⟩
  simp [m374_sizeNonReshaped, htarget, hsource, hparent, htargetSingleton, hdivHead]

theorem approved_ordinary_size_conservation :
    Statements.OrdinarySizeConservation := by
  intro T S t s p a hsmall hview
  by_cases hrank : p.rank = 0
  · exact ordinarySize_zeroRank_case t s p a hsmall hrank hview
  · cases htarget : t.singleton with
    | true =>
      exact ordinarySize_singletonTarget_case t s p a hsmall hrank htarget hview
    | false =>
      have htargetFalse : t.singleton = false := htarget
      have htValid : Strict.ValidStorageLayout t := hsmall.1
      obtain ⟨_, hT, hS, hP, _⟩ := reinterpretarray_m73_successShape t s p a hview
      obtain ⟨dims, hsize⟩ :=
        m374_nonSingleton_succeeds t s p a hT hS hP htValid htargetFalse
      by_cases htail : ((p.size.map (fun d => d.val.toNat)).drop 1).prod = 0
      · have hzeroTail := ordinarySize_nonSingleton_zeroTail t s p a dims hsmall hrank
          htargetFalse hview hsize htail
        exact ⟨dims, hzeroTail.1, hzeroTail.2⟩
      · exact ordinarySize_nonSingleton_positiveTail t s p a hsmall hrank
          htargetFalse hview htail

end JuliaLean.Proofs.base.reinterpretarray

namespace JuliaLean.ChatGPT.Batch4.Group18
open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Proofs.base.reinterpretarray

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- reinterpretarrays-size-overflow: reinterpret(T, A) either throws or has size(R, 1) * sizeof(T) == size(A, 1) * sizeof(eltype(A)). -/
theorem ReinterpretarraysSizeOverflow_refuted : ¬ JuliaLean.Proofs.base.reinterpretarray.ReinterpretSizeOverflow := by
  intro claim
  have constructed : m73_reinterpret (primitiveLayout 32 4) (primitiveLayout 64 8)
      overflowInput = .ok overflowView := by
    unfold m73_reinterpret
    rw [hasBitPadding_primitiveLayout, hasBitPadding_primitiveLayout]
    rfl
  have measured : m374_sizeNonReshaped ArrayInput.size divInt overflowView =
      .ok [zero] := by rfl
  have impossible := claim (primitiveLayout 32 4) (primitiveLayout 64 8)
    overflowInput overflowView [zero] constructed measured
  have unequal : ¬ (zero.val * (primitiveLayout 32 4).alignedSize.val =
      (overflowInput.size.headD zero).val * (primitiveLayout 64 8).alignedSize.val) := by decide
  exact unequal impossible

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.Proofs.base.reinterpretarray

/-- Computing an axis length from its two wrapped endpoints cancels the offset. -/
theorem shapeEndpointLength (first size : I64) :
    (first + size - one - first + one) = size := by
  apply jint_eq_of_val
  simp only [val_add, val_sub, one_val, wrapInt_add_left, wrapInt_sub_left]
  rw [show first.val + size.val - 1 - first.val + 1 = size.val by omega]
  exact JuliaLean.Proofs.base.int.wrapInt_val size

theorem shapeStandardOftype (axis : Axis) (size : I64) :
    standardOftype axis axis.first (axis.first + size - one) =
      ⟨axis.first, size⟩ := by
  unfold standardOftype
  rw [shapeEndpointLength]

theorem shapeDivPositive (numerator denominator : I64)
    (hdenominator : 0 < denominator.val) :
    ∃ quotient, divInt numerator denominator = .ok quotient := by
  refine ⟨JInt.wrap .i64 (numerator.val.tdiv denominator.val), ?_⟩
  unfold divInt JInt.div
  rw [ite_eq_right (by omega)]
  rw [ite_eq_right (fun h => by have := h.2.2; omega)]
  rfl

theorem shapeNonReshaped {T S A : Type}
    (a : ReinterpretArray T S (ArrayInput A)) (dims : List I64) (axs : List Axis)
    (hsize : a.parent.size = a.parent.axes.map Axis.length)
    (hnonempty : 0 < a.parent.axes.length)
    (hdims : m374_sizeNonReshaped ArrayInput.size divInt a = .ok dims)
    (haxs : m387_axesNonReshaped ArrayInput.axes divInt standardOftype a = .ok axs) :
    axs.map Axis.length = dims ∧
    dims.length = a.parent.size.length ∧
    dims.drop 1 = a.parent.size.drop 1 ∧
    axs.drop 1 = a.parent.axes.drop 1 ∧
    (axs.headD ⟨one, zero⟩).first = (a.parent.axes.headD ⟨one, zero⟩).first := by
  cases he : a.parent.axes with
  | nil => simp only [he, List.length_nil] at hnonempty; omega
  | cons axis tail =>
    have hp : a.parent.size = axis.length :: tail.map Axis.length := by
      rw [hsize, he, List.map_cons]
    unfold m374_sizeNonReshaped at hdims
    unfold m387_axesNonReshaped at haxs
    simp only [hp, he, List.headD_cons, List.drop_succ_cons, List.drop_zero] at hdims haxs
    by_cases hsingleton : a.target.singleton = true
    · simp only [hsingleton, ↓reduceIte, resultPure, resultBindOk] at hdims haxs
      cases hdims
      cases haxs
      rw [shapeStandardOftype]
      simp only [hp, he, List.map_cons, List.length_cons, List.length_map,
        List.drop_succ_cons, List.drop_zero, List.headD_cons, and_self]
    · simp only [hsingleton, ↓reduceIte] at hdims haxs
      cases hd : divInt (axis.length * a.source.alignedSize) a.target.alignedSize with
      | error error =>
        simp only [hd, resultBindError] at hdims
        contradiction
      | ok quotient =>
        simp only [hd, resultBindOk, resultPure] at hdims haxs
        cases hdims
        cases haxs
        rw [shapeStandardOftype]
        simp only [hp, he, List.map_cons, List.length_cons, List.length_map,
          List.drop_succ_cons, List.drop_zero, List.headD_cons, and_self]

theorem shapeReshaped {T S A : Type} (target source : TypeLayout) (p : ArrayInput A)
    (r : ReinterpretArray T S (ArrayInput A))
    (hsize : p.size = p.axes.map Axis.length) (haxes : p.axes.length = p.rank)
    (htarget : 0 < target.alignedSize.val) (hsource : 0 < source.alignedSize.val)
    (hrun : m107_reinterpretReshape target source p = .ok r) :
    ∃ dims axs,
      m379_sizeReshaped ArrayInput.size divInt r = .ok dims ∧
      m393_axesReshaped ArrayInput.axes divInt r = .ok axs ∧
      axs.map Axis.length = dims ∧ dims.length = r.rank := by
  obtain ⟨_, hp, _, ht, hs, _, _, hequal, hsmaller, hlarger⟩ :=
    reinterpretConstructorValidation.2.2 target source p r hrun
  change r.parent = p at hp
  by_cases hlt : target.alignedSize < source.alignedSize
  · obtain ⟨quotient, hquotient⟩ := shapeDivPositive source.alignedSize target.alignedSize htarget
    have hrank := (hsmaller hlt).2.2
    refine ⟨quotient :: p.size, ⟨one, quotient⟩ :: p.axes, ?_, ?_, ?_, ?_⟩
    · simp only [m379_sizeReshaped, hp, ht, hs, hlt, ↓reduceIte,
        hquotient, resultBindOk, resultPure]
    · simp only [m393_axesReshaped, hp, ht, hs, hlt, ↓reduceIte,
        hquotient, resultBindOk, resultPure]
    · simp only [List.map_cons, hsize]
    · simp only [List.length_cons, hsize, List.length_map, haxes, hrank]
  · by_cases hgt : source.alignedSize < target.alignedSize
    · have hrank := (hlarger hgt).2.2.2
      refine ⟨p.size.drop 1, p.axes.drop 1, ?_, ?_, ?_, ?_⟩
      · simp only [m379_sizeReshaped, hp, ht, hs, hlt, hgt, ↓reduceIte, resultPure]
      · simp only [m393_axesReshaped, hp, ht, hs, hlt, hgt, ↓reduceIte, resultPure]
      · rw [List.map_drop, ← hsize]
      · rw [List.length_drop, hsize, List.length_map, haxes]
        omega
    · have heq : source.alignedSize = target.alignedSize := by
        apply jint_eq_of_val
        change ¬ target.alignedSize.val < source.alignedSize.val at hlt
        change ¬ source.alignedSize.val < target.alignedSize.val at hgt
        omega
      have hrank := hequal heq
      refine ⟨p.size, p.axes, ?_, ?_, hsize.symm, ?_⟩
      · simp only [m379_sizeReshaped, hp, ht, hs, hlt, hgt, ↓reduceIte, resultPure]
      · simp only [m393_axesReshaped, hp, ht, hs, hlt, hgt, ↓reduceIte, resultPure]
      · rw [hsize, List.length_map, haxes, hrank]

theorem ReinterpretarrayRankShape_proven :
    JuliaLean.Proofs.base.reinterpretarray.ReinterpretShapeDimensions := by
  refine ⟨shapeNonReshaped, ?_, shapeReshaped⟩
  intro T S A a
  exact ⟨rfl, rfl, rfl⟩

theorem ReinterpretarrayShapeDimensions_proven :
    JuliaLean.Proofs.base.reinterpretarray.ReinterpretShapeDimensions :=
  ReinterpretarrayRankShape_proven

theorem ReinterpretarrayParentDimensions_proven :
    JuliaLean.Proofs.base.reinterpretarray.ReinterpretShapeDimensions :=
  ReinterpretarrayRankShape_proven

theorem reinterpretConstructorRank_proven :
    JuliaLean.Proofs.base.reinterpretarray.ReinterpretConstructorRank := by
  constructor
  · intro T S A target source p r h
    exact (reinterpretConstructorValidation.2.1 target source p r h).2.1
  · intro T S A target source p r h
    obtain ⟨_, _, _, _, _, _, _, hequal, hsmaller, hlarger⟩ :=
      reinterpretConstructorValidation.2.2 target source p r h
    exact ⟨hequal, fun hlt => (hsmaller hlt).2.2, fun hlt => (hlarger hlt).2.2.2⟩



open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Proofs.base.reinterpretarray

/-- The string conversion contract follows the empty, padding, and copying branches. -/
theorem ReinterpretarrayEmptyString_proven :
    JuliaLean.Proofs.base.reinterpretarray.Strict.FullStringBytes := by
  intro T S A R length empty callString stringBytes a bytes ht hr hn hl he hcall
  by_cases hb : bytes = []
  · subst bytes
    have hv : (length a).val = 0 := by
      simp only [List.length_nil] at hl
      omega
    have hz : length a = zero := jint_eq_of_val (by rw [hv, zero_val])
    rw [ite_eq_left rfl]
    exact (reinterpretStringConversion length empty callString a).1 hz
  · rw [ite_eq_right hb]
    have hz : length a ≠ zero := by
      intro heq
      rw [heq, zero_val, Int.toNat_zero] at hl
      exact hb (List.eq_nil_of_length_eq_zero hl.symm)
    by_cases hp : a.source.datatypePadding = true
    · rw [ite_eq_left hp]
      apply (reinterpretStringConversion length empty callString a).2.1 hz
      · simp only [hr, hp, Bool.not_true]
      · apply (reinterpretPaddingChecks.1 a.target a.source).2
        · simp only [m824_ispacked, hp, Bool.not_true]
        · rw [ht]
          rfl
    · rw [ite_eq_right hp]
      have hpf : a.source.datatypePadding = false := Bool.eq_false_iff.mpr hp
      have hra : a.readable = true := by simp only [hr, hpf, Bool.not_false]
      obtain ⟨text, htext, hbytes⟩ := hcall (length a) hn (by omega)
      refine ⟨text, ?_, ?_⟩
      · rw [(reinterpretStringConversion length empty callString a).2.2 hz hra]
        exact htext
      · rw [hl, List.take_length] at hbytes
        exact hbytes

/-- Parent reconstruction preserves the supplied copy in every identity branch. -/
theorem ReinterpretarrayUnaliasCopy_proven :
    JuliaLean.Proofs.base.reinterpretarray.Strict.FullUnaliasCopy := by
  intro T S A target source p p' a copy get aliases hcopy hrank haxes hget halias
  constructor
  · intro h73
    obtain ⟨hrebuild, ht, hs, hp⟩ :=
      m73_congr_parent target source p p' a hrank haxes h73
    by_cases hid : target.id = source.id
    · refine ⟨.parent p', p', ?_, rfl, ?_, ?_⟩
      · simp only [m371_unaliascopy, hp, hcopy, resultBindOk, ht, hs, hid,
          beq_self_eq_true, ↓reduceIte, m104_reinterpretIdentity, resultPure]
      · simpa only [m369_parent, hp] using hget
      · simpa only [m370_dataids, hp] using halias
    · refine ⟨.view ⟨p', a.rank, a.target, a.source, a.readable, a.writable, false⟩,
        p', ?_, rfl, ?_, ?_⟩
      · simp only [m371_unaliascopy, hp, hcopy, resultBindOk, ht, hs,
          beq_eq_false_iff_ne.mpr hid, Bool.false_eq_true, ↓reduceIte, hrebuild, resultPure]
      · simpa only [m369_parent, hp] using hget
      · simpa only [m370_dataids, hp] using halias
  · intro h188
    obtain ⟨hrebuild, ht, hs, hp⟩ :=
      m107_congr_parent target source p p' a hrank haxes h188
    by_cases hid : target.id = source.id
    · refine ⟨.parent p', p', ?_, rfl, ?_, ?_⟩
      · simp only [m372_unaliascopyReshaped, hp, hcopy, resultBindOk, ht, hs, hid,
          beq_self_eq_true, ↓reduceIte, m145_reinterpretReshapeIdentity, resultPure]
      · simpa only [m369_parent, hp] using hget
      · simpa only [m370_dataids, hp] using halias
    · refine ⟨.view ⟨p', a.rank, a.target, a.source, a.readable, a.writable, true⟩,
        p', ?_, rfl, ?_, ?_⟩
      · simp only [m372_unaliascopyReshaped, hp, hcopy, resultBindOk, ht, hs,
          beq_eq_false_iff_ne.mpr hid, Bool.false_eq_true, ↓reduceIte,
          m188_reinterpretReshape, hrebuild, resultPure]
      · simpa only [m369_parent, hp] using hget
      · simpa only [m370_dataids, hp] using halias

/-- The combined metadata contract includes the complete copying result. -/
theorem ReinterpretarrayParentMetadata_proven :
    JuliaLean.Proofs.base.reinterpretarray.Strict.FullParentMetadata :=
  ⟨Strict.constructorParentPreservation, ReinterpretarrayUnaliasCopy_proven⟩

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.ChatGPT.Batch4.Group18
open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.Proofs.base.reinterpretarray

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- reinterpretarrays-ra-getindex-bytes: reinterpret(T, A)[i1, J...] returns the sizeof(T) parent bytes starting at byte (i1-1)*sizeof(T) of column J across scalar, multiple, sub-element and partial-copy branches, and throws BoundsError outside 1:size(R, 1). -/
theorem ReinterpretarraysRaGetindexBytes_proven : JuliaLean.Proofs.base.reinterpretarray.RaGetCorrect :=
  JuliaLean.Proofs.base.reinterpretarray.raGetCorrect

/-- reinterpretarrays-ra-setindex-bytes: reinterpret(T, A)[i1, J...] = v overwrites the sizeof(T) parent bytes starting at byte (i1-1)*sizeof(T) of column J with the bytes of v, preserves every other byte, and throws BoundsError outside 1:size(R, 1). -/
theorem ReinterpretarraysRaSetindexBytes_proven : JuliaLean.Proofs.base.reinterpretarray.RaSetCorrect :=
  JuliaLean.Proofs.base.reinterpretarray.raSetCorrect

/-- reinterpretarray-zero-set: Zero-dimensional setindex! reinterprets the converted value directly into a.parent[] when scalar reinterpret is applicable, and otherwise delegates to linear setindex! at firstindex(a). -/
theorem ReinterpretarrayZeroSet_proven : JuliaLean.Proofs.base.reinterpretarray.RaSetCorrect :=
  JuliaLean.Proofs.base.reinterpretarray.raSetCorrect

/-- memsafety-reinterpretarray-getindex: Checked ReinterpretArray reads require readable storage, restrict pointer reads to distinct element sizes on pointer-indexable parents, propagate bounds errors, and read only the addressed parent elements. -/
theorem MemsafetyReinterpretarrayGetindex_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretGetMemorySafe :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretGetMemorySafe

/-- reinterpretarray-pointer-metadata: Pointer conversion and element-size metadata follow the parent conversion and specialized parent-indexability rules. -/
theorem ReinterpretarrayPointerMetadata_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretGetMemorySafe :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretGetMemorySafe

/-- memsafety-reinterpretarray-setindex: Checked ReinterpretArray writes require writable storage, convert values before bounds or parent mutation, and preserve the parent byte-image length and outside bytes. -/
theorem MemsafetyReinterpretarraySetindex_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretSetMemorySafe :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretSetMemorySafe

/-- reinterpretarray-reshaped-get: Successful reshaped element reads return the exact target-sized byte window across singleton, equal-size, multi-parent, and sub-element branches. -/
theorem ReinterpretarrayReshapedGet_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretReshapedGetSet :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretReshapedGetSet

/-- reinterpretarray-reshaped-set: Successful reshaped assignment writes the exact target bytes into the parent storage across singleton, equal-size, multi-parent, and sub-element branches. -/
theorem ReinterpretarrayReshapedSet_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretReshapedGetSet :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretReshapedGetSet

/-- reinterpretarray-reshaped-get-set: Reshaped _getindex_ra and _setindex_ra! read and write the exact target bytes across singleton, equal-size, multi-parent (sizeof(T) > sizeof(S), both linear-offset and Cartesian), and sub-element (sizeof(T) < sizeof(S)) branches. -/
theorem ReinterpretarrayReshapedGetSet_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretReshapedGetSet :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretReshapedGetSet

/-- reinterpretarray-cartesian-routing: SCartesianIndex2 routing maps (i, j) to (first(axes(A,1))+i-1, trailing...), and SCartesianIndex2 getindex and setindex! on a ReshapedReinterpretArray read and write the exact i-th target slice of parent element j without altering other slices. -/
theorem ReinterpretarrayCartesianRouting_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretCartesianGetSet :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretCartesianGetSet

/-- reinterpretarray-isassigned-bounds: Ordinary isassigned returns false out of bounds and delegates to _isassigned_ra in bounds, while SCartesianIndex2 isassigned checks the parent at ind.j. -/
theorem ReinterpretarrayIsassignedBounds_proven : JuliaLean.Proofs.base.reinterpretarray.ReinterpretIsAssignedBounds :=
  JuliaLean.Proofs.base.reinterpretarray.reinterpretIsAssignedBounds

end JuliaLean.ChatGPT.Batch4.Group18

namespace JuliaLean.Proofs.base.reinterpretarray

open JuliaLean.Registry
def entries : List JuliaLean.Registry.Entry := [
  { id := "reinterpretarrays-ra-getindex-bytes", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["getindex(::ReinterpretArray, i1, tailinds...)", "_getindex_ra(::NonReshapedReinterpretArray)", "getindex(::NonReshapedReinterpretArray{T,0,S})", "getindex(::ReshapedReinterpretArray{T,0})", "getindex(::ReinterpretArray, i::Int)"],
    statement := "Every integer-coordinate, linear and zero-dimensional read returns the parent value bytes in its target-sized window across scalar, multi-parent, sub-element and partial-copy branches, including pointer dispatch; incompatible padding and out-of-bounds accesses raise their respective errors.",
    source := "base/reinterpretarray.jl:35-72, 413-570", status := .todo,
    prop := ``Statements.AllReads, thm := none },
  { id := "reinterpretarrays-ra-setindex-bytes", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["setindex!(::ReinterpretArray, v, i1, tailinds...)", "_setindex_ra!(::NonReshapedReinterpretArray)", "setindex!(::NonReshapedReinterpretArray{T,0,S}, v)", "setindex!(::ReshapedReinterpretArray{T,0}, v)", "setindex!(::ReinterpretArray, v, i::Int)"],
    statement := "Every integer-coordinate, linear and zero-dimensional assignment updates the selected parent value bytes and preserves all other value bytes across scalar, multi-parent, sub-element and partial-copy branches, including pointer dispatch; conversion, padding and bounds failures propagate.",
    source := "base/reinterpretarray.jl:35-72, 572-734", status := .todo,
    prop := ``Statements.AllWrites, thm := none },
  { id := "reinterpretarrays-size-overflow", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(T, ::AbstractArray)", "size(::NonReshapedReinterpretArray)", "axes(::NonReshapedReinterpretArray)"],
    statement := "reinterpret(T, A) either throws or has size(R, 1) * sizeof(T) == size(A, 1) * sizeof(eltype(A)).",
    source := "base/reinterpretarray.jl:3-7, 76-78, 374-392", status := .refuted,
    refutationEvidence := .runtime,
    prop := ``ReinterpretSizeOverflow, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarraysSizeOverflow_refuted,
    issue := "bugs/reinterpretarrays-size-overflow.yaml",
    notes := "psize[1] * aligned_sizeof(S) wraps in Int before div: reinterpret(NTuple{3,UInt8}, 1:2^61) has size (0,) and reinterpret(Int32, 1:2^62) has negative size." },
  { id := "memsafety-reinterpretarray-getindex", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["getindex(::ReinterpretArray)", "_getindex_ptr", "_getindex_ra", "check_readable", "check_ptr_indexable", "elsize", "cconvert"],
    statement := "Checked ReinterpretArray reads require readable storage, restrict pointer reads to distinct element sizes on pointer-indexable parents, propagate bounds errors, and read only the addressed parent elements.",
    source := "base/reinterpretarray.jl:237-242, 403-570", status := .todo,
    prop := ``ReinterpretGetMemorySafe, thm := none,
    notes := "Prop proves nonpointer byte bounds only for a one-dimensional column and gives a callback pointer route; prose promises addressed-parent-element safety for all checked reads." },
  { id := "memsafety-reinterpretarray-setindex", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["setindex!(::ReinterpretArray)", "_setindex_ptr!", "_setindex_ra!", "check_writable", "check_ptr_indexable", "setindex!(::ReshapedReinterpretArray,::SCartesianIndex2)"],
    statement := "Every checked integer-coordinate, linear, zero-dimensional and valid static Cartesian write enforces padding compatibility, preserves the parent byte-image length and all value bytes outside the target window, and propagates conversion and bounds failures in the selected dispatch order.",
    source := "base/reinterpretarray.jl:244-254, 572-734", status := .todo,
    prop := ``Statements.AllWrites, thm := none },
  { id := "memsafety-reinterpretarray-mapreduce", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_mapreduce", "mapreduce_impl(::SCartesianIndex2)"],
    statement := "Every valid static Cartesian box is reduced without out-of-box reads, including native-integer endpoint axes and every positive block size.",
    source := "base/reinterpretarray.jl:946-985", status := .refuted,
    prop := ``Statements.property_memsafety_reinterpretarray_mapreduce,
      thm := some ``approved_memsafety_mapreduce_refuted,
    issue := "related #38627 (closed; similar offset-axis reduce/mapreduce overflow), fixed by merged PR #38643. Searches: JuliaLang/julia issues `reinterpretarray mapreduce` found #38627; PRs `38627 mapreduce` found #38643; exact issue query `reinterpret mapreduce BoundsError offset` found none; exact PR query found 2 unrelated results (#43334, #27386). The current one-element ReinterpretArray endpoint repro remains." },
  { id := "reinterpretarray-rank-shape", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type,::AbstractArray)", "reinterpret(reshape,::Type,::AbstractArray)", "ReinterpretArray{T}(::typeof(reshape),::AbstractArray)"],
    statement := "Successful constructors keep the non-reshape rank and adjust reshape rank only by the element-size ratio.",
    source := "base/reinterpretarray.jl:73-144; constructor invariant", status := .proven,
    prop := ``ReinterpretConstructorRank, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.reinterpretConstructorRank_proven },
  { id := "reinterpretarray-constructor-validation", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type,::AbstractArray)", "ReinterpretArray{T}(::typeof(reshape),::AbstractArray)", "reinterpret(::typeof(reshape),::Type,::AbstractArray)", "throwbits", "throwsize0", "throwsingleton", "throwbitpadding", "thrownonint", "throwaxes1", "throwintmult", "throwsize1", "throwfromsingleton"],
    statement := "Both constructors accept exactly the documented isbits, bit-padding, singleton, size-divisibility and axis conditions; successful views preserve the parent and have the documented rank and byte-padding access permissions.",
    source := "base/reinterpretarray.jl:14-31, 73-144, 188", status := .refuted,
    issue := "none found (queries: reinterpret size overflow; ReinterpretArray overflow; reinterpret negative size; reinterpret large range)",
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.FullConstructorValidation, thm := some ``Strict.fullConstructorValidation_refuted},
  { id := "reinterpretarray-padding-flags", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["array_subpadding", "check_readable", "check_writable", "reinterpret(::Type,::AbstractArray)", "ReinterpretArray{T}(::typeof(reshape),::AbstractArray)"],
    statement := "Successful plain and reshaped reinterpret constructors on recursive isbits layouts without unions cache read and write flags exactly when periodic value-byte inclusion holds, for aligned sizes within Julia's UInt32 datatype-size limit.",
    source := "base/reinterpretarray.jl:73-144, 237-254, 775-813", status := .proven,
    prop := ``Statements.Round10.property_reinterpretarray_padding_flags, thm := some ``Statements.r10_constructorPaddingFlags_proven },
  { id := "reinterpretarray-stride-behavior", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["strides(::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray})", "stride", "strides(::ReinterpretArray)", "_checked_strides", "_checkcontiguous"],
    statement := "Contiguous parents use size_to_strides(1, size(a)...), equal-size elements keep parent strides, noncontiguous first dimensions throw ArgumentError, exact byte strides divide by sizeof(T), and stride(A, k) returns strides(A)[k] or length(A).",
    source := "base/reinterpretarray.jl:207-232", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.FullStrideContract, thm := some ``Strict.fullStrideContract},
  { id := "reinterpretarray-index-style", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}})", "IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}})", "IndexStyle(::IndexSCartesian2{K},::IndexSCartesian2{K})"],
    statement := "All parent indexing styles are handled; a static channel count conserves exactly one source element byte width, and non-linear parent styles become ordinary Cartesian indexing.",
    source := "base/reinterpretarray.jl:263-273, 333-344", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.FullIndexStyles, thm := some ``Strict.fullIndexStyles},
  { id := "reinterpretarray-cartesian-iteration", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SCartesianIndices2{K}", "eachindex(::IndexSCartesian2{K},::ReshapedReinterpretArray)", "eachindex(::IndexSCartesian2{K},::AbstractArray,::AbstractArray...)", "size(::SCartesianIndices2{K})", "first(::SCartesianIndices2{K})", "last(::SCartesianIndices2{K})", "iterate(::SCartesianIndices2{K})", "nextind(::AbstractArray,::SCartesianIndex2{K})", "prevind(::AbstractArray,::SCartesianIndex2{K})"],
    statement := "Cartesian iteration advances and reverses indices across the full representable outer axis, including nonempty axes beginning at typemin(Int); multi-array eachindex requires matching outer axes.",
    source := "base/reinterpretarray.jl:280-325; base/abstractarray.jl:396-404", status := .proven,
    prop := ``JuliaLean.Statements.reinterpretarray.round7.property_reinterpretarray_cartesian_iteration,
    thm := some ``JuliaLean.Statements.reinterpretarray.round7.cart_iteration,
    notes := "The axis domain allows first == typemin(Int) and requires representable endpoints. The eachindex range is supplied by the parent's linear-index model." },
  { id := "reinterpretarray-nested-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T},::AbstractArray{T})", "reinterpret(::typeof(reshape),::Type{T},::AbstractArray{T})", "reinterpret(::Type{T},::NonReshapedReinterpretArray)", "reinterpret(::typeof(reshape),::Type{T},::ReshapedReinterpretArray)", "parent(::ReinterpretArray)", "dataids(::ReinterpretArray)", "unaliascopy(::NonReshapedReinterpretArray)", "unaliascopy(::ReshapedReinterpretArray)", "has_offset_axes(::ReinterpretArray)"],
    statement := "Every successful nested reshaped reinterpretation preserves the root parent, target element metadata and unnecessary-layer elimination.",
    source := "base/reinterpretarray.jl:104, 145, 190-194, 369-372, 401", status := .proven,
    prop := ``Statements.property_reinterpretarray_nested_dispatch,
      thm := some ``approved_nested_dispatch },
  { id := "reinterpretarray-shape-dimensions", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["size(::NonReshapedReinterpretArray)", "size(::ReshapedReinterpretArray)", "size(::NonReshapedReinterpretArray{T,0})", "axes(::NonReshapedReinterpretArray)", "axes(::ReshapedReinterpretArray)", "axes(::NonReshapedReinterpretArray{T,0})"],
    statement := "Non-reshaped size and axes scale only the first dimension while preserving trailing dimensions and first-axis offset; reshaped size and axes prepend S÷T, drop the first dimension, or preserve dimensions; 0D size and axes are empty.",
    source := "base/reinterpretarray.jl:374-399", status := .proven,
    prop := ``ReinterpretShapeDimensions, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayShapeDimensions_proven },
  { id := "reinterpretarray-parent-metadata", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["parent", "dataids", "has_offset_axes", "unaliascopy"],
    statement := "Parent identity, alias metadata, offset-axis queries, and unaliascopy come from the underlying parent array.",
    source := "base/reinterpretarray.jl:73-144, 369-372, 401", status := .proven,
    prop := ``Strict.FullParentMetadata, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayParentMetadata_proven },
  { id := "reinterpretarray-pointer-metadata", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["cconvert", "elsize", "check_ptr_indexable"],
    statement := "Pointer conversion and element-size metadata follow the parent conversion and specialized parent-indexability rules.",
    source := "base/reinterpretarray.jl:403-428", status := .proven,
    prop := ``ReinterpretGetMemorySafe, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayPointerMetadata_proven },
  { id := "reinterpretarray-cartesian-routing", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_getindex(::IndexSCartesian2,::AbstractArray,::SCartesianIndex2)", "_setindex!(::IndexSCartesian2,::AbstractArray,v,::SCartesianIndex2)", "_scartesian2_trailing", "getindex(::ReshapedReinterpretArray,::SCartesianIndex2)", "setindex!(::ReshapedReinterpretArray,v,::SCartesianIndex2)"],
    statement := "SCartesianIndex2 routing maps (i, j) to (first(axes(A,1))+i-1, trailing...), and SCartesianIndex2 getindex and setindex! on a ReshapedReinterpretArray read and write the exact i-th target slice of parent element j without altering other slices.",
    source := "base/reinterpretarray.jl:347-363, 454-459, 598-608", status := .todo,
    prop := ``Statements.FullCartesianRouting, thm := none },
  { id := "reinterpretarray-isassigned-bounds", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["isassigned(::ReinterpretArray,::Integer...)", "isassigned(::ReinterpretArray,::SCartesianIndex2)", "_isassigned_ra"],
    statement := "Ordinary isassigned returns false out of bounds and delegates to _isassigned_ra in bounds, while SCartesianIndex2 isassigned checks the parent at ind.j.",
    source := "base/reinterpretarray.jl:432-434", status := .proven,
    prop := ``ReinterpretIsAssignedBounds, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayIsassignedBounds_proven },
  { id := "reinterpretarray-empty-string", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["String(::ReinterpretArray{UInt8,1})"],
    statement := "String(v) preserves every byte of nonempty readable views, including invalid UTF-8 bytes, rejects incompatible padding, and returns the empty string on empty views without reading storage.",
    source := "base/reinterpretarray.jl:937-942", status := .proven,
    prop := ``Strict.FullStringBytes, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayEmptyString_proven },
  { id := "reinterpretarray-stride-components", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["strides", "stride", "_checked_strides", "_checkcontiguous"],
    statement := "Stride construction follows parent size-to-strides, retains contiguous parent strides, and rejects remainders in byte-to-element stride conversion.",
    source := "base/reinterpretarray.jl:207-232", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.FullStrideContract, thm := some ``Strict.fullStrideContract},
  { id := "reinterpretarray-padding-checks", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["check_readable", "check_writable", "showerror(::PaddingError)"],
    statement := "For accepted recursive isbits layouts without unions whose aligned sizes fit Julia's UInt32 datatype-size limit, read and write checks accept exactly the periodic value-byte compatibility relation and throw an error on incompatible layouts.",
    source := "base/reinterpretarray.jl:73-144,237-254,750-813; src/datatype.c:191,718-729,850-851,872,1048; src/builtins.c:2593-2594; src/julia.h:723,1686; base/runtime_internals.jl:668-688", status := .proven,
    prop := ``Statements.property_reinterpretarray_padding_checks, thm := some ``Statements.r9_paddingChecks_proven },
  { id := "reinterpretarray-index-combination", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}})", "IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}})", "IndexStyle(::IndexSCartesian2{K},::IndexSCartesian2{K})"],
    statement := "Static Cartesian style combination retains the channel count, whose product with target byte width equals source byte width; linear and non-linear parents are both included.",
    source := "base/reinterpretarray.jl:263-273", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.FullIndexStyles, thm := some ``Strict.fullIndexStyles},
  { id := "reinterpretarray-cartesian-operations", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SCartesianIndices2{K}", "size(::SCartesianIndices2{K})", "axes(::SCartesianIndices2{K})", "first(::SCartesianIndices2{K})", "last(::SCartesianIndices2{K})", "getindex(::SCartesianIndices2{K},::Int,::Int)"],
    statement := "Cartesian index size, axes and endpoints match the channel and outer range. Direct getindex uses UnitRange positional indexing, while IdentityUnitRange returns its label; OneTo starts at 1, so both forms agree there.",
    source := "base/reinterpretarray.jl:298-307; base/range.jl:959-964; base/indices.jl:369-378", status := .proven,
    prop := ``JuliaLean.Statements.reinterpretarray.round7.property_reinterpretarray_cartesian_operations,
    thm := some ``JuliaLean.Statements.reinterpretarray.round7.cart_operations,
    notes := "The statement instantiates m304_indicesGet with the installed UnitRange and IdentityUnitRange access models. IdentityUnitRange checks the label with the installed checkindexReal model before returning it; Axis stores only first and length." },
  { id := "reinterpretarray-unalias-copy", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["unaliascopy(::NonReshapedReinterpretArray)", "unaliascopy(::ReshapedReinterpretArray)"],
    statement := "Unaliasing a valid view preserves all parent values and separates alias identities, for matching and differing element types and both reshape variants.",
    source := "base/reinterpretarray.jl:371-372", status := .proven,
    prop := ``Strict.FullUnaliasCopy, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayUnaliasCopy_proven },
  { id := "reinterpretarray-parent-dimensions", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["size", "axes"],
    statement := "Non-reshape size and axes keep parent trailing dimensions, while reshape axes consume or add the channel dimension.",
    source := "base/reinterpretarray.jl:374-399", status := .proven,
    prop := ``ReinterpretShapeDimensions, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayParentDimensions_proven },
  { id := "reinterpretarray-elsize", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["elsize"],
    statement := "For every index, pointer addressing uses the parent's physical element spacing for equal-sized types and the target storage width otherwise, with native address wrapping.",
    source := "base/reinterpretarray.jl:403-409", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.PhysicalElementSpacing, thm := some ``Strict.physicalElementSpacing},
  { id := "reinterpretarray-reshaped-get", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_getindex_ra(::ReshapedReinterpretArray)", "getindex(::ReinterpretArray)"],
    statement := "Reshaped reads return the target-sized parent value-byte window for arbitrary ranks, layouts and indices across singleton, scalar, equal-size, both multi-parent routes and sub-element branches; public reads enforce padding and bounds checks.",
    source := "base/reinterpretarray.jl:35-72, 413-570", status := .todo,
    prop := ``Statements.ReshapedReads, thm := none },
  { id := "reinterpretarray-cartesian-set", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["setindex!(::ReshapedReinterpretArray,::SCartesianIndex2)", "getindex(::ReshapedReinterpretArray,::SCartesianIndex2)"],
    statement := "For every parent array satisfying its read/write interface laws, Cartesian assignment reads back the written target bytes and preserves every disjoint byte in the source value and all other parent elements.",
    source := "base/reinterpretarray.jl:454-459, 598-608", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.CartesianParentLens, thm := some ``Strict.cartesianParentLens},
  { id := "reinterpretarray-reshaped-set", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_setindex_ra!(::ReshapedReinterpretArray)", "setindex!(::ReinterpretArray)"],
    statement := "Reshaped assignment updates the exact selected parent value bytes and preserves all other value bytes and the parent shape across singleton, scalar, equal-size, both multi-parent routes and sub-element branches; conversion, padding and bounds failures propagate.",
    source := "base/reinterpretarray.jl:35-72, 572-734", status := .todo,
    prop := ``Statements.ReshapedWrites, thm := none },
  { id := "reinterpretarray-mapreduce-routing", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_mapreduce", "mapreduce_impl"],
    statement := "Static Cartesian mapreduce terminates and computes the complete element sum for every channel count, column count, valid offset axis and positive pairwise block size.",
    source := "base/reinterpretarray.jl:946-985", status := .refuted,
    prop := ``Statements.property_reinterpretarray_mapreduce_routing,
      thm := some ``Strict.approved_mapreduce_routing_refuted,
    issue := "none found (queries: reinterpret mapreduce typemax; reinterpret mapreduce overflow)" },
  { id := "reinterpretarray-zero-set", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["setindex!(::NonReshapedReinterpretArray{T,0,S}, v)", "setindex!(::ReshapedReinterpretArray{T,0}, v)"],
    statement := "Zero-dimensional setindex! reinterprets the converted value directly into a.parent[] when scalar reinterpret is applicable, and otherwise delegates to linear setindex! at firstindex(a).",
    source := "base/reinterpretarray.jl:572-580", status := .proven,
    prop := ``RaSetCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group18.ReinterpretarrayZeroSet_proven },
  { id := "reinterpretarray-reshaped-get-set", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_getindex_ra(::ReshapedReinterpretArray)", "_setindex_ra!(::ReshapedReinterpretArray)", "getindex(::ReinterpretArray)", "setindex!(::ReinterpretArray)"],
    statement := "Reshaped reads and writes preserve the selected target value bytes and every disjoint parent value byte for arbitrary ranks, layouts and indices across singleton, scalar, equal-size, both target-larger-than-source multi-parent routes and target-smaller-than-source slices, with public padding, conversion and bounds errors.",
    source := "base/reinterpretarray.jl:35-72, 413-570, 572-734", status := .todo,
    prop := ``Statements.ReshapedReadsWrites, thm := none },
  { id := "reinterpretarray-inexact-stride-rejected", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_checked_strides", "strides(::ReinterpretArray)"],
    statement := "For arbitrary-length byte-stride tuples, exact divisions return every mathematical quotient; any non-integral stride is rejected, and divide-by-zero or signed division overflow is propagated before integrality checks.",
    source := "base/reinterpretarray.jl:225-230", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Strict.FullCheckedStrides, thm := some ``Strict.fullCheckedStrides},
  { id := "reinterpretarray-mapreduce-offset-overflow", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_mapreduce", "mapreduce_impl", "getindex(::ReshapedReinterpretArray,::SCartesianIndex2)"],
    statement := "Public reductions terminate without reading outside the parent axis, including offset endpoints.",
    source := "base/reinterpretarray.jl:454-459, 946-985", status := .refuted,
    prop := ``Statements.property_reinterpretarray_mapreduce_offset_overflow,
      thm := some ``approved_mapreduce_offset_overflow_refuted,
    issue := "none found (queries: reinterpret mapreduce typemax; reinterpret mapreduce overflow)" },
  { id := "reinterpretarray-constructor-validation-ordinary", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type,::AbstractArray)", "ReinterpretArray{T}(::typeof(reshape),::AbstractArray)", "reinterpret(::typeof(reshape),::Type{T},::AbstractArray)"],
    statement := "For every shape-valid parent with representable axes, plain and reshaped reinterpret follow the documented layout checks. For a non-singleton plain reinterpret with changed element size, the first axis must start at 1 and its exact mathematical length-times-source-size product must divide by target size; otherwise construction throws an error.",
    source := "base/reinterpretarray.jl:3-8, 35-103, 107-144, 151-188", status := .refuted,
    prop := ``JuliaLean.Statements.reinterpretarray.round7.property_reinterpretarray_constructor_validation_ordinary,
    thm := some ``Strict.ordinaryConstructorValidation_refuted,
    issue := "none found (queries: reinterpret size overflow; ReinterpretArray overflow; reinterpret negative size; reinterpret large range)",
    notes := "All parent types, including lazy and offset parents, remain in scope; dimensions have no typemax(Int) cap. The exact product avoids restating the model's wrapped Int64 multiplication, so reinterpretarrays-size-overflow can refute the statement." },
  { id := "reinterpretarray-totuple", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_totuple(::Type{All32{E,N}}, ::Union{Array,Memory})"],
    statement := "Tuple conversion consumes the requested first N+32 iterated elements of an array independently of its rank and shape.",
    source := "Tuple conversion iterable contract; base/reinterpretarray.jl:990-1000",
    status := .refuted, prop := ``Strict.FullTuplePrefix,
    thm := some ``Strict.fullTuplePrefix_refuted,
    issue := "bugs/reinterpretarray-totuple.yaml",
    notes := "The source model rejects a 4×8 UInt8 matrix when constructing NTuple{32,UInt8}, despite 32 available elements; the concrete counterexample uses zero bytes because rejection precedes reading." },
  { id := "reinterpretarrays-size-ordinary", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type,::AbstractArray)", "size(::NonReshapedReinterpretArray)"],
    statement := "Successful reinterpretations of ordinary small one-based dense arrays preserve total storage byte count.",
    source := "base/reinterpretarray.jl:73-103, 374-385", status := .proven,
    prop := ``Statements.OrdinarySizeConservation,
    thm := some ``approved_ordinary_size_conservation }
]
end JuliaLean.Proofs.base.reinterpretarray




namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12
open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Embed model exceptions in a state-preserving effect monad that also admits
arbitrary user exception payloads. Catching a model exception leaves unrelated
user exceptions untouched. This is an observation harness, not a model callee. -/
@[instance_reducible] def modelExceptions (World UserError : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ UserError) World) where
  throw e := fun w => .error (.inl e) w
  tryCatch action handler := fun w =>
    match action w with
    | .ok value after => .ok value after
    | .error (.inl e) after => handler e after
    | .error (.inr e) after => .error (.inr e) after

/-- Same-element reinterpretation leaves every observation of the original
array unchanged, including heap handles and alias identities. No storage or
shape requirement is imposed on the input array.
Documentation: base/reinterpretarray.jl:35-38,104,145. -/
def IdentityObservations : Prop :=
  ∀ (A Observation : Type) (observe : A → Observation) (a : A),
    observe (m104_reinterpretIdentity a) = observe a ∧
    observe (m145_reinterpretReshapeIdentity a) = observe a

/-- An observer records calls outside the arbitrary callee's mutable world.
The callee may return any result, mutate World arbitrarily, or throw any E.
No behavioral law is assumed. -/
def observedCall {A R World E : Type}
    (callee : TypeLayout → A → EStateM E World R)
    (target : TypeLayout) (a : A) :
    EStateM E (List (TypeLayout × A) × World) R := fun initial =>
  let calls := initial.1 ++ [(target, a)]
  match callee target a initial.2 with
  | .ok value after => .ok value (calls, after)
  | .error e after => .error e (calls, after)

/-- Observational call accounting over every parent dispatch: exactly one call
uses the stored parent and requested element type, on both success and failure.
The dispatcher has arbitrary behavior; the independent observer owns its log.
Invariant: base/reinterpretarray.jl:190; view parent at lines3-12. -/
def ParentDispatchArguments : Prop :=
  ∀ (A R O World E : Type) (callee : TypeLayout → A → EStateM E World R)
    (target : TypeLayout) (view : View O A) (initial : World),
    let ops : ParentReinterpretOps (EStateM E (List (TypeLayout × A) × World)) A R :=
      ⟨observedCall callee⟩
    match reinterpretParent ops target view ([], initial) with
    | .ok _ after => after.1 = [(target, view.parent)]
    | .error _ after => after.1 = [(target, view.parent)]

/-- A Julia conditional accepts either Bool value, and rejects every non-Bool
result with TypeError without further effects. This tests the actual boolean
assertion, independent of the dispatch operation that produced the value.
Invariant: conditional contexts in base/reinterpretarray.jl:85-99,124-138. -/
def BooleanConsumption : Prop :=
  ∀ (World UserError O : Type) (initial : World),
    letI := modelExceptions World UserError
    (∀ b : Bool, requireBool (m := EStateM (Error ⊕ UserError) World) (O := O) (.accepted b) initial = .ok b initial) ∧
    (∀ v : Value O, requireBool (m := EStateM (Error ⊕ UserError) World) (.rejected v) initial = .error (.inl .typeError) initial)

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

abbrev ConstructorBoolValue (O : Type) :=
  JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O)

/-- All selected-call outcomes are observed outside the callback world.
Type validation, dimensionality, subpadding and Bool conversion have explicit
arguments and results; remaining calls retain their exact failure identity. -/
inductive ConstructorEvent (A O E : Type) where
  | typeBool (operation : String) (argument : TypeLayout)
      (outcome : Except E (ConstructorBoolValue O))
  | subpadding (source target : TypeLayout) (outcome : Except E (ConstructorBoolValue O))
  | convertBool (argument : O) (outcome : Except E (ConstructorBoolValue O))
  | dimensions (argument : A) (outcome : Except E (Value O))
  | rankArithmetic (subtract : Bool) (left right : Value O) (outcome : Except E (Value O))
  | ordinary (operation : String) (failure : Option E)

structure ConstructorObservation (A O E World : Type) where
  before : World
  event : ConstructorEvent A O E
  after : World

abbrev ConstructorObservedWorld (A O E World : Type) :=
  List (ConstructorObservation A O E World) × World

abbrev ConstructorObservedM (A O E World : Type) :=
  EStateM (Error ⊕ E) (ConstructorObservedWorld A O E World)

/-- Concrete and user exceptions remain distinct; throwing either retains the
world at its exact source position. -/
@[instance_reducible] def constructorExceptionsDynamic (World E : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ E) World) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value after => .ok value after
    | .error (.inl error) after => handler error after
    | .error (.inr error) after => .error (.inr error) after

def constructorCallFailure {E X : Type} : Except E X → Option E
  | .ok _ => none
  | .error error => some error

/-- Independent outcome/state instrumentation; there is no law on the raw
operation and no way for it to rewrite the observation list. -/
def observeConstructor {A O E World X : Type}
    (event : Except E X → ConstructorEvent A O E)
    (action : EStateM E World X) : ConstructorObservedM A O E World X := fun initial =>
  match action initial.2 with
  | .ok value after => .ok value
      (initial.1 ++ [⟨initial.2, event (.ok value), after⟩], after)
  | .error error after => .error (.inr error)
      (initial.1 ++ [⟨initial.2, event (.error error), after⟩], after)

/-- Instrument every selected field, including calls not expected in a given
branch. This makes the trace and exception statements independent of dispatch
purity, correctness, return types, and mutation behavior. -/
def observeConstructorOps {A Ax O E World : Type}
    (ops : DynamicConstructorOps (EStateM E World) A Ax O) :
    DynamicConstructorOps (ConstructorObservedM A O E World) A Ax O where
  isType := ops.isType
  arrays := {
    values := {
      multiplyInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.multiplyInt" (constructorCallFailure outcome)) (ops.arrays.values.multiplyInt x y)
      remainderInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.remainderInt" (constructorCallFailure outcome)) (ops.arrays.values.remainderInt x y)
      equalInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.equalInt" (constructorCallFailure outcome)) (ops.arrays.values.equalInt x y)
      notEqualInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.notEqualInt" (constructorCallFailure outcome)) (ops.arrays.values.notEqualInt x y)
      addInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.addInt" (constructorCallFailure outcome)) (ops.arrays.values.addInt x y)
      subtractInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.subtractInt" (constructorCallFailure outcome)) (ops.arrays.values.subtractInt x y)
      greaterInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.greaterInt" (constructorCallFailure outcome)) (ops.arrays.values.greaterInt x y)
      divideFromInt := fun x y => observeConstructor (fun outcome => .ordinary "arrays.values.divideFromInt" (constructorCallFailure outcome)) (ops.arrays.values.divideFromInt x y)
    }
    axes := fun a => observeConstructor (fun outcome => .ordinary "arrays.axes" (constructorCallFailure outcome)) (ops.arrays.axes a)
    axesGet := fun x i => observeConstructor (fun outcome => .ordinary "arrays.axesGet" (constructorCallFailure outcome)) (ops.arrays.axesGet x i)
    length := fun x => observeConstructor (fun outcome => .ordinary "arrays.length" (constructorCallFailure outcome)) (ops.arrays.length x)
    first := fun x => observeConstructor (fun outcome => .ordinary "arrays.first" (constructorCallFailure outcome)) (ops.arrays.first x)
    axis := fun a i => observeConstructor (fun outcome => .ordinary "arrays.axis" (constructorCallFailure outcome)) (ops.arrays.axis a i)
    equalOneTo := fun x expected => observeConstructor (fun outcome => .ordinary "arrays.equalOneTo" (constructorCallFailure outcome)) (ops.arrays.equalOneTo x expected)
    eltype := fun a => observeConstructor (fun outcome => .ordinary "arrays.eltype" (constructorCallFailure outcome)) (ops.arrays.eltype a)
    alignedSizeOther := fun x => observeConstructor (fun outcome => .ordinary "arrays.alignedSizeOther" (constructorCallFailure outcome)) (ops.arrays.alignedSizeOther x)
    ndims := fun a => observeConstructor (.dimensions a) (ops.arrays.ndims a)
  }
  types := {
    isBits := fun t => observeConstructor (.typeBool "isBits" t) (ops.types.isBits t)
    bitPadding := fun t => observeConstructor (.typeBool "bitPadding" t) (ops.types.bitPadding t)
    singleton := fun t => observeConstructor (.typeBool "singleton" t) (ops.types.singleton t)
    alignedSize := fun x => observeConstructor (fun outcome => .ordinary "types.alignedSize" (constructorCallFailure outcome)) (ops.types.alignedSize x)
    alignedOther := fun x => observeConstructor (fun outcome => .ordinary "types.alignedOther" (constructorCallFailure outcome)) (ops.types.alignedOther x)
    subpadding := fun s t => observeConstructor (.subpadding s t) (ops.types.subpadding s t)
  }
  scalars := {
    equal := fun x y => observeConstructor (fun outcome => .ordinary "scalars.equal" (constructorCallFailure outcome)) (ops.scalars.equal x y)
    notEqual := fun x y => observeConstructor (fun outcome => .ordinary "scalars.notEqual" (constructorCallFailure outcome)) (ops.scalars.notEqual x y)
    greater := fun x y => observeConstructor (fun outcome => .ordinary "scalars.greater" (constructorCallFailure outcome)) (ops.scalars.greater x y)
    less := fun x y => observeConstructor (fun outcome => .ordinary "scalars.less" (constructorCallFailure outcome)) (ops.scalars.less x y)
    multiply := fun x y => observeConstructor (fun outcome => .ordinary "scalars.multiply" (constructorCallFailure outcome)) (ops.scalars.multiply x y)
    remainder := fun x y => observeConstructor (fun outcome => .ordinary "scalars.remainder" (constructorCallFailure outcome)) (ops.scalars.remainder x y)
    divide := fun x y => observeConstructor (fun outcome => .ordinary "scalars.divide" (constructorCallFailure outcome)) (ops.scalars.divide x y)
    add := fun x y => observeConstructor (.rankArithmetic false x y) (ops.scalars.add x y)
    subtract := fun x y => observeConstructor (.rankArithmetic true x y) (ops.scalars.subtract x y)
  }
  convertBool := fun x => observeConstructor (.convertBool x) (ops.convertBool x)
  oneToOther := fun x => observeConstructor (fun outcome => .ordinary "oneToOther" (constructorCallFailure outcome)) (ops.oneToOther x)
  equalAxisOther := fun axis value => observeConstructor (fun outcome => .ordinary "equalAxisOther" (constructorCallFailure outcome)) (ops.equalAxisOther axis value)

/-- Extract only observed user failures; concrete source failures are separate. -/
def constructorEventFailure {A O E : Type} : ConstructorEvent A O E → Option E
  | .typeBool _ _ outcome | .subpadding _ _ outcome | .convertBool _ outcome =>
    constructorCallFailure outcome
  | .dimensions _ outcome | .rankArithmetic _ _ _ outcome => constructorCallFailure outcome
  | .ordinary _ failure => failure

/-- A complete observation chain threads every callback's actual world and
preserves the last world on return or exception. -/
def ConstructorWorldChain {A O E World : Type} (initial final : World) :
    List (ConstructorObservation A O E World) → Prop
  | [] => final = initial
  | observation :: rest => observation.before = initial ∧
      ConstructorWorldChain observation.after final rest

/-- Any observed user exception is the first failure, is the exact final
exception, and ends the trace. Source errors and success require all selected
calls to have succeeded. No callback correctness assumptions are made. -/
def ConstructorExceptionTrace {A O E World X : Type}
    (outcome : Except (Error ⊕ E) X)
    (events : List (ConstructorObservation A O E World)) : Prop :=
  match outcome with
  | .error (.inr error) =>
    ∃ pre last, events = pre ++ [last] ∧
      (∀ observation ∈ pre, constructorEventFailure observation.event = none) ∧
      constructorEventFailure last.event = some error
  | _ => ∀ observation ∈ events, constructorEventFailure observation.event = none

/-- Classification of the source conditional's terminating outcomes. A custom
non-Bool value produces TypeError; an undesired Bool produces ArgumentError
when the local helper accepts both Type arguments, and otherwise its exact
MethodError. A user exception retains its exact payload. -/
def ConstructorTypeCheckFailure {O E : Type} (typesAdmitted : Bool)
    (helper : String) (expected : Bool)
    (outcome : Except E (ConstructorBoolValue O)) (error : Error ⊕ E) : Prop :=
  (∃ userError, outcome = .error userError ∧ error = .inr userError) ∨
  (∃ value, outcome = .ok (.rejected value) ∧ error = .inl .typeError) ∨
  (∃ value : Bool, outcome = .ok (.accepted value) ∧ value ≠ expected ∧
    (typesAdmitted = true ∧ error = .inl (.reinterpret .argument) ∨
      typesAdmitted = false ∧ error = .inl (.array (.julia (.methodError helper)))))

/-- Both constructors first query target/source isbits, then target/source
bit padding. Early failures stop at the exact observed query. Only the four
actual passing Bool values permit later work. Static layout flags are never
assumed to describe the selected query outcomes.
Invariant: base/reinterpretarray.jl:85-88,124-127. -/
def ConstructorTypePrefix {A O E World X : Type}
    (isType : TypeLayout → Bool) (target source : TypeLayout) (initial final : World)
    (outcome : Except (Error ⊕ E) X)
    (events : List (ConstructorObservation A O E World)) : Prop :=
  (∃ response error, ConstructorTypeCheckFailure (isType source && isType target) "throwbits" true response error ∧
    outcome = .error error ∧
    events = [⟨initial, .typeBool "isBits" target response, final⟩]) ∨
  (∃ response error w1, ConstructorTypeCheckFailure (isType source && isType target) "throwbits" true response error ∧
    outcome = .error error ∧ events = [
      ⟨initial, .typeBool "isBits" target (.ok (.accepted true)), w1⟩,
      ⟨w1, .typeBool "isBits" source response, final⟩]) ∨
  (∃ response error w1 w2, ConstructorTypeCheckFailure (isType source && isType target) "throwbitpadding" false response error ∧
    outcome = .error error ∧ events = [
      ⟨initial, .typeBool "isBits" target (.ok (.accepted true)), w1⟩,
      ⟨w1, .typeBool "isBits" source (.ok (.accepted true)), w2⟩,
      ⟨w2, .typeBool "bitPadding" target response, final⟩]) ∨
  (∃ response error w1 w2 w3, ConstructorTypeCheckFailure (isType source && isType target) "throwbitpadding" false response error ∧
    outcome = .error error ∧ events = [
      ⟨initial, .typeBool "isBits" target (.ok (.accepted true)), w1⟩,
      ⟨w1, .typeBool "isBits" source (.ok (.accepted true)), w2⟩,
      ⟨w2, .typeBool "bitPadding" target (.ok (.accepted false)), w3⟩,
      ⟨w3, .typeBool "bitPadding" source response, final⟩]) ∨
  (∃ w1 w2 w3 w4 tail, events = [
      ⟨initial, .typeBool "isBits" target (.ok (.accepted true)), w1⟩,
      ⟨w1, .typeBool "isBits" source (.ok (.accepted true)), w2⟩,
      ⟨w2, .typeBool "bitPadding" target (.ok (.accepted false)), w3⟩,
      ⟨w3, .typeBool "bitPadding" source (.ok (.accepted false)), w4⟩] ++ tail)

/-- Runtime type-parameter admission is representation data, independent of
any selected method's result correctness. -/
def ConstructorRankAdmitted {O : Type} : Value O → Prop
  | .native _ => True
  | .other _ admitted => admitted = true

/-- Every successful ordinary view retains the exact input handle, both type
tokens, its original rank value and ordinary form. Every selected operation,
state and user exception is included; there is no static metadata premise.
Documentation: base/reinterpretarray.jl:3-12,35-38,73-103. -/
def PlainConstructorContract : Prop :=
  ∀ (World E A Ax O : Type)
    (ops : DynamicConstructorOps (EStateM (Error ⊕ E) World) A Ax O)
    (target source : TypeLayout) (rank : Value O) (array : A) (initial : World),
    letI := constructorExceptionsDynamic World E
    match reinterpret ops target source rank array initial with
    | .error _ _ => True
    | .ok view _ => view.parent = array ∧ view.target = target ∧ view.source = source ∧
        view.rank = rank ∧ view.reshaped = false ∧ ConstructorRankAdmitted view.rank

/-- Every successful reshape view retains the exact parent and both type
identities and has an admissible runtime rank parameter. Rank-producing calls
and final-construction behavior are checked by the separate observed contracts.
Documentation: base/reinterpretarray.jl:3-12,107-144,151-160. -/
def ReshapeConstructorContract : Prop :=
  ∀ (World E A Ax O : Type)
    (ops : DynamicConstructorOps (EStateM (Error ⊕ E) World) A Ax O)
    (target source : TypeLayout) (array : A) (initial : World),
    letI := constructorExceptionsDynamic World E
    match reinterpretReshape ops target source array initial with
    | .error _ _ => True
    | .ok view _ => view.parent = array ∧ view.target = target ∧ view.source = source ∧
        view.reshaped = true ∧ ConstructorRankAdmitted view.rank

/-- The generic public wrapper inherits parent/type identity and the actual
admissible rank of its concrete reshape constructor. It cannot return the
custom result variant when the generic constructor was selected.
Documentation: base/reinterpretarray.jl:151-188. -/
def ReshapeWrapperGenericContract : Prop :=
  ∀ (World E A Ax O Custom R : Type)
    (ops : DynamicConstructorOps (EStateM (Error ⊕ E) World) A Ax O)
    (dispatch : ReshapeDispatchOps (EStateM (Error ⊕ E) World) Custom R)
    (target source : TypeLayout) (array : A) (initial : World),
    letI := constructorExceptionsDynamic World E
    match reinterpretReshapeArray ops dispatch target source (.generic array) initial with
    | .error _ _ => True
    | .ok (.inr _) _ => False
    | .ok (.inl view) _ =>
      view.parent = array ∧ view.target = target ∧ view.source = source ∧
        view.reshaped = true ∧ ConstructorRankAdmitted view.rank

/-- Exact selected-constructor observation, including result/error identity
and both state snapshots. -/
def observeCustomConstructor {A R E World : Type}
    (callee : TypeLayout → A → EStateM E World R) (target : TypeLayout) (array : A) :
    EStateM (Error ⊕ E)
      (List (World × TypeLayout × A × Except E R × World) × World) R := fun initial =>
  match callee target array initial.2 with
  | .ok result after => .ok result
      (initial.1 ++ [(initial.2, target, array, .ok result, after)], after)
  | .error error after => .error (.inr error)
      (initial.1 ++ [(initial.2, target, array, .error error, after)], after)

/-- A selected custom wrapper invokes its original target/array exactly once
and forwards the actual result or user error and post-call state. All generic
constructor operations are arbitrary and irrelevant to this selected path.
Invariant: base/reinterpretarray.jl:188. -/
def ReshapeWrapperCustomArguments : Prop :=
  ∀ (World E A Ax O Custom R : Type)
    (ops : DynamicConstructorOps
      (EStateM (Error ⊕ E)
        (List (World × TypeLayout × Custom × Except E R × World) × World)) A Ax O)
    (callee : TypeLayout → Custom → EStateM E World R)
    (target source : TypeLayout) (array : Custom) (initial : World),
    letI := constructorExceptionsDynamic
      (List (World × TypeLayout × Custom × Except E R × World) × World) E
    let dispatch : ReshapeDispatchOps
        (EStateM (Error ⊕ E)
          (List (World × TypeLayout × Custom × Except E R × World) × World)) Custom R :=
      ⟨observeCustomConstructor callee⟩
    match reinterpretReshapeArray ops dispatch target source (.custom array) ([], initial) with
    | .ok (.inl _) _ => False
    | .ok (.inr result) after =>
      after.1 = [(initial, target, array, .ok result, after.2)]
    | .error (.inr error) after =>
      after.1 = [(initial, target, array, .error error, after.2)]
    | .error (.inl _) _ => False

/-- Both full constructors preserve the selected type-check pre, every
state transition, and the first actual user error, without any callee law.
Concrete validation errors cannot conceal a selected operation's failure.
Invariant: base/reinterpretarray.jl:73-144. -/
def ConstructorValidationEffects : Prop :=
  ∀ (A Ax O E World : Type)
    (ops : DynamicConstructorOps (EStateM E World) A Ax O)
    (target source : TypeLayout) (rank : Value O) (array : A) (initial : World),
    letI := constructorExceptionsDynamic (ConstructorObservedWorld A O E World) E
    let watched := observeConstructorOps ops
    let correct (result : EStateM.Result (Error ⊕ E)
        (ConstructorObservedWorld A O E World) (View O A)) : Prop :=
      match result with
      | .ok view after =>
        ConstructorWorldChain initial after.2 after.1 ∧
        ConstructorExceptionTrace (.ok view) after.1 ∧
        ConstructorTypePrefix ops.isType target source initial after.2 (.ok view) after.1
      | .error error after =>
        ConstructorWorldChain initial after.2 after.1 ∧
        ConstructorExceptionTrace (X := View O A) (.error error) after.1 ∧
        ConstructorTypePrefix (X := View O A) ops.isType target source initial after.2 (.error error) after.1
    correct (reinterpret watched target source rank array ([], initial)) ∧
    correct (reinterpretReshape watched target source array ([], initial))

/-- Pure lazy-capture diagnostics retain their original ArgumentError class
for arbitrary accepted payloads. The effectful integer-multiple and size
messages are deliberately covered by their separate dispatched contracts.
Invariant: base/reinterpretarray.jl:14-31,74-84,119-123. -/
def DiagnosticExceptionClasses : Prop :=
  ∀ (Msg Dim Ax Src Tgt : Type) (s t u : TypeLayout)
    (msg : Msg) (dim : Dim) (ax : Ax) (sv : Src) (tv : Tgt),
    (m14_throwbits s t u : RResult Unit) = .error .argument ∧
    (throwSize0 s t msg : RResult Unit) = .error .argument ∧
    (m23_throwsingleton s t : RResult Unit) = .error .argument ∧
    (m27_throwbitpadding s t u : RResult Unit) = .error .argument ∧
    (throwNonIntegral s t dim : RResult Unit) = .error .argument ∧
    (throwFirstAxis s t ax : RResult Unit) = .error .argument ∧
    (throwFromSingleton sv tv : RResult Unit) = .error .argument

/-- Independent field-preparation specification. An actual Bool requires no
conversion. Native Int accepts exactly 0 and 1, otherwise InexactError. A
selected non-native conversion preserves its raw result tag without an early
Bool assertion, including every exception and state mutation. -/
def ConstructorBoolPreparation {A O E World : Type}
    (input : ConstructorBoolValue O)
    (outcome : Except (Error ⊕ E) (ConstructorBoolValue O))
    (initial final : World) (events : List (ConstructorObservation A O E World)) : Prop :=
  match input with
  | .accepted value =>
    outcome = .ok (.accepted value) ∧ events = [] ∧ final = initial
  | .rejected (.native value) =>
    events = [] ∧ final = initial ∧
    (if value.val = 0 then outcome = .ok (.accepted false)
     else if value.val = 1 then outcome = .ok (.accepted true)
     else outcome = .error (.inl (.array (.julia (.inexactError "Bool")))))
  | .rejected (.other value _) =>
    match outcome with
    | .ok result => events = [⟨initial, .convertBool value (.ok result), final⟩]
    | .error (.inr error) => events = [⟨initial, .convertBool value (.error error), final⟩]
    | .error (.inl _) => False

/-- An independently specified final construction: check rank admissibility,
prepare readable then writable, and only afterwards assert both fields Bool.
All input identities and flags of a successful allocation are accounted for.
This relation contains no call to newDynamicView or prepareViewBool. -/
def NewDynamicViewSpecification {A O E World : Type}
    (target source : TypeLayout) (array : A) (rank : Value O)
    (readable writable : ConstructorBoolValue O) (reshaped : Bool)
    (initial final : World) (outcome : Except (Error ⊕ E) (View O A))
    (events : List (ConstructorObservation A O E World)) : Prop :=
  if (match rank with | .native _ => true | .other _ admitted => admitted) then
    match outcome with
    | .ok view =>
      view.parent = array ∧ view.target = target ∧ view.source = source ∧
      view.rank = rank ∧ view.reshaped = reshaped ∧
      ∃ middle readEvents writeEvents,
        ConstructorBoolPreparation readable (.ok (.accepted view.readable))
          initial middle readEvents ∧
        ConstructorBoolPreparation writable (.ok (.accepted view.writable))
          middle final writeEvents ∧ events = readEvents ++ writeEvents
    | .error error =>
      ConstructorBoolPreparation readable (.error error) initial final events ∨
      (∃ readValue middle readEvents writeEvents,
        ConstructorBoolPreparation readable (.ok readValue) initial middle readEvents ∧
        ConstructorBoolPreparation writable (.error error) middle final writeEvents ∧
        events = readEvents ++ writeEvents) ∨
      (∃ readValue writeValue middle readEvents writeEvents,
        ConstructorBoolPreparation readable (.ok readValue) initial middle readEvents ∧
        ConstructorBoolPreparation writable (.ok writeValue) middle final writeEvents ∧
        events = readEvents ++ writeEvents ∧
        ((∃ value, readValue = .rejected value) ∨ (∃ value, writeValue = .rejected value)) ∧
        error = .inl .typeError)
  else outcome = .error (.inl .typeError) ∧ events = [] ∧ final = initial

/-- Direct full-domain contract for final construction. In particular, a
wrong result from readable's selected convert(Bool, ...) does not skip the
writable conversion; both conversions precede the final new field checks.
An inadmissible rank fails first. Arbitrary custom fields/results are retained.
Invariant: base/reinterpretarray.jl:102,143; src/julia-syntax.scm:795-806,3870-3893. -/
def NewDynamicViewEffects : Prop :=
  ∀ (A Ax O E World : Type)
    (ops : DynamicConstructorOps (EStateM E World) A Ax O)
    (target source : TypeLayout) (array : A) (rank : Value O)
    (readable writable : ConstructorBoolValue O) (reshaped : Bool) (initial : World),
    letI := constructorExceptionsDynamic (ConstructorObservedWorld A O E World) E
    match newDynamicView (observeConstructorOps ops) target source array rank
        readable writable reshaped ([], initial) with
    | .ok view after => NewDynamicViewSpecification target source array rank
        readable writable reshaped initial after.2 (.ok view) after.1
    | .error error after => NewDynamicViewSpecification target source array rank
        readable writable reshaped initial after.2 (.error error) after.1

/-- Rank observations are exactly ndims and its optional selected addition/subtraction by one call.
Other scalar work computes sizes or validation predicates, not the rank. -/
def isConstructorRankEvent {A O E : Type} : ConstructorEvent A O E → Bool
  | .dimensions .. | .rankArithmetic .. => true
  | _ => false

/-- The reshaped rank comes from exactly one ndims observation. It is either
that result, a native addition/subtraction by one with exact modular meaning, or the actual result of
one selected addition/subtraction by one call with the dimension result and native one as arguments.
This origin invariant does not assume any law on custom dimension arithmetic. -/
def ReshapeRankOrigin {A O E World : Type} (array : A)
    (events : List (ConstructorObservation A O E World)) (rank : Value O) : Prop :=
  (∃ dimension before after,
    events.filter (fun observation => isConstructorRankEvent observation.event) =
      [⟨before, .dimensions array (.ok dimension), after⟩] ∧
    (rank = dimension ∨
      ∃ input output : I64, dimension = .native input ∧ rank = .native output ∧
        (output.val % (2 ^ 64) = (input.val + 1) % (2 ^ 64) ∨
         output.val % (2 ^ 64) = (input.val - 1) % (2 ^ 64)))) ∨
  (∃ dimension subtract before middle after,
    (match dimension with | .native _ => False | .other _ _ => True) ∧
    events.filter (fun observation => isConstructorRankEvent observation.event) = [
      ⟨before, .dimensions array (.ok dimension), middle⟩,
      ⟨middle, .rankArithmetic subtract dimension (.native one) (.ok rank), after⟩])

/-- Only the final pair of padding calls and the following Bool conversions
belong to this phase. -/
def isConstructorFinalEvent {A O E : Type} : ConstructorEvent A O E → Bool
  | .subpadding .. | .convertBool .. => true
  | _ => false

/-- Independent final-phase contract. Reaching construction requires both
subpadding(T,S) and subpadding(S,T), in order, before rank checking or any Bool
conversion. Their exact raw results become the readable/writable inputs.
Failure during either query prevents every later phase operation. -/
def ConstructorFinalPhase {A O E World : Type}
    (target source : TypeLayout) (array : A) (reshaped : Bool)
    (rankOrigin : List (ConstructorObservation A O E World) → Value O → Prop)
    (final : World) (outcome : Except (Error ⊕ E) (View O A))
    (events : List (ConstructorObservation A O E World)) : Prop :=
  ((∀ observation ∈ events, isConstructorFinalEvent observation.event = false) ∧
    ∃ error, outcome = .error error) ∨
  (∃ pre before error,
    (∀ observation ∈ pre, isConstructorFinalEvent observation.event = false) ∧
    events = pre ++ [⟨before, .subpadding target source (.error error), final⟩] ∧
    outcome = .error (.inr error)) ∨
  (∃ pre before middle readable error,
    (∀ observation ∈ pre, isConstructorFinalEvent observation.event = false) ∧
    events = pre ++ [
      ⟨before, .subpadding target source (.ok readable), middle⟩,
      ⟨middle, .subpadding source target (.error error), final⟩] ∧
    outcome = .error (.inr error)) ∨
  (∃ pre before middle constructionStart readable writable rank tail,
    (∀ observation ∈ pre, isConstructorFinalEvent observation.event = false) ∧
    rankOrigin pre rank ∧ events = pre ++ [
      ⟨before, .subpadding target source (.ok readable), middle⟩,
      ⟨middle, .subpadding source target (.ok writable), constructionStart⟩] ++ tail ∧
    NewDynamicViewSpecification target source array rank readable writable reshaped
      constructionStart final outcome tail)

/-- Both public constructors place the actual two padding results into the
independently specified final construction phase. The plain rank is its input;
the reshaped rank has the exact observed dimension/arithmetic origin. Together
with the pre/state contract this excludes early field conversion, reversed
padding arguments, omitted padding calls and wrong-result replacement.
Invariant: base/reinterpretarray.jl:100-103,128-144. -/
def ConstructorPaddingAndFields : Prop :=
  ∀ (A Ax O E World : Type)
    (ops : DynamicConstructorOps (EStateM E World) A Ax O)
    (target source : TypeLayout) (rank : Value O) (array : A) (initial : World),
    letI := constructorExceptionsDynamic (ConstructorObservedWorld A O E World) E
    let watched := observeConstructorOps ops
    let plain := reinterpret watched target source rank array ([], initial)
    let reshaped := reinterpretReshape watched target source array ([], initial)
    (match plain with
      | .ok view after => ConstructorFinalPhase target source array false
          (fun _ actualRank => actualRank = rank) after.2 (.ok view) after.1
      | .error error after => ConstructorFinalPhase target source array false
          (fun _ actualRank => actualRank = rank) after.2 (.error error) after.1) ∧
    (match reshaped with
      | .ok view after => ConstructorFinalPhase target source array true
          (ReshapeRankOrigin array) after.2 (.ok view) after.1
      | .error error after => ConstructorFinalPhase target source array true
          (ReshapeRankOrigin array) after.2 (.error error) after.1)

/-- The generic public wrapper preserves the concrete constructor's observed
validation, padding/conversion phase, original parent/type identities and exact
user error/state behavior. The custom dispatch field is also instrumented and
must never be selected on this argument variant.
Invariant: base/reinterpretarray.jl:188 and constructor lines107-144. -/
def ReshapeWrapperGenericEffects : Prop :=
  ∀ (A Ax O E World Custom R : Type)
    (ops : DynamicConstructorOps (EStateM E World) A Ax O)
    (dispatch : ReshapeDispatchOps (EStateM E World) Custom R)
    (target source : TypeLayout) (array : A) (initial : World),
    letI := constructorExceptionsDynamic (ConstructorObservedWorld A O E World) E
    let watched := observeConstructorOps ops
    let watchedDispatch : ReshapeDispatchOps
        (ConstructorObservedM A O E World) Custom R := {
      custom := fun t a => observeConstructor
        (fun outcome => .ordinary "wrapperCustom" (constructorCallFailure outcome))
        (dispatch.custom t a)
    }
    let correct (outcome : Except (Error ⊕ E) (View O A))
        (after : ConstructorObservedWorld A O E World) : Prop :=
      ConstructorWorldChain initial after.2 after.1 ∧
      ConstructorExceptionTrace outcome after.1 ∧
      ConstructorTypePrefix ops.isType target source initial after.2 outcome after.1 ∧
      ConstructorFinalPhase target source array true (ReshapeRankOrigin array)
        after.2 outcome after.1 ∧
      (∀ observation ∈ after.1, match observation.event with
        | .ordinary name _ => name ≠ "wrapperCustom"
        | _ => True)
    match reinterpretReshapeArray watched watchedDispatch target source (.generic array)
        ([], initial) with
    | .ok (.inl view) after => correct (.ok view) after
    | .ok (.inr _) _ => False
    | .error error after => correct (.error error) after

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Mathematical observations of selected diagnostic calls. Actual arguments
and outcomes are retained, including type objects, non-Type eltype returns,
non-native sizes and arbitrary division results. -/
inductive DynamicDiagnosticEvent (A Ax O E : Type) where
  | elementType (array : A) (outcome : Except E (TypeValue O))
  | firstAxis (array : A) (index : I64) (outcome : Except E Ax)
  | alignedSize (argument : TypeValue O) (outcome : Except E (Value O))
  | division (numerator denominator : Value O) (outcome : Except E (Value O))
  | unexpected (operation : String)

/-- Each observation owns before/after snapshots outside the arbitrary
callback world. A callback cannot alter its observation list. -/
structure DynamicDiagnosticObservation (World Event : Type) where
  before : World
  event : Event
  after : World

abbrev DynamicDiagnosticWorld (A Ax O E World : Type) :=
  List (DynamicDiagnosticObservation World (DynamicDiagnosticEvent A Ax O E)) × World

abbrev DynamicDiagnosticM (A Ax O E World : Type) :=
  EStateM (Error ⊕ E) (DynamicDiagnosticWorld A Ax O E World)

/-- Source/native errors remain separate from arbitrary user exceptions.
Both channels retain mutations made before their throw point. -/
@[instance_reducible] def dynamicDiagnosticExceptions (World E : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ E) World) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value after => .ok value after
    | .error (.inl error) after => handler error after
    | .error (.inr error) after => .error (.inr error) after

/-- Observe any raw operation without assuming its result, purity, or
success. The actual result/error and both state snapshots enter the log. -/
def observeDynamicDiagnostic {A Ax O E World X : Type}
    (event : Except E X → DynamicDiagnosticEvent A Ax O E)
    (action : EStateM E World X) : DynamicDiagnosticM A Ax O E World X := fun initial =>
  match action initial.2 with
  | .ok value after => .ok value
      (initial.1 ++ [⟨initial.2, event (.ok value), after⟩], after)
  | .error error after => .error (.inr error)
      (initial.1 ++ [⟨initial.2, event (.error error), after⟩], after)

/-- Instrument every type-query field, including unrelated operations that
must not be introduced by a diagnostic implementation. -/
def dynamicDiagnosticTypes {A Ax O E World : Type}
    (ops : TypeQueryOps (EStateM E World) O) :
    TypeQueryOps (DynamicDiagnosticM A Ax O E World) O where
  isBits := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "isBits") (ops.isBits value)
  bitPadding := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "bitPadding") (ops.bitPadding value)
  singleton := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "singleton") (ops.singleton value)
  alignedSize := fun value => observeDynamicDiagnostic
    (.alignedSize (.type value)) (ops.alignedSize value)
  alignedOther := fun value => observeDynamicDiagnostic
    (.alignedSize (.other value)) (ops.alignedOther value)
  subpadding := fun source target => observeDynamicDiagnostic
    (fun _ => .unexpected "subpadding") (ops.subpadding source target)

/-- Observe the two actual division operands. Every other scalar operation
is separately visible as an unexpected event. -/
def dynamicDiagnosticScalars {A Ax O E World : Type}
    (ops : ScalarOps (EStateM E World) O) :
    ScalarOps (DynamicDiagnosticM A Ax O E World) O where
  equal := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "equal") (ops.equal x y)
  notEqual := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "notEqual") (ops.notEqual x y)
  greater := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "greater") (ops.greater x y)
  less := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "less") (ops.less x y)
  add := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "add") (ops.add x y)
  subtract := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "subtract") (ops.subtract x y)
  multiply := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "multiply") (ops.multiply x y)
  remainder := fun x y => observeDynamicDiagnostic
    (fun _ => .unexpected "remainder") (ops.remainder x y)
  divide := fun x y => observeDynamicDiagnostic (.division x y) (ops.divide x y)

/-- Both eltype calls and the first-axis call are independently observed.
All remaining array/old-scalar operations are instrumented as well, so a
spurious operation cannot be hidden by the observation harness. -/
def dynamicDiagnosticArrays {A Ax O E World : Type}
    (ops : ConstructorOps (EStateM E World) A Ax O) :
    ConstructorOps (DynamicDiagnosticM A Ax O E World) A Ax O where
  values := {
    multiplyInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.multiplyInt") (ops.values.multiplyInt x y)
    remainderInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.remainderInt") (ops.values.remainderInt x y)
    equalInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.equalInt") (ops.values.equalInt x y)
    notEqualInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.notEqualInt") (ops.values.notEqualInt x y)
    addInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.addInt") (ops.values.addInt x y)
    subtractInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.subtractInt") (ops.values.subtractInt x y)
    greaterInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.greaterInt") (ops.values.greaterInt x y)
    divideFromInt := fun x y => observeDynamicDiagnostic
      (fun _ => .unexpected "old.divideFromInt") (ops.values.divideFromInt x y)
  }
  axes := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "axes") (ops.axes value)
  axesGet := fun value index => observeDynamicDiagnostic
    (fun _ => .unexpected "axesGet") (ops.axesGet value index)
  length := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "length") (ops.length value)
  first := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "first") (ops.first value)
  ndims := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "ndims") (ops.ndims value)
  axis := fun value index => observeDynamicDiagnostic
    (.firstAxis value index) (ops.axis value index)
  equalOneTo := fun value expected => observeDynamicDiagnostic
    (fun _ => .unexpected "equalOneTo") (ops.equalOneTo value expected)
  eltype := fun value => observeDynamicDiagnostic (.elementType value) (ops.eltype value)
  alignedSizeOther := fun value => observeDynamicDiagnostic
    (fun _ => .unexpected "old.alignedSizeOther") (ops.alignedSizeOther value)

/-- The integer-multiple diagnostic evaluates target size before source size
and then raises ArgumentError. Neither result is constrained to Int or Bool.
Any user exception stops at the actual call and preserves its exact payload
and post-call world; no operation is permitted after that failure.
Invariant: base/reinterpretarray.jl:108-112. -/
def IntMultipleDiagnosticEffects : Prop :=
  ∀ (O E World R : Type) (types : TypeQueryOps (EStateM E World) O)
    (source target : TypeLayout) (initial : World),
    letI := dynamicDiagnosticExceptions (DynamicDiagnosticWorld Unit Unit O E World) E
    let watched := dynamicDiagnosticTypes (A := Unit) (Ax := Unit) types
    match (throwIntMultiple (α := R) watched source target) ([], initial) with
    | .ok _ _ => False
    | .error (.inl error) after =>
      error = .reinterpret .argument ∧
      ∃ (targetSize sourceSize : Value O) (middle : World), after.1 = [
        ⟨initial, .alignedSize (.type target) (.ok targetSize), middle⟩,
        ⟨middle, .alignedSize (.type source) (.ok sourceSize), after.2⟩]
    | .error (.inr error) after =>
      after.1 = [⟨initial, .alignedSize (.type target) (.error error), after.2⟩] ∨
      ∃ (targetSize : Value O) (middle : World), after.1 = [
        ⟨initial, .alignedSize (.type target) (.ok targetSize), middle⟩,
        ⟨middle, .alignedSize (.type source) (.error error), after.2⟩]

/-- At least one operand has a non-native runtime type. This is a
representation classification, not a behavioural assumption on division. -/
def DiagnosticNonNativePair {O : Type} : Value O → Value O → Prop
  | .native _, .native _ => False
  | _, _ => True

/-- Mathematical native-division failure criterion, independent of the
arithmetic model. A successful quotient is only captured by the lazy message,
after which the diagnostic itself raises ArgumentError. -/
def DynamicDiagnosticNativeFailure (numerator denominator : I64) (error : Error) : Prop :=
  if denominator.val = 0 ∨
      (numerator.val = -(2 ^ 63 : Int) ∧ denominator.val = -1) then
    error = .reinterpret .divide
  else error = .reinterpret .argument

/-- The five successful diagnostic observations preceding division. The
second eltype result itself is the argument of the final aligned-size query;
all intermediate worlds are explicit independent observations. -/
def DynamicSize1Prefix {A Ax O E World : Type}
    (array : A) (target : TypeLayout) (first second : TypeValue O) (axis : Ax)
    (numerator denominator : Value O)
    (initial w1 w2 w3 w4 w5 : World) :
    List (DynamicDiagnosticObservation World (DynamicDiagnosticEvent A Ax O E)) := [
  ⟨initial, .elementType array (.ok first), w1⟩,
  ⟨w1, .firstAxis array one (.ok axis), w2⟩,
  ⟨w2, .alignedSize (.type target) (.ok numerator), w3⟩,
  ⟨w3, .elementType array (.ok second), w4⟩,
  ⟨w4, .alignedSize second (.ok denominator), w5⟩]

/-- A source/native exception follows all five successful observations. A
native operand pair performs no selected division call and follows the exact
DivideError criterion; every other pair performs one observed division using
both actual size results, then raises ArgumentError without type-checking the
arbitrary quotient. -/
def DynamicSize1NativeTrace {A Ax O E World : Type}
    (array : A) (target : TypeLayout) (initial final : World) (error : Error)
    (events : List (DynamicDiagnosticObservation World (DynamicDiagnosticEvent A Ax O E))) : Prop :=
  (∃ (first second : TypeValue O) (axis : Ax) (x y : I64) (w1 w2 w3 w4 : World),
    events = DynamicSize1Prefix array target first second axis (.native x) (.native y)
      initial w1 w2 w3 w4 final ∧ DynamicDiagnosticNativeFailure x y error) ∨
  (∃ (first second : TypeValue O) (axis : Ax) (numerator denominator quotient : Value O)
      (w1 w2 w3 w4 w5 : World),
    DiagnosticNonNativePair numerator denominator ∧
    events = DynamicSize1Prefix array target first second axis numerator denominator
      initial w1 w2 w3 w4 w5 ++
      [⟨w5, .division numerator denominator (.ok quotient), final⟩] ∧
    error = .reinterpret .argument)

/-- A user error has a nonempty legal prefix, ending at its actual failed
operation with no later call. The error payload and every before/after world
must agree with the external observations. -/
def DynamicSize1UserTrace {A Ax O E World : Type}
    (array : A) (target : TypeLayout) (initial final : World) (error : E)
    (events : List (DynamicDiagnosticObservation World (DynamicDiagnosticEvent A Ax O E))) : Prop :=
  events = [⟨initial, .elementType array (.error error), final⟩] ∨
  (∃ (first : TypeValue O) (w1 : World), events = [
    ⟨initial, .elementType array (.ok first), w1⟩,
    ⟨w1, .firstAxis array one (.error error), final⟩]) ∨
  (∃ (first : TypeValue O) (axis : Ax) (w1 w2 : World), events = [
    ⟨initial, .elementType array (.ok first), w1⟩,
    ⟨w1, .firstAxis array one (.ok axis), w2⟩,
    ⟨w2, .alignedSize (.type target) (.error error), final⟩]) ∨
  (∃ (first : TypeValue O) (axis : Ax) (numerator : Value O) (w1 w2 w3 : World), events = [
    ⟨initial, .elementType array (.ok first), w1⟩,
    ⟨w1, .firstAxis array one (.ok axis), w2⟩,
    ⟨w2, .alignedSize (.type target) (.ok numerator), w3⟩,
    ⟨w3, .elementType array (.error error), final⟩]) ∨
  (∃ (first second : TypeValue O) (axis : Ax) (numerator : Value O)
      (w1 w2 w3 w4 : World), events = [
    ⟨initial, .elementType array (.ok first), w1⟩,
    ⟨w1, .firstAxis array one (.ok axis), w2⟩,
    ⟨w2, .alignedSize (.type target) (.ok numerator), w3⟩,
    ⟨w3, .elementType array (.ok second), w4⟩,
    ⟨w4, .alignedSize second (.error error), final⟩]) ∨
  (∃ (first second : TypeValue O) (axis : Ax) (numerator denominator : Value O)
      (w1 w2 w3 w4 w5 : World),
    DiagnosticNonNativePair numerator denominator ∧
    events = DynamicSize1Prefix array target first second axis numerator denominator
      initial w1 w2 w3 w4 w5 ++
      [⟨w5, .division numerator denominator (.error error), final⟩])

/-- Complete diagnostic call/error/state accounting over arbitrary array,
type-query and scalar dispatch. The two eltype observations, first-axis query,
target-size query and second-result-dependent size query are all required.
Both actual size values flow to division; a custom quotient may be any value.
No callee law or purity, native-size, Bool-result, or successful-call premise
narrows the quantification. Unrelated operations cannot appear in the trace.
Invariant: base/reinterpretarray.jl:113-118. -/
def DispatchedSize1DiagnosticEffects : Prop :=
  ∀ (A Ax O E World R : Type)
    (arrays : ConstructorOps (EStateM E World) A Ax O)
    (types : TypeQueryOps (EStateM E World) O)
    (scalars : ScalarOps (EStateM E World) O)
    (array : A) (target : TypeLayout) (initial : World),
    letI := dynamicDiagnosticExceptions (DynamicDiagnosticWorld A Ax O E World) E
    match (throwSize1Dispatched (α := R) (dynamicDiagnosticArrays arrays)
        (dynamicDiagnosticTypes types) (dynamicDiagnosticScalars scalars) array target)
        ([], initial) with
    | .ok _ _ => False
    | .error (.inl error) after =>
      DynamicSize1NativeTrace array target initial after.2 error after.1
    | .error (.inr error) after =>
      DynamicSize1UserTrace array target initial after.2 error after.1

/-- Native/native generic-scalar paths keep the exact native type and world.
Addition, subtraction and multiplication obey 64-bit modular arithmetic;
remainder and division obey signed truncation and their distinct error
criteria. All four comparisons agree with mathematical order. The selected
callbacks are arbitrary and must not affect these known native paths.
Invariant: base/reinterpretarray.jl:89-99,128-139,266-272;
doc/src/manual/integers-and-floating-point-numbers.md (overflow). -/
def NativeScalarPairArithmetic : Prop :=
  ∀ (World E O : Type) (ops : ScalarOps (EStateM (Error ⊕ E) World) O)
    (x y : I64) (initial : World),
    letI := dynamicDiagnosticExceptions World E
    let exactMod (action : EStateM (Error ⊕ E) World (Value O)) (value : Int) :=
      ∃ result : I64, action initial = .ok (.native result) initial ∧
        result.val % (2 ^ 64) = value % (2 ^ 64)
    exactMod (scalarAdd ops (.native x) (.native y)) (x.val + y.val) ∧
    exactMod (scalarSubtract ops (.native x) (.native y)) (x.val - y.val) ∧
    exactMod (scalarMultiply ops (.native x) (.native y)) (x.val * y.val) ∧
    (if y.val = 0 then
      scalarRemainder ops (.native x) (.native y) initial =
        .error (.inl (.reinterpret .divide)) initial
     else ∃ result : I64,
      scalarRemainder ops (.native x) (.native y) initial = .ok (.native result) initial ∧
      result.val = x.val.tmod y.val) ∧
    (if y.val = 0 ∨ (x.val = -(2 ^ 63) ∧ y.val = -1) then
      scalarDivide ops (.native x) (.native y) initial =
        .error (.inl (.reinterpret .divide)) initial
     else ∃ result : I64,
      scalarDivide ops (.native x) (.native y) initial = .ok (.native result) initial ∧
      result.val = x.val.tdiv y.val) ∧
    scalarEqual ops (.native x) (.native y) initial =
      .ok (decide (x.val = y.val)) initial ∧
    scalarNotEqual ops (.native x) (.native y) initial =
      .ok (decide (x.val ≠ y.val)) initial ∧
    scalarGreater ops (.native x) (.native y) initial =
      .ok (decide (x.val > y.val)) initial ∧
    scalarLess ops (.native x) (.native y) initial =
      .ok (decide (x.val < y.val)) initial

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Distinguish the helper's concrete Julia errors from arbitrary user
exceptions while preserving the world at either throw point. -/
@[instance_reducible] def axesExceptions98 (World UserError : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ UserError) World) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value after => .ok value after
    | .error (.inl error) after => handler error after
    | .error (.inr error) after => .error (.inr error) after

/-- Native tuple lookup is one-based: every split before the selected element
determines the returned payload, while every index outside the tuple raises
BoundsError. The complete native Int domain and every machine-sized tuple are
included. Results and errors leave the world unchanged; selected operations
are arbitrary and are not needed for this branch.
Invariant: axes(a)[1] at base/reinterpretarray.jl:91;
base/tuple.jl native getindex bounds; doc/src/manual/arrays.md (indexing). -/
def NativeAxesLookup : Prop :=
  ∀ (World UserError A Axis O : Type)
    (ops : ConstructorOps (EStateM (Error ⊕ UserError) World) A Axis O)
    (tuple : NativeTuple Axis) (index : I64) (initial : World),
    letI := axesExceptions98 World UserError
    let result := axesGet ops (.tuple tuple) index initial
    ((index.val < 1 ∨ (tuple.values.length : Int) < index.val) →
      result = .error (.inl (.array (.julia .boundsError))) initial) ∧
    (∀ (before after : List Axis) (selected : Axis),
      tuple.values = before ++ selected :: after →
      index.val = (before.length : Int) + 1 → result = .ok selected initial)

/-- Observe an exact custom index call independently of its mutable world. -/
structure AxesCall98 (O Axis UserError World : Type) where
  before : World
  argument : O
  index : I64
  outcome : Except UserError Axis
  after : World

/-- The observed custom operation retains every result, exception, and state
transition; it cannot edit its externally owned observation list. -/
def observeAxes98 {O Axis UserError World : Type}
    (callee : O → I64 → EStateM UserError World Axis) (argument : O) (index : I64) :
    EStateM (Error ⊕ UserError)
      (List (AxesCall98 O Axis UserError World) × World) Axis := fun initial =>
  match callee argument index initial.2 with
  | .ok result after => .ok result
      (initial.1 ++ [⟨initial.2, argument, index, .ok result, after⟩], after)
  | .error error after => .error (.inr error)
      (initial.1 ++ [⟨initial.2, argument, index, .error error, after⟩], after)

/-- A custom axes container receives exactly one getindex call with the
unchanged container and native index. Its actual result, exception and world
are forwarded without any tuple assumption or a spurious native exception.
The entire callback domain is quantified with no correctness law.
Invariant: axes(a)[1] at base/reinterpretarray.jl:91 and open getindex dispatch. -/
def CustomAxesLookup : Prop :=
  ∀ (World UserError A Axis O : Type)
    (ops : ConstructorOps
      (EStateM (Error ⊕ UserError)
        (List (AxesCall98 O Axis UserError World) × World)) A Axis O)
    (callee : O → I64 → EStateM UserError World Axis)
    (argument : O) (index : I64) (initial : World),
    letI := axesExceptions98 (List (AxesCall98 O Axis UserError World) × World) UserError
    let watched := { ops with axesGet := observeAxes98 callee }
    match axesGet watched (.other argument) index ([], initial) with
    | .ok result after =>
      after.1 = [⟨initial, argument, index, .ok result, after.2⟩]
    | .error (.inr error) after =>
      after.1 = [⟨initial, argument, index, .error error, after.2⟩]
    | .error (.inl _) _ => False

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Observe both model exceptions and arbitrary user exception payloads while
preserving state on errors. The local adapter catches only model exceptions and
passes user exceptions through without interpretation. -/
@[instance_reducible] def strideModelExceptions (World UserError : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ UserError) World) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value final => .ok value final
    | .error (.inl error) final => handler error final
    | .error (.inr error) final => .error (.inr error) final

/-- The first array query's exception and preceding mutation are preserved for every
selected dispatch table, index, and initial state. No contract for ndims is assumed.
Julia source: base/reinterpretarray.jl:208-209. -/
def StrideDimensionErrorPrecedence : Prop :=
  ∀ (W UserError A O C : Type) (ops : StrideSelectOps (EStateM (Error ⊕ UserError) W) A O C)
    (a : A) (index : Value O) (initial : W),
    letI := strideModelExceptions W UserError
    match ops.ndims a initial with
    | .ok _ _ => True
    | .error error final =>
        stride ops a index initial = .error error final

/-- Concrete native Int operations, with no custom values or callee laws. -/
def nativeCheckedStrideOps : CheckedStrideOps (Except Error) Empty Empty Empty where
  divremOtherLeft := fun value _ => nomatch value
  divremNativeOther := fun _ value => nomatch value
  resultGet := fun value _ => nomatch value
  resultFirst := fun value => nomatch value
  iszeroOther := fun value => nomatch value
  ismissingOther := fun value => nomatch value

/-- The native projection preserves the input tuple's representable arity. -/
def nativeStrideInput (values : NativeTuple I64) : NativeTuple (Value Empty) :=
  ⟨values.values.map Value.native, by simpa using values.nativeArity⟩

/-- Observable calls recorded around arbitrary user dispatch. Native operations do
not create artificial calls. This recording wrapper imposes no law on the user code. -/
inductive StrideCall where
  | division
  | remainder
  | zero
  | falseZero
  | missing
  | first
  | style
  | dimensions
  | comparison
  | strides
  | length
  | conversion
  | indexing
  deriving Repr, DecidableEq

/-- Preserve every value/error and final user state, adding an isolated audit trace.
The before-event remains visible even when the user callee raises an exception. -/
def traceStrideCall {W UserError A : Type} (before : List StrideCall)
    (after : A → List StrideCall) (action : EStateM UserError W A) :
    EStateM (Error ⊕ UserError) (W × List StrideCall) A :=
  fun (world, calls) =>
    match action world with
    | .ok value final => .ok value (final, calls ++ before ++ after value)
    | .error error final => .error (.inr error) (final, calls ++ before)

/-- The identical selected methods, with call recording around their actual execution. -/
def tracedCheckedStrideOps {W UserError O C P : Type}
    (ops : CheckedStrideOps (EStateM UserError W) O C P) :
    CheckedStrideOps (EStateM (Error ⊕ UserError) (W × List StrideCall)) O C P where
  divremOtherLeft := fun x y => traceStrideCall [.division] (fun _ => [])
    (ops.divremOtherLeft x y)
  divremNativeOther := fun x y => traceStrideCall [.division] (fun _ => [])
    (ops.divremNativeOther x y)
  resultGet := fun x index => traceStrideCall [.remainder] (fun _ => [])
    (ops.resultGet x index)
  resultFirst := fun x => traceStrideCall [.first] (fun _ => []) (ops.resultFirst x)
  iszeroOther := fun x => traceStrideCall [.zero]
    (fun value => match value with | .boolean false => [.falseZero] | _ => [])
    (ops.iszeroOther x)
  ismissingOther := fun x => traceStrideCall [.missing] (fun _ => [])
    (ops.ismissingOther x)

/-- Extract the call trace regardless of whether the computation succeeded or threw. -/
def strideCalls {E W A : Type} : EStateM.Result E (W × List StrideCall) A → List StrideCall
  | .ok _ (_, calls) => calls
  | .error _ (_, calls) => calls

/-- Three semantic phases: eager divisions, remainder tests, and quotient extraction. -/
def strideCallPhase : StrideCall → Nat
  | .division => 0
  | .remainder | .zero | .falseZero | .missing => 1
  | .first => 2
  | .style | .dimensions | .comparison | .strides | .length | .conversion | .indexing => 0

/-- Contiguity belongs to the backing array. Altering a view's type metadata, rank,
reshape tag, or cached permissions cannot affect the result, exception, or state.
No property is assumed of the parent query.
Julia source: base/reinterpretarray.jl:232. -/
def ContiguityDependsOnlyOnParent : Prop :=
  ∀ (W UserError A R O : Type) (ops : CheckContiguousOps (EStateM (Error ⊕ UserError) W) A R)
    (first second : View O A),
    first.parent = second.parent → checkContiguous ops first = checkContiguous ops second

/-- Ordinary reinterpret styles always expose one of the two standard styles,
regardless of what custom style object the parent query returns.
Julia source: base/reinterpretarray.jl:263-264. -/
def PlainIndexStyleRange : Prop :=
  ∀ (W UserError P O : Type) (ops : IndexStyleOps (EStateM (Error ⊕ UserError) W) P O)
    (parentType : P) (initial : W),
    match plainIndexStyle ops parentType initial with
    | .error _ _ => True
    | .ok result _ => result = .linear ∨ result = .cartesian

/-- Record the single selected IndexStyle method while leaving user behavior arbitrary. -/
def tracedIndexStyleOps {W UserError P O : Type} (ops : IndexStyleOps (EStateM UserError W) P O) :
    IndexStyleOps (EStateM (Error ⊕ UserError) (W × List StrideCall)) P O where
  parentStyle := fun parentType => traceStrideCall [.style] (fun _ => [])
    (ops.parentStyle parentType)

/-- A plain style query evaluates the parent style exactly once, even if it throws.
Julia source: base/reinterpretarray.jl:263-264. -/
def PlainIndexStyleSingleObservation : Prop :=
  ∀ (W UserError P O : Type) (ops : IndexStyleOps (EStateM UserError W) P O)
    (parentType : P) (initial : W),
    strideCalls (plainIndexStyle (tracedIndexStyleOps ops) parentType (initial, [])) = [.style]

/-- The scalar to_index conversion preserves the full runtime K and both native
coordinate fields, including machine extrema and non-native K parameters.
Julia source: base/reinterpretarray.jl:279. -/
def ToIndexCoordinatePreservation : Prop :=
  ∀ (O : Type) (index : RuntimeStaticIndex O),
    (toStaticIndex index).parameter = index.parameter ∧
    (toStaticIndex index).coordinates.i = index.coordinates.i ∧
    (toStaticIndex index).coordinates.j = index.coordinates.j

/-- Modular adjacency of two-dimensional native coordinates. This geometric relation
mentions no comparison against K and does not duplicate the branch condition. -/
def ForwardAdjacent (before after : SCartesianIndex2) : Prop :=
  (after.j = before.j ∧ (after.i.val - before.i.val - 1) % (2 ^ 64) = 0) ∨
    (after.i.val = 1 ∧ (after.j.val - before.j.val - 1) % (2 ^ 64) = 0)

/-- A previous step either decrements the inner coordinate or crosses exactly one
outer-coordinate boundary. In the second case the actual user K conversion is free
to choose the inner native coordinate or throw. -/
def BackwardAdjacent (before after : SCartesianIndex2) : Prop :=
  (after.j = before.j ∧ (after.i.val - before.i.val + 1) % (2 ^ 64) = 0) ∨
    (after.j.val - before.j.val + 1) % (2 ^ 64) = 0

/-- Generated branches preserve K and modular adjacency for arbitrary selected
comparisons, conversions, states and errors. The selection predicates describe actual
dispatch of the two possible constructor argument lists; no law is assumed for a custom
constructor, whose return is unrestricted. All constructor tables remain quantified.
Julia source: base/reinterpretarray.jl:280-283. -/
def StaticIndexAdjacency : Prop :=
  ∀ (W UserError A O : Type) (ops : StaticConstructorOps (EStateM (Error ⊕ UserError) W) O)
    (array : A) (index : RuntimeStaticIndex O) (initial : W),
    letI := strideModelExceptions W UserError
    ((ops.selectCustom index.parameter (.native (index.coordinates.i + one))
          (.native index.coordinates.j) = false ∧
      ops.selectCustom index.parameter (.native one)
          (.native (index.coordinates.j + one)) = false) →
      match nextStaticIndex ops array index initial with
      | .error _ _ => True
      | .ok (.index result) _ => result.parameter = index.parameter ∧
          ForwardAdjacent index.coordinates result.coordinates
      | .ok (.other _) _ => False) ∧
    ((ops.selectCustom index.parameter (.native (index.coordinates.i - one))
          (.native index.coordinates.j) = false ∧
      ops.selectCustom index.parameter index.parameter
          (.native (index.coordinates.j - one)) = false) →
      match previousStaticIndex ops array index initial with
      | .error _ _ => True
      | .ok (.index result) _ => result.parameter = index.parameter ∧
          BackwardAdjacent index.coordinates result.coordinates
      | .ok (.other _) _ => False)

/-- No open scalar operation can be reached for this concrete native instantiation. -/
def nativeStaticIndexOps : StaticIndexOps (Except Error) Empty where
  intLessOther := fun _ value => nomatch value
  convertInt := fun value => nomatch value

/-- Concrete generated constructor dispatch for native-only scalar values. The custom
branch is unselected for every such value and cannot affect native observations. -/
def nativeStaticConstructorOps : StaticConstructorOps (Except Error) Empty where
  coordinates := nativeStaticIndexOps
  selectCustom := fun _ _ _ => false
  custom := fun _ _ _ => .error Error.typeError

/-- Forward and backward traversal are inverse for every valid native channel
coordinate and every outer machine integer, including both wrapping endpoints.
The channel/coordinate requirements are exactly the finite iterator invariants.
Julia source: base/reinterpretarray.jl:280-283,288. -/
def StaticIndexNativeRoundtrip : Prop :=
  ∀ (channel : I64) (coordinates : SCartesianIndex2),
    1 < channel.val → 1 ≤ coordinates.i.val → coordinates.i.val ≤ channel.val →
    let original : RuntimeStaticIndex Empty := ⟨.native channel, coordinates⟩
    ((nextStaticIndex nativeStaticConstructorOps () original >>= fun next =>
      match next with
      | .index next => previousStaticIndex nativeStaticConstructorOps () next
      | .other value => pure (.other value)) = .ok (.index original)) ∧
    ((previousStaticIndex nativeStaticConstructorOps () original >>= fun previous =>
      match previous with
      | .index previous => nextStaticIndex nativeStaticConstructorOps () previous
      | .other value => pure (.other value)) = .ok (.index original))

/-- Neither scalar stepping method inspects the AbstractArray argument. This covers
custom constructors returning arbitrary values, custom arrays and arbitrary exceptions
without imposing any array or constructor correctness law.
Julia source: base/reinterpretarray.jl:280-283. -/
def StaticIndexArrayIndependence : Prop :=
  ∀ (W UserError A B O : Type) (ops : StaticConstructorOps (EStateM (Error ⊕ UserError) W) O)
    (first : A) (second : B) (index : RuntimeStaticIndex O),
    letI := strideModelExceptions W UserError
    nextStaticIndex ops first index = nextStaticIndex ops second index ∧
    previousStaticIndex ops first index = previousStaticIndex ops second index

/-- Generated geometry, native roundtrips and array independence cover both stepping methods. -/
def StaticIndexMotionContract : Prop :=
  StaticIndexAdjacency ∧ StaticIndexNativeRoundtrip ∧ StaticIndexArrayIndependence

/-- Instrument every selected call of stride(A,k), retaining all user state and
exceptions. The trace cannot be altered by user callees, which see only W. -/
def tracedStrideSelectOps {W UserError A O C : Type}
    (ops : StrideSelectOps (EStateM UserError W) A O C) :
    StrideSelectOps (EStateM (Error ⊕ UserError) (W × List StrideCall)) A O C where
  ndims := fun a => traceStrideCall [.dimensions] (fun _ => []) (ops.ndims a)
  strides := fun a => traceStrideCall [.strides] (fun _ => []) (ops.strides a)
  length := fun a => traceStrideCall [.length] (fun _ => []) (ops.length a)
  nativeLeOther := fun x y => traceStrideCall [.comparison] (fun _ => [])
    (ops.nativeLeOther x y)
  otherLe := fun x y => traceStrideCall [.comparison] (fun _ => []) (ops.otherLe x y)
  selectTupleIndex := ops.selectTupleIndex
  tupleCustomGet := fun values k => traceStrideCall [.indexing] (fun _ => [])
    (ops.tupleCustomGet values k)
  convertIndex := fun k => traceStrideCall [.conversion] (fun _ => []) (ops.convertIndex k)
  customGet := fun c k => traceStrideCall [.indexing] (fun _ => []) (ops.customGet c k)

/-- Semantic precedence of the dimension observation, comparison, chosen array
query, and indexing/conversion. Unrelated events cannot be produced by this wrapper. -/
def strideSelectPhase : StrideCall → Nat
  | .dimensions => 0
  | .comparison => 1
  | .strides | .length => 2
  | .conversion | .indexing => 3
  | _ => 4

/-- Dimension lookup always occurs exactly once. Comparison precedes the one chosen
array query; length and strides cannot both be evaluated, and no index conversion or
custom element access happens before strides. All dispatch and failures are arbitrary.
Julia source: base/reinterpretarray.jl:208-209. -/
def StrideEvaluationProtocol : Prop :=
  ∀ (W UserError A O C : Type) (ops : StrideSelectOps (EStateM UserError W) A O C)
    (a : A) (index : Value O) (initial : W),
    letI := strideModelExceptions (W × List StrideCall) UserError
    let calls := strideCalls (stride (tracedStrideSelectOps ops) a index (initial, []))
    calls.head? = some .dimensions ∧
    calls.count .dimensions = 1 ∧ calls.count .comparison ≤ 1 ∧
    calls.count .strides + calls.count .length ≤ 1 ∧
    calls.count .conversion + calls.count .indexing ≤ calls.count .strides ∧
    calls.Pairwise (fun before after => strideSelectPhase before ≤ strideSelectPhase after)

/-- The primitive tuple branch obeys exact one-based bounds on every native index.
This invariant directly tests the concrete helper used by the public stride method,
without any correctness law or assumption about the unrelated dispatch fields.
Julia source: base/reinterpretarray.jl:208-209; base/tuple.jl:33. -/
def StrideTupleNativeBounds : Prop :=
  ∀ (W UserError A O C : Type) (ops : StrideSelectOps (EStateM (Error ⊕ UserError) W) A O C)
    (values : NativeTuple (Value O)) (index : I64) (initial : W),
    letI := strideModelExceptions W UserError
    index.val < 1 ∨ (values.values.length : Int) < index.val →
      strideGet ops (.tuple values) (.native index) initial =
        .error (.inl (.tuple (.julia .boundsError))) initial

/-- A non-native Integer tuple subscript executes exactly one selected tuple indexing
call or, on generic Integer dispatch, one Int conversion. It never performs an array
query or both competing indexing paths. Arbitrary effects and failures are retained.
Julia source: base/reinterpretarray.jl:208-209; base/tuple.jl:34. -/
def StrideTupleConversionObservation : Prop :=
  ∀ (W UserError A O C : Type) (ops : StrideSelectOps (EStateM UserError W) A O C)
    (values : NativeTuple (Value O)) (index : O) (parameter : Bool) (initial : W),
    letI := strideModelExceptions (W × List StrideCall) UserError
    strideCalls (strideGet (tracedStrideSelectOps ops) (.tuple values)
      (.other index parameter) (initial, [])) =
        (if ops.selectTupleIndex values index then [.indexing] else [.conversion])

/-- Selected tuple indexing receives the original tuple and non-native Integer,
without conversion or reconstruction, and returns its arbitrary value/error/state.
This is the independent forwarding contract for a genuinely selected user overload.
Julia source: base/reinterpretarray.jl:208-209. -/
def StrideSelectedTupleForwarding : Prop :=
  ∀ (W UserError A O C : Type)
    (ops : StrideSelectOps (EStateM (Error ⊕ UserError) W) A O C)
    (values : NativeTuple (Value O)) (index : O) (parameter : Bool),
    letI := strideModelExceptions W UserError
    ops.selectTupleIndex values index = true →
    strideGet ops (.tuple values) (.other index parameter) = ops.tupleCustomGet values index

/-- Core tuple fields have integer names. Every Symbol conversion result, even a
Symbol whose spelling is a numeral, raises FieldError rather than TypeError; every
other non-Int result raises TypeError. This independently distinguishes the two runtime
error classes across every native-sized tuple and arbitrary payload/state.
Julia source: base/tuple.jl:34; src/builtins.c:1173-1194;
src/datatype.c:1859-1884; src/rtutils.c:170-173. -/
def StrideConvertedFieldClasses : Prop :=
  ∀ (W UserError O : Type) (values : NativeTuple (Value O)) (payload : O) (initial : W),
    letI := strideModelExceptions W UserError
    (tupleFieldRead (m := EStateM (Error ⊕ UserError) W) values (.symbol payload) initial =
      .error (.inl (.tuple .fieldError)) initial) ∧
    (tupleFieldRead (m := EStateM (Error ⊕ UserError) W) values (.other payload) initial =
      .error (.inl Error.typeError) initial)

/-- Error precedence, branch isolation, checked native bounds, and mandatory Integer
conversion cover all explicit helpers used by the full stride method. -/
def StrideContract : Prop :=
  StrideDimensionErrorPrecedence ∧ StrideEvaluationProtocol ∧
    StrideTupleNativeBounds ∧ StrideTupleConversionObservation ∧
    StrideSelectedTupleForwarding ∧ StrideConvertedFieldClasses

/-- Observe one forwarding call's original arguments and arbitrary user outcome,
keeping user exceptions separate from the model error channel. The user's method
sees only its original World, and cannot alter the isolated argument log. -/
def observeForwardArguments {World UserError Arguments A : Type}
    (arguments : Arguments) (action : EStateM UserError World A) :
    EStateM (Error ⊕ UserError) (World × List Arguments) A :=
  fun (world, seen) =>
    match action world with
    | .ok value final => .ok value (final, seen ++ [arguments])
    | .error error final => .error (.inr error) (final, seen ++ [arguments])

/-- Extract argument observations from either success or failure. -/
def forwardArguments {E World Arguments A : Type} :
    EStateM.Result E (World × List Arguments) A → List Arguments
  | .ok _ (_, seen) => seen
  | .error _ (_, seen) => seen

/-- The installed value-based similar forwarder makes exactly one allocation-method
call with the original parent, requested type, and dimensions. This holds for every
stateful user method, including arbitrary exceptions; no allocation law is assumed.
Julia source: base/reinterpretarray.jl:234; doc/src/manual/interfaces.md:224-233. -/
def SimilarParentArguments : Prop :=
  ∀ (World UserError A T S D R : Type)
    (callee : A → T → D → EStateM UserError World R)
    (view : ReinterpretArray T S A) (target : T) (dims : D) (initial : World),
    let observed := fun (parent : A) (type : T) (shape : D) =>
      observeForwardArguments (parent, type, shape) (callee parent type shape)
    forwardArguments (m234_similar observed view target dims (initial, [])) =
      [(view.parent, target, dims)]

/-- The installed type-based similar forwarder makes exactly one call with the stored
parent type and unchanged dimensions, independent of the wrapper type token. Arbitrary
user exceptions and state changes remain in the observed domain.
Julia source: base/reinterpretarray.jl:235; doc/src/manual/interfaces.md:224-233. -/
def SimilarTypeArguments : Prop :=
  ∀ (World UserError P TA D R : Type)
    (callee : P → D → EStateM UserError World R)
    (wrapperType : TA) (parentType : P) (dims : D) (initial : World),
    let observed := fun (parent : P) (shape : D) =>
      observeForwardArguments (parent, shape) (callee parent shape)
    forwardArguments (m235_similarType (_T := Unit) (_N := Unit) (_O := Unit)
      observed wrapperType dims parentType (initial, [])) = [(parentType, dims)]

/-- Narrow argument-identity coverage for both reused public forwarding methods. -/
def SimilarForwardingArguments : Prop := SimilarParentArguments ∧ SimilarTypeArguments

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

inductive StyleRouteCall where
  | size | less | parent | divide | constructor | unused
  deriving Repr, DecidableEq

/-- Observations are isolated from mutable user state and capture actual selected
metadata results, not a correctness assumption about those queries. -/
structure StyleRouteTrace (W UserError P O : Type) where
  calls : List StyleRouteCall := []
  typeArguments : List TypeLayout := []
  widths : List (TypeLayout × Value O) := []
  lastWidthWorld : Option W := none
  parentArguments : List P := []
  parents : List (RuntimeIndexStyle O) := []
  lessArguments : List (Value O × Value O) := []
  divideArguments : List (Value O × Value O) := []
  constructorArguments : List (Value O) := []
  terminals : List (EStateM.Result UserError W (RuntimeIndexStyle O)) := []

/-- Wrap a selected method without exposing the audit log to it. -/
def observeStyleRoute {W UserError X Log : Type}
    (before : Log → Log) (after : EStateM.Result UserError W X → Log → Log)
    (action : EStateM UserError W X) : EStateM (Error ⊕ UserError) (W × Log) X :=
  fun (world, log) =>
    let result := action world
    let log := after result (before log)
    match result with
    | .ok value final => .ok value (final, log)
    | .error error final => .error (.inr error) (final, log)

def styleRouteTrace {E W Log X : Type} : EStateM.Result E (W × Log) X → Log
  | .ok _ (_, log) => log
  | .error _ (_, log) => log

def eraseStyleRoute {E W Log X : Type} :
    EStateM.Result E (W × Log) X → EStateM.Result E W X
  | .ok value (world, _) => .ok value world
  | .error error (world, _) => .error error world

def embedStyleTerminal {W UserError X : Type} :
    EStateM.Result UserError W X → EStateM.Result (Error ⊕ UserError) W X
  | .ok value world => .ok value world
  | .error error world => .error (.inr error) world

/-- Exact constructor argument and terminal observations for arbitrary selected methods. -/
def tracedStyleConstructorOps {W UserError P O : Type}
    (ops : StaticStyleConstructorOps (EStateM UserError W) O) :
    StaticStyleConstructorOps
      (EStateM (Error ⊕ UserError) (W × StyleRouteTrace W UserError P O)) O where
  selectCustom := ops.selectCustom
  custom := fun parameter => observeStyleRoute
    (fun log => { log with
      calls := log.calls ++ [.constructor]
      constructorArguments := log.constructorArguments ++ [parameter] })
    (fun result log => { log with terminals := log.terminals ++ [result] })
    (ops.custom parameter)

/-- Reuse every actual method, adding only isolated observations of its execution. -/
def tracedReshapedStyleOps {W UserError P O : Type}
    (ops : ReshapedIndexStyleOps (EStateM UserError W) P O) :
    ReshapedIndexStyleOps
      (EStateM (Error ⊕ UserError) (W × StyleRouteTrace W UserError P O)) P O where
  types := {
    isBits := fun value => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.types.isBits value)
    bitPadding := fun value => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.types.bitPadding value)
    singleton := fun value => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.types.singleton value)
    alignedOther := fun value => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.types.alignedOther value)
    subpadding := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.types.subpadding left right)
    alignedSize := fun type => observeStyleRoute
      (fun log => { log with
        calls := log.calls ++ [.size]
        typeArguments := log.typeArguments ++ [type] })
      (fun result log => match result with
        | .ok value final => { log with
            widths := log.widths ++ [(type, value)]
            lastWidthWorld := some final }
        | .error _ _ => log) (ops.types.alignedSize type) }
  scalars := {
    equal := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.equal left right)
    notEqual := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.notEqual left right)
    greater := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.greater left right)
    add := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.add left right)
    subtract := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.subtract left right)
    multiply := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.multiply left right)
    remainder := fun left right => observeStyleRoute
      (fun log => { log with calls := log.calls ++ [.unused] })
      (fun _ log => log) (ops.scalars.remainder left right)
    less := fun left right => observeStyleRoute
      (fun log => { log with
        calls := log.calls ++ [.less]
        lessArguments := log.lessArguments ++ [(left, right)] })
      (fun _ log => log) (ops.scalars.less left right)
    divide := fun left right => observeStyleRoute
      (fun log => { log with
        calls := log.calls ++ [.divide]
        divideArguments := log.divideArguments ++ [(left, right)] })
      (fun _ log => log) (ops.scalars.divide left right) }
  parentStyle := fun parent => observeStyleRoute
    (fun log => { log with
      calls := log.calls ++ [.parent]
      parentArguments := log.parentArguments ++ [parent] })
    (fun result log => match result with
      | .ok value _ => { log with parents := log.parents ++ [value] }
      | .error _ _ => log) (ops.parentStyle parent)
  constructors := tracedStyleConstructorOps ops.constructors

/-- The style query preserves metadata-call order, repeated observations and scalar
operand order. It queries the parent at most once, reevaluates both widths only for a
linear parent, and passes arbitrary selected-constructor values/errors/states unchanged.
All methods and user exception objects are unrestricted; recorded native values imply
native arithmetic without imposing any law on a metadata callback.
Julia source: base/reinterpretarray.jl:266-272. -/
def ReshapedStyleEvaluation : Prop :=
  ∀ (W UserError P O : Type) (ops : ReshapedIndexStyleOps (EStateM UserError W) P O)
    (parent : P) (target source : TypeLayout) (initial : W),
    letI := strideModelExceptions (W × StyleRouteTrace W UserError P O) UserError
    let result := reshapedIndexStyle (tracedReshapedStyleOps ops) parent target source (initial, {})
    let log := styleRouteTrace result
    log.typeArguments.head? = some target ∧
    (∃ rest, log.typeArguments ++ rest = [target, source, source, target]) ∧
    (∃ rest, (log.calls.filter (fun call => call == .size || call == .parent)) ++ rest =
      [.size, .size, .parent, .size, .size]) ∧
    log.parentArguments.length ≤ 1 ∧
    (∀ argument ∈ log.parentArguments, argument = parent) ∧
    log.constructorArguments.length ≤ 1 ∧ .unused ∉ log.calls ∧
    (2 < log.typeArguments.length → log.parents = [.linear]) ∧
    (∀ t s, log.widths.take 2 = [(target, .native t), (source, .native s)] →
      log.parentArguments = [parent]) ∧
    (∀ t s, log.widths.take 2 = [(target, t), (source, s)] →
      ∀ pair ∈ log.lessArguments, pair = (t, s)) ∧
    (∀ t s s' t', log.widths = [(target, t), (source, s), (source, s'), (target, t')] →
      ∀ pair ∈ log.divideArguments, pair = (s', t')) ∧
    (log.constructorArguments ≠ [] → log.typeArguments = [target, source, source, target] ∧
      log.parents = [.linear]) ∧
    (∀ terminal ∈ log.terminals, eraseStyleRoute result = embedStyleTerminal terminal)

/-- The first type-metadata exception precedes every later metadata, style and scalar
call, retaining its arbitrary exception object and preceding state changes.
Julia source: base/reinterpretarray.jl:266-272. -/
def ReshapedStyleInitialFailure : Prop :=
  ∀ (W UserError P O : Type)
    (ops : ReshapedIndexStyleOps (EStateM (Error ⊕ UserError) W) P O)
    (parent : P) (target source : TypeLayout) (initial : W),
    letI := strideModelExceptions W UserError
    match ops.types.alignedSize target initial with
    | .ok _ _ => True
    | .error error final => reshapedIndexStyle ops parent target source initial = .error error final

/-- Native division is specified by mathematical divisibility, using the *second*
source/target observations. Neither equality of repeated queries nor successful array
construction is assumed. A zero divisor and signed quotient overflow both retain
DivideError at the final metadata state; no custom constructor is reached.
Julia source: base/reinterpretarray.jl:268. -/
def IndexStyleZeroWidthDivision : Prop :=
  ∀ (W UserError P O : Type) (ops : ReshapedIndexStyleOps (EStateM UserError W) P O)
    (parent : P) (target source : TypeLayout) (initial : W)
    (firstTarget firstSource secondSource secondTarget : I64) (lastWorld : W),
    letI := strideModelExceptions (W × StyleRouteTrace W UserError P O) UserError
    let result := reshapedIndexStyle (tracedReshapedStyleOps ops) parent target source (initial, {})
    let log := styleRouteTrace result
    log.widths = [(target, .native firstTarget), (source, .native firstSource),
      (source, .native secondSource), (target, .native secondTarget)] →
    log.lastWidthWorld = some lastWorld →
    (secondTarget.val = 0 ∨
      secondSource.val = IntTy.min .i64 ∧ secondTarget.val = -1) →
    eraseStyleRoute result = .error (.inl (.reinterpret .divide)) lastWorld ∧
      log.constructorArguments = []

/-- When runtime dispatch chooses the generated style constructor, every successful
native quotient equals the mathematical truncating quotient of the reobserved widths.
The first comparison may observe different widths; arbitrary callback mutations persist.
Julia source: base/reinterpretarray.jl:266-272. -/
def IndexStyleChannelQuotient : Prop :=
  ∀ (W UserError P O : Type) (ops : ReshapedIndexStyleOps (EStateM UserError W) P O)
    (parent : P) (target source : TypeLayout) (initial : W)
    (firstTarget firstSource secondSource secondTarget : I64) (lastWorld : W),
    letI := strideModelExceptions (W × StyleRouteTrace W UserError P O) UserError
    let result := reshapedIndexStyle (tracedReshapedStyleOps ops) parent target source (initial, {})
    let log := styleRouteTrace result
    let quotient : I64 := JInt.wrap .i64 (secondSource.val.tdiv secondTarget.val)
    log.widths = [(target, .native firstTarget), (source, .native firstSource),
      (source, .native secondSource), (target, .native secondTarget)] →
    log.lastWidthWorld = some lastWorld → secondTarget.val ≠ 0 →
    ¬ (secondSource.val = IntTy.min .i64 ∧ secondTarget.val = -1) →
    ops.constructors.selectCustom (.native quotient) = false →
    eraseStyleRoute result = .ok (.static (.native quotient)) lastWorld

/-- Type-parameter validity is runtime metadata, independent of constructor behavior. -/
def styleParameterValid : Value O → Bool
  | .native _ => true
  | .other _ valid => valid

/-- Combining equal static styles preserves K in the generated branch. A selected
specialized constructor receives exactly the full K and its result/error/state is retained.
Invalid type application fails before any constructor call. The statement includes all
negative/native and valid non-native parameters and every selected constructor behavior.
Julia source: base/reinterpretarray.jl:260,273. -/
def StaticStyleParameterPreservation : Prop :=
  ∀ (W UserError O : Type) (ops : StaticStyleConstructorOps (EStateM UserError W) O)
    (parameter : Value O) (left right : StaticStyleToken (Value O) parameter) (initial : W),
    letI := strideModelExceptions (W × StyleRouteTrace W UserError Unit O) UserError
    let result := combineStaticStyle (tracedStyleConstructorOps (P := Unit) ops) left right (initial, {})
    let log := styleRouteTrace result
    log.constructorArguments =
      (if styleParameterValid parameter && ops.selectCustom parameter then [parameter] else []) ∧
    (∀ terminal ∈ log.terminals, eraseStyleRoute result = embedStyleTerminal terminal) ∧
    (styleParameterValid parameter = false →
      eraseStyleRoute result = .error (.inl Error.typeError) initial) ∧
    (styleParameterValid parameter = true → ops.selectCustom parameter = false →
      eraseStyleRoute result = .ok (.static parameter) initial)

/-- Plain routing range, full selected-metadata evaluation, and concrete native division
invariants cover both public style queries without constraining custom callees. -/
def IndexStyleContract : Prop :=
  PlainIndexStyleRange ∧ PlainIndexStyleSingleObservation ∧ ReshapedStyleEvaluation ∧
    ReshapedStyleInitialFailure ∧ IndexStyleZeroWidthDivision ∧ IndexStyleChannelQuotient

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Observation-only exception adapter: model faults and arbitrary user exceptions both retain the final user world. This is a statement harness, not an assumed property of dispatch.
Julia source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
-- /Source
@[instance_reducible] def staticModelExceptions (World UserError : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ UserError) World) where
  throw e := fun w => .error (.inl e) w
  tryCatch action handler := fun w =>
    match action w with
    | .ok value after => .ok value after
    | .error (.inl e) after => handler e after
    | .error (.inr e) after => .error (.inr e) after

/-- An independent observer owns the trace and records a selected call before its effects, and the actual value only after a successful return. Dispatch cannot edit this log; its arbitrary result, exception and world are preserved.
Julia source: base/reinterpretarray.jl:298-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:298-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(iter::SCartesianIndices2{K}) where K = (K, length(iter.indices2))
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- 
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
def observeStaticIO {Event W E A : Type}
    (before : Event) (after : A → Event) (action : EStateM E W A) :
    EStateM E (List Event × W) A := fun initial =>
  let calls := initial.1 ++ [before]
  match action initial.2 with
  | .ok value world => .ok value (calls ++ [after value], world)
  | .error error world => .error error (calls, world)

/-- The outer constructor rejects non-native and at-most-one counts before all selected effects. Its generated inner constructor preserves range/K identity; actual K/R-specific constructors preserve their exact observed arbitrary result or exception. The entire native and non-native parameter domains are quantified.
Julia source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:288-288 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K} = (@assert K::Int > 1 "invalid index"; SCartesianIndices2{K,typeof(indices2)}(indices2))
-- /Source
def StaticIndicesConstructorContract : Prop :=
  ∀ (W E O R Out : Type) (ops : StaticRangeConstructorOps (EStateM (Error ⊕ E) W) O R Out)
    (parameter : Value O) (range : R) (initial : W),
    letI := staticModelExceptions
      (List (Sum (Value O × R) (Sum (RuntimeStaticIndices O R) Out)) × W) E
    let watched : StaticRangeConstructorOps
        (EStateM (Error ⊕ E)
          (List (Sum (Value O × R) (Sum (RuntimeStaticIndices O R) Out)) × W)) O R Out := {
      selectCustom := ops.selectCustom
      custom := fun k r => observeStaticIO (.inl (k, r)) Sum.inr (ops.custom k r) }
    let result := staticIndicesConstructor watched parameter range ([], initial)
    match parameter with
    | .other _ _ => result = .error (.inl Error.typeError) ([], initial)
    | .native k =>
        if k.val ≤ 1 then result = .error (.inl (.reinterpret .assertion)) ([], initial)
        else if ops.selectCustom parameter range then
          match result with
          | .error _ after => after.1 = [.inl (parameter, range)]
          | .ok value after => after.1 = [.inl (parameter, range), .inr value]
        else
          match result with
          | .ok (.inl iterator) after =>
              iterator.parameter = parameter ∧ iterator.indices2 = range ∧ after = ([], initial)
          | _ => False

/-- All executions first query the actual parent with linear style. A failed parent query is propagated with its world; successful known-range results preserve the exact K and range handle. No law is assumed of either selected dispatch.
Julia source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:290-290 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K} = SCartesianIndices2{K}(eachindex(IndexLinear(), parent(A)))
-- /Source
def StaticReshapedEachindexContract : Prop :=
  ∀ (W E A R C Out O : Type)
    (ops : StaticEachOps (EStateM (Error ⊕ E) W) A R C Out O)
    (parameter : Value O) (view : View O A) (initial : W),
    letI := staticModelExceptions W E
    let result := staticEachindexReshaped ops parameter view initial
    (match ops.eachindex .linear view.parent initial with
      | .error error world => result = .error error world
      | .ok (.custom _) _ => True
      | .ok (.known range) _ =>
          ops.constructors.selectCustom parameter range = false →
            match result with
            | .error _ _ => True
            | .ok (.inr _) _ => False
            | .ok (.inl iterator) _ =>
                iterator.parameter = parameter ∧ iterator.indices2 = range) ∧
    (match result with
      | .ok (.inl _) _ =>
          match parameter with | .native k => 1 < k.val | .other _ _ => False
      | _ => True)

/-- An independent observation flattens captured lazy diagnostic pieces: original axis handles and arbitrary custom join results stay distinguishable. It does not execute join dispatch or render any captured object.
Julia source: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- /Source
def staticJoinedValues {A O : Type} : StaticJoinedDiagnostic A O → List (Sum A (Value O))
  | .pair first second => [.inl first, .inl second]
  | .more first rest => .inl first :: staticJoinedValues rest
  | .custom value => [.inr value]

/-- When actual join selection is the concrete Base implementation at every suffix, lazy capture retains every original axis in order and is pure. The complete default outer helper then throws DimensionMismatch, while its one-argument default remains MethodError. All unused custom callbacks remain unrestricted.
Julia source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
def StaticMismatchCaptureContract : Prop :=
  ∀ (W E A O : Type) (ops : StaticMismatchOps (EStateM (Error ⊕ E) W) A O)
    (first second : A) (rest : NativeTuple A) (initial : W),
    letI := staticModelExceptions W E
    let known := { ops with selectJoin := fun _ _ => false }
    (match captureStaticAxesDispatched known first (second :: rest.values) initial with
      | .error _ _ => False
      | .ok captured after =>
          staticJoinedValues captured = (first :: second :: rest.values).map Sum.inl ∧
          after = initial) ∧
    (throwStaticEachMismatch known first (second :: rest.values) : EStateM (Error ⊕ E) W Unit) initial =
      .error (.inl (.array (.dimensionMismatch "all inputs to eachindex must have the same axes"))) initial ∧
    (throwStaticEachMismatch known first [] : EStateM (Error ⊕ E) W Unit) initial =
      .error (.inl (.array (.julia (.methodError "_join_comma_and")))) initial

/-- The length observer identifies the original range and actual successful returned value. All other range and conversion methods remain universally quantified and cannot alter the observation state.
Julia source: base/reinterpretarray.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(iter::SCartesianIndices2{K}) where K = (K, length(iter.indices2))
-- /Source
def StaticIndicesSizeContract : Prop :=
  ∀ (W E R O : Type) (ops : StaticRangeOps (EStateM (Error ⊕ E) W) R O)
    (iter : RuntimeStaticIndices O R) (initial : W),
    let lifted : StaticRangeOps
        (EStateM (Error ⊕ E) (List (Sum R (Value O)) × W)) R O := {
      constructors := {
        coordinates := {
          intLessOther := fun n o => observeStaticIO (.inr (.native n)) (fun _ => .inr (.other o false)) (ops.constructors.coordinates.intLessOther n o)
          convertInt := fun o => observeStaticIO (.inr (.other o false)) (fun _ => .inr (.other o false)) (ops.constructors.coordinates.convertInt o) }
        selectCustom := ops.constructors.selectCustom
        custom := fun k i j => observeStaticIO (.inr k) (fun _ => .inr i) (ops.constructors.custom k i j) }
      length := fun range => observeStaticIO (.inl range) Sum.inr (ops.length range)
      first := fun range => observeStaticIO (.inr (.native zero)) Sum.inr (ops.first range)
      last := fun range => observeStaticIO (.inr (.native zero)) Sum.inr (ops.last range) }
    match staticIndicesSize lifted iter ([], initial) with
    | .error _ after => after.1 = [.inl iter.indices2]
    | .ok result after =>
        result.1 = iter.parameter ∧ after.1 = [.inl iter.indices2, .inr result.2]

/-- Every successful axes result retains the original second-axis handle. For native K the first axis is a native OneTo with mathematically clipped endpoint, requires no custom call, and cannot throw; every non-native call is observed exactly once with its unchanged value.
Julia source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(iter::SCartesianIndices2{K}) where K = (OneTo(K), iter.indices2)
-- /Source
def StaticIndicesAxesContract : Prop :=
  ∀ (W E R O Ax : Type) (ops : StaticAxesOps (EStateM (Error ⊕ E) W) O Ax)
    (iter : RuntimeStaticIndices O R) (initial : W),
    letI := staticModelExceptions (List (Sum O Ax) × W) E
    let lifted : StaticAxesOps (EStateM (Error ⊕ E) (List (Sum O Ax) × W)) O Ax := {
      oneToOther := fun other => observeStaticIO (.inl other) Sum.inr (ops.oneToOther other) }
    let result := staticIndicesAxes lifted iter ([], initial)
    (match result with | .ok axes _ => axes.2 = iter.indices2 | .error _ _ => True) ∧
    (match iter.parameter with
      | .native k =>
          match result with
          | .error _ _ => False
          | .ok (.inr _, _) _ => False
          | .ok (.inl axis, _) after =>
              axis.stop.val = max 0 k.val ∧ after = ([], initial)
      | .other value _ =>
          match result with
          | .error _ after => after.1 = [.inl value]
          | .ok (.inl _, _) _ => False
          | .ok (.inr axis, _) after => after.1 = [.inl value, .inr axis])

/-- Native fields remain exactly unchanged and never execute arbitrary conversion code. Every successful generated index constructor retains its parameter and the already-native coordinate arguments; all non-native conversions, errors and mutations remain unrestricted.
Julia source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
def StaticCoordinateConstructionContract : Prop :=
  ∀ (W E O : Type) (ops : StaticIndexOps (EStateM (Error ⊕ E) W) O)
    (parameter i j : Value O) (initial : W),
    letI := staticModelExceptions W E
    (∀ (native : I64), staticCoordinate ops (.native native) initial = .ok (.accepted native) initial) ∧
    (match constructStaticIndex ops parameter i j initial with
      | .error _ _ => True
      | .ok index _ =>
          index.parameter = parameter ∧
          (match i with | .native n => index.coordinates.i = n | .other _ _ => True) ∧
          (match j with | .native n => index.coordinates.j = n | .other _ _ => True))

/-- For all custom endpoints and constructor behavior, every successful generated first index is in channel one and retains K; arbitrary selected custom results remain permitted. An endpoint exception is propagated before any field conversion with precisely its post-call world.
Julia source: base/reinterpretarray.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- /Source
def StaticIndicesFirstContract : Prop :=
  ∀ (W E R O : Type) (ops : StaticRangeOps (EStateM (Error ⊕ E) W) R O)
    (iter : RuntimeStaticIndices O R) (initial : W),
    letI := staticModelExceptions W E
    let result := staticIndicesFirst ops iter initial
    match ops.first iter.indices2 initial with
    | .error error world => result = .error error world
    | .ok endpoint _ =>
        let generated := !(ops.constructors.selectCustom iter.parameter (.native one) endpoint)
        generated = true →
          match result with
          | .error _ _ => True
          | .ok (.other _) _ => False
          | .ok (.index index) _ =>
              index.parameter = iter.parameter ∧ index.coordinates.i.val = 1 ∧
              (match endpoint with | .native n => index.coordinates.j = n | .other _ _ => True)

/-- For all native and non-native K and endpoints, successful generated last indices preserve K and native K becomes the exact first coordinate; custom constructor results remain unrestricted. A failing last(range) always precedes K conversion and is propagated with its state.
Julia source: base/reinterpretarray.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:302-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
def StaticIndicesLastContract : Prop :=
  ∀ (W E R O : Type) (ops : StaticRangeOps (EStateM (Error ⊕ E) W) R O)
    (iter : RuntimeStaticIndices O R) (initial : W),
    letI := staticModelExceptions W E
    let result := staticIndicesLast ops iter initial
    match ops.last iter.indices2 initial with
    | .error error world => result = .error error world
    | .ok endpoint _ =>
        let generated := !(ops.constructors.selectCustom iter.parameter iter.parameter endpoint)
        generated = true →
          match result with
          | .error _ _ => True
          | .ok (.other _) _ => False
          | .ok (.index index) _ => index.parameter = iter.parameter ∧
              (match iter.parameter with | .native k => index.coordinates.i = k | .other _ _ => True) ∧
              (match endpoint with | .native n => index.coordinates.j = n | .other _ _ => True)

/-- Native range elements produce exact generated indices, retaining K and both requested/returned coordinates without conversion effects. When the actual outer/Bool/axes/tuple/failing-helper methods are their default selections, an out-of-range native first coordinate throws before any custom check, lookup, conversion or mutation, even when the second coordinate is arbitrary. With checks elided, the range lookup is the first effect and its failures are preserved.
Julia source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
--     @boundscheck checkbounds(iter, i, j)
--     return SCartesianIndex2{K}(i, iter.indices2[j])
-- end
-- /Source
def StaticIndicesGetContract : Prop :=
  ∀ (W E R O Ax : Type) (ops : StaticGetOps (EStateM (Error ⊕ E) W) R O Ax)
    (enabled : Bool) (iter : RuntimeStaticIndices O R) (i j : I64) (initial : W),
    letI := staticModelExceptions W E
    let result := staticIndicesGet ops enabled iter i j initial
    (enabled = true → ∀ (k : I64), iter.parameter = .native k →
      ops.selectCheckbounds iter i j = false →
      ops.selectCheckboundsBool iter i j = false →
      ops.selectAxes iter = false →
      ops.selectTupleIndices
        [StaticBoundsAxis.native ⟨JInt.lit .i64 (max 0 k.val)⟩, .range iter.indices2]
        [i, j] = false →
      ops.selectThrowBounds iter i j = false →
      (i.val < 1 ∨ max 0 k.val < i.val) →
      result = .error (.inl (.array (.julia .boundsError))) initial) ∧
    (enabled = false →
      match ops.getRange iter.indices2 j initial with
      | .error error world => result = .error error world
      | .ok (.native endpoint) world =>
          ops.constructors.selectCustom iter.parameter (.native i) (.native endpoint) = false →
            match result with
            | .ok (.index index) after =>
                index.parameter = iter.parameter ∧ index.coordinates.i = i ∧
                index.coordinates.j = endpoint ∧ after = world
            | _ => False
      | .ok (.other _ _) _ => True)

/-- The SIMD metadata methods preserve all observations of the original custom outer range and exact type parameter. The native index kernel preserves the outer coordinate and increments the inner coordinate modulo the full 64-bit signed range, including overflow.
Julia source: base/reinterpretarray.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:327-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- SimdLoop.simd_outer_range(iter::SCartesianIndices2) = iter.indices2
-- SimdLoop.simd_inner_length(::SCartesianIndices2{K}, ::Any) where K = K
-- @inline function SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}
--     SCartesianIndex2{K}(I1+1, Ilast)
-- end
-- /Source
def StaticSimdContract : Prop :=
  ∀ (W E O R A Observation : Type) (observe : R → Observation)
    (ops : StaticConstructorOps (EStateM (Error ⊕ E) W) O)
    (iter : RuntimeStaticIndices O R) (other : A) (last inner : I64) (initial : W),
    letI := staticModelExceptions W E
    observe (staticSimdOuter iter) = observe iter.indices2 ∧
    staticSimdInnerLength iter other = iter.parameter ∧
    (ops.selectCustom iter.parameter (.native (inner + one)) (.native last) = false →
      match staticSimdIndex ops iter last inner initial with
      | .ok (.index index) after =>
          index.parameter = iter.parameter ∧ index.coordinates.j = last ∧
          index.coordinates.i.val =
            (inner.val + 1 - IntTy.min .i64) % (2 ^ 64) + IntTy.min .i64 ∧ after = initial
      | _ => False)

/-- The fallback invokes exactly one selected Cartesian method with the original array and every arbitrary index payload, on success or exception; its result is the observed returned value. The reshaped specialization preserves every observation of the original array for the same complete index domain.
Julia source: base/reinterpretarray.jl:333-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:333-334 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _maybe_reshape(::IndexSCartesian2, A::AbstractArray, I...) = _maybe_reshape(IndexCartesian(), A, I...)
-- _maybe_reshape(::IndexSCartesian2, A::ReshapedReinterpretArray, I...) = A
-- /Source
def StaticMaybeReshapeContract : Prop :=
  ∀ (W E A I R O Observation : Type)
    (ops : StaticMaybeReshapeOps (EStateM E W) A I R O)
    (observe : A → Observation) (array : A) (indices : NativeTuple I) (initial : W),
    let lifted : StaticMaybeReshapeOps
        (EStateM E (List (Sum (RuntimeIndexStyle O × A × NativeTuple I) R) × W)) A I R O := {
      fallback := fun style a is => observeStaticIO (.inl (style, a, is)) Sum.inr (ops.fallback style a is) }
    (match staticMaybeReshape lifted array indices ([], initial) with
      | .error _ after => after.1 = [.inl (.cartesian, array, indices)]
      | .ok value after => after.1 = [.inl (.cartesian, array, indices), .inr value]) ∧
    observe (staticMaybeReshapeIdentity array indices) = observe array

/-- The existing native-vararg Cartesian fallback models each perform exactly one call using the original array, value where present, and all machine-sized indices. The observer retains successful returned values and errors without any law on user dispatch.
Julia source: base/reinterpretarray.jl:337-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:337-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _getindex(::IndexSCartesian2, A::AbstractArray, I::Vararg{Int, N}) where {N}
--     @_propagate_inbounds_meta
--     _getindex(IndexCartesian(), A, I...)
-- end
-- function _setindex!(::IndexSCartesian2, A::AbstractArray, v, I::Vararg{Int, N}) where {N}
--     @_propagate_inbounds_meta
--     _setindex!(IndexCartesian(), A, v, I...)
-- end
-- /Source
def StaticCartesianFallbackContract : Prop :=
  ∀ (W E A V Out : Type)
    (get : A → List I64 → EStateM E W Out)
    (set : A → V → List I64 → EStateM E W Out)
    (array : A) (value : V) (indices : NativeTuple I64) (initial : W),
    (match m337_getindexFallback
      (fun a is => observeStaticIO
        (Event := Sum (A × List I64) Out) (.inl (a, is)) Sum.inr (get a is))
      array indices.values ([], initial) with
      | .error _ after => after.1 = [.inl (array, indices.values)]
      | .ok result after => after.1 = [.inl (array, indices.values), .inr result]) ∧
    (match m341_setindexFallback
      (fun a v is => observeStaticIO
        (Event := Sum (A × V × List I64) Out) (.inl (a, v, is)) Sum.inr (set a v is))
      array value indices.values ([], initial) with
      | .error _ after => after.1 = [.inl (array, value, indices.values)]
      | .ok result after => after.1 = [.inl (array, value, indices.values), .inr result])

/-- A trace distinguishes all source dispatch operations and their actual replies. The observer can see effects and exceptions without assuming equality, axes, or iterator correctness.
Julia source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
--     iter = eachindex(style, A)
--     itersBs = map(C->eachindex(style, C), B)
--     all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
--     return iter
-- end
-- /Source
inductive StaticManyEvent (A Iter Ax Pred O F : Type) where
  | each (style : RuntimeIndexStyle O) (array : A)
  | iterator (value : Iter)
  | closure (value : Iter)
  | closureResult (value : F)
  | allCall (predicate : F) (values : List Iter)
  | fixedAllCall (iterator : Iter) (values : List Iter)
  | allResult (value : JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  | equal (left right : Iter)
  | predicate (value : StridePredicate Pred)
  | missing (value : Pred)
  | missingResult (value : JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O))
  | axes (array : A)
  | axesResult (value : Ax)
  | mismatch (label : String) (first : Ax) (others : List Ax)
  | mismatchResult (value : Value O)
  | join (first : Ax) (others : List Ax)
  | joinResult (value : Value O)

/-- Instrumentation only: each arbitrary callee runs on its original world, with before/after trace events stored in a separate immutable observer channel.
Julia source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
--     iter = eachindex(style, A)
--     itersBs = map(C->eachindex(style, C), B)
--     all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
--     return iter
-- end
-- /Source
def observeStaticMany {W E A Iter Ax Pred O F : Type}
    (ops : StaticManyOps (EStateM (Error ⊕ E) W) A Iter Ax Pred O F) :
    StaticManyOps
      (EStateM (Error ⊕ E) (List (StaticManyEvent A Iter Ax Pred O F) × W))
      A Iter Ax Pred O F where
  eachindex := fun style array =>
    observeStaticIO (.each style array) StaticManyEvent.iterator (ops.eachindex style array)
  selectEqualityClosure := ops.selectEqualityClosure
  equalityClosure := fun iterator =>
    observeStaticIO (.closure iterator) StaticManyEvent.closureResult (ops.equalityClosure iterator)
  allCustom := fun predicate values =>
    observeStaticIO (.allCall predicate values) StaticManyEvent.allResult (ops.allCustom predicate values)
  selectAllCustom := ops.selectAllCustom
  customAllFixed := fun iterator values =>
    observeStaticIO (.fixedAllCall iterator values) StaticManyEvent.allResult (ops.customAllFixed iterator values)
  equal := fun left right =>
    observeStaticIO (.equal left right) StaticManyEvent.predicate (ops.equal left right)
  ismissingOther := fun value =>
    observeStaticIO (.missing value) StaticManyEvent.missingResult (ops.ismissingOther value)
  axes := fun array =>
    observeStaticIO (.axes array) StaticManyEvent.axesResult (ops.axes array)
  mismatch := {
    selectMismatch := ops.mismatch.selectMismatch
    customMismatch := fun label first others =>
      observeStaticIO (.mismatch label first others) StaticManyEvent.mismatchResult
        (ops.mismatch.customMismatch label first others)
    selectJoin := ops.mismatch.selectJoin
    customJoin := fun first others =>
      observeStaticIO (.join first others) StaticManyEvent.joinResult
        (ops.mismatch.customJoin first others) }

/-- Phases describe an independent temporal contract: obtaining all iterators precedes every equality/missing test; diagnostic axes precede every selected mismatch or join call. This observer classifies events and does not execute the model algorithm.
Julia source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
--     iter = eachindex(style, A)
--     itersBs = map(C->eachindex(style, C), B)
--     all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
--     return iter
-- end
-- /Source
def staticManyPhase {A Iter Ax Pred O F : Type} : StaticManyEvent A Iter Ax Pred O F → Nat
  | .each _ _ | .iterator _ => 0
  | .closure _ | .closureResult _ => 1
  | .equal _ _ | .predicate _ | .missing _ | .missingResult _ | .allCall _ _ | .fixedAllCall _ _ | .allResult _ => 2
  | .axes _ | .axesResult _ => 3
  | .mismatch _ _ _ | .mismatchResult _ | .join _ _ | .joinResult _ => 4

/-- A second observation-only exception adapter distinguishes local Core field faults from both ordinary model errors and arbitrary user exceptions, preserving the world at the exact failing observation.
Julia source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
@[instance_reducible] def staticFieldExceptions (W E : Type) :
    MonadExceptOf StaticFieldFault (EStateM (Error ⊕ (StaticFieldFault ⊕ E)) W) where
  throw error := fun world => .error (.inr (.inl error)) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value after => .ok value after
    | .error (.inr (.inl error)) after => handler error after
    | .error (.inl error) after => .error (.inl error) after
    | .error (.inr (.inr error)) after => .error (.inr (.inr error)) after

/-- A field observation preserves the exact stored payload or distinguishes missing, undefined and invalid-typed field observations. It never mutates the world and never returns a fabricated value for any malformed layout.
Julia source: base/docs/basedocs.jl:2609-2620; base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/docs/basedocs.jl:2609-2620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     getfield(value, name::Symbol, [order::Symbol], [boundscheck::Bool=true])
--     getfield(value, i::Int, [order::Symbol], [boundscheck::Bool=true])
-- 
-- Extract a field from a composite `value` by name or position.
-- 
-- Optionally, an ordering can be defined for the operation.
-- If the field was declared `@atomic`, the specification is strongly recommended to be
-- compatible with the stores to that location.
-- Otherwise, if not declared as `@atomic`, this parameter must be `:not_atomic` if specified.
-- 
-- The bounds check may be disabled, in which case the behavior of this function is
-- undefined if `i` is out of bounds.
-- /Source
-- Source: base/boot.jl:497-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct UndefRefError       <: Exception
--     UndefRefError() = new()
-- end
-- /Source
def StaticFieldObservationContract : Prop :=
  ∀ (A W : Type) (field : StaticField A) (initial : W),
    match (readStaticField field : EStateM StaticFieldFault W A) initial with
    | .ok value after => field = .present value ∧ after = initial
    | .error error after => after = initial ∧
        match error with
        | .bounds => field = .absent
        | .undefinedField => field = .undefined
        | .invalidType => field = .invalidType

/-- Concrete tuple destructuring reads exactly the required leading elements, ignores extra values, leaves state untouched, and rejects every too-short tuple with BoundsError. All arbitrary dispatch tables are quantified and remain unexecuted for this concrete Base instantiation.
Julia source: base/reinterpretarray.jl:309-325; base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
-- Source: base/tuple.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- indexed_iterate(t::Tuple, i::Int, state=1) = (@inline; (getfield(t, i), i+1))
-- /Source
def StaticTupleDestructuringContract : Prop :=
  ∀ (W E R O C DS : Type)
    (ops : StaticIterationOps (EStateM (Error ⊕ (StaticFieldFault ⊕ E)) W) R O C DS)
    (values : NativeTuple (Value O)) (initial : W),
    letI := staticModelExceptions W (StaticFieldFault ⊕ E)
    letI := staticFieldExceptions W E
    (match staticUnpackTwo ops (.tuple values) initial with
      | .ok pair after =>
          values.values[0]? = some pair.1 ∧ values.values[1]? = some pair.2 ∧ after = initial
      | .error error after =>
          values.values.length < 2 ∧ error = .inl (.tuple (.julia .boundsError)) ∧ after = initial) ∧
    (match staticUnpackThree ops (.tuple values) initial with
      | .ok state after =>
          values.values[0]? = some state.state1 ∧
          values.values[1]? = some state.item2 ∧
          values.values[2]? = some state.state2 ∧ after = initial
      | .error error after =>
          values.values.length < 3 ∧ error = .inl (.tuple (.julia .boundsError)) ∧ after = initial)

/-- A metamorphic observer changes only the otherwise-unobserved second field of a chosen custom indexed_iterate return. It preserves every selected call, payload outside that field, error and mutation.
Julia source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def replaceStaticFinalField {m : Type → Type} [Monad m] {R O C DS : Type}
    (ops : StaticIterationOps m R O C DS) (ordinal : I64) (replacement : StaticField DS) :
    StaticIterationOps m R O C DS :=
  { ops with indexedNext := fun object index state => do
      let reply ← ops.indexedNext object index state
      pure (if index = ordinal then { reply with second := replacement } else reply) }

/-- For every arbitrary custom indexed_iterate implementation, changing its final reply second field—even between present, absent and undefined—cannot alter tuple-assignment output, error or mutable state. The first field remains checked. This tests the distinction between intermediate iteration state and the unused final state.
Julia source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def StaticFinalDestructuringFieldIgnored : Prop :=
  ∀ (W E R O C DS : Type)
    (ops : StaticIterationOps (EStateM (Error ⊕ (StaticFieldFault ⊕ E)) W) R O C DS)
    (object : C) (left right : StaticField DS) (initial : W),
    letI := staticModelExceptions W (StaticFieldFault ⊕ E)
    letI := staticFieldExceptions W E
    staticUnpackTwo (replaceStaticFinalField ops (JInt.lit .i64 2) left) (.custom object) initial =
      staticUnpackTwo (replaceStaticFinalField ops (JInt.lit .i64 2) right) (.custom object) initial ∧
    staticUnpackThree (replaceStaticFinalField ops (JInt.lit .i64 3) left) (.custom object) initial =
      staticUnpackThree (replaceStaticFinalField ops (JInt.lit .i64 3) right) (.custom object) initial

/-- Every initial returned state begins in channel one and retains the unconverted item. Native range elements produce exact generated indices preserving K; more-specific constructors may return arbitrary values. The first range call error and its mutation are preserved, and nothing stops immediately with that call world. Every custom reply shape and conversion is quantified without laws.
Julia source: base/reinterpretarray.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def StaticInitialIterationContract : Prop :=
  ∀ (W E R O C DS : Type)
    (ops : StaticIterationOps (EStateM (Error ⊕ (StaticFieldFault ⊕ E)) W) R O C DS)
    (iter : RuntimeStaticIndices O R) (initial : W),
    letI := staticModelExceptions W (StaticFieldFault ⊕ E)
    letI := staticFieldExceptions W E
    let result := staticIndicesIterate ops iter initial
    (match ops.start iter.indices2 initial with
      | .error error world => result = .error error world
      | .ok .nothing world => result = .ok none world
      | .ok _ _ => True) ∧
    (match result with
      | .ok (some (item, state)) _ =>
          state.state1 = .native one ∧
          (match state.item2 with
            | .native value =>
                ops.constructors.selectCustom iter.parameter (.native one) (.native value) = false →
                  match item with
                  | .index index => index.parameter = iter.parameter ∧
                      index.coordinates.i.val = 1 ∧ index.coordinates.j = value
                  | .other _ => False
            | .other _ _ => True)
      | _ => True)

/-- Whenever both returned state coordinates are native, successful iteration produces the exact generated index with K retained. Other selected constructor results remain unrestricted. Across the complete native tuple-state domain, an interior channel advances arithmetically and preserves the outer iteration state without any effect; at a boundary the parent step receives the exact state2 and its failures are preserved. Arbitrary/malformed/custom states remain in the universal domain.
Julia source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:316-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def StaticStatefulIterationContract : Prop :=
  ∀ (W E R O C DS : Type)
    (ops : StaticIterationOps (EStateM (Error ⊕ (StaticFieldFault ⊕ E)) W) R O C DS)
    (iter : RuntimeStaticIndices O R) (argument : StaticStateArgument O C) (initial : W),
    letI := staticModelExceptions W (StaticFieldFault ⊕ E)
    letI := staticFieldExceptions W E
    let result := staticIndicesIterateState ops iter argument initial
    (match result with
      | .ok (some (item, state)) _ =>
          match state.state1, state.item2 with
          | .native i, .native j =>
              ops.constructors.selectCustom iter.parameter (.native i) (.native j) = false →
                match item with
                | .index index => index.parameter = iter.parameter ∧
                    index.coordinates.i = i ∧ index.coordinates.j = j
                | .other _ => False
          | _, _ => True
      | _ => True) ∧
    (match argument, iter.parameter with
      | .tuple values, .native k =>
          match values.values with
          | .native channel :: .native item :: state2 :: _ =>
              if channel.val < k.val then
                ops.constructors.selectCustom iter.parameter (.native (channel + one)) (.native item) = false →
                match result with
                | .ok (some (.index index, state)) after =>
                    index.coordinates.i.val = channel.val + 1 ∧ index.coordinates.j = item ∧
                    state.state1 = .native index.coordinates.i ∧
                    state.item2 = .native item ∧ state.state2 = state2 ∧ after = initial
                | _ => False
              else
                match ops.step iter.indices2 state2 initial with
                | .error error after => result = .error error after
                | .ok _ _ => True
          | _ => True
      | _, _ => True)

/-- Lift a user operation through an untouched observer channel. Only selected constructor calls can append the constructor trace; all other user effects still act on the original world.
Julia source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
def liftStaticWorld {Log W E A : Type} (action : EStateM E W A) :
    EStateM E (Log × W) A := fun initial =>
  match action initial.2 with
  | .ok value after => .ok value (initial.1, after)
  | .error error after => .error error (initial.1, after)

/-- Observe selected constructor arguments and the actual arbitrary returned value. Generated conversion callees run on the original user world and cannot modify the isolated constructor log.
Julia source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
def observeStaticConstructor {W E O : Type}
    (ops : StaticConstructorOps (EStateM E W) O) :
    StaticConstructorOps
      (EStateM E (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W)) O where
  coordinates := {
    intLessOther := fun i o => liftStaticWorld (ops.coordinates.intLessOther i o)
    convertInt := fun o => liftStaticWorld (ops.coordinates.convertInt o) }
  selectCustom := ops.selectCustom
  custom := fun k i j => observeStaticIO (.inl (k, i, j)) Sum.inr (ops.custom k i j)

/-- Once the generated method is selected, native Int/Int construction is concrete and effect-free. Every selected custom constructor, including a K-specific method on native coordinates, receives K/i/j once and returns its exact observed arbitrary runtime result or propagates its error; generated construction retains K and never calls the custom method.
Julia source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
def StaticConstructorDispatchContract : Prop :=
  ∀ (W E O : Type) (ops : StaticConstructorOps (EStateM (Error ⊕ E) W) O)
    (k i j : Value O) (initial : W),
    letI := staticModelExceptions
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W) E
    let result := callStaticIndexConstructor (observeStaticConstructor ops) k i j ([], initial)
    if ops.selectCustom k i j then
      match result with
      | .error _ after => after.1 = [.inl (k, i, j)]
      | .ok value after => after.1 = [.inl (k, i, j), .inr value]
    else
      match i, j with
      | .native first, .native second =>
          match result with
          | .ok (.index index) after =>
              index.parameter = k ∧ index.coordinates.i = first ∧ index.coordinates.j = second ∧
              after = ([], initial)
          | _ => False
      | _, _ =>
          match result with
          | .error _ after => after.1 = []
          | .ok (.other _) _ => False
          | .ok (.index index) after => index.parameter = k ∧ after.1 = []

/-- The endpoint observer instruments only constructor dispatch while lifting arbitrary range operations and their effects unchanged.
Julia source: base/reinterpretarray.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
def observeStaticRangeConstructor {W E R O : Type}
    (ops : StaticRangeOps (EStateM E W) R O) :
    StaticRangeOps
      (EStateM E (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W)) R O where
  constructors := observeStaticConstructor ops.constructors
  length := fun range => liftStaticWorld (ops.length range)
  first := fun range => liftStaticWorld (ops.first range)
  last := fun range => liftStaticWorld (ops.last range)

/-- An independent single-constructor-call trace contract: a selected custom method must be called once and its observed return must be the public result. Generated construction has no custom dispatch event.
Julia source: base/reinterpretarray.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
def staticSelectedConstructorTrace {W E O : Type} (selected : Bool)
    (arguments : Value O × Value O × Value O)
    (result : EStateM.Result E
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W)
      (StaticIndexResult O)) : Prop :=
  if selected then
    match result with
    | .error _ after => after.1 = [.inl arguments]
    | .ok value after => after.1 = [.inl arguments, .inr value]
  else
    match result with
    | .error _ after => after.1 = []
    | .ok _ after => after.1 = []

/-- Both endpoint methods preserve every selected constructor outcome, including non-index values and errors. They pass the original K, the original endpoint before conversion, and channel one or K exactly, after the endpoint operation has completed. No custom constructor correctness law is used.
Julia source: base/reinterpretarray.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:301-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(iter::SCartesianIndices2{K}) where {K} = SCartesianIndex2{K}(1, first(iter.indices2))
-- last(iter::SCartesianIndices2{K}) where {K}  = SCartesianIndex2{K}(K, last(iter.indices2))
-- /Source
def StaticEndpointCustomConstructorContract : Prop :=
  ∀ (W E R O : Type) (ops : StaticRangeOps (EStateM (Error ⊕ E) W) R O)
    (iter : RuntimeStaticIndices O R) (initial : W),
    letI := staticModelExceptions
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W) E
    let observed := observeStaticRangeConstructor ops
    let firstResult := staticIndicesFirst observed iter ([], initial)
    let lastResult := staticIndicesLast observed iter ([], initial)
    (match ops.first iter.indices2 initial with
      | .error error world => firstResult = .error error ([], world)
      | .ok endpoint _ =>
          let selected := ops.constructors.selectCustom iter.parameter (.native one) endpoint
          staticSelectedConstructorTrace selected (iter.parameter, .native one, endpoint) firstResult) ∧
    (match ops.last iter.indices2 initial with
      | .error error world => lastResult = .error error ([], world)
      | .ok endpoint _ =>
          let selected := ops.constructors.selectCustom iter.parameter iter.parameter endpoint
          staticSelectedConstructorTrace selected (iter.parameter, iter.parameter, endpoint) lastResult)

/-- The lookup observer records only a genuinely selected custom constructor call; all axis checks, conversion operations and range lookup effects remain arbitrary and retain their world.
Julia source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
--     @boundscheck checkbounds(iter, i, j)
--     return SCartesianIndex2{K}(i, iter.indices2[j])
-- end
-- /Source
def observeStaticGetConstructor {W E R O Ax : Type}
    (ops : StaticGetOps (EStateM E W) R O Ax) :
    StaticGetOps
      (EStateM E (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W)) R O Ax where
  constructors := observeStaticConstructor ops.constructors
  axes := { oneToOther := fun o => liftStaticWorld (ops.axes.oneToOther o) }
  selectCheckbounds := ops.selectCheckbounds
  customCheckbounds := fun a i j => liftStaticWorld (ops.customCheckbounds a i j)
  selectCheckboundsBool := ops.selectCheckboundsBool
  customCheckboundsBool := fun a i j => liftStaticWorld (ops.customCheckboundsBool a i j)
  selectAxes := ops.selectAxes
  customAxes := fun a => liftStaticWorld (ops.customAxes a)
  selectTupleIndices := ops.selectTupleIndices
  customTupleIndices := fun axes indices => liftStaticWorld (ops.customTupleIndices axes indices)
  selectOtherIndices := ops.selectOtherIndices
  customOtherIndices := fun axes indices => liftStaticWorld (ops.customOtherIndices axes indices)
  selectThrowBounds := ops.selectThrowBounds
  customThrowBounds := fun a i j => liftStaticWorld (ops.customThrowBounds a i j)
  lengthCustom := fun a => liftStaticWorld (ops.lengthCustom a)
  lengthRange := fun a => liftStaticWorld (ops.lengthRange a)
  equalLengthOne := fun a i => liftStaticWorld (ops.equalLengthOne a i)
  ismissingOther := fun a => liftStaticWorld (ops.ismissingOther a)
  checkCustomFirst := fun a i => liftStaticWorld (ops.checkCustomFirst a i)
  checkRange := fun r j => liftStaticWorld (ops.checkRange r j)
  getRange := fun r j => liftStaticWorld (ops.getRange r j)

/-- At most one custom constructor is called during scalar lookup. Whenever it is selected, its K and first coordinate are exactly the iterator parameter and requested index, and its arbitrary returned value becomes the public result without reinterpretation. Errors cannot create a fabricated successful return event.
Julia source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
--     @boundscheck checkbounds(iter, i, j)
--     return SCartesianIndex2{K}(i, iter.indices2[j])
-- end
-- /Source
def StaticGetCustomConstructorContract : Prop :=
  ∀ (W E R O Ax : Type) (ops : StaticGetOps (EStateM (Error ⊕ E) W) R O Ax)
    (enabled : Bool) (iter : RuntimeStaticIndices O R) (i j : I64) (initial : W),
    letI := staticModelExceptions
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W) E
    match staticIndicesGet (observeStaticGetConstructor ops) enabled iter i j ([], initial) with
    | .error _ after =>
        after.1 = [] ∨ ∃ endpoint, after.1 = [.inl (iter.parameter, .native i, endpoint)]
    | .ok value after =>
        after.1 = [] ∨ ∃ endpoint,
          after.1 = [.inl (iter.parameter, .native i, endpoint), .inr value]

/-- Only selected constructor calls can write the independent observer log. Range iteration, arbitrary arithmetic/comparison, conversion and custom destructuring all execute with their unrestricted original effects and error channels.
Julia source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def observeStaticIterationConstructor {W E R O C DS : Type}
    (ops : StaticIterationOps (EStateM E W) R O C DS) :
    StaticIterationOps
      (EStateM E (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W)) R O C DS where
  constructors := observeStaticConstructor ops.constructors
  values := {
    multiplyInt := fun o i => liftStaticWorld (ops.values.multiplyInt o i)
    remainderInt := fun o i => liftStaticWorld (ops.values.remainderInt o i)
    equalInt := fun o i => liftStaticWorld (ops.values.equalInt o i)
    notEqualInt := fun o i => liftStaticWorld (ops.values.notEqualInt o i)
    addInt := fun o i => liftStaticWorld (ops.values.addInt o i)
    subtractInt := fun o i => liftStaticWorld (ops.values.subtractInt o i)
    greaterInt := fun o i => liftStaticWorld (ops.values.greaterInt o i)
    divideFromInt := fun i o => liftStaticWorld (ops.values.divideFromInt i o) }
  start := fun range => liftStaticWorld (ops.start range)
  step := fun range state => liftStaticWorld (ops.step range state)
  indexedFirst := fun object i => liftStaticWorld (ops.indexedFirst object i)
  indexedNext := fun object i state => liftStaticWorld (ops.indexedNext object i state)
  lessOtherInt := fun o i => liftStaticWorld (ops.lessOtherInt o i)
  lessOthers := fun left right => liftStaticWorld (ops.lessOthers left right)

/-- For a returned iteration pair, any selected constructor receives exactly K and the unconverted channel/item carried in the returned state, and its actual arbitrary value is retained as the iteration item. Exhaustion cannot have called a constructor; any failing custom call is the only constructor event.
Julia source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def staticIterationConstructorTrace {W E O : Type} (parameter : Value O)
    (result : EStateM.Result E
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W)
      (Option (StaticIndexResult O × StaticIterationState O))) : Prop :=
  match result with
  | .error _ after =>
      after.1 = [] ∨ ∃ i j, after.1 = [.inl (parameter, i, j)]
  | .ok none after => after.1 = []
  | .ok (some (value, state)) after =>
      after.1 = [] ∨
        after.1 = [.inl (parameter, state.state1, state.item2), .inr value]

/-- Both initial and stateful iteration preserve all arbitrary selected constructor returns and never rewrite the state item to its converted native coordinate. The constructor trace relates the real returned result with the returned unconverted state for every custom iterator, state shape, arithmetic operation, error and mutation.
Julia source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:309-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(iter::SCartesianIndices2{K}) where {K}
--     ret = iterate(iter.indices2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- 
-- function iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}
--     if state1 < K
--         item1 = state1 + 1
--         return SCartesianIndex2{K}(item1, item2), (item1, item2, state2)
--     end
--     ret = iterate(iter.indices2, state2)
--     ret === nothing && return nothing
--     item2, state2 = ret
--     return SCartesianIndex2{K}(1, item2), (1, item2, state2)
-- end
-- /Source
def StaticIterationCustomConstructorContract : Prop :=
  ∀ (W E R O C DS : Type)
    (ops : StaticIterationOps (EStateM (Error ⊕ (StaticFieldFault ⊕ E)) W) R O C DS)
    (iter : RuntimeStaticIndices O R) (argument : StaticStateArgument O C) (initial : W),
    letI := staticModelExceptions
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W) (StaticFieldFault ⊕ E)
    letI := staticFieldExceptions
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W) E
    let observed := observeStaticIterationConstructor ops
    staticIterationConstructorTrace iter.parameter (staticIndicesIterate observed iter ([], initial)) ∧
    staticIterationConstructorTrace iter.parameter
      (staticIndicesIterateState observed iter argument ([], initial))

/-- The generated default constructor evaluates every field conversion before new validates returned field types. A wrong-type first conversion does not suppress the second conversion or its effects/errors; a genuine first conversion exception still stops immediately.
Julia source: base/reinterpretarray.jl:275-278; base/essentials.jl:1453-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:275-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct SCartesianIndex2{K}   # can't make <:AbstractCartesianIndex without N, and 2 would be a bit misleading
--     i::Int
--     j::Int
-- end
-- /Source
-- Source: base/essentials.jl:1453-1489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         end
--     end
-- 
--     # Inner constructor: (::Type{T{A,B,...}})(x, y, ...) with convert calls
--     # Build lambda body using Core.Argument references
--     nstmts = ((n - nany) + (n - nany)) + 1
--     body_args = Array{Any,1}(Core.undef, nstmts)
--     new_args = Array{Any,1}(Core.undef, n)
--     i = 1
--     bidx = 1
--     while i !== n + 1
--         ft = fts[i]
--         if ft === Any
--             @inbounds new_args[i] = Core.Argument(i + 1)
--         else
--             # Use an isa check to avoid depending on convert inlining.
--             # This matches the old convert-for-type-decl pattern:
--             #   isa(arg, fieldtype(self, i)) ? arg : convert(fieldtype(self, i), arg)
--             # The isa check is important because user code may define ambiguous
--             # convert methods (e.g. convert(::Any, v::T) = v) that prevent the
--             # optimizer from inlining convert(fieldtype(self, i), arg) when the
--             # field type is Any after specialization.
--             ft_expr = Expr(:call, GlobalRef(Core, :fieldtype), Core.Argument(1), i)
--             ft_ssa = Expr(:ssavalue, bidx)
--             cnvt_ssa = Expr(:ssavalue, bidx + 1)
--             isa_check = Expr(:call, GlobalRef(Core, :isa), Core.Argument(i + 1), ft_ssa)
--             convert_expr = Expr(:call, GlobalRef(Base, :convert), ft_ssa, Core.Argument(i + 1))
--             @inbounds body_args[bidx] = Expr(:(=), ft_ssa, ft_expr)
--             @inbounds body_args[bidx + 1] = Expr(:(=), cnvt_ssa, Expr(:if, isa_check,
--                                                Core.Argument(i + 1), convert_expr))
--             @inbounds new_args[i] = cnvt_ssa
--             bidx = bidx + 2
--         end
--         i = i + 1
--     end
--     body_args[nstmts] = Expr(:return, Expr(:new, Core.Argument(1), new_args...))
--     lambda = Expr(:lambda, argnames,
-- /Source
def StaticGeneratedConversionPrecedence : Prop :=
  ∀ (W E O : Type) (ops : StaticIndexOps (EStateM (Error ⊕ E) W) O)
    (parameter : Value O) (first second : O) (firstTag secondTag : Bool) (initial : W),
    letI := staticModelExceptions W E
    let result := constructStaticIndex ops parameter (.other first firstTag) (.other second secondTag) initial
    match ops.convertInt first initial with
    | .error error after => result = .error error after
    | .ok (.accepted _) _ => True
    | .ok (.rejected _) afterFirst =>
        match ops.convertInt second afterFirst with
        | .error error afterSecond => result = .error error afterSecond
        | .ok _ afterSecond => result = .error (.inl Error.typeError) afterSecond

/-- SIMD index construction preserves every selected K-specific constructor result and exact arguments after native wrapping of the inner coordinate. Generated construction makes no custom call; selected methods may return any runtime value or error.
Julia source: base/reinterpretarray.jl:329-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:329-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}
--     SCartesianIndex2{K}(I1+1, Ilast)
-- end
-- /Source
def StaticSimdConstructorDispatchContract : Prop :=
  ∀ (W E O R : Type) (ops : StaticConstructorOps (EStateM (Error ⊕ E) W) O)
    (iter : RuntimeStaticIndices O R) (last inner : I64) (initial : W),
    letI := staticModelExceptions
      (List (Sum (Value O × Value O × Value O) (StaticIndexResult O)) × W) E
    staticSelectedConstructorTrace
      (ops.selectCustom iter.parameter (.native (inner + one)) (.native last))
      (iter.parameter, .native (inner + one), .native last)
      (staticSimdIndex (observeStaticConstructor ops) iter last inner ([], initial))

/-- Every genuinely selected checkbounds target receives the original iterator and both indices and preserves its actual mutable-world/error outcome; successful outer and failed-bounds returns are ignored. Only actual Bool results can control the default wrapper. Selected axes and tuple-check targets preserve arbitrary results without arity or correctness assumptions.
Julia source: base/reinterpretarray.jl:304-307; base/essentials.jl:389-393; base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:304-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}
--     @boundscheck checkbounds(iter, i, j)
--     return SCartesianIndex2{K}(i, iter.indices2[j])
-- end
-- /Source
-- Source: base/essentials.jl:389-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(A::AbstractArray, I...)
--     @inline
--     checkbounds(Bool, A, I...) || _throw_boundserror_indices(A, I...)
--     nothing
-- end
-- /Source
-- Source: base/abstractarray.jl:682-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- 
-- # Linear indexing is explicitly allowed when there is only one (non-cartesian) index;
-- # indices that do not allow linear indexing (e.g., logical arrays, cartesian indices, etc)
-- # must add specialized methods to implement their restrictions
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- 
-- """
--     checkbounds(A, I...)
-- 
-- Throw an error if the specified indices `I` are not in bounds for the given array `A`.
-- """
-- checkbounds(A::AbstractArray, I...)
-- 
-- """
--     checkbounds_indices(Bool, IA, I)
-- 
-- Return `true` if the "requested" indices in the tuple `I` fall within
-- the bounds of the "permitted" indices specified by the tuple
-- `IA`. This function recursively consumes elements of these tuples,
-- usually in a 1-for-1 fashion,
-- 
--     checkbounds_indices(Bool, (IA1, IA...), (I1, I...)) = checkindex(Bool, IA1, I1) &
--                                                           checkbounds_indices(Bool, IA, I)
-- 
-- Note that [`checkindex`](@ref) is being used to perform the actual
-- bounds-check for a single dimension of the array.
-- 
-- There are two important exceptions to the 1-1 rule: linear indexing and
-- CartesianIndex{N}, both of which may "consume" more than one element
-- of `IA`.
-- 
-- See also [`checkbounds`](@ref).
-- """
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
def StaticBoundsDispatchContract : Prop :=
  ∀ (W E R O Ax : Type) (ops : StaticGetOps (EStateM (Error ⊕ E) W) R O Ax)
    (iter : RuntimeStaticIndices O R) (i j : I64) (initial : W),
    letI := staticModelExceptions W E
    let result := staticIndicesCheckbounds ops iter i j initial
    (ops.selectCheckbounds iter i j = true →
      match ops.customCheckbounds iter i j initial with
      | .error error world => result = .error error world
      | .ok _ world => result = .ok () world) ∧
    (ops.selectCheckboundsBool iter i j = true →
      staticIndicesCheckboundsBool ops iter i j initial = ops.customCheckboundsBool iter i j initial) ∧
    (ops.selectAxes iter = true → staticBoundsAxes ops iter initial = ops.customAxes iter initial) ∧
    (∀ (axes : NativeTuple (StaticBoundsAxis R Ax)) (indices : NativeTuple I64),
      ops.selectTupleIndices axes.values indices.values = true →
      staticBoundsTuple ops axes.values indices.values initial =
        ops.customTupleIndices axes.values indices.values initial) ∧
    (ops.selectCheckbounds iter i j = false →
      ops.selectCheckboundsBool iter i j = true →
      match ops.customCheckboundsBool iter i j initial with
      | .error error world => result = .error error world
      | .ok (.boolean true) world => result = .ok () world
      | .ok (.boolean false) world =>
          if ops.selectThrowBounds iter i j then
            match ops.customThrowBounds iter i j world with
            | .error error after => result = .error error after
            | .ok _ after => result = .ok () after
          else result = .error (.inl (.array (.julia .boundsError))) world
      | .ok _ world => result = .error (.inl .typeError) world) ∧
    (ops.selectCheckboundsBool iter i j = false →
      ops.selectAxes iter = true →
      match ops.customAxes iter initial with
      | .error error world => staticIndicesCheckboundsBool ops iter i j initial = .error error world
      | .ok (.tuple _) _ => True
      | .ok (.other other) world =>
          if ops.selectOtherIndices other [i, j] then
            staticIndicesCheckboundsBool ops iter i j initial = ops.customOtherIndices other [i, j] world
          else staticIndicesCheckboundsBool ops iter i j initial =
            .error (.inl (.array (.julia (.methodError "checkbounds_indices")))) world)

/-- For every native-sized tuple of OneTo axes, default tuple bounds checking is exactly the independent mathematical rectangular membership condition: omitted dimensions have extent one and every extra dimension must be singleton. Original signed stops construct valid OneTo extents by max(0,stop). The result is pure for arbitrary user operations whenever the actually relevant tuple methods are the defaults.
Julia source: base/abstractarray.jl:722-728; base/range.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/range.jl:860-860 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     length(r::OneTo{<:smallints}) = Int(r.stop)
-- /Source
def StaticBoundsNativeAxesContract : Prop :=
  ∀ (W E R O Ax : Type) (ops : StaticGetOps (EStateM (Error ⊕ E) W) R O Ax)
    (stops : NativeTuple I64) (i j : I64) (initial : W),
    letI := staticModelExceptions W E
    let axes : List (StaticBoundsAxis R Ax) := stops.values.map
      (fun stop => .native ⟨JInt.lit .i64 (max 0 stop.val)⟩)
    let firstExtent := (stops.values[0]?.map (fun stop => max 0 stop.val)).getD 1
    let secondExtent := (stops.values[1]?.map (fun stop => max 0 stop.val)).getD 1
    let nativeInside := decide (1 ≤ i.val ∧ i.val ≤ firstExtent ∧
      1 ≤ j.val ∧ j.val ≤ secondExtent)
    let singletonRest := (stops.values.drop 2).all (fun stop => decide (max 0 stop.val = 1))
    ops.selectTupleIndices axes [i, j] = false →
    ops.selectTupleIndices axes.tail [j] = false →
    ops.selectTupleIndices axes.tail.tail [] = false →
    staticBoundsTuple ops axes [i, j] initial = .ok (.boolean (nativeInside && singletonRest)) initial

/-- The trailing-axis all truth table is independent of the recursive implementation. First length/equality errors and false values suppress later work; a missing first predicate still evaluates a second native-length predicate, whose false dominates missing. Wrong native predicate values raise TypeError after the actual selected effects. No callback correctness or purity is assumed.
Julia source: base/abstractarray.jl:728-728; base/anyall.jl:204-220; base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:728-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
-- Source: base/anyall.jl:204-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for ItrT = (Tuple,Any)
--     # define a generic method and a specialized version for `Tuple`,
--     # whose method bodies are identical, while giving better effects to the later
--     @eval function _all(f, itr::$ItrT, ::Colon)
--         $(ItrT === Tuple ? :(@_terminates_locally_meta) : :nothing)
--         anymissing = false
--         for x in itr
--             v = f(x)
--             if ismissing(v)
--                 anymissing = true
--             else
--                 v || return false
--             end
--         end
--         return anymissing ? missing : true
--     end
-- end
-- /Source
-- Source: base/anyall.jl:237-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This is similar to any(f, ::Tuple) defined above.
-- function all(f, itr::Tuple)
--     if itr isa NTuple || length(itr) > 32
--         return _all(f, itr, :)
--     end
--     _all_tuple(f, false, itr...)
-- end
-- 
-- @inline function _all_tuple(f, anymissing::Bool, x, rest...)
--     v = f(x)
--     if ismissing(v)
--         anymissing = true
--     # this syntax allows throwing a TypeError for non-Bool, for consistency with any
--     elseif v
--         nothing
--     else
--         return false
--     end
--     return _all_tuple(f, anymissing, rest...)
-- end
-- @inline _all_tuple(_, anymissing::Bool) = anymissing ? missing : true
-- /Source
def StaticBoundsTrailingContract : Prop :=
  ∀ (W E R O Ax : Type) (ops : StaticGetOps (EStateM (Error ⊕ E) W) R O Ax)
    (first second : Ax) (initial : W),
    letI := staticModelExceptions W E
    let single := staticBoundsTrailingAll ops false [StaticBoundsAxis.custom first] initial
    let pair := staticBoundsTrailingAll ops false
      [StaticBoundsAxis.custom first, .custom second] initial
    match ops.lengthCustom first initial with
    | .error error world => single = .error error world ∧ pair = .error error world
    | .ok (.native length) world =>
        single = .ok (.boolean (decide (length.val = 1))) world ∧
        (length.val ≠ 1 → pair = .ok (.boolean false) world)
    | .ok (.other other _) world =>
        match ops.equalLengthOne other one world with
        | .error error after => single = .error error after ∧ pair = .error error after
        | .ok (.boolean boolean) after =>
            single = .ok (.boolean boolean) after ∧
            (boolean = false → pair = .ok (.boolean false) after)
        | .ok .missing after =>
            single = .ok .missing after ∧
            (match ops.lengthCustom second after with
              | .error error finalWorld => pair = .error error finalWorld
              | .ok (.native length) finalWorld =>
                  pair = .ok (if length.val = 1 then .missing else .boolean false) finalWorld
              | .ok (.other _ _) _ => True)
        | .ok (.other (.native _)) after =>
            single = .error (.inl .typeError) after ∧ pair = .error (.inl .typeError) after
        | .ok (.other (.other value _)) after =>
            match ops.ismissingOther value after with
            | .error error finalWorld => single = .error error finalWorld ∧ pair = .error error finalWorld
            | .ok (.accepted true) finalWorld => single = .ok .missing finalWorld
            | .ok _ finalWorld =>
                single = .error (.inl .typeError) finalWorld ∧ pair = .error (.inl .typeError) finalWorld

/-- An isolated observer records only selected recursive join entry and successful return. Callback code runs in its original mutable world; outer helper dispatch and pure selection metadata are preserved without fabricated events.
Julia source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
def observeStaticMismatchJoin {W E A O : Type}
    (ops : StaticMismatchOps (EStateM E W) A O) :
    StaticMismatchOps
      (EStateM E (List (Sum (A × List A) (Value O)) × W)) A O where
  selectMismatch := ops.selectMismatch
  customMismatch := fun label first others =>
    liftStaticWorld (ops.customMismatch label first others)
  selectJoin := ops.selectJoin
  customJoin := fun first others =>
    observeStaticIO (.inl (first, others)) Sum.inr (ops.customJoin first others)

/-- Full recursive join dispatch makes at most one selected call, on a nonempty suffix of the original arguments. Its returned value occupies exactly that suffix in the lazy capture; its actual error/world is preserved. With no selected call, capture is pure and retains all original handles, or the one-argument default reports MethodError.
Julia source: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- /Source
def StaticJoinDispatchContract : Prop :=
  ∀ (W E A O : Type) (ops : StaticMismatchOps (EStateM (Error ⊕ E) W) A O)
    (first : A) (others : NativeTuple A) (initial : W),
    letI := staticModelExceptions (List (Sum (A × List A) (Value O)) × W) E
    match captureStaticAxesDispatched (observeStaticMismatchJoin ops) first others.values ([], initial) with
    | .error error after =>
        match after.1 with
        | [] => error = .inl (.array (.julia (.methodError "_join_comma_and"))) ∧ after.2 = initial
        | [.inl (selected, rest)] =>
            (∃ leading, first :: others.values = leading ++ selected :: rest) ∧
            ops.customJoin selected rest initial = .error error after.2
        | _ => False
    | .ok capture after =>
        match after.1 with
        | [] => staticJoinedValues capture = (first :: others.values).map Sum.inl ∧ after.2 = initial
        | [.inl (selected, rest), .inr value] =>
            (∃ leading, first :: others.values = leading ++ selected :: rest ∧
              staticJoinedValues capture = leading.map Sum.inl ++ [.inr value]) ∧
            ops.customJoin selected rest initial = .ok value after.2
        | _ => False

/-- A selected outer mismatch helper may return any value, which is ignored while its exact world survives; its errors propagate. The concrete default outer helper cannot return successfully. Its join-call observer distinguishes a selected inner error from successful lazy capture, and requires the resulting DimensionMismatch or missing-method class at the exact post-call world.
Julia source: base/reinterpretarray.jl:291-296; base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027. -/
-- Source: base/reinterpretarray.jl:291-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function eachindex(style::IndexSCartesian2{K}, A::AbstractArray, B::AbstractArray...) where {K}
--     iter = eachindex(style, A)
--     itersBs = map(C->eachindex(style, C), B)
--     all(==(iter), itersBs) || throw_eachindex_mismatch_indices("axes", axes(A), map(axes, B)...)
--     return iter
-- end
-- /Source
-- Source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
def StaticMismatchDispatchContract : Prop :=
  ∀ (W E A O : Type) (ops : StaticMismatchOps (EStateM (Error ⊕ E) W) A O)
    (first : A) (others : NativeTuple A) (initial : W),
    letI := staticModelExceptions W E
    let call := staticMismatchCall ops first others.values initial
    letI := staticModelExceptions (List (Sum (A × List A) (Value O)) × W) E
    let failed := (throwStaticEachMismatch (observeStaticMismatchJoin ops) first others.values :
      EStateM (Error ⊕ E) (List (Sum (A × List A) (Value O)) × W) Unit) ([], initial)
    (if ops.selectMismatch "axes" first others.values then
      match ops.customMismatch "axes" first others.values initial with
      | .error error after => call = .error error after
      | .ok _ after => call = .ok () after
     else match call with | .error _ _ => True | .ok _ _ => False) ∧
    (match failed with
      | .ok _ _ => False
      | .error error after =>
          match after.1 with
          | [] => after.2 = initial ∧
              error = if others.values.isEmpty then
                .inl (.array (.julia (.methodError "_join_comma_and")))
              else .inl (.array (.dimensionMismatch "all inputs to eachindex must have the same axes"))
          | [.inl (selected, rest)] =>
              (∃ leading, first :: others.values = leading ++ selected :: rest) ∧
              ops.customJoin selected rest initial = .error error after.2
          | [.inl (selected, rest), .inr value] =>
              (∃ leading, first :: others.values = leading ++ selected :: rest) ∧
              ops.customJoin selected rest initial = .ok value after.2 ∧
              error = .inl (.array (.dimensionMismatch "all inputs to eachindex must have the same axes"))
          | _ => False)

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- An observation of a user operation, outside the world that operation may
mutate. Before/after snapshots permit independent checking of state threading.
These lists are mathematical traces, not Julia arrays. -/
structure Observation49 (World Event : Type) where
  before : World
  event : Event
  after : World

/-- Observe arbitrary successful or exceptional stateful operations without
assuming a purity, correctness or result-type law. -/
def observe49 {World Event E X : Type} (event : Except E X → Event)
    (action : EStateM E World X) :
    EStateM E (List (Observation49 World Event) × World) X := fun initial =>
  match action initial.2 with
  | .ok value after =>
    .ok value (initial.1 ++ [⟨initial.2, event (.ok value), after⟩], after)
  | .error error after =>
    .error error (initial.1 ++ [⟨initial.2, event (.error error), after⟩], after)

/-- The observable arguments and outcomes of two successive selected calls. -/
inductive Flow49Event (X Fixed Intermediate R E : Type) where
  | first (argument : X) (outcome : Except E Intermediate)
  | second (fixed : Fixed) (argument : Intermediate) (outcome : Except E R)

/-- Successful two-call accounting preserves the actual intermediate value,
the returned result and both state transitions. -/
def SuccessfulFlow49 {X Fixed Intermediate R E World : Type}
    (argument : X) (fixed : Fixed) (initial final : World) (result : R)
    (events : List (Observation49 World (Flow49Event X Fixed Intermediate R E))) : Prop :=
  ∃ (intermediate : Intermediate) (middle : World), events = [
    ⟨initial, .first argument (.ok intermediate), middle⟩,
    ⟨middle, .second fixed intermediate (.ok result), final⟩]

/-- Failure occurs at one observed call, preserves its payload and post-error
world, and prevents any later call. -/
def FailedFlow49 {X Fixed Intermediate R E World : Type}
    (argument : X) (fixed : Fixed) (initial final : World) (error : E)
    (events : List (Observation49 World (Flow49Event X Fixed Intermediate R E))) : Prop :=
  events = [⟨initial, .first argument (.error error), final⟩] ∨
  ∃ (intermediate : Intermediate) (middle : World), events = [
    ⟨initial, .first argument (.ok intermediate), middle⟩,
    ⟨middle, .second fixed intermediate (.error error), final⟩]

/-- Abstract-array eachindex obtains the parent once, then passes that exact
result and the unchanged style to eachindex once. Every user return value,
exception and state mutation is included, including type-changing parents.
Invariant: base/reinterpretarray.jl:365; doc/src/manual/interfaces.md:211-233. -/
def AbstractEachIndexFlow : Prop :=
  ∀ (A Parent Style R E World : Type)
    (ops : EachIndexAbstractOps (EStateM E World) A Parent Style R)
    (style : Style) (a : A) (initial : World),
    let watched : EachIndexAbstractOps
        (EStateM E (List (Observation49 World (Flow49Event A Style Parent R E)) × World))
        A Parent Style R := {
      parent := fun value => observe49 (.first value) (ops.parent value)
      eachindex := fun tag value => observe49 (.second tag value) (ops.eachindex tag value)
    }
    match eachIndexAbstract watched style a ([], initial) with
    | .ok result after => SuccessfulFlow49 a style initial after.2 result after.1
    | .error error after => FailedFlow49 a style initial after.2 error after.1

/-- Every observation of parent(a) is an observation of the original stored
parent, including an allocation/alias handle. No shape or storage restriction
is imposed on the parent carrier. Invariant: base/reinterpretarray.jl:369. -/
def StoredParentObservations : Prop :=
  ∀ (T S A Observation : Type) (observe : A → Observation)
    (a : ReinterpretArray T S A), observe (m369_parent a) = observe a.parent

/-- dataids and has_offset_axes each forward exactly one query to the stored
parent. Their arbitrary values, exceptions and before/after worlds are retained.
This also includes non-Bool custom offset queries because these wrappers do not
consume the result as a conditional. Invariant: base/reinterpretarray.jl:370,401. -/
def ParentMetadataObservations : Prop :=
  ∀ (T S A R E World : Type) (callee : A → EStateM E World R)
    (a : ReinterpretArray T S A) (initial : World),
    let watched := fun value => observe49 (fun outcome => (value, outcome)) (callee value)
    let correct (action :
        EStateM E (List (Observation49 World (A × Except E R)) × World) R) : Prop :=
      match action ([], initial) with
      | .ok result after => after.1 = [⟨initial, (a.parent, .ok result), after.2⟩]
      | .error error after => after.1 = [⟨initial, (a.parent, .error error), after.2⟩]
    correct (m370_dataids watched a) ∧ correct (m401_hasOffset watched a)

/-- Both unaliascopy overloads copy the stored parent once before reinterpreting
the actual copy. The original target type and the statically selected plain or
reshape argument form are preserved, independently of the view's stored flags.
There is no assumption that user copy or reinterpret operations are correct.
Invariant: base/reinterpretarray.jl:371-372. -/
def UnaliasCopyFlow : Prop :=
  ∀ (A Copied R O E World : Type)
    (ops : UnaliasCopyOps (EStateM E World) A Copied R)
    (a : View O A) (initial : World),
    let watched : UnaliasCopyOps
        (EStateM E
          (List (Observation49 World (Flow49Event A (Bool × TypeLayout) Copied R E)) × World))
        A Copied R := {
      copy := fun value => observe49 (.first value) (ops.copy value)
      plain := fun target value => observe49
        (.second (false, target) value) (ops.plain target value)
      reshaped := fun target value => observe49
        (.second (true, target) value) (ops.reshaped target value)
    }
    let correct (reshaped : Bool) (action :
        EStateM E
          (List (Observation49 World (Flow49Event A (Bool × TypeLayout) Copied R E)) × World) R) : Prop :=
      match action ([], initial) with
      | .ok result after =>
        SuccessfulFlow49 a.parent (reshaped, a.target) initial after.2 result after.1
      | .error error after =>
        FailedFlow49 a.parent (reshaped, a.target) initial after.2 error after.1
    correct false (unaliasCopyPlain watched a) ∧
    correct true (unaliasCopyReshaped watched a)

/-- A zero-dimensional view reports exactly zero size components and zero
axes, regardless of its parent metadata or target element layout. The rank
premise is the actual type-level zero-dimensional dispatch invariant.
Documentation: base/reinterpretarray.jl:385,399; doc/src/manual/interfaces.md:211-233. -/
def ZeroDimensionalShape : Prop :=
  ∀ (T S A : Type) (a : ReinterpretArray T S A), a.rank = 0 →
    (m385_sizeZero a).length = 0 ∧ (m399_axesZero a).length = 0

/-- cconvert requests a pointer to the SOURCE element type from the original
stored parent, exactly once. It retains the arbitrary returned object, errors
and state changes; Julia permits cconvert to allocate a different object.
Documentation: base/reinterpretarray.jl:410;
doc/src/manual/calling-c-and-fortran-code.md:268-275. -/
def CconvertParentObservations : Prop :=
  ∀ (T S A R E World : Type)
    (callee : TypeLayout → A → EStateM E World R)
    (a : ReinterpretArray T S A) (initial : World),
    let watched := fun target value => observe49
      (fun outcome => ((target, value), outcome)) (callee target value)
    match m410_cconvert watched a ([], initial) with
    | .ok result after =>
      after.1 = [⟨initial, ((a.source, a.parent), .ok result), after.2⟩]
    | .error error after =>
      after.1 = [⟨initial, ((a.source, a.parent), .error error), after.2⟩]

/-- Independently observed parent conversion and selected custom Ptr call. -/
inductive PointerEvent49 (A Custom Other E : Type) where
  | parent (element : TypeLayout) (array : A) (outcome : Except E (PointerArgument Custom))
  | custom (element : TypeLayout) (value : PointerArgument Custom) (outcome : Except E (PointerConstruction Other))

/-- On actual selection of the known Core constructor, native pointer construction preserves all 64 address bits and
uses the requested target type. A selected custom constructor instead retains
its arbitrary exact result. Expected addresses are mathematical residues or
the input pointer's address; no pointer model appears on the specification side. -/
def SuccessfulPointer49 {A Custom Other O E World : Type}
    (selected : TypeLayout → PointerArgument Custom → Bool)
    (a : View O A) (initial final : World) (result : PointerConstruction Other)
    (events : List (Observation49 World (PointerEvent49 A Custom Other E))) : Prop :=
  (∃ (input : I64) (output : JuliaLean.BootCov.IntConv.Ptr),
    selected a.target (.signed input) = false ∧
    events = [⟨initial, .parent a.source a.parent (.ok (.signed input)), final⟩] ∧
    result = .pointer a.target output ∧
    output.addr.val = input.val % (2 ^ 64)) ∨
  (∃ (input : JInt .u64) (output : JuliaLean.BootCov.IntConv.Ptr),
    selected a.target (.unsigned input) = false ∧
    events = [⟨initial, .parent a.source a.parent (.ok (.unsigned input)), final⟩] ∧
    result = .pointer a.target output ∧ output.addr.val = input.val) ∨
  (∃ (inputType : TypeLayout) (input output : JuliaLean.BootCov.IntConv.Ptr),
    selected a.target (.pointer inputType input) = false ∧
    events = [⟨initial, .parent a.source a.parent (.ok (.pointer inputType input)), final⟩] ∧
    result = .pointer a.target output ∧ output.addr.val = input.addr.val) ∨
  (∃ (input : PointerArgument Custom) (middle : World),
    (selected a.target input = true ∨ ∃ payload, input = .custom payload) ∧
    events = [
      ⟨initial, .parent a.source a.parent (.ok input), middle⟩,
      ⟨middle, .custom a.target input (.ok result), final⟩])

/-- Pointer conversion preserves the exact first failure and the post-error
world, and only calls a selected constructor after a successful parent result, including native input shapes when the target-specific method is selected. -/
def FailedPointer49 {A Custom Other O E World : Type}
    (selected : TypeLayout → PointerArgument Custom → Bool)
    (a : View O A) (initial final : World) (error : E)
    (events : List (Observation49 World (PointerEvent49 A Custom Other E))) : Prop :=
  events = [⟨initial, .parent a.source a.parent (.error error), final⟩] ∨
  ∃ (input : PointerArgument Custom) (middle : World),
    (selected a.target input = true ∨ ∃ payload, input = .custom payload) ∧
    events = [
      ⟨initial, .parent a.source a.parent (.ok input), middle⟩,
      ⟨middle, .custom a.target input (.error error), final⟩]

/-- Complete unsafe_convert observation: correct parent/source request,
native pointer address conservation, target retagging, custom dispatch, return
forwarding, exception precedence, and unchanged state between selected calls.
The parent may return any represented native or custom value; there is no
assumption that it returns a Ptr or that a custom Ptr constructor is correct.
Documentation: base/reinterpretarray.jl:411; base/boot.jl:1203;
base/pointer.jl:3-9; doc/src/manual/interfaces.md:400-407. -/
def UnsafeConvertViewObservations : Prop :=
  ∀ (A Custom Other O E World : Type)
    (ops : UnsafeConvertViewOps (EStateM E World) A Custom Other)
    (a : View O A) (initial : World),
    let watched : UnsafeConvertViewOps
        (EStateM E
          (List (Observation49 World (PointerEvent49 A Custom Other E)) × World))
        A Custom Other := {
      parentUnsafe := fun source value => observe49
        (.parent source value) (ops.parentUnsafe source value)
      selectCustom := ops.selectCustom
      customConstruct := fun target value => observe49
        (.custom target value) (ops.customConstruct target value)
    }
    match unsafeConvertView watched a ([], initial) with
    | .ok result after => SuccessfulPointer49 ops.selectCustom a initial after.2 result after.1
    | .error error after => FailedPointer49 ops.selectCustom a initial after.2 error after.1


end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Argument and outcome observations for type-level element size. The trace
is held outside the arbitrary callees' mutable world. -/
inductive ElementSizeEvent (Parent O E : Type) where
  | size (typeObject : TypeLayout) (outcome : Except E (Value O))
  | equal (left right : Value O)
      (outcome : Except E (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool (Value O)))
  | parent (typeObject : Parent) (outcome : Except E (Value O))
  | unexpected (operation : String)

/-- Observe every selected operation, including operations that the source
method must never invoke. No result, success or purity law is imposed. -/
def observeElementSizeOps {Parent O E World : Type}
    (ops : DynamicElementSizeOps (EStateM E World) Parent O) :
    DynamicElementSizeOps
      (EStateM E (List (Observation49 World (ElementSizeEvent Parent O E)) × World))
      Parent O where
  types := {
    isBits := fun t => observe49 (fun _ => .unexpected "isbitstype") (ops.types.isBits t)
    bitPadding := fun t => observe49 (fun _ => .unexpected "has_bit_padding") (ops.types.bitPadding t)
    singleton := fun t => observe49 (fun _ => .unexpected "issingletontype") (ops.types.singleton t)
    alignedSize := fun t => observe49 (.size t) (ops.types.alignedSize t)
    alignedOther := fun v => observe49 (fun _ => .unexpected "aligned_sizeof(non-Type)") (ops.types.alignedOther v)
    subpadding := fun s t => observe49 (fun _ => .unexpected "array_subpadding") (ops.types.subpadding s t)
  }
  scalars := {
    equal := fun x y => observe49 (.equal x y) (ops.scalars.equal x y)
    notEqual := fun x y => observe49 (fun _ => .unexpected "!=") (ops.scalars.notEqual x y)
    greater := fun x y => observe49 (fun _ => .unexpected ">") (ops.scalars.greater x y)
    less := fun x y => observe49 (fun _ => .unexpected "<") (ops.scalars.less x y)
    add := fun x y => observe49 (fun _ => .unexpected "+") (ops.scalars.add x y)
    subtract := fun x y => observe49 (fun _ => .unexpected "-") (ops.scalars.subtract x y)
    multiply := fun x y => observe49 (fun _ => .unexpected "*") (ops.scalars.multiply x y)
    remainder := fun x y => observe49 (fun _ => .unexpected "rem") (ops.scalars.remainder x y)
    divide := fun x y => observe49 (fun _ => .unexpected "div") (ops.scalars.divide x y)
  }
  elsize := fun p => observe49 (.parent p) (ops.elsize p)

/-- A source equality either compares native mathematical Int values without
dispatch, or observes one selected comparison on the actual two non-native
operand values. This is a trace specification, not an invocation of scalarEqual. -/
def ElementComparisonTrace {Parent O E World : Type}
    (left right : Value O) (before after : World) (condition : Bool)
    (events : List (Observation49 World (ElementSizeEvent Parent O E))) : Prop :=
  match left, right with
  | .native x, .native y =>
      events = [] ∧ after = before ∧ condition = decide (x.val = y.val)
  | _, _ => events = [⟨before, .equal left right (.ok (.accepted condition)), after⟩]

/-- The actual selected operation's returned value or exception determines the
wrapper outcome, with no subsequent state changes. -/
def ElementSizeOutcome {O E World : Type}
    (outcome : Except E (Value O)) (world : World)
    (result : EStateM.Result E World (Value O)) : Prop :=
  match outcome with
  | .ok value => result = .ok value world
  | .error error => result = .error error world

/-- A complete observable protocol: two ordered type queries, the actual
equality (including rejected non-Bool values), then exactly one parent-type
query or a fresh target-type query. Earlier errors prevent all later effects.
The relation checks intermediate values and before/after worlds without calling
the model or assuming any selected method is correct. -/
def ElementSizeTraceContract {Parent O UserError World : Type}
    (target source : TypeLayout) (parentType : Parent) (initial : World)
    (result : EStateM.Result (Error ⊕ UserError) World (Value O))
    (events : List (Observation49 World (ElementSizeEvent Parent O (Error ⊕ UserError)))) : Prop :=
  (∃ error final,
    events = [⟨initial, .size target (.error error), final⟩] ∧
    result = .error error final) ∨
  (∃ first firstWorld error final,
    events = [⟨initial, .size target (.ok first), firstWorld⟩,
      ⟨firstWorld, .size source (.error error), final⟩] ∧
    result = .error error final) ∨
  (∃ first second firstWorld secondWorld rest,
    events = [⟨initial, .size target (.ok first), firstWorld⟩,
      ⟨firstWorld, .size source (.ok second), secondWorld⟩] ++ rest ∧
    ((∃ condition comparisonWorld comparisonEvents final outcome,
      ElementComparisonTrace first second secondWorld comparisonWorld condition comparisonEvents ∧
      rest = comparisonEvents ++ [⟨comparisonWorld,
        (if condition then .parent parentType outcome else .size target outcome), final⟩] ∧
      ElementSizeOutcome outcome final result) ∨
     ((match first, second with | .native _, .native _ => False | _, _ => True) ∧
       ((∃ error final,
         rest = [⟨secondWorld, .equal first second (.error error), final⟩] ∧
         result = .error error final) ∨
        (∃ value final,
         rest = [⟨secondWorld, .equal first second (.ok (.rejected value)), final⟩] ∧
         result = .error (.inl .typeError) final)))))

/-- Type-level elsize preserves repeated type-query dispatch, parent TYPE
identity, non-Bool failures, selected return values and every state transition.
In particular, an unequal comparison does not reuse the first target-size
result. This covers all native/custom scalar results and arbitrary user errors.
Invariant: base/reinterpretarray.jl:403-409. -/
def DynamicElementSizeProtocol : Prop :=
  ∀ (Parent O UserError World : Type)
    (ops : DynamicElementSizeOps (EStateM (Error ⊕ UserError) World) Parent O)
    (target source : TypeLayout) (parentType : Parent) (initial : World),
    letI := modelExceptions
      (List (Observation49 World (ElementSizeEvent Parent O (Error ⊕ UserError))) × World)
      UserError
    match elementSizeOfType (observeElementSizeOps ops) target source parentType ([], initial) with
    | .ok value after =>
        ElementSizeTraceContract target source parentType initial (.ok value after.2) after.1
    | .error error after =>
        ElementSizeTraceContract target source parentType initial (.error error after.2) after.1

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- ReshapedArray and fast SubArray wrappers use their actual parent field and
make one selected call. Arbitrary metadata, return types, exceptions and world
changes are included. An independent trace checks the exact argument and result
without requiring a purity or correctness premise.
Invariant: base/reinterpretarray.jl:425-426; base/reshapedarray.jl:258;
base/subarray.jl:86. -/
def WrapperPointerProtocol : Prop :=
  ∀ (A Metadata R E World : Type) (callee : A → EStateM E World R)
    (wrapper : StoredParent A Metadata) (initial : World),
    let watched : ParentPointerOps
        (EStateM E (List (Observation49 World (A × Except E R)) × World)) A R :=
      ⟨fun value => observe49 (fun outcome => (value, outcome)) (callee value)⟩
    let correct (action :
        EStateM E (List (Observation49 World (A × Except E R)) × World) R) : Prop :=
      match action ([], initial) with
      | .ok value after =>
          after.1 = [⟨initial, (wrapper.parent, .ok value), after.2⟩]
      | .error error after =>
          after.1 = [⟨initial, (wrapper.parent, .error error), after.2⟩]
    correct (checkPointerReshaped watched wrapper) ∧
    correct (checkPointerSubarray watched wrapper)

/-- Static assignment queries forward the exact parent and outer coordinate,
independent of the static parameter and inner coordinate. The query's arbitrary
return value, error and state transition remain unchanged; even a non-Bool result
is retained because this wrapper does not consume it as a condition.
Invariant: base/reinterpretarray.jl:433. -/
def StaticAssignmentProtocol : Prop :=
  ∀ (A R O K E World : Type) (callee : A → I64 → EStateM E World R)
    (view : View O A) (index : RuntimeStaticIndex K) (initial : World),
    let watched : ParentAssignedOps
        (EStateM E (List (Observation49 World ((A × I64) × Except E R)) × World)) A R :=
      ⟨fun value coordinate => observe49
        (fun outcome => ((value, coordinate), outcome)) (callee value coordinate)⟩
    match isAssignedStatic watched view index ([], initial) with
    | .ok value after =>
        after.1 = [⟨initial, ((view.parent, index.coordinates.j), .ok value), after.2⟩]
    | .error error after =>
        after.1 = [⟨initial, ((view.parent, index.coordinates.j), .error error), after.2⟩]

/-- The internal fallback cannot further reject a successful Boolean bounds
guard in its caller, for any accepted heterogeneous vararg tuple and either
pointer-indexability flag. This is the helper's role in the enclosing assignment
predicate, without claiming that the fallback checks actual initialized storage.
Invariant: base/reinterpretarray.jl:432-434. -/
def AssignmentFallbackGuard : Prop :=
  ∀ (A O I : Type) (view : View O A) (indices : NativeTuple I)
    (bounds pointer : Bool),
    (bounds && (pointer || isAssignedFallback view indices)) = bounds

/-- The error display first formats the original source and target Type objects
with the exact surrounding literals, then prints that actual result to the
original IO object. A failure at either selected call is propagated with its
state, and a formatting failure prevents printing. The observation harness
quantifies over every string and print implementation, with arbitrary results.
Documentation: base/reinterpretarray.jl:736-743. -/
def PaddingDisplayProtocol : Prop :=
  ∀ (IO Ty Text R E World : Type)
    (ops : PaddingDisplayOps (EStateM E World) IO Ty Text R)
    (io : IO) (padding : PaddingException Ty) (initial : World),
    let format := ("Padding of type ", padding.source,
      " is not compatible with type ", padding.target, ".")
    let watched : PaddingDisplayOps
        (EStateM E (List (Observation49 World
          (Flow49Event (String × Ty × String × Ty × String) IO Text R E)) × World))
        IO Ty Text R := {
      string := fun leading source middle target trailing => observe49
        (.first (leading, source, middle, target, trailing))
        (ops.string leading source middle target trailing)
      print := fun output message => observe49 (.second output message)
        (ops.print output message)
    }
    match showPaddingError watched io padding ([], initial) with
    | .ok result after =>
        SuccessfulFlow49 format io initial after.2 result after.1
    | .error error after =>
        FailedFlow49 format io initial after.2 error after.1

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- The primitive width uses uint32_t arithmetic in the C helper. This
mathematical residue tests flag extraction, multiplication, subtraction and
wrapping without calling any bit-arithmetic model on the expected side.
Invariant: src/julia.h:1693-1697; needed by base/reinterpretarray.jl:470. -/
def PrimitiveWidthArithmetic81 : Prop :=
  ∀ layout : JuliaLean.base.runtime_internals.DataTypeLayout,
    (declaredBitCount layout).val =
      (8 * layout.size.val - ((layout.flags.val / 256) % 128)) % (2 ^ 32)

/-- A type object denotes itself; an ordinary object denotes its actual
runtime DataType. This relation intentionally does not unwrap UnionAll. -/
def ResolvedDataType81 {m : Type → Type} {MW V D N Mod P Sym O : Type}
    (ops : ScalarPrimitiveOps m MW V D N Mod P Sym O) (value : V) (datatype : D) : Prop :=
  (ops.runtime.isAType value = true ∧ ops.runtime.asDatatype value = some datatype) ∨
  (ops.runtime.isAType value = false ∧ ops.runtime.typeof value = datatype)

/-- Mathematical meaning of a primitive width, independent of the Core
builtin model and of the native bitfield operations it invokes. -/
def PrimitiveWidthMeaning81 {m : Type → Type} {MW V D N Mod P Sym O : Type}
    (ops : ScalarPrimitiveOps m MW V D N Mod P Sym O) (value : V) (width : Int) : Prop :=
  ∃ datatype : D, ResolvedDataType81 ops value datatype ∧
    (ops.runtime.dataFlags datatype).val / 128 % 2 = 1 ∧
    width = (8 * (ops.primitiveLayout datatype).size.val -
      ((ops.primitiveLayout datatype).flags.val / 256 % 128)) % (2 ^ 32)

/-- Core.bitsizeof succeeds exactly on a primitive DataType or a primitive
instance and reports the independently specified declared width. Every other
value raises ErrorException. This includes UnionAll type objects and preserves
the distinction from the generic isprimitivetype query's unwrapping behavior.
Documentation: base/essentials.jl:844-878; src/builtins.c:680-692. -/
def CoreBitSizeContract81 : Prop :=
  ∀ (m : Type → Type) (MW V D N Mod P Sym O : Type)
    (ops : ScalarPrimitiveOps m MW V D N Mod P Sym O) (value : V),
    (∀ result : I64,
      coreBitSizeOf ops value = .ok result ↔ PrimitiveWidthMeaning81 ops value result.val) ∧
    (coreBitSizeOf ops value = .error .errorException ↔
      ¬ ∃ width : Int, PrimitiveWidthMeaning81 ops value width) ∧
    coreBitSizeOf ops value ≠ .error .typeError

/-- Independent predicate interpretation for the selected installed default.
The flag bit is specified arithmetically; no native query model appears here. -/
def DefaultPrimitiveMeaning81 {m : Type → Type} {MW V D N Mod P Sym O : Type}
    (ops : ScalarPrimitiveOps m MW V D N Mod P Sym O) (value : V) : Bool :=
  match ops.runtime.asDatatype (ops.runtime.unwrap value) with
  | none => false
  | some datatype => (ops.runtime.dataFlags datatype).val / 128 % 2 == 1

/-- A callback observation is kept outside the callback's mutable world. -/
structure PrimitiveObservation81 (V O E World : Type) where
  before : World
  argument : V
  outcome : Except E (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool O)
  after : World

/-- Record an arbitrary selected query, preserving its raw Bool/non-Bool
return classification, user exception, and post-call world. -/
def observePrimitive81 {V O E World : Type}
    (callee : V → EStateM E World
      (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool O))
    (value : V) : EStateM (ScalarPredicateError ⊕ E)
      (List (PrimitiveObservation81 V O E World) × World)
      (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool O) := fun initial =>
  match callee value initial.2 with
  | .ok result after => .ok result
      (initial.1 ++ [⟨initial.2, value, .ok result, after⟩], after)
  | .error error after => .error (.inr error)
      (initial.1 ++ [⟨initial.2, value, .error error, after⟩], after)

/-- Concrete source errors remain distinct from arbitrary user errors. -/
@[instance_reducible] def scalarExceptions81 (World E : Type) :
    MonadExceptOf ScalarPredicateError (EStateM (ScalarPredicateError ⊕ E) World) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value after => .ok value after
    | .error (.inl error) after => handler error after
    | .error (.inr error) after => .error (.inr error) after

/-- One query either observes the installed metadata with no user call, or
produces one externally recorded actual selected-method observation. -/
def PrimitiveQueryEvidence81 {m : Type → Type} {MW V D N Mod P Sym O E World : Type}
    (ops : ScalarPrimitiveOps m MW V D N Mod P Sym O)
    (argument : PrimitiveQueryArgument V)
    (outcome : Except E (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool O))
    (initial final : World) (events : List (PrimitiveObservation81 V O E World)) : Prop :=
  match argument with
  | .default value =>
    outcome = .ok (.accepted (DefaultPrimitiveMeaning81 ops value)) ∧
      events = [] ∧ final = initial
  | .selected value => events = [⟨initial, value, outcome, final⟩]

/-- Every two-query path records S before T and threads the observed world.
The second outcome can be a Bool, non-Bool value, or arbitrary exception. -/
def PrimitivePairEvidence81 {m : Type → Type} {MW V D N Mod P Sym O E World : Type}
    (ops : ScalarPrimitiveOps m MW V D N Mod P Sym O)
    (target source : PrimitiveQueryArgument V)
    (second : Except E (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion Bool O))
    (initial final : World) (events : List (PrimitiveObservation81 V O E World)) : Prop :=
  ∃ (middle : World) (sourceEvents targetEvents : List (PrimitiveObservation81 V O E World)),
    PrimitiveQueryEvidence81 ops source (.ok (.accepted true)) initial middle sourceEvents ∧
    PrimitiveQueryEvidence81 ops target second middle final targetEvents ∧
    events = sourceEvents ++ targetEvents

/-- Independent complete-domain accounting for the scalar applicability
predicate. False and non-Bool outcomes stop at the actual query; errors retain
the exact post-call world and payload. When both queries are true, acceptance
is exactly equality of the mathematically declared primitive widths. Default
and selected query cases are both quantified, including primitive instances
accepted by custom predicates and type objects whose Core builtin rejects them.
Invariant: base/reinterpretarray.jl:469-471; base/essentials.jl:844-878. -/
def ScalarApplicabilityFlow81 : Prop :=
  ∀ (MW V D N Mod P Sym O E World : Type)
    (ops : ScalarPrimitiveOps (EStateM E World) MW V D N Mod P Sym O)
    (target source : PrimitiveQueryArgument V) (initial : World),
    letI := scalarExceptions81 (List (PrimitiveObservation81 V O E World) × World) E
    let watched : ScalarPrimitiveOps
        (EStateM (ScalarPredicateError ⊕ E)
          (List (PrimitiveObservation81 V O E World) × World))
        MW V D N Mod P Sym O := {
      runtime := ops.runtime
      primitiveLayout := ops.primitiveLayout
      selectedPrimitive := observePrimitive81 ops.selectedPrimitive
    }
    match scalarReinterpretApplicable watched target source ([], initial) with
    | .ok result after =>
      (result = false ∧ PrimitiveQueryEvidence81 ops source
        (.ok (.accepted false)) initial after.2 after.1) ∨
      (result = false ∧ PrimitivePairEvidence81 ops target source
        (.ok (.accepted false)) initial after.2 after.1) ∨
      (PrimitivePairEvidence81 ops target source (.ok (.accepted true))
        initial after.2 after.1 ∧
        ∃ (targetWidth sourceWidth : Int),
          PrimitiveWidthMeaning81 ops target.value targetWidth ∧
          PrimitiveWidthMeaning81 ops source.value sourceWidth ∧
          result = decide (targetWidth = sourceWidth))
    | .error (.inr error) after =>
      PrimitiveQueryEvidence81 ops source (.error error) initial after.2 after.1 ∨
      PrimitivePairEvidence81 ops target source (.error error) initial after.2 after.1
    | .error (.inl .typeError) after =>
      (∃ value : O, PrimitiveQueryEvidence81 ops source (.ok (.rejected value))
        initial after.2 after.1) ∨
      (∃ value : O, PrimitivePairEvidence81 ops target source (.ok (.rejected value))
        initial after.2 after.1)
    | .error (.inl .errorException) after =>
      PrimitivePairEvidence81 ops target source (.ok (.accepted true))
        initial after.2 after.1 ∧
        ((¬ ∃ width : Int, PrimitiveWidthMeaning81 ops target.value width) ∨
          ((∃ width : Int, PrimitiveWidthMeaning81 ops target.value width) ∧
            ¬ ∃ width : Int, PrimitiveWidthMeaning81 ops source.value width))

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean.base.reinterpretarray.Models2Group12

/-- Concrete layout packing depends only on the lowest flags bit. No user
operation is needed, and every initial world is unchanged. The mathematical
remainder is independent of the runtime's bitfield implementation.
Invariant: base/reinterpretarray.jl:827-829 and base/runtime_internals.jl:702. -/
def PackedLayoutLowBit : Prop :=
  ∀ (World V D N Mod P Sym Input Other : Type)
    (ops : IsPackedOps World V D N Mod P Sym Input Other)
    (layout : JuliaLean.base.runtime_internals.DataTypeLayout) (initial : World),
    isPackedDispatched ops (.layout layout) initial =
      some (.ok (.boolean (layout.flags.val % 2 == 0), initial))

/-- DataType packing observes the layout at its actual stored pointer. Null
layout produces the native UndefRefError before loading; successful loads use
the low flags bit, while a loader failure or divergence propagates unchanged.
These are observations of arbitrary runtime operations, not assumed laws for
those operations. All exceptional post-operation worlds are retained.
Invariant: base/reinterpretarray.jl:827-829;
base/runtime_internals.jl:642-646,701-702. -/
def PackedDatatypeObservations : Prop :=
  ∀ (World V D N Mod P Sym Input Other : Type)
    (ops : IsPackedOps World V D N Mod P Sym Input Other)
    (datatype : D) (initial : World),
    let pointer := ops.runtime.layout datatype
    let result := isPackedDispatched ops (.datatype datatype) initial
    (ops.runtime.isNull pointer = true →
      result = some (.error
        (.foreignError "UndefRefError" "null datatype layout", initial))) ∧
    (ops.runtime.isNull pointer = false →
      (∀ (layout : JuliaLean.base.runtime_internals.DataTypeLayout) (after : World),
        ops.runtime.loadLayout pointer initial = some (.ok (layout, after)) →
        result = some (.ok (.boolean (layout.flags.val % 2 == 0), after))) ∧
      (∀ (error : JuliaLean.base.io.Error) (after : World),
        ops.runtime.loadLayout pointer initial = some (.error (error, after)) →
        result = some (.error (error, after))) ∧
      (ops.runtime.loadLayout pointer initial = none → result = none))

/-- An external mathematical trace retains call arguments, outcomes, and both
world snapshots. The user operations cannot rewrite this trace. -/
structure PackedObservation98 (World Event : Type) where
  before : World
  event : Event
  after : World

/-- The two dispatch positions remain distinguished even if their argument or
result carriers happen to coincide. -/
inductive PackedEvent98 (Input Other : Type) where
  | haspadding (argument : Input)
      (outcome : Except JuliaLean.base.io.Error (PackedValue Other))
  | negate (argument : Other)
      (outcome : Except JuliaLean.base.io.Error (PackedValue Other))

/-- Record each finite callback result and its post-operation world while
preserving an arbitrary callback's exception and divergence behavior. -/
def observePacked98 {World Event A : Type}
    (event : Except JuliaLean.base.io.Error A → Event)
    (action : JuliaLean.base.io.M World A) :
    JuliaLean.base.io.M (List (PackedObservation98 World Event) × World) A := fun initial =>
  match action initial.2 with
  | none => none
  | some (.ok (value, after)) =>
    some (.ok (value,
      (initial.1 ++ [⟨initial.2, event (.ok value), after⟩], after)))
  | some (.error (error, after)) =>
    some (.error (error,
      (initial.1 ++ [⟨initial.2, event (.error error), after⟩], after)))

/-- A successful custom path either complements the observed native Bool with
one call or forwards the exact result of ! on the observed non-Bool value.
Both the intermediate value and intermediate world come from observations. -/
def SuccessfulPacked98 {World Input Other : Type}
    (argument : Input) (initial final : World) (result : PackedValue Other)
    (events : List (PackedObservation98 World (PackedEvent98 Input Other))) : Prop :=
  (∃ (padding : Bool),
    events = [⟨initial, .haspadding argument (.ok (.boolean padding)), final⟩] ∧
    ((padding = true ∧ result = .boolean false) ∨
      (padding = false ∧ result = .boolean true))) ∨
  (∃ (intermediate : Other) (middle : World), events = [
    ⟨initial, .haspadding argument (.ok (.other intermediate)), middle⟩,
    ⟨middle, .negate intermediate (.ok result), final⟩])

/-- The first failing callback determines the exception and final world, and
prevents every later call. No error kind or successful return type is assumed. -/
def FailedPacked98 {World Input Other : Type}
    (argument : Input) (initial final : World) (error : JuliaLean.base.io.Error)
    (events : List (PackedObservation98 World (PackedEvent98 Input Other))) : Prop :=
  events = [⟨initial, .haspadding argument (.error error), final⟩] ∨
  ∃ (intermediate : Other) (middle : World), events = [
    ⟨initial, .haspadding argument (.ok (.other intermediate)), middle⟩,
    ⟨middle, .negate intermediate (.error error), final⟩]

/-- For another selected method, datatype_haspadding is observed exactly once and !
is called only for its actual non-Bool result. All user result values, errors,
effects and divergence are quantified without correctness assumptions. There
is no final Bool restriction: custom negation can return any PackedValue.
Invariant: base/reinterpretarray.jl:827-829. -/
def PackedCustomFlow : Prop :=
  ∀ (World V D N Mod P Sym Input Other : Type)
    (runtime : JuliaLean.base.runtime_internals.TypeOps
      (List (PackedObservation98 World (PackedEvent98 Input Other)) × World)
      V D N Mod P Sym)
    (haspadding : Input → JuliaLean.base.io.M World (PackedValue Other))
    (negate : Other → JuliaLean.base.io.M World (PackedValue Other))
    (argument : Input) (initial : World),
    let watched : IsPackedOps
        (List (PackedObservation98 World (PackedEvent98 Input Other)) × World)
        V D N Mod P Sym Input Other := {
      runtime := runtime
      haspadding := fun value => observePacked98 (.haspadding value) (haspadding value)
      negate := fun value => observePacked98 (.negate value) (negate value)
    }
    match isPackedDispatched watched (.selected argument) ([], initial) with
    | some (.ok (result, after)) =>
      SuccessfulPacked98 argument initial after.2 result after.1
    | some (.error (error, after)) =>
      FailedPacked98 argument initial after.2 error after.1
    | none => haspadding argument initial = none ∨
      ∃ (intermediate : Other) (middle : World),
        haspadding argument initial = some (.ok (.other intermediate, middle)) ∧
        negate intermediate middle = none

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean.base.reinterpretarray.Models2Group12

inductive StructPaddingEvent (W UserError Ty Mask R : Type) where
  | bytesCall (type : Ty) (world : W)
  | bytesReturn (result : EStateM.Result UserError W Mask)
  | equalCall (output input : Mask) (world : W)
  | equalReturn (result : EStateM.Result UserError W R)

def observeStructPadding {W UserError X Event : Type}
    (before : W → Event) (after : EStateM.Result UserError W X → Event)
    (action : EStateM UserError W X) : EStateM UserError (W × List Event) X :=
  fun (world, events) =>
    let result := action world
    let events := events ++ [before world, after result]
    match result with
    | .ok value final => .ok value (final, events)
    | .error error final => .error error (final, events)

def tracedStructSubpaddingOps {W UserError Ty Mask R : Type}
    (ops : StructSubpaddingOps (EStateM UserError W) Ty Mask R) :
    StructSubpaddingOps
      (EStateM UserError (W × List (StructPaddingEvent W UserError Ty Mask R))) Ty Mask R where
  nonPadding := fun type => observeStructPadding (.bytesCall type) .bytesReturn
    (ops.nonPadding type)
  equal := fun output input => observeStructPadding (.equalCall output input) .equalReturn
    (ops.equal output input)

def structPaddingEvents {E W X Event : Type} :
    EStateM.Result E (W × List Event) X → List Event
  | .ok _ (_, events) => events
  | .error _ (_, events) => events

def eraseStructPaddingEvents {E W X Event : Type} :
    EStateM.Result E (W × List Event) X → EStateM.Result E W X
  | .ok value (world, _) => .ok value world
  | .error error (world, _) => .error error world

/-- The comparison retains output/input order, complete returned operands and callback
state continuity. First or second observation failure prevents comparison; otherwise
its arbitrary return or exception is preserved without a Bool assertion. All selected
methods and user exception payloads are quantified without correctness laws.
Julia source: base/reinterpretarray.jl:815-817. -/
def StructSubpaddingObservations : Prop :=
  ∀ (W UserError Ty Mask R : Type)
    (ops : StructSubpaddingOps (EStateM UserError W) Ty Mask R)
    (output input : Ty) (initial : W),
    let result := structSubpadding (tracedStructSubpaddingOps ops) output input (initial, [])
    let events := structPaddingEvents result
    (∃ error final,
      events = [.bytesCall output initial, .bytesReturn (.error error final)] ∧
      eraseStructPaddingEvents result = .error error final) ∨
    (∃ outputMask middle error final,
      events = [.bytesCall output initial, .bytesReturn (.ok outputMask middle),
        .bytesCall input middle, .bytesReturn (.error error final)] ∧
      eraseStructPaddingEvents result = .error error final) ∨
    (∃ outputMask firstWorld inputMask secondWorld terminal,
      events = [.bytesCall output initial, .bytesReturn (.ok outputMask firstWorld),
        .bytesCall input firstWorld, .bytesReturn (.ok inputMask secondWorld),
        .equalCall outputMask inputMask secondWorld, .equalReturn terminal] ∧
      eraseStructPaddingEvents result = terminal)

@[instance_reducible] def paddingModelExceptions (W UserError : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ UserError) W) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value final => .ok value final
    | .error (.inl error) final => handler error final
    | .error (.inr error) final => .error (.inr error) final

inductive PackedSizeCall where
  | query | negate | sizeof | mask | count
  deriving Repr, DecidableEq

structure PackedSizeTrace (W UserError Ty O Mask R : Type) where
  calls : List PackedSizeCall := []
  queryArguments : List Ty := []
  queries : List (PackedValue O × W) := []
  negateArguments : List O := []
  negations : List (PackedValue O × W) := []
  sizeArguments : List Ty := []
  maskArguments : List Ty := []
  masks : List (Mask × W) := []
  countArguments : List Mask := []
  terminals : List (EStateM.Result UserError W R) := []

def observePackedSize {W UserError X Log : Type}
    (before : Log → Log) (after : EStateM.Result UserError W X → Log → Log)
    (action : EStateM UserError W X) : EStateM (Error ⊕ UserError) (W × Log) X :=
  fun (world, log) =>
    let result := action world
    let log := after result (before log)
    match result with
    | .ok value final => .ok value (final, log)
    | .error error final => .error (.inr error) (final, log)

def tracedPackedSizeOps {W UserError Ty O Mask R : Type}
    (ops : PackedSizeOps (EStateM UserError W) Ty O Mask R) :
    PackedSizeOps
      (EStateM (Error ⊕ UserError) (W × PackedSizeTrace W UserError Ty O Mask R)) Ty O Mask R where
  hasPadding := fun type => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.query]
      queryArguments := log.queryArguments ++ [type] })
    (fun result log => match result with
      | .ok value final => { log with queries := log.queries ++ [(value, final)] }
      | .error _ _ => log) (ops.hasPadding type)
  negate := fun value => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.negate]
      negateArguments := log.negateArguments ++ [value] })
    (fun result log => match result with
      | .ok value final => { log with negations := log.negations ++ [(value, final)] }
      | .error _ _ => log) (ops.negate value)
  sizeOf := fun type => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.sizeof]
      sizeArguments := log.sizeArguments ++ [type] })
    (fun result log => { log with terminals := log.terminals ++ [result] }) (ops.sizeOf type)
  nonPadding := fun type => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.mask]
      maskArguments := log.maskArguments ++ [type] })
    (fun result log => match result with
      | .ok value final => { log with masks := log.masks ++ [(value, final)] }
      | .error _ _ => log) (ops.nonPadding type)
  count := fun mask => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.count]
      countArguments := log.countArguments ++ [mask] })
    (fun result log => { log with terminals := log.terminals ++ [result] }) (ops.count mask)

def packedSizeTrace {E W Log X : Type} : EStateM.Result E (W × Log) X → Log
  | .ok _ (_, log) => log
  | .error _ (_, log) => log

def erasePackedSizeTrace {E W Log X : Type} :
    EStateM.Result E (W × Log) X → EStateM.Result E W X
  | .ok value (world, _) => .ok value world
  | .error error (world, _) => .error error world

def embedPackedTerminal {W UserError X : Type} :
    EStateM.Result UserError W X → EStateM.Result (Error ⊕ UserError) W X
  | .ok value world => .ok value world
  | .error error world => .error (.inr error) world

def packedSizePhase : PackedSizeCall → Nat
  | .query => 0
  | .negate => 1
  | .sizeof | .mask => 2
  | .count => 3

/-- The condition is observed before either exclusive size branch. Native Boolean
complement selects the correct branch without custom negation; non-Bool values use
their selected ! method. Both size branches preserve their original type argument,
count consumes the actual mask, and terminal value/error/state is unchanged. A wrong
negation return becomes TypeError before either size branch.
Julia source: base/reinterpretarray.jl:819-825. -/
def PackedSizeProtocol : Prop :=
  ∀ (W UserError Ty O Mask R : Type)
    (ops : PackedSizeOps (EStateM UserError W) Ty O Mask R) (type : Ty) (initial : W),
    letI := paddingModelExceptions (W × PackedSizeTrace W UserError Ty O Mask R) UserError
    let result := packedSize (tracedPackedSizeOps ops) type (initial, {})
    let log := packedSizeTrace result
    log.queryArguments = [type] ∧ log.calls.count .query = 1 ∧
    log.calls.count .negate ≤ 1 ∧ log.calls.count .sizeof + log.calls.count .mask ≤ 1 ∧
    log.calls.count .count ≤ log.calls.count .mask ∧
    log.calls.Pairwise (fun before after => packedSizePhase before ≤ packedSizePhase after) ∧
    (∀ arg ∈ log.sizeArguments, arg = type) ∧
    (∀ arg ∈ log.maskArguments, arg = type) ∧
    (∀ world, log.queries = [(.boolean false, world)] →
      log.calls = [.query, .sizeof] ∧ log.sizeArguments = [type] ∧ log.negateArguments = []) ∧
    (∀ world, log.queries = [(.boolean true, world)] →
      log.maskArguments = [type] ∧ log.sizeArguments = [] ∧ log.negateArguments = []) ∧
    (∀ value world, log.queries = [(.other value, world)] → log.negateArguments = [value]) ∧
    (∀ world, log.negations = [(.boolean true, world)] →
      log.sizeArguments = [type] ∧ log.maskArguments = []) ∧
    (∀ world, log.negations = [(.boolean false, world)] →
      log.maskArguments = [type] ∧ log.sizeArguments = []) ∧
    (∀ value world, log.negations = [(.other value, world)] →
      erasePackedSizeTrace result = .error (.inl Error.typeError) world ∧
      log.sizeArguments = [] ∧ log.maskArguments = []) ∧
    (∀ mask world, log.masks = [(mask, world)] → log.countArguments = [mask]) ∧
    (∀ terminal ∈ log.terminals, erasePackedSizeTrace result = embedPackedTerminal terminal)

/-- Initial metadata errors preserve arbitrary payload and post-error state before
negation or either size branch. No behavior law is imposed on the selected query.
Julia source: base/reinterpretarray.jl:819-825. -/
def PackedSizeInitialFailure : Prop :=
  ∀ (W UserError Ty O Mask R : Type)
    (ops : PackedSizeOps (EStateM (Error ⊕ UserError) W) Ty O Mask R)
    (type : Ty) (initial : W),
    letI := paddingModelExceptions W UserError
    match ops.hasPadding type initial with
    | .ok _ _ => True
    | .error error final => packedSize ops type initial = .error error final

def PackedSizeContract : Prop := PackedSizeProtocol ∧ PackedSizeInitialFailure

open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.base.reinterpretarray.Models2Group12
set_option maxHeartbeats 1600000

theorem staticBoundsDispatchContract_proven : StaticBoundsDispatchContract := by
  intro W E R O Ax ops iter i j initial
  letI := staticModelExceptions W E
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    cases hr : ops.customCheckbounds iter i j initial <;>
      simp [staticIndicesCheckbounds, h, hr, bind, pure, EStateM.bind, EStateM.pure]
  · intro h
    simp [staticIndicesCheckboundsBool, h]
  · intro h
    simp [staticBoundsAxes, h]
  · intro axes indices h
    rw [staticBoundsTuple.eq_def]
    simp [h]
  · intro houter hbool
    cases hr : ops.customCheckboundsBool iter i j initial with
    | error error world =>
      simp [staticIndicesCheckbounds, staticIndicesCheckboundsBool, houter, hbool,
        hr, bind, EStateM.bind]
    | ok predicate world =>
      cases predicate with
      | boolean valid =>
        cases valid
        · by_cases hthrow : ops.selectThrowBounds iter i j = true
          · cases ht : ops.customThrowBounds iter i j world <;>
              simp [staticIndicesCheckbounds, staticIndicesCheckboundsBool, houter, hbool,
                hthrow, ht, hr, bind, pure, EStateM.bind, EStateM.pure]
          · simp [staticIndicesCheckbounds, staticIndicesCheckboundsBool, houter, hbool,
              hthrow, hr, liftResult, JuliaLean.base.essentials.checkboundsGeneric,
              bind, pure, EStateM.bind, EStateM.pure]
            rfl
        · simp [staticIndicesCheckbounds, staticIndicesCheckboundsBool, houter, hbool,
            hr, liftResult, JuliaLean.base.essentials.checkboundsGeneric,
            bind, pure, EStateM.bind, EStateM.pure]
      | missing =>
        simp [staticIndicesCheckbounds, staticIndicesCheckboundsBool, houter, hbool,
          hr, bind, EStateM.bind]
        rfl
      | other other =>
        simp [staticIndicesCheckbounds, staticIndicesCheckboundsBool, houter, hbool,
          hr, bind, EStateM.bind]
        rfl
  · intro hbool haxes
    cases hr : ops.customAxes iter initial with
    | error error world =>
      simp [staticIndicesCheckboundsBool, staticBoundsAxes, hbool, haxes, hr,
        bind, EStateM.bind]
    | ok axes world =>
      cases axes with
      | tuple axes => trivial
      | other other =>
        by_cases hs : ops.selectOtherIndices other [i,j] = true
        · simp [staticIndicesCheckboundsBool, staticBoundsAxes, hbool, haxes, hr, hs,
            bind, EStateM.bind]
        · simp [staticIndicesCheckboundsBool, staticBoundsAxes, hbool, haxes, hr, hs,
            bind, EStateM.bind]
          rfl


open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.base.reinterpretarray.Models2Group12
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

theorem staticGeneratedConversionPrecedence_proven : StaticGeneratedConversionPrecedence := by
  intro W E O ops parameter first second firstTag secondTag initial
  cases hf : ops.convertInt first initial with
  | error error after => simp [constructStaticIndex, staticCoordinate, bind, EStateM.bind, hf]
  | ok result after =>
    cases result with
    | accepted value => trivial
    | rejected value =>
      cases hs : ops.convertInt second after with
      | error error final => simp [constructStaticIndex, staticCoordinate, bind, EStateM.bind, hf, hs]
      | ok result final =>
        cases result <;>
          simp [constructStaticIndex, staticCoordinate, bind, EStateM.bind, hf, hs] <;> rfl

theorem staticTupleDestructuringContract_proven : StaticTupleDestructuringContract := by
  intro W E R O C DS ops values initial
  rcases values with ⟨xs, bound⟩
  cases xs with
  | nil =>
    simp [staticUnpackTwo, staticUnpackThree, JuliaLean.base.tuple.indexedIterateTuple,
      JuliaLean.base.tuple.getfield, JuliaLean.base.tuple.bounds, liftResult, bind, pure,
      Except.bind, Except.pure, EStateM.bind, EStateM.pure]
    constructor <;> exact ⟨rfl, rfl⟩
  | cons a xs =>
    cases xs with
    | nil =>
      simp [staticUnpackTwo, staticUnpackThree, JuliaLean.base.tuple.indexedIterateTuple,
        JuliaLean.base.tuple.getfield, JuliaLean.base.tuple.bounds, liftResult, bind, pure,
        Except.bind, Except.pure, EStateM.bind, EStateM.pure]
      constructor <;> exact ⟨rfl, rfl⟩
    | cons b xs =>
      cases xs with
      | nil =>
        simp [staticUnpackTwo, staticUnpackThree, JuliaLean.base.tuple.indexedIterateTuple,
          JuliaLean.base.tuple.getfield, JuliaLean.base.tuple.bounds, liftResult, bind, pure,
          Except.bind, Except.pure, EStateM.bind, EStateM.pure] <;> exact ⟨rfl, rfl⟩
      | cons c xs =>
        simp [staticUnpackTwo, staticUnpackThree, JuliaLean.base.tuple.indexedIterateTuple,
          JuliaLean.base.tuple.getfield, JuliaLean.base.tuple.bounds, liftResult, bind, pure,
          Except.bind, Except.pure, EStateM.bind, EStateM.pure]

theorem staticFinalDestructuringFieldIgnored_proven : StaticFinalDestructuringFieldIgnored := by
  intro W E R O C DS ops object left right initial
  have h23 : JInt.lit .i64 2 ≠ JInt.lit .i64 3 := by decide
  constructor <;>
    simp [staticUnpackTwo, staticUnpackThree, replaceStaticFinalField, h23]

theorem staticSimdConstructorDispatchContract_proven : StaticSimdConstructorDispatchContract := by
  intro W E O R ops iter last inner initial
  by_cases hs : ops.selectCustom iter.parameter (.native (inner + one)) (.native last) = true
  · cases h : ops.custom iter.parameter (.native (inner + one)) (.native last) initial <;>
      simp [staticSelectedConstructorTrace, staticSimdIndex, callStaticIndexConstructor,
        observeStaticConstructor, observeStaticIO, hs, h]
  · simp [staticSelectedConstructorTrace, staticSimdIndex, callStaticIndexConstructor,
      observeStaticConstructor, constructStaticIndex, staticCoordinate, hs, bind, pure,
      EStateM.bind, EStateM.pure, Functor.map, EStateM.map]

private theorem signedWrap64 (value : Int) :
    wrapInt .i64 value =
      (value - IntTy.min .i64) % (2^64) + IntTy.min .i64 := by
  simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.min]
  omega

theorem staticSimdContract_proven : StaticSimdContract := by
  intro W E O R A Observation observe ops iter other last inner initial
  refine ⟨rfl, rfl, ?_⟩
  intro hs
  simp [staticSimdIndex, callStaticIndexConstructor, constructStaticIndex, staticCoordinate,
    hs, bind, pure, EStateM.bind, EStateM.pure, Functor.map, EStateM.map]
  change (inner + one).val = _
  rw [val_add, one_val, signedWrap64]
  rfl


open JuliaLean JuliaLean.base.reinterpretarray JuliaLean.base.reinterpretarray.Models2Group12
set_option maxHeartbeats 1600000

private theorem paddingLowBit (layout : JuliaLean.base.runtime_internals.DataTypeLayout) :
    JuliaLean.base.runtime_internals.datatypeHaspaddingLayout layout =
      (layout.flags.val % 2 != 0) := by
  have hf := layout.flags.property
  change 0 ≤ layout.flags.val ∧ layout.flags.val ≤ 65535 at hf
  unfold JuliaLean.base.runtime_internals.datatypeHaspaddingLayout JuliaLean.base.runtime_internals.has16
  rw [BitVec.toNat_and, BitVec.toNat_ofInt]
  change (((layout.flags.val % 65536).toNat &&& 1) != 0) = _
  rw [Int.emod_eq_of_lt hf.1 (by omega), Nat.and_one_is_mod]
  have hn : (layout.flags.val.toNat % 2 : Nat) = (layout.flags.val % 2).toNat := by omega
  rw [hn]
  apply congrArg Bool.not
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  omega

private theorem nativeNotBool (value : Bool) :
    JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool value = !value := by
  cases value <;> decide

theorem packedLayoutLowBit_proven : PackedLayoutLowBit := by
  intro World V D N Mod P Sym Input Other ops layout initial
  have hh := paddingLowBit layout
  change some (Except.ok (PackedValue.boolean
    (JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool
      (JuliaLean.base.runtime_internals.datatypeHaspaddingLayout layout)), initial)) = _
  rw [nativeNotBool, hh]
  simp [bne]

theorem packedDatatypeObservations_proven : PackedDatatypeObservations := by
  intro World V D N Mod P Sym Input Other ops datatype initial
  constructor
  · intro hn
    simp [isPackedDispatched, JuliaLean.base.runtime_internals.datatypeHaspadding,
      JuliaLean.base.runtime_internals.dataTypeLayout, hn, bind, pure,
      Option.bind]
    rfl
  · intro hn
    refine ⟨?_, ?_, ?_⟩
    · intro layout after hload
      simp [isPackedDispatched, JuliaLean.base.runtime_internals.datatypeHaspadding,
        JuliaLean.base.runtime_internals.dataTypeLayout, hn, hload, bind, pure,
        Option.bind, nativeNotBool, paddingLowBit, bne]
    · intro error after hload
      simp [isPackedDispatched, JuliaLean.base.runtime_internals.datatypeHaspadding,
        JuliaLean.base.runtime_internals.dataTypeLayout, hn, hload, bind, pure,
        Option.bind]
    · intro hload
      simp [isPackedDispatched, JuliaLean.base.runtime_internals.datatypeHaspadding,
        JuliaLean.base.runtime_internals.dataTypeLayout, hn, hload, bind, pure,
        Option.bind]

theorem structSubpaddingObservations_proven : StructSubpaddingObservations := by
  intro W UserError Ty Mask R ops output input initial
  cases ho : ops.nonPadding output initial with
  | error error final =>
    left
    refine ⟨error, final, ?_, ?_⟩ <;>
      simp [structSubpadding, tracedStructSubpaddingOps, observeStructPadding,
        structPaddingEvents, eraseStructPaddingEvents, bind, EStateM.bind, ho]
  | ok outputMask firstWorld =>
    cases hi : ops.nonPadding input firstWorld with
    | error error final =>
      right; left
      refine ⟨outputMask, firstWorld, error, final, ?_, ?_⟩ <;>
        simp [structSubpadding, tracedStructSubpaddingOps, observeStructPadding,
          structPaddingEvents, eraseStructPaddingEvents, bind, EStateM.bind, ho, hi]
    | ok inputMask secondWorld =>
      right; right
      cases he : ops.equal outputMask inputMask secondWorld with
      | error error final =>
        refine ⟨outputMask, firstWorld, inputMask, secondWorld, .error error final, ?_, ?_⟩ <;>
          simp [structSubpadding, tracedStructSubpaddingOps, observeStructPadding,
            structPaddingEvents, eraseStructPaddingEvents, bind, EStateM.bind, ho, hi, he]
      | ok value final =>
        refine ⟨outputMask, firstWorld, inputMask, secondWorld, .ok value final, ?_, ?_⟩ <;>
          simp [structSubpadding, tracedStructSubpaddingOps, observeStructPadding,
            structPaddingEvents, eraseStructPaddingEvents, bind, EStateM.bind, ho, hi, he]


end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- An external observation distinguishes every selected operation in the
source, retains its actual argument and successful value or exception, and
cannot be changed by an arbitrary callback. -/
inductive PaddingEvent95 (T C O : Type) where
  | packed (argument : T) (outcome : Except JuliaLean.base.io.Error (PackedValue O))
  | mask (argument : T) (outcome : Except JuliaLean.base.io.Error C)
  | empty (argument : C) (outcome : Except JuliaLean.base.io.Error (PackedValue O))
  | length (argument : C) (outcome : Except JuliaLean.base.io.Error (Value O))
  | read (argument : C) (index : I64)
      (outcome : Except JuliaLean.base.io.Error (PackedValue O))
  | negation (argument : O) (outcome : Except JuliaLean.base.io.Error (PackedValue O))
  | greater (index : I64) (length : O)
      (outcome : Except JuliaLean.base.io.Error (PackedValue O))

structure PaddingObservation95 (W T C O : Type) where
  before : W
  event : PaddingEvent95 T C O
  after : W

/-- The supplied IO monad retains partial worlds on exceptions and denotes
divergence by none. The observer preserves those behaviors exactly. -/
def observePadding95 {W T C O A : Type}
    (event : Except JuliaLean.base.io.Error A → PaddingEvent95 T C O)
    (action : JuliaLean.base.io.M W A) :
    JuliaLean.base.io.M (List (PaddingObservation95 W T C O) × W) A := fun initial =>
  match action initial.2 with
  | none => none
  | some (.ok (value, after)) => some (.ok (value,
      (initial.1 ++ [⟨initial.2, event (.ok value), after⟩], after)))
  | some (.error (error, after)) => some (.error (error,
      (initial.1 ++ [⟨initial.2, event (.error error), after⟩], after)))

def watchedPadding95 {W T C O : Type} (ops : ArrayPaddingOps W T C O) :
    ArrayPaddingOps (List (PaddingObservation95 W T C O) × W) T C O where
  isPacked := fun x => observePadding95 (.packed x) (ops.isPacked x)
  nonPadding := fun x => observePadding95 (.mask x) (ops.nonPadding x)
  isEmpty := fun x => observePadding95 (.empty x) (ops.isEmpty x)
  length := fun x => observePadding95 (.length x) (ops.length x)
  getindex := fun x i => observePadding95 (.read x i) (ops.getindex x i)
  negate := fun x => observePadding95 (.negation x) (ops.negate x)
  greaterOther := fun i x => observePadding95 (.greater i x) (ops.greaterOther i x)

/-- State continuity is independent of the implementation of every callback. -/
def PaddingWorldChain95 {W T C O : Type} (initial : W) :
    List (PaddingObservation95 W T C O) → W → Prop
  | [], final => initial = final
  | event :: rest, final => event.before = initial ∧
      PaddingWorldChain95 event.after rest final

def paddingFailure95 {T C O : Type} : PaddingEvent95 T C O → Option JuliaLean.base.io.Error
  | .packed _ outcome => match outcome with | .error error => some error | .ok _ => none
  | .mask _ outcome => match outcome with | .error error => some error | .ok _ => none
  | .empty _ outcome => match outcome with | .error error => some error | .ok _ => none
  | .length _ outcome => match outcome with | .error error => some error | .ok _ => none
  | .read _ _ outcome => match outcome with | .error error => some error | .ok _ => none
  | .negation _ outcome => match outcome with | .error error => some error | .ok _ => none
  | .greater _ _ outcome => match outcome with | .error error => some error | .ok _ => none

/-- Native conditional failure, distinct from an observed callback throw. -/
def paddingTypeError95 : JuliaLean.base.io.Error :=
  .foreignError "TypeError" "non-boolean condition"

/-- A stopping Boolean guard either has an observed exception, consumes a
non-Bool and raises TypeError, or consumes true and returns its specified
answer. False is deliberately excluded: it must continue to the next call. -/
def PaddingGuardStop95 {O : Type} (answer : Bool)
    (observed : Except JuliaLean.base.io.Error (PackedValue O))
    (outcome : Except JuliaLean.base.io.Error Bool) : Prop :=
  (∃ error, observed = .error error ∧ outcome = .error error) ∨
  (∃ other, observed = .ok (.other other) ∧ outcome = .error paddingTypeError95) ∨
  (observed = .ok (.boolean true) ∧ outcome = .ok answer)

/-- Independent arithmetic and dispatch contract for one counter update.
The increment is specified by integer congruence, not by the model's addition.
Only a successful true comparison resets to one. -/
def PaddingAdvanceTrace95 {T C O : Type} (index : I64) (length : Value O)
    (outcome : Except JuliaLean.base.io.Error I64)
    (events : List (PaddingEvent95 T C O)) : Prop :=
  ∃ incremented : I64,
    incremented.val % (2 : Int)^64 = (index.val + 1) % (2 : Int)^64 ∧
    match length with
    | .native bound => events = [] ∧
        ((bound.val < incremented.val ∧ outcome = .ok one) ∨
         (incremented.val ≤ bound.val ∧ outcome = .ok incremented))
    | .other bound _ =>
        (∃ error, events = [.greater incremented bound (.error error)] ∧
          outcome = .error error) ∨
        (events = [.greater incremented bound (.ok (.boolean true))] ∧
          outcome = .ok one) ∨
        (events = [.greater incremented bound (.ok (.boolean false))] ∧
          outcome = .ok incremented) ∨
        (∃ other, events = [.greater incremented bound (.ok (.other other))] ∧
          outcome = .error paddingTypeError95)

/-- A completed iteration with no mismatch has one of these readable-byte
witnesses. In particular, a false source byte prevents target indexing. -/
def PaddingReadPass95 {T C O : Type} (source target : C) (si ti : I64)
    (events : List (PaddingEvent95 T C O)) : Prop :=
  events = [.read source si (.ok (.boolean false))] ∨
  events = [.read source si (.ok (.boolean true)),
    .read target ti (.ok (.boolean true))] ∨
  ∃ other, events = [.read source si (.ok (.boolean true)),
    .read target ti (.ok (.other other)), .negation other (.ok (.boolean false))]

/-- Terminal loop observations provide an actual mismatch witness for false,
and a final read-pass plus two independently specified resets for true.
This is a terminal-frame invariant, not a reimplementation of the recursive
loop; it makes no assumption about masks, lengths, or earlier iterations. -/
def PaddingLoopTerminal95 {T C O : Type} (source target : C)
    (sourceLength targetLength : Value O) (outcome : Except JuliaLean.base.io.Error Bool)
    (events : List (PaddingEvent95 T C O)) : Prop :=
  match outcome with
  | .ok false =>
      (∃ pre si ti, events = pre ++ [.read source si (.ok (.boolean true)),
        .read target ti (.ok (.boolean false))]) ∨
      (∃ pre si ti other, events = pre ++ [.read source si (.ok (.boolean true)),
        .read target ti (.ok (.other other)), .negation other (.ok (.boolean true))])
  | .ok true =>
      ∃ pre si ti reads sourceAdvance targetAdvance,
        events = pre ++ reads ++ sourceAdvance ++ targetAdvance ∧
        PaddingReadPass95 source target si ti reads ∧
        PaddingAdvanceTrace95 si sourceLength (.ok one) sourceAdvance ∧
        PaddingAdvanceTrace95 ti targetLength (.ok one) targetAdvance
  | .error error =>
      (∃ pre last, events = pre ++ [last] ∧
        (∀ event ∈ pre, paddingFailure95 event = none) ∧
        paddingFailure95 last = some error) ∨
      (error = paddingTypeError95 ∧
        (∀ event ∈ events, paddingFailure95 event = none) ∧
        ((∃ pre index other, events = pre ++ [.read source index (.ok (.other other))]) ∨
         (∃ pre argument other, events = pre ++ [.negation argument (.ok (.other other))]) ∨
         (∃ pre index length other,
           events = pre ++ [.greater index length (.ok (.other other))])))

/-- Complete finite entry protocol. It specifies the target/source order of
packing, the source/target order of masks, target/source emptiness, and both
length calls before any loop event. Actual values are captured in the trace;
there are no callee laws or assumed native results. -/
def PaddingEntryProtocol95 {T C O : Type} (source target : T)
    (outcome : Except JuliaLean.base.io.Error Bool)
    (events : List (PaddingEvent95 T C O)) : Prop :=
  (∃ result, events = [.packed target result] ∧ PaddingGuardStop95 true result outcome) ∨
  (∃ result, events = [.packed target (.ok (.boolean false)), .packed source result] ∧
    PaddingGuardStop95 false result outcome) ∨
  (∃ error, events = [.packed target (.ok (.boolean false)),
    .packed source (.ok (.boolean false)), .mask source (.error error)] ∧
    outcome = .error error) ∨
  (∃ sm error, events = [.packed target (.ok (.boolean false)),
    .packed source (.ok (.boolean false)), .mask source (.ok sm),
    .mask target (.error error)] ∧ outcome = .error error) ∨
  (∃ sm tm result, events = [.packed target (.ok (.boolean false)),
    .packed source (.ok (.boolean false)), .mask source (.ok sm), .mask target (.ok tm),
    .empty tm result] ∧ PaddingGuardStop95 true result outcome) ∨
  (∃ sm tm result, events = [.packed target (.ok (.boolean false)),
    .packed source (.ok (.boolean false)), .mask source (.ok sm), .mask target (.ok tm),
    .empty tm (.ok (.boolean false)), .empty sm result] ∧
    PaddingGuardStop95 false result outcome) ∨
  (∃ sm tm error, events = [.packed target (.ok (.boolean false)),
    .packed source (.ok (.boolean false)), .mask source (.ok sm), .mask target (.ok tm),
    .empty tm (.ok (.boolean false)), .empty sm (.ok (.boolean false)),
    .length sm (.error error)] ∧ outcome = .error error) ∨
  (∃ sm tm sl error, events = [.packed target (.ok (.boolean false)),
    .packed source (.ok (.boolean false)), .mask source (.ok sm), .mask target (.ok tm),
    .empty tm (.ok (.boolean false)), .empty sm (.ok (.boolean false)),
    .length sm (.ok sl), .length tm (.error error)] ∧ outcome = .error error) ∨
  (∃ sm tm sl tl loopEvents,
    events = [.packed target (.ok (.boolean false)),
      .packed source (.ok (.boolean false)), .mask source (.ok sm), .mask target (.ok tm),
      .empty tm (.ok (.boolean false)), .empty sm (.ok (.boolean false)),
      .length sm (.ok sl), .length tm (.ok tl)] ++ loopEvents ∧
    PaddingLoopTerminal95 sm tm sl tl outcome loopEvents)

/-- For every carrier, initial world and arbitrary selected IO operation,
finite public executions obey the independent entry protocol and terminal
witnesses, preserve every intermediate world, and propagate the first actual
callback exception. Divergence is allowed, with separate nontermination
transparency properties below; no successful or terminating callback law is
assumed. Invariant: base/reinterpretarray.jl:775-813. -/
def ArrayPaddingFiniteProtocol : Prop :=
  ∀ (W T C O : Type) (ops : ArrayPaddingOps W T C O)
    (source target : T) (initial : W),
    match arraySubpaddingDispatched (watchedPadding95 ops) source target ([], initial) with
    | none => True
    | some (.ok (answer, after)) =>
        PaddingWorldChain95 initial after.1 after.2 ∧
        (∀ observation ∈ after.1, paddingFailure95 observation.event = none) ∧
        PaddingEntryProtocol95 source target (.ok answer) (after.1.map (·.event))
    | some (.error (error, after)) =>
        PaddingWorldChain95 initial after.1 after.2 ∧
        PaddingEntryProtocol95 source target (.error error) (after.1.map (·.event))

/-- The independent advance contract covers every signed native Int index,
including wraparound, every length value, arbitrary selected comparison
outcomes and state, and comparison divergence.
Helper invariant: base/reinterpretarray.jl:800-807. -/
def ArrayPaddingCounterAdvance : Prop :=
  ∀ (W T C O : Type) (ops : ArrayPaddingOps W T C O)
    (index : I64) (length : Value O) (initial : W),
    let result := arrayPaddingAdvance (watchedPadding95 ops) index length ([], initial)
    match result with
    | none => ∃ bound parameter incremented,
        length = .other bound parameter ∧
        incremented.val % (2 : Int)^64 = (index.val + 1) % (2 : Int)^64 ∧
        ops.greaterOther incremented bound initial = none
    | some (.ok (next, after)) =>
        PaddingWorldChain95 initial after.1 after.2 ∧
        PaddingAdvanceTrace95 index length (.ok next) (after.1.map (·.event))
    | some (.error (error, after)) =>
        PaddingWorldChain95 initial after.1 after.2 ∧
        PaddingAdvanceTrace95 index length (.error error) (after.1.map (·.event))

/-- A direct native guard consumes only Bool, preserves every world, and
raises the source TypeError for every other value.
Helper invariant: base/reinterpretarray.jl:779-790,796,801,805. -/
def ArrayPaddingBooleanConsumption : Prop :=
  ∀ (W O : Type) (initial : W),
    (∀ boolean : Bool, arrayPaddingCondition (World := W) (O := O) (.boolean boolean) initial =
      some (.ok (boolean, initial))) ∧
    (∀ other : O, arrayPaddingCondition (World := W) (.other other) initial =
      some (.error (paddingTypeError95, initial)))

/-- An observed initial packing failure, divergence, non-Bool or true answer
is the entire public result; a false target answer permits only the same
analysis of the source query next. Thus early divergence is not hidden by a
finite-trace condition. All callback post-worlds are retained.
Invariant: base/reinterpretarray.jl:779-786. -/
def ArrayPaddingEntryTransparency : Prop :=
  ∀ (W T C O : Type) (ops : ArrayPaddingOps W T C O)
    (source target : T) (initial : W),
    let result := arraySubpaddingDispatched ops source target initial
    match ops.isPacked target initial with
    | none => result = none
    | some (.error (error, after)) => result = some (.error (error, after))
    | some (.ok (.other _, after)) => result = some (.error (paddingTypeError95, after))
    | some (.ok (.boolean true, after)) => result = some (.ok (true, after))
    | some (.ok (.boolean false, after)) =>
        match ops.isPacked source after with
        | none => result = none
        | some (.error (error, final)) => result = some (.error (error, final))
        | some (.ok (.other _, final)) => result = some (.error (paddingTypeError95, final))
        | some (.ok (.boolean true, final)) => result = some (.ok (false, final))
        | some (.ok (.boolean false, _)) => True

/-- Directly observes the first read frame at every native counter pair.
Actual source read failure/non-Bool/divergence stops before target indexing;
a true source value makes target failure/divergence or actual mismatches
transparent, with custom negation only for non-Bool target results. The
nonterminal cases impose no invented mask or length assumptions.
Helper invariant: base/reinterpretarray.jl:795-798. -/
def ArrayPaddingFirstReadTransparency : Prop :=
  ∀ (W T C O : Type) (ops : ArrayPaddingOps W T C O)
    (source target : C) (sourceLength targetLength : Value O)
    (si ti : I64) (initial : W),
    let result := arrayPaddingLoop ops source target sourceLength targetLength si ti initial
    match ops.getindex source si initial with
    | none => result = none
    | some (.error (error, after)) => result = some (.error (error, after))
    | some (.ok (.other _, after)) => result = some (.error (paddingTypeError95, after))
    | some (.ok (.boolean false, _)) => True
    | some (.ok (.boolean true, after)) =>
        match ops.getindex target ti after with
        | none => result = none
        | some (.error (error, final)) => result = some (.error (error, final))
        | some (.ok (.boolean false, final)) => result = some (.ok (false, final))
        | some (.ok (.boolean true, _)) => True
        | some (.ok (.other other, middle)) =>
            match ops.negate other middle with
            | none => result = none
            | some (.error (error, final)) => result = some (.error (error, final))
            | some (.ok (.other _, final)) => result = some (.error (paddingTypeError95, final))
            | some (.ok (.boolean true, final)) => result = some (.ok (false, final))
            | some (.ok (.boolean false, _)) => True

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- A custom PaddingError constructor can return any object; Julia throw propagates
that exact object through the arbitrary user exception channel. -/
@[instance_reducible] def permissionUserExceptions (W UserError : Type) :
    MonadExceptOf UserError (EStateM (Error ⊕ UserError) W) where
  throw error := fun world => .error (.inr error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value final => .ok value final
    | .error (.inl error) final => .error (.inl error) final
    | .error (.inr error) final => handler error final

inductive PermissionCall where
  | subpadding | negation | constructor | conversion
  deriving Repr, DecidableEq

structure PermissionTrace (W UserError O : Type) where
  calls : List PermissionCall := []
  paddingArguments : List (TypeLayout × TypeLayout) := []
  paddingResults : List (PackedValue O × W) := []
  negationArguments : List O := []
  negationResults : List (PackedValue O × W) := []
  constructorArguments : List (TypeLayout × TypeLayout) := []
  constructorResults : List (EStateM.Result UserError W UserError) := []
  conversionArguments : List TypeLayout := []
  conversionResults : List
    (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion TypeLayout (Value O) × W) := []

/-- Record all selected operations while keeping the log inaccessible to user code. -/
def tracedPermissionOps {W UserError O : Type}
    (ops : PermissionOps (EStateM UserError W) O UserError) :
    PermissionOps
      (EStateM (Error ⊕ UserError) (W × PermissionTrace W UserError O)) O UserError where
  subpadding := fun first second => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.subpadding]
      paddingArguments := log.paddingArguments ++ [(first, second)] })
    (fun result log => match result with
      | .ok value final => { log with paddingResults := log.paddingResults ++ [(value, final)] }
      | .error _ _ => log) (ops.subpadding first second)
  negate := fun value => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.negation]
      negationArguments := log.negationArguments ++ [value] })
    (fun result log => match result with
      | .ok value final => { log with negationResults := log.negationResults ++ [(value, final)] }
      | .error _ _ => log) (ops.negate value)
  selectCustomError := ops.selectCustomError
  constructCustomError := fun first second => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.constructor]
      constructorArguments := log.constructorArguments ++ [(first, second)] })
    (fun result log => { log with constructorResults := log.constructorResults ++ [result] })
    (ops.constructCustomError first second)
  isType := ops.isType
  convertType := fun type => observePackedSize
    (fun log => { log with
      calls := log.calls ++ [.conversion]
      conversionArguments := log.conversionArguments ++ [type] })
    (fun result log => match result with
      | .ok value final => { log with conversionResults := log.conversionResults ++ [(value, final)] }
      | .error _ _ => log) (ops.convertType type)

/-- A test harness selecting the two public permission checks, with no alternative
implementation of either body. -/
def permissionRun {m : Type → Type} [Monad m] [MonadExceptOf Error m]
    {A O V E : Type} [MonadExceptOf E m] (write : Bool)
    (ops : PermissionOps m O E) (view : View V A) : m Unit :=
  if write then checkWritable ops view else checkReadable ops view

def permissionPhase : PermissionCall → Nat
  | .subpadding => 0
  | .negation => 1
  | .constructor | .conversion => 2

/-- Cached permission bypasses every selected metadata, negation, conversion and
exception-constructor method, for all views and arbitrary user exception payloads.
Julia source: base/reinterpretarray.jl:237-254. -/
def PermissionCacheBypass : Prop :=
  ∀ (W UserError A O V : Type)
    (ops : PermissionOps (EStateM (Error ⊕ UserError) W) O UserError)
    (view : View V A) (initial : W),
    letI := paddingModelExceptions W UserError
    letI := permissionUserExceptions W UserError
    (view.readable = true → checkReadable ops view initial = .ok () initial) ∧
    (view.writable = true → checkWritable ops view initial = .ok () initial)

/-- Read and write queries preserve their distinct operand orders; error construction
always receives target/source order. Negation has its actual native/custom dispatch,
and the if type check follows it. A selected constructor's returned object is genuinely
thrown, while an exception raised by that constructor is preserved without replacement.
All source methods, custom negation values, conversions and user errors are unrestricted.
Julia source: base/reinterpretarray.jl:237-254. -/
def PermissionEvaluation : Prop :=
  ∀ (W UserError A O V : Type) (ops : PermissionOps (EStateM UserError W) O UserError)
    (view : View V A) (write : Bool) (initial : W),
    letI := paddingModelExceptions (W × PermissionTrace W UserError O) UserError
    letI := permissionUserExceptions (W × PermissionTrace W UserError O) UserError
    let result := permissionRun write (tracedPermissionOps ops) view (initial, {})
    let log := packedSizeTrace result
    let cached := if write then view.writable else view.readable
    let first := if write then view.source else view.target
    let second := if write then view.target else view.source
    log.paddingArguments = (if cached then [] else [(first, second)]) ∧
    log.calls.count .subpadding ≤ 1 ∧ log.calls.count .negation ≤ 1 ∧
    log.calls.count .constructor ≤ 1 ∧ log.calls.count .conversion ≤ 2 ∧
    log.calls.Pairwise (fun before after => permissionPhase before ≤ permissionPhase after) ∧
    (∀ args ∈ log.constructorArguments, args = (view.target, view.source)) ∧
    (log.constructorArguments ≠ [] → log.conversionArguments = []) ∧
    (∃ rest, log.conversionArguments ++ rest =
      ([view.target, view.source].filter (fun value => !(ops.isType value)))) ∧
    (∀ world, log.paddingResults = [(.boolean true, world)] →
      erasePackedSizeTrace result = .ok () world ∧ log.negationArguments = [] ∧
      log.constructorArguments = [] ∧ log.conversionArguments = []) ∧
    (∀ value world, log.paddingResults = [(.other value, world)] →
      log.negationArguments = [value]) ∧
    (∀ world, log.negationResults = [(.boolean false, world)] →
      erasePackedSizeTrace result = .ok () world ∧
      log.constructorArguments = [] ∧ log.conversionArguments = []) ∧
    (∀ value world, log.negationResults = [(.other value, world)] →
      erasePackedSizeTrace result = .error (.inl Error.typeError) world ∧
      log.constructorArguments = [] ∧ log.conversionArguments = []) ∧
    (∀ value world, .ok value world ∈ log.constructorResults →
      erasePackedSizeTrace result = .error (.inr value) world) ∧
    (∀ error world, .error error world ∈ log.constructorResults →
      erasePackedSizeTrace result = .error (.inr error) world) ∧
    (∀ world,
      (log.paddingResults = [(.boolean false, world)] ∨
        log.negationResults = [(.boolean true, world)]) →
      ops.selectCustomError view.target view.source = false →
      ops.isType view.target = true → ops.isType view.source = true →
      erasePackedSizeTrace result = .error (.inl (.reinterpret .padding)) world)

/-- First subpadding errors precede negation, error construction and field conversion,
retaining the exact exception object and post-error state.
Julia source: base/reinterpretarray.jl:237-254. -/
def PermissionInitialFailure : Prop :=
  ∀ (W UserError A O V : Type)
    (ops : PermissionOps (EStateM (Error ⊕ UserError) W) O UserError)
    (view : View V A) (write : Bool) (initial : W),
    letI := paddingModelExceptions W UserError
    letI := permissionUserExceptions W UserError
    (if write then view.writable else view.readable) = false →
    match ops.subpadding (if write then view.source else view.target)
        (if write then view.target else view.source) initial with
    | .ok _ _ => True
    | .error error final => permissionRun write ops view initial = .error error final

/-- Generated PaddingError construction retains already-Type arguments with no
conversion. When both need conversion, a wrong first conversion result still precedes
the second conversion before final new rejects the field. This is a constructor
evaluation invariant, not a correctness law for convert(Type,x).
Julia source: base/reinterpretarray.jl:736-739; base/essentials.jl:1456-1488. -/
def PaddingErrorFieldConversion : Prop :=
  ∀ (W UserError O : Type) (ops : PermissionOps (EStateM UserError W) O UserError)
    (first second : TypeLayout) (initial : W),
    letI := paddingModelExceptions (W × PermissionTrace W UserError O) UserError
    let result := constructPaddingFailure (tracedPermissionOps ops) first second (initial, {})
    let log := packedSizeTrace result
    (ops.selectCustomError first second = false →
      ops.isType first = true → ops.isType second = true →
      erasePackedSizeTrace result = .ok (.standard first second) initial ∧
      log.calls = []) ∧
    (ops.selectCustomError first second = false →
      ops.isType first = false → ops.isType second = false →
      match ops.convertType first initial with
      | .ok (.rejected _) _ => log.conversionArguments = [first, second]
      | _ => True)

def PermissionContract : Prop :=
  PermissionCacheBypass ∧ PermissionEvaluation ∧ PermissionInitialFailure ∧ PaddingErrorFieldConversion

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean JuliaLean.base.reinterpretarray
open JuliaLean.base.reinterpretarray.Models2Group12

/-- Keep model exceptions distinct from arbitrary user exception objects. -/
@[instance_reducible] def frontendModelExceptions (W UserError : Type) :
    MonadExceptOf Error (EStateM (Error ⊕ UserError) W) where
  throw error := fun world => .error (.inl error) world
  tryCatch action handler := fun world =>
    match action world with
    | .ok value final => .ok value final
    | .error (.inl error) final => handler error final
    | .error (.inr error) final => .error (.inr error) final

inductive FrontendCall where
  | eachindex | sizeOther | sizeStatic | sizeGet | rangeLength | equality | eltype | empty
  | firstOther | lastOther | firstStatic | lastStatic | rangeFirst | rangeLast
  | conversion | constructor | less | worker
  deriving DecidableEq, Repr

/-- The observation log is separate from user state. It records arguments and actual
returned values without any assumed law for a selected dispatch target. -/
structure FrontendTrace
    (W UserError F OP A O Range IterCustom Eltype R : Type) where
  calls : List FrontendCall := []
  styles : List (RuntimeIndexStyle O × A) := []
  iterators : List (MapreduceIndices O Range IterCustom) := []
  selectedSizeArguments : List (RuntimeStaticIndices O Range) := []
  selectedFirstArguments : List (RuntimeStaticIndices O Range) := []
  selectedLastArguments : List (RuntimeStaticIndices O Range) := []
  selectedFailures : List (UserError × W) := []
  lengths : List (Value O) := []
  firsts : List (Value O) := []
  lasts : List (Value O) := []
  customFirsts : List (StaticIndexResult O) := []
  customLasts : List (StaticIndexResult O) := []
  emptyArguments : List (F × OP × A × Eltype) := []
  workerArguments : List (F × OP × A × StaticIndexResult O × StaticIndexResult O) := []
  terminals : List (EStateM.Result UserError W R) := []

/-- Add observations around an actual selected computation. Its state and exception
payload are preserved, and it cannot write the observation log. -/
def observeFrontend {W UserError X Log : Type}
    (before : Log → Log) (after : EStateM.Result UserError W X → Log → Log)
    (action : EStateM UserError W X) : EStateM (Error ⊕ UserError) (W × Log) X :=
  fun (world, log) =>
    let result := action world
    let log := after result (before log)
    match result with
    | .ok value final => .ok value (final, log)
    | .error error final => .error (.inr error) (final, log)

/-- The same user methods, with an isolated trace around every leaf call. Generated
constructors and known static-iterator methods remain inside the model under test. -/
def tracedStaticMapreduceOps
    {W UserError F OP A O Range IterCustom SizeCustom Eltype R : Type}
    (ops : StaticMapreduceOps (EStateM UserError W)
      F OP A O Range IterCustom SizeCustom Eltype R) :
    StaticMapreduceOps
      (EStateM (Error ⊕ UserError)
        (W × FrontendTrace W UserError F OP A O Range IterCustom Eltype R))
      F OP A O Range IterCustom SizeCustom Eltype R where
  eachindex := fun style array =>
    observeFrontend
      (fun log => { log with
        calls := log.calls ++ [.eachindex]
        styles := log.styles ++ [(style, array)] })
      (fun result log => match result with
        | .ok value _ => { log with iterators := log.iterators ++ [value] }
        | .error _ _ => log) (ops.eachindex style array)
  range := {
    constructors := {
      coordinates := {
        intLessOther := fun x y => observeFrontend
          (fun log => { log with calls := log.calls ++ [.less] })
          (fun _ log => log) (ops.range.constructors.coordinates.intLessOther x y)
        convertInt := fun value => observeFrontend
          (fun log => { log with calls := log.calls ++ [.conversion] })
          (fun _ log => log) (ops.range.constructors.coordinates.convertInt value) }
      selectCustom := ops.range.constructors.selectCustom
      custom := fun k i j => observeFrontend
        (fun log => { log with calls := log.calls ++ [.constructor] })
        (fun _ log => log) (ops.range.constructors.custom k i j) }
    length := fun range => observeFrontend
      (fun log => { log with calls := log.calls ++ [.rangeLength] })
      (fun result log => match result with
        | .ok value _ => { log with lengths := log.lengths ++ [value] }
        | .error _ _ => log) (ops.range.length range)
    first := fun range => observeFrontend
      (fun log => { log with calls := log.calls ++ [.rangeFirst] })
      (fun result log => match result with
        | .ok value _ => { log with firsts := log.firsts ++ [value] }
        | .error _ _ => log) (ops.range.first range)
    last := fun range => observeFrontend
      (fun log => { log with calls := log.calls ++ [.rangeLast] })
      (fun result log => match result with
        | .ok value _ => { log with lasts := log.lasts ++ [value] }
        | .error _ _ => log) (ops.range.last range) }
  selectSizeCustom := ops.selectSizeCustom
  sizeStaticCustom := fun indices => observeFrontend
    (fun log => { log with
      calls := log.calls ++ [.sizeStatic]
      selectedSizeArguments := log.selectedSizeArguments ++ [indices] })
    (fun result log => match result with
      | .ok _ _ => log
      | .error error final => { log with selectedFailures := log.selectedFailures ++ [(error, final)] })
    (ops.sizeStaticCustom indices)
  selectFirstCustom := ops.selectFirstCustom
  firstStaticCustom := fun indices => observeFrontend
    (fun log => { log with
      calls := log.calls ++ [.firstStatic]
      selectedFirstArguments := log.selectedFirstArguments ++ [indices] })
    (fun result log => match result with
      | .ok value _ => { log with customFirsts := log.customFirsts ++ [value] }
      | .error error final => { log with selectedFailures := log.selectedFailures ++ [(error, final)] })
    (ops.firstStaticCustom indices)
  selectLastCustom := ops.selectLastCustom
  lastStaticCustom := fun indices => observeFrontend
    (fun log => { log with
      calls := log.calls ++ [.lastStatic]
      selectedLastArguments := log.selectedLastArguments ++ [indices] })
    (fun result log => match result with
      | .ok value _ => { log with customLasts := log.customLasts ++ [value] }
      | .error error final => { log with selectedFailures := log.selectedFailures ++ [(error, final)] })
    (ops.lastStaticCustom indices)
  sizeOther := fun indices => observeFrontend
    (fun log => { log with calls := log.calls ++ [.sizeOther] })
    (fun _ log => log) (ops.sizeOther indices)
  sizeGetOther := fun size index => observeFrontend
    (fun log => { log with calls := log.calls ++ [.sizeGet] })
    (fun _ log => log) (ops.sizeGetOther size index)
  equalZeroOther := fun value zero => observeFrontend
    (fun log => { log with calls := log.calls ++ [.equality] })
    (fun _ log => log) (ops.equalZeroOther value zero)
  iteratorEltype := fun array => observeFrontend
    (fun log => { log with calls := log.calls ++ [.eltype] })
    (fun _ log => log) (ops.iteratorEltype array)
  empty := fun f op array kind => observeFrontend
    (fun log => { log with
      calls := log.calls ++ [.empty]
      emptyArguments := log.emptyArguments ++ [(f, op, array, kind)] })
    (fun result log => { log with terminals := log.terminals ++ [result] })
    (ops.empty f op array kind)
  firstOther := fun indices => observeFrontend
    (fun log => { log with calls := log.calls ++ [.firstOther] })
    (fun result log => match result with
      | .ok value _ => { log with customFirsts := log.customFirsts ++ [value] }
      | .error _ _ => log) (ops.firstOther indices)
  lastOther := fun indices => observeFrontend
    (fun log => { log with calls := log.calls ++ [.lastOther] })
    (fun result log => match result with
      | .ok value _ => { log with customLasts := log.customLasts ++ [value] }
      | .error _ _ => log) (ops.lastOther indices)
  reduce := fun f op array first last => observeFrontend
    (fun log => { log with
      calls := log.calls ++ [.worker]
      workerArguments := log.workerArguments ++ [(f, op, array, first, last)] })
    (fun result log => { log with terminals := log.terminals ++ [result] })
    (ops.reduce f op array first last)

def frontendTraceOf {E W Log X : Type} : EStateM.Result E (W × Log) X → Log
  | .ok _ (_, log) => log
  | .error _ (_, log) => log

def eraseFrontendTrace {E W Log X : Type} :
    EStateM.Result E (W × Log) X → EStateM.Result E W X
  | .ok value (world, _) => .ok value world
  | .error error (world, _) => .error error world

def embedFrontendTerminal {W UserError X : Type} :
    EStateM.Result UserError W X → EStateM.Result (Error ⊕ UserError) W X
  | .ok value world => .ok value world
  | .error error world => .error (.inr error) world

/-- The observable phases exclude coordinate conversions and selected constructors,
which are local to the endpoint computations and may occur in either endpoint. -/
def frontendPhase : FrontendCall → Nat
  | .eachindex => 0
  | .rangeLength | .sizeOther | .sizeStatic => 1
  | .sizeGet => 2
  | .equality => 3
  | .eltype | .firstOther | .firstStatic | .rangeFirst => 4
  | .lastOther | .lastStatic | .rangeLast => 5
  | .empty | .worker => 6
  | .conversion | .constructor | .less => 7

/-- All selected dispatch is quantified without laws. Observations test the original
style and array identity, exclusive empty/nonempty routing, endpoint order, exact worker
arguments for each custom endpoint independently, including mixed custom/default routes,
native-coordinate construction for generated static endpoints,
actual K/R-specific size/first/last selection and arguments, and complete terminal
result/error/state preservation. Zero-length static ranges never
perform endpoint operations, even when K is non-native or invalid for a native field.
Julia source: base/reinterpretarray.jl:946-954. -/
def StaticMapreduceProtocol : Prop :=
  ∀ (W UserError F OP A O Range IterCustom SizeCustom Eltype R : Type)
    (ops : StaticMapreduceOps (EStateM UserError W)
      F OP A O Range IterCustom SizeCustom Eltype R)
    (f : F) (op : OP) (parameter : Value O)
    (style : StaticStyleToken (Value O) parameter) (array : A) (initial : W),
    letI := frontendModelExceptions
      (W × FrontendTrace W UserError F OP A O Range IterCustom Eltype R) UserError
    let result := mapreduceStatic (tracedStaticMapreduceOps ops) f op style array (initial, {})
    let log := frontendTraceOf result
    log.styles = [(.static parameter, array)] ∧
    log.calls.count .eachindex = 1 ∧
    log.calls.count .rangeLength + log.calls.count .sizeOther + log.calls.count .sizeStatic ≤ 1 ∧
    log.calls.count .rangeFirst + log.calls.count .firstOther + log.calls.count .firstStatic ≤ 1 ∧
    log.calls.count .rangeLast + log.calls.count .lastOther + log.calls.count .lastStatic ≤ 1 ∧
    log.calls.count .empty + log.calls.count .worker ≤ 1 ∧
    .less ∉ log.calls ∧
    ((log.calls.filter (fun call => call != .conversion && call != .constructor)).Pairwise
      (fun before after => frontendPhase before ≤ frontendPhase after)) ∧
    (∀ args ∈ log.emptyArguments, ∃ kind, args = (f, op, array, kind)) ∧
    (∀ args ∈ log.workerArguments, ∃ first last, args = (f, op, array, first, last)) ∧
    (∀ terminal ∈ log.terminals, eraseFrontendTrace result = embedFrontendTerminal terminal) ∧
    (.empty ∈ log.calls → .worker ∉ log.calls ∧ .rangeFirst ∉ log.calls ∧
      .rangeLast ∉ log.calls ∧ .firstOther ∉ log.calls ∧ .lastOther ∉ log.calls ∧
      .firstStatic ∉ log.calls ∧ .lastStatic ∉ log.calls ∧ .conversion ∉ log.calls ∧ .constructor ∉ log.calls) ∧
    (∀ first last, log.customFirsts = [first] → log.customLasts = [last] →
      log.workerArguments = [(f, op, array, first, last)]) ∧
    (∀ observed first last, log.customFirsts = [observed] →
      (f, op, array, first, last) ∈ log.workerArguments → first = observed) ∧
    (∀ observed first last, log.customLasts = [observed] →
      (f, op, array, first, last) ∈ log.workerArguments → last = observed) ∧
    (∀ indices, log.iterators = [.static indices] →
      (∀ selected ∈ log.selectedSizeArguments, selected = indices) ∧
      (∀ selected ∈ log.selectedFirstArguments, selected = indices) ∧
      (∀ selected ∈ log.selectedLastArguments, selected = indices) ∧
      (ops.selectSizeCustom indices = true → log.selectedSizeArguments = [indices]) ∧
      (ops.selectSizeCustom indices = false → log.selectedSizeArguments = []) ∧
      (ops.selectFirstCustom indices = false → log.selectedFirstArguments = []) ∧
      (ops.selectLastCustom indices = false → log.selectedLastArguments = [])) ∧
    (∀ error world, (error, world) ∈ log.selectedFailures →
      eraseFrontendTrace result = .error (.inr error) world) ∧
    (∀ indices, log.iterators = [.static indices] → log.lengths = [.native zero] →
      log.calls.count .eltype = 1 ∧ .rangeFirst ∉ log.calls ∧ .rangeLast ∉ log.calls ∧
      .firstStatic ∉ log.calls ∧ .lastStatic ∉ log.calls ∧ .worker ∉ log.calls ∧ .conversion ∉ log.calls ∧ .constructor ∉ log.calls) ∧
    (∀ indices n k first last,
      log.iterators = [.static indices] → log.lengths = [.native n] → n ≠ zero →
      indices.parameter = .native k → log.firsts = [.native first] →
      log.lasts = [.native last] →
      ops.range.constructors.selectCustom (.native k) (.native one) (.native first) = false →
      ops.range.constructors.selectCustom (.native k) (.native k) (.native last) = false →
      log.workerArguments = [(f, op, array,
        .index ⟨.native k, ⟨one, first⟩⟩, .index ⟨.native k, ⟨k, last⟩⟩)])

/-- The first selected lookup's exception and preceding state changes are preserved
before every subsequent size, endpoint or reduction action.
Julia source: base/reinterpretarray.jl:946-954. -/
def StaticMapreduceInitialFailure : Prop :=
  ∀ (W UserError F OP A O Range IterCustom SizeCustom Eltype R : Type)
    (ops : StaticMapreduceOps (EStateM (Error ⊕ UserError) W)
      F OP A O Range IterCustom SizeCustom Eltype R)
    (f : F) (op : OP) (parameter : Value O)
    (style : StaticStyleToken (Value O) parameter) (array : A) (initial : W),
    letI := frontendModelExceptions W UserError
    match ops.eachindex (.static parameter) array initial with
    | .ok _ _ => True
    | .error error final => mapreduceStatic ops f op style array initial = .error error final

/-- Literal tuple index two obeys its mathematical positional specification and bounds
for every constructible tuple, regardless of unrelated selected callbacks.
Julia source: base/reinterpretarray.jl:948; base/tuple.jl:33. -/
def StaticMapreduceTupleSecond : Prop :=
  ∀ (W UserError F OP A O Range IterCustom SizeCustom Eltype R : Type)
    (ops : StaticMapreduceOps (EStateM (Error ⊕ UserError) W)
      F OP A O Range IterCustom SizeCustom Eltype R)
    (values : NativeTuple (Value O)) (initial : W),
    letI := frontendModelExceptions W UserError
    (values.values.length < 2 →
      staticMapreduceSecondSize ops (.tuple values) initial =
        .error (.inl (.tuple (.julia .boundsError))) initial) ∧
    (∀ second, values.values[1]? = some second →
      staticMapreduceSecondSize ops (.tuple values) initial = .ok second initial)

/-- Generic equality failures are preserved; a returned non-Bool becomes TypeError
only after the selected equality's effects, at the source if condition.
Julia source: base/reinterpretarray.jl:949. -/
def StaticMapreduceConditionType : Prop :=
  ∀ (W UserError F OP A O Range IterCustom SizeCustom Eltype R : Type)
    (ops : StaticMapreduceOps (EStateM (Error ⊕ UserError) W)
      F OP A O Range IterCustom SizeCustom Eltype R)
    (value : O) (parameter : Bool) (initial : W),
    letI := frontendModelExceptions W UserError
    match ops.equalZeroOther value zero initial with
    | .error error final => staticMapreduceIsZero ops (.other value parameter) initial =
        .error error final
    | .ok (.rejected _) final => staticMapreduceIsZero ops (.other value parameter) initial =
        .error (.inl Error.typeError) final
    | .ok (.accepted _) _ => True

def StaticMapreduceContract : Prop :=
  StaticMapreduceProtocol ∧ StaticMapreduceInitialFailure ∧
    StaticMapreduceTupleSecond ∧ StaticMapreduceConditionType

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12

namespace JuliaLean.Proofs.base.reinterpretarray.Models2Group12

open JuliaLean.base.reinterpretarray.Models2Group12

/-- Isolated observations retain the exact arguments, pre-call state and returned
state or exception. Selected user code has no access to this log. -/
inductive DefaultReductionEvent
    (W UserError F OP A FirstOther LastOther Block R : Type) where
  | tuningCall (f : F) (op : OP) (world : W)
  | tuningReturn (result : EStateM.Result UserError W Block)
  | workerCall (f : F) (op : OP) (array : A)
      (first : RuntimeStaticIndex FirstOther) (last : RuntimeStaticIndex LastOther)
      (block : Block) (world : W)
  | workerReturn (result : EStateM.Result UserError W R)

/-- Record calls around arbitrary computations without changing their returned value,
exception payload or user state. The log is not part of the user's mutable state. -/
def observeDefaultReduction {W UserError X Event : Type}
    (before : W → Event) (after : EStateM.Result UserError W X → Event)
    (action : EStateM UserError W X) : EStateM UserError (W × List Event) X :=
  fun (world, events) =>
    let result := action world
    let events := events ++ [before world, after result]
    match result with
    | .ok value final => .ok value (final, events)
    | .error error final => .error error (final, events)

/-- The exact selected methods, surrounded only by observers. -/
def observedDefaultMapreduceOps
    {W UserError F OP A FirstOther LastOther Block R : Type}
    (ops : DefaultMapreduceOps (EStateM UserError W)
      F OP A FirstOther LastOther Block R) :
    DefaultMapreduceOps
      (EStateM UserError (W × List
        (DefaultReductionEvent W UserError F OP A FirstOther LastOther Block R)))
      F OP A FirstOther LastOther Block R where
  pairwiseBlocksize := fun f op =>
    observeDefaultReduction (.tuningCall f op) .tuningReturn (ops.pairwiseBlocksize f op)
  reduce := fun f op array first last block =>
    observeDefaultReduction (.workerCall f op array first last block) .workerReturn
      (ops.reduce f op array first last block)

/-- Forget observations while retaining both successful and exceptional state. -/
def eraseDefaultReductionLog {W UserError X Event : Type} :
    EStateM.Result UserError (W × List Event) X → EStateM.Result UserError W X
  | .ok value (world, _) => .ok value world
  | .error error (world, _) => .error error world

def defaultReductionLog {W UserError X Event : Type} :
    EStateM.Result UserError (W × List Event) X → List Event
  | .ok _ (_, events) => events
  | .error _ (_, events) => events

/-- The default helper preserves the original function, operator, array and both
complete endpoint objects. Exactly one tuning call occurs. Its failure is terminal;
otherwise exactly one worker receives its unrestricted result and resulting state.
The helper returns the worker's value/error/state without alteration. This trace
invariant quantifies over arbitrary user methods, states and exception payloads;
it supplies no law for either selected method and permits distinct endpoint parameters.
Julia source: base/reinterpretarray.jl:984-985. -/
def DefaultMapreduceForwarding : Prop :=
  ∀ (W UserError F OP A FirstOther LastOther Block R : Type)
    (ops : DefaultMapreduceOps (EStateM UserError W)
      F OP A FirstOther LastOther Block R)
    (f : F) (op : OP) (array : A) (first : RuntimeStaticIndex FirstOther)
    (last : RuntimeStaticIndex LastOther) (initial : W),
    let result := mapreduceDefault (observedDefaultMapreduceOps ops)
      f op array first last (initial, [])
    let events := defaultReductionLog result
    (∃ error final,
      events = [.tuningCall f op initial, .tuningReturn (.error error final)] ∧
      eraseDefaultReductionLog result = .error error final) ∨
    (∃ block intermediate terminal,
      events = [.tuningCall f op initial, .tuningReturn (.ok block intermediate),
        .workerCall f op array first last block intermediate, .workerReturn terminal] ∧
      eraseDefaultReductionLog result = terminal)

open JuliaLean JuliaLean.base.reinterpretarray

theorem identityObservations_proven : IdentityObservations := by
  intro A Observation observe a
  exact ⟨rfl, rfl⟩

theorem parentDispatchArguments_proven : ParentDispatchArguments := by
  intro A R O World E callee target view initial
  cases h : callee target view.parent initial <;>
    simp [reinterpretParent, observedCall, h]

theorem booleanConsumption_proven : BooleanConsumption := by
  intro World UserError O initial
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem diagnosticExceptionClasses_proven : DiagnosticExceptionClasses := by
  intro Msg Dim Ax Src Tgt s t u msg dim ax sv tv
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem contiguityDependsOnlyOnParent_proven : ContiguityDependsOnlyOnParent := by
  intro W UserError A R O ops first second h
  simp only [checkContiguous, h]

theorem toIndexCoordinatePreservation_proven : ToIndexCoordinatePreservation := by
  intro O index
  exact ⟨rfl, rfl, rfl⟩

theorem similarForwardingArguments_proven : SimilarForwardingArguments := by
  constructor
  · intro World UserError A T S D R callee view target dims initial
    cases h : callee view.parent target dims initial <;>
      simp [m234_similar, observeForwardArguments, forwardArguments, h]
  · intro World UserError P TA D R callee wrapperType parentType dims initial
    cases h : callee parentType dims initial <;>
      simp [m235_similarType, observeForwardArguments, forwardArguments, h]

theorem staticMaybeReshapeContract_proven : StaticMaybeReshapeContract := by
  intro W E A I R O Observation ops observe array indices initial
  cases h : ops.fallback .cartesian array indices initial <;>
    simp [staticMaybeReshape, observeStaticIO, staticMaybeReshapeIdentity, h]

theorem staticCartesianFallbackContract_proven : StaticCartesianFallbackContract := by
  intro W E A V Out get set array value indices initial
  cases hg : get array indices.values initial <;>
    cases hs : set array value indices.values initial <;>
      simp [m337_getindexFallback, m341_setindexFallback, observeStaticIO, hg, hs]

theorem storedParentObservations_proven : StoredParentObservations := by
  intro T S A Observation observe a
  rfl

theorem parentMetadataObservations_proven : ParentMetadataObservations := by
  intro T S A R E World callee a initial
  cases h : callee a.parent initial <;>
    simp [m370_dataids, m401_hasOffset, observe49, h]

theorem zeroDimensionalShape_proven : ZeroDimensionalShape := by
  intro T S A a h
  exact ⟨rfl, rfl⟩

theorem cconvertParentObservations_proven : CconvertParentObservations := by
  intro T S A R E World callee a initial
  cases h : callee a.source a.parent initial <;>
    simp [m410_cconvert, observe49, h]

theorem wrapperPointerProtocol_proven : WrapperPointerProtocol := by
  intro A Metadata R E World callee wrapper initial
  cases h : callee wrapper.parent initial <;>
    simp [checkPointerReshaped, checkPointerSubarray, reshapedStoredParent, subarrayStoredParent, observe49, h]

theorem staticAssignmentProtocol_proven : StaticAssignmentProtocol := by
  intro A R O K E World callee view index initial
  cases h : callee view.parent index.coordinates.j initial <;>
    simp [isAssignedStatic, observe49, h]

theorem assignmentFallbackGuard_proven : AssignmentFallbackGuard := by
  intro A O I view indices bounds pointer
  cases bounds <;> cases pointer <;> rfl

theorem arrayPaddingBooleanConsumption_proven : ArrayPaddingBooleanConsumption := by
  intro W O initial
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem defaultMapreduceForwarding_proven : DefaultMapreduceForwarding := by
  intro W UserError F OP A FirstOther LastOther Block R ops f op array first last initial
  cases ht : ops.pairwiseBlocksize f op initial with
  | error error final =>
    left
    refine ⟨error, final, ?_, ?_⟩ <;>
      simp [mapreduceDefault, observedDefaultMapreduceOps, observeDefaultReduction,
        defaultReductionLog, eraseDefaultReductionLog, bind, EStateM.bind, ht]
  | ok block intermediate =>
    cases hw : ops.reduce f op array first last block intermediate with
    | error error final =>
      right
      refine ⟨block, intermediate, .error error final, ?_, ?_⟩ <;>
        simp [mapreduceDefault, observedDefaultMapreduceOps, observeDefaultReduction,
          defaultReductionLog, eraseDefaultReductionLog, bind, EStateM.bind, ht, hw]
    | ok value final =>
      right
      refine ⟨block, intermediate, .ok value final, ?_, ?_⟩ <;>
        simp [mapreduceDefault, observedDefaultMapreduceOps, observeDefaultReduction,
          defaultReductionLog, eraseDefaultReductionLog, bind, EStateM.bind, ht, hw]

theorem customAxesLookup_proven : CustomAxesLookup := by
  intro World UserError A Axis O ops callee argument index initial
  cases h : callee argument index initial <;>
    simp [axesGet, observeAxes98, h]

theorem staticIndicesSizeContract_proven : StaticIndicesSizeContract := by
  intro W E R O ops iter initial
  cases h : ops.length iter.indices2 initial <;>
    simp [staticIndicesSize, observeStaticIO, Functor.map, bind, pure, EStateM.map, EStateM.bind, EStateM.pure, h]

theorem staticFieldObservationContract_proven : StaticFieldObservationContract := by
  intro A W field initial
  cases field <;> exact ⟨rfl, rfl⟩

theorem abstractEachIndexFlow_proven : AbstractEachIndexFlow := by
  intro A Parent Style R E World ops style a initial
  cases hp : ops.parent a initial with
  | error error final =>
    simp [eachIndexAbstract, observe49, bind, EStateM.bind, hp, FailedFlow49]
  | ok parent middle =>
    cases he : ops.eachindex style parent middle <;>
      simp [eachIndexAbstract, observe49, bind, EStateM.bind, hp, he,
        FailedFlow49, SuccessfulFlow49] <;>
      exact ⟨parent, middle, by simp⟩

theorem unaliasCopyFlow_proven : UnaliasCopyFlow := by
  intro A Copied R O E World ops a initial
  cases hc : ops.copy a.parent initial with
  | error error final =>
    simp [unaliasCopyPlain, unaliasCopyReshaped, observe49, bind, EStateM.bind, hc, FailedFlow49]
  | ok copied middle =>
    constructor
    · cases he : ops.plain a.target copied middle <;>
        simp [unaliasCopyPlain, observe49, bind, EStateM.bind, hc, he,
          FailedFlow49, SuccessfulFlow49] <;>
        exact ⟨copied, middle, by simp⟩
    · cases he : ops.reshaped a.target copied middle <;>
        simp [unaliasCopyReshaped, observe49, bind, EStateM.bind, hc, he,
          FailedFlow49, SuccessfulFlow49] <;>
        exact ⟨copied, middle, by simp⟩

theorem paddingDisplayProtocol_proven : PaddingDisplayProtocol := by
  intro IO Ty Text R E World ops io padding initial
  cases hs : ops.string "Padding of type " padding.source
      " is not compatible with type " padding.target "." initial with
  | error error final =>
    simp [showPaddingError, observe49, bind, EStateM.bind, hs, FailedFlow49]
  | ok message middle =>
    cases he : ops.print io message middle <;>
      simp [showPaddingError, observe49, bind, EStateM.bind, hs, he,
        FailedFlow49, SuccessfulFlow49] <;>
      exact ⟨message, middle, by simp⟩


theorem reshapeWrapperCustomArguments_proven : ReshapeWrapperCustomArguments := by
  intro World E A Ax O Custom R ops callee target source array initial
  cases h : callee target array initial <;>
    simp [reinterpretReshapeArray, observeCustomConstructor, Functor.map, EStateM.map, h]

theorem staticIndicesConstructorContract_proven : StaticIndicesConstructorContract := by
  intro W E O R Out ops parameter range initial
  cases parameter with
  | other value valid => rfl
  | native k =>
    by_cases hk : k.val ≤ 1
    · have hnot : ¬ 1 < k.val := by omega
      simp [staticIndicesConstructor, hk, hnot]
      rfl
    · have hpos : 1 < k.val := by omega
      by_cases hs : ops.selectCustom (.native k) range = true
      · cases h : ops.custom (.native k) range initial <;>
          simp [staticIndicesConstructor, hk, hpos, hs, observeStaticIO, h]
      · simp [staticIndicesConstructor, hk, hpos, hs, pure, EStateM.pure]

theorem nativeAxesLookup_proven : NativeAxesLookup := by
  intro World UserError A Axis O ops tuple index initial
  constructor
  · intro hbad
    rcases hbad with hlow | hhigh
    · simp only [axesGet, JuliaLean.base.abstractarray.tupleGet, if_pos hlow, liftResult]
      rfl
    · have hn : tuple.values.length ≤ (index.val - 1).toNat := by omega
      have hnone := List.getElem?_eq_none hn
      have ht : JuliaLean.base.abstractarray.tupleGet tuple.values index =
          .error (.julia .boundsError) := by
        unfold JuliaLean.base.abstractarray.tupleGet
        split
        · rfl
        · rw [hnone]
      simp only [axesGet, ht, liftResult]
      rfl
  · intro before after selected hsplit hindex
    have hn : ¬ index.val < 1 := by omega
    have hp : (index.val - 1).toNat = before.length := by omega
    simp [axesGet, JuliaLean.base.abstractarray.tupleGet, hn, hp, hsplit,
      List.getElem?_append, liftResult, pure, EStateM.pure]

end JuliaLean.Proofs.base.reinterpretarray.Models2Group12


namespace JuliaLean.Proofs.base.reinterpretarray
open JuliaLean.Registry

def entriesModels2Group12 : List Entry := [
  { id := "reinterpretarray-identity-observations", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::AbstractArray{T}) where {T}", "reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray{T}) where {T}"],
    statement := "Same-element reinterpretation preserves every observation of the original array, including alias identities.",
    source := "base/reinterpretarray.jl:35-38,104,145", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.IdentityObservations, thm := some ``Models2Group12.identityObservations_proven },
  { id := "reinterpretarray-parent-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::NonReshapedReinterpretArray) where {T}"],
    statement := "Every selected parent reinterpret operation is invoked exactly once with the requested element type and stored parent, on success and failure.",
    source := "base/reinterpretarray.jl:3-12,190", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ParentDispatchArguments, thm := some ``Models2Group12.parentDispatchArguments_proven },
  { id := "reinterpretarray-boolean-consumption", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret", "ReinterpretArray{T}"],
    statement := "Conditional consumption accepts both Bool values and rejects every non-Bool comparison result with TypeError before any subsequent effects.",
    source := "base/reinterpretarray.jl:85-99,124-138", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.BooleanConsumption, thm := some ``Models2Group12.booleanConsumption_proven },
  { id := "reinterpretarray-constructor-plain", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}"],
    statement := "Every successful ordinary constructor retains the original parent handle, both type identities, the input rank value, the non-reshape form and valid runtime rank admission, for arbitrary selected operations, states and exceptions.",
    source := "base/reinterpretarray.jl:3-12,35-38,73-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PlainConstructorContract, thm := none },
  { id := "reinterpretarray-constructor-reshape", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}"],
    statement := "Every successful reshape constructor retains the original parent and both type identities, has the reshape form and an admissible runtime rank, for arbitrary selected operations, states and exceptions.",
    source := "base/reinterpretarray.jl:3-12,107-144,151-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ReshapeConstructorContract, thm := none },
  { id := "reinterpretarray-reshape-wrapper-generic", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T}"],
    statement := "The generic wrapper returns only a concrete reshaped view with the original parent/type identities and an admissible rank; its arbitrary selected effects are covered by the companion wrapper observation contract.",
    source := "base/reinterpretarray.jl:151-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ReshapeWrapperGenericContract, thm := none },
  { id := "reinterpretarray-reshape-wrapper-custom", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T}"],
    statement := "A selected custom constructor receives the exact requested type and original array once, preserving its actual result or user exception and before/after state.",
    source := "Invariant: base/reinterpretarray.jl:188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ReshapeWrapperCustomArguments, thm := some ``Models2Group12.reshapeWrapperCustomArguments_proven },
  { id := "reinterpretarray-diagnostic-errors", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["throwbits", "throwsize0", "throwsingleton", "throwbitpadding", "thrownonint", "throwaxes1", "throwfromsingleton"],
    statement := "Pure lazy-capture diagnostics always throw ArgumentError for every accepted captured payload; effectful size diagnostics have separate dispatched contracts.",
    source := "Invariant: base/reinterpretarray.jl:14-31,74-84,119-123 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.DiagnosticExceptionClasses, thm := some ``Models2Group12.diagnosticExceptionClasses_proven },
  { id := "reinterpretarray-constructor-validation-effects", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}", "ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}"],
    statement := "Both full constructors observe target/source isbits followed by target/source padding in order, stop with the precise early ArgumentError or diagnostic MethodError according to actual Type membership, TypeError or user error, preserve the first actual user failure, and thread every selected-call state without laws on callbacks.",
    source := "Invariant: base/reinterpretarray.jl:73-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ConstructorValidationEffects, thm := none },
  { id := "reinterpretarray-new-view-field-effects", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}", "ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}"],
    statement := "Final construction rejects an inadmissible rank before conversion, skips existing Bool values, concretely converts native Int 0/1 or raises InexactError, preserves arbitrary custom conversion outcomes and state, and delays final Bool field checks until both conversions finish.",
    source := "Helper invariant: base/reinterpretarray.jl:102,143; src/julia-syntax.scm:795-806,3870-3893 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.NewDynamicViewEffects, thm := none },
  { id := "reinterpretarray-constructor-padding-fields", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}", "ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}"],
    statement := "Both actual subpadding results are obtained in target/source then source/target order before rank checks or Bool conversion, and feed the independently specified final construction; the plain rank is unchanged and the reshape rank has its actual dimension/arithmetic observation origin.",
    source := "Invariant: base/reinterpretarray.jl:100-103,128-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ConstructorPaddingAndFields, thm := none },
  { id := "reinterpretarray-reshape-wrapper-generic-effects", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::typeof(reshape), ::Type{T}, a::AbstractArray) where {T}"],
    statement := "The generic wrapper preserves the concrete constructor validation and field-conversion observation contracts, the original parent/type and rank origin, and exact user error/state behavior; it never calls the custom constructor field.",
    source := "Invariant: base/reinterpretarray.jl:188; constructor lines107-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ReshapeWrapperGenericEffects, thm := none },
  { id := "reinterpretarray-intmultiple-diagnostic-effects", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["throwintmult(S::Type, T::Type)"],
    statement := "For arbitrary selected type-size queries, the integer-multiple diagnostic evaluates target then source, captures arbitrary returned values without a type assertion, preserves the exact first user error and post-call world, and raises ArgumentError only after both successes.",
    source := "Invariant: base/reinterpretarray.jl:108-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.IntMultipleDiagnosticEffects, thm := none },
  { id := "reinterpretarray-size1-dispatched-diagnostic-effects", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["throwsize1(a::AbstractArray, T::Type)"],
    statement := "For arbitrary array, type-query and scalar dispatch, the size diagnostic preserves both eltype calls, axes(a,1), target-size evaluation and the second-eltype-dependent size query; exact actual size values feed division, and all results, user errors, native DivideError, ArgumentError and world transitions obey the observed source call order.",
    source := "Invariant: base/reinterpretarray.jl:113-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.DispatchedSize1DiagnosticEffects, thm := none },
  { id := "reinterpretarray-native-scalar-pair-arithmetic", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}", "ReinterpretArray{T}(::typeof(reshape), a::A) where {T,S,A<:AbstractArray{S}}", "IndexStyle"],
    statement := "All native/native generic scalar paths retain native values and unchanged world, implement exact 64-bit modular arithmetic, signed truncating quotient/remainder with correct errors, and the four mathematical comparisons, independently of arbitrary selected callbacks.",
    source := "Helper invariant: base/reinterpretarray.jl:89-99,128-139,266-272; doc/src/manual/integers-and-floating-point-numbers.md @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.NativeScalarPairArithmetic, thm := none },
  { id := "reinterpretarray-native-axes-lookup", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}"],
    statement := "The constructor's native tuple axes lookup returns the independently specified one-based element or BoundsError for every out-of-range native index, with unchanged world.",
    source := "Helper invariant: base/reinterpretarray.jl:91; doc/src/manual/arrays.md @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.NativeAxesLookup, thm := some ``Models2Group12.nativeAxesLookup_proven },
  { id := "reinterpretarray-custom-axes-lookup", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["reinterpret(::Type{T}, a::A) where {T,N,S,A<:AbstractArray{S,N}}"],
    statement := "The constructor's custom axes lookup forwards exactly one unchanged container/index call, its actual result or error, and its post-call world for every arbitrary selected operation.",
    source := "Helper invariant: base/reinterpretarray.jl:91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.CustomAxesLookup, thm := some ``Models2Group12.customAxesLookup_proven },
  { id := "reinterpretarray-stride-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["stride(A::Union{DenseArray,StridedReshapedArray,StridedReinterpretArray}, k::Integer)"],
    statement := "For every stateful array and scalar dispatch, stride preserves the first dimension-query error, evaluates only the selected array branch in source order, applies true one-based bounds for native tuple indices, selects a specialized tuple index method or exactly one conversion for a non-native Integer tuple index, and distinguishes converted Symbol FieldError from other wrong-type TypeError.",
    source := "base/reinterpretarray.jl:208-209; base/tuple.jl:33-34; src/builtins.c:1173-1194; src/datatype.c:1859-1884; src/rtutils.c:170-173", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StrideContract, thm := none },

  { id := "reinterpretarray-parent-contiguity", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_checkcontiguous(::Type{Bool}, A::ReinterpretArray)"],
    statement := "For arbitrary parent contiguity dispatch and mutable state, changing a reinterpret view's metadata while preserving its exact parent cannot alter the result, exception, or state.",
    source := "base/reinterpretarray.jl:232", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ContiguityDependsOnlyOnParent, thm := some ``Models2Group12.contiguityDependsOnlyOnParent_proven },
  { id := "reinterpretarray-similar-arguments", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["similar(a::ReinterpretArray, T::Type, d::Dims)", "similar(::Type{TA}, dims::Dims) where {T,N,O,P,TA<:ReinterpretArray{T,N,O,P}}"],
    statement := "Both reused similar methods make exactly one selected allocation call with unchanged parent or parent type, requested target type where present, and dimensions, for arbitrary stateful user methods and exception payloads.",
    source := "base/reinterpretarray.jl:234-235; doc/src/manual/interfaces.md:224-233", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.SimilarForwardingArguments, thm := some ``Models2Group12.similarForwardingArguments_proven },
  { id := "reinterpretarray-index-style-routing", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["IndexStyle(::Type{ReinterpretArray{T,N,S,A,false}}) where {T,N,S,A<:AbstractArray{S,N}}", "IndexStyle(::Type{ReinterpretArray{T,N,S,A,true}}) where {T,N,S,A<:AbstractArray{S}}"],
    statement := "Plain views return standard linear or Cartesian styles; reshaped style queries preserve repeated metadata observations and exact scalar/parent call order, propagate arbitrary selected constructor results and errors, and obey checked native division and mathematical quotients on reobserved widths when generated construction is selected.",
    source := "base/reinterpretarray.jl:263-272; doc/src/manual/interfaces.md:217-239", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.IndexStyleContract, thm := none },
  { id := "reinterpretarray-static-style-parameter", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["IndexStyle(::IndexSCartesian2{K}, ::IndexSCartesian2{K}) where {K}"],
    statement := "Combining two equal static styles forwards their full K to parameterized constructor dispatch; generated construction preserves K, specialized constructor results/errors/states are unrestricted and retained, and invalid type application precedes construction.",
    source := "base/reinterpretarray.jl:260,273", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticStyleParameterPreservation, thm := none },
  { id := "reinterpretarray-index-identity", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["to_index(i::SCartesianIndex2)"],
    statement := "The scalar index conversion preserves the complete runtime channel parameter and both native coordinate fields, including non-native parameters and machine-integer extrema.",
    source := "base/reinterpretarray.jl:275-279", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ToIndexCoordinatePreservation, thm := some ``Models2Group12.toIndexCoordinatePreservation_proven },
  { id := "reinterpretarray-static-index-motion", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["nextind(::AbstractArray, i::SCartesianIndex2{K}) where {K}", "prevind(::AbstractArray, i::SCartesianIndex2{K}) where {K}"],
    statement := "Generated scalar index steps preserve K and modular adjacency; both stepping methods retain arbitrary K-specific constructor results and ignore the array; native valid channel coordinates roundtrip forward/backward across the full Int outer-coordinate domain.",
    source := "base/reinterpretarray.jl:280-283,288", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndexMotionContract, thm := none },
  { id := "reinterpretarray-static-range-constructor", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SCartesianIndices2{K}(indices2::AbstractUnitRange{Int}) where {K}"],
    statement := "The outer static-range constructor rejects non-native and at-most-one parameters before all effects, preserves parameter/range identity on generated inner construction, and retains every actually selected K/R-specific constructor result or exception.",
    source := "base/reinterpretarray.jl:288", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndicesConstructorContract, thm := some ``Models2Group12.staticIndicesConstructorContract_proven },
  { id := "reinterpretarray-static-reshaped-eachindex", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["eachindex(::IndexSCartesian2{K}, A::ReshapedReinterpretArray) where {K}"],
    statement := "Reshaped eachindex first queries the actual parent with linear style, preserves its errors and post-call world, and retains exact range/parameter identity in every known-constructor result.",
    source := "base/reinterpretarray.jl:290", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticReshapedEachindexContract, thm := none },




  { id := "reinterpretarray-static-range-size", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["size(iter::SCartesianIndices2{K}) where K"],
    statement := "The size result preserves exact K and the actual observed range length; the range length is called once using the original range object, including failure traces.",
    source := "base/reinterpretarray.jl:298", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndicesSizeContract, thm := some ``Models2Group12.staticIndicesSizeContract_proven },
  { id := "reinterpretarray-static-range-axes", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["axes(iter::SCartesianIndices2{K}) where K"],
    statement := "The second axis preserves original range identity; native K yields a pure OneTo with endpoint max(0,K), while non-native OneTo selection is called once with unchanged argument and retains its actual result or exception.",
    source := "base/reinterpretarray.jl:299", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndicesAxesContract, thm := none },

  { id := "reinterpretarray-static-generated-conversion-order", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SCartesianIndex2{K} generated conversion/new validation"],
    statement := "A wrong first field-conversion return does not suppress the second conversion or its effects/errors; generated new validates returned field types only after all conversion expressions complete.",
    source := "base/reinterpretarray.jl:275-278; base/essentials.jl:1453-1489", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticGeneratedConversionPrecedence, thm := some ``Models2Group12.staticGeneratedConversionPrecedence_proven },
  { id := "reinterpretarray-static-constructor-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SCartesianIndex2{K}(i,j) generated/custom dispatch"],
    statement := "Actual constructor selection precedes generated field handling, including K-specific methods on native coordinates. Every selected method receives K/i/j exactly once and preserves its arbitrary result/error; the generated native Int/Int case remains concrete and effect-free.",
    source := "base/reinterpretarray.jl:275-278", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticConstructorDispatchContract, thm := none },
  { id := "reinterpretarray-static-range-first", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["first(iter::SCartesianIndices2{K}) where {K}"],
    statement := "The first range endpoint is observed before construction; generated results preserve K and channel one, native endpoint coordinates remain exact, and endpoint failures preserve their mutable world.",
    source := "base/reinterpretarray.jl:301", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndicesFirstContract, thm := none },
  { id := "reinterpretarray-static-range-last", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["last(iter::SCartesianIndices2{K}) where {K}"],
    statement := "The last range endpoint is observed before constructor selection and K conversion; generated results preserve K and native coordinate arguments, while endpoint failures preserve their mutable world.",
    source := "base/reinterpretarray.jl:302", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndicesLastContract, thm := none },
  { id := "reinterpretarray-static-endpoint-custom-results", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["first(iter::SCartesianIndices2{K}) where {K}", "last(iter::SCartesianIndices2{K}) where {K}"],
    statement := "Both endpoint methods call each selected constructor with unchanged K and pre-conversion endpoint in the required argument positions and retain every arbitrary returned runtime value or error.",
    source := "base/reinterpretarray.jl:301,302", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticEndpointCustomConstructorContract, thm := none },
  { id := "reinterpretarray-static-range-getindex", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}"],
    statement := "When the outer/Bool/axes/tuple/failing-helper methods are their actual defaults, bounds-enabled lookup rejects out-of-range native first coordinates before all custom effects; elided checks preserve the first range lookup failure, and native range elements produce exact indices with no conversion effects when the generated constructor is selected.",
    source := "base/reinterpretarray.jl:304-307; base/abstractarray.jl:682-685,721-728; base/essentials.jl:389-393", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIndicesGetContract, thm := none },
  { id := "reinterpretarray-static-bounds-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}"],
    statement := "Actual selected checkbounds, Bool checkbounds, axes and tuple/non-tuple checking retain their exact arguments, arbitrary returns, effects and exceptions. The default wrapper consumes only Bool, preserves successful custom failed-bounds returns, and reports missing non-tuple methods at the correct call.",
    source := "base/reinterpretarray.jl:304-307; base/abstractarray.jl:682-685,722-728; base/essentials.jl:18-19,389-393", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticBoundsDispatchContract, thm := some ``Models2Group12.staticBoundsDispatchContract_proven },
  { id := "reinterpretarray-static-bounds-native", juliaFile := "base/abstractarray.jl",
    juliaFns := ["checkbounds_indices(::Type{Bool}, ::Tuple, ::Tuple)"],
    statement := "Default concrete bounds recursion over every native-sized tuple of native OneTo axes is pure and equals mathematical rectangular membership, with omitted dimensions of extent one and extra dimensions required to be singleton.",
    source := "base/abstractarray.jl:722-728; base/range.jl:860", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticBoundsNativeAxesContract, thm := none },
  { id := "reinterpretarray-static-bounds-trailing", juliaFile := "base/abstractarray.jl",
    juliaFns := ["checkbounds_indices(::Type{Bool}, ::Tuple, ::Tuple{})"],
    statement := "Trailing-axis all preserves actual length/equality/missing-test errors and state, suppresses later work after false, continues after missing, and lets a later false dominate missing. Non-Bool native predicates fail their Bool context.",
    source := "base/abstractarray.jl:728; base/anyall.jl:204-220,237-257", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticBoundsTrailingContract, thm := none },
  { id := "reinterpretarray-static-getindex-custom-result", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["getindex(iter::SCartesianIndices2{K}, i::Int, j::Int) where {K}"],
    statement := "Scalar lookup makes at most one selected custom constructor call using the exact K and requested first coordinate; its observed arbitrary returned value becomes the public result without reinterpretation.",
    source := "base/reinterpretarray.jl:304", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticGetCustomConstructorContract, thm := none },
  { id := "reinterpretarray-static-field-observation", juliaFile := "base/boot.jl",
    juliaFns := ["Core.getfield(raw_indexed_iterate_result, numeric_field)"],
    statement := "Numeric raw-result field observation returns exactly the stored value or distinguishes BoundsError, UndefRefError and TypeError without defaults or state changes.",
    source := "base/docs/basedocs.jl:2609-2620; base/boot.jl:497-499; runtime src/builtins.c:1173-1235", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticFieldObservationContract, thm := some ``Models2Group12.staticFieldObservationContract_proven },
  { id := "reinterpretarray-static-tuple-destructuring", juliaFile := "base/tuple.jl",
    juliaFns := ["indexed_iterate(::Tuple, ::Int, state=1)", "SCartesianIndices2 iterate state destructuring"],
    statement := "Concrete tuple destructuring reads the required leading two or three values, ignores extras, preserves the world and reports BoundsError for every too-short tuple, without invoking arbitrary dispatch.",
    source := "base/reinterpretarray.jl:309-325; base/tuple.jl:161; doc/src/manual/functions.md:394-410", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticTupleDestructuringContract, thm := some ``Models2Group12.staticTupleDestructuringContract_proven },
  { id := "reinterpretarray-static-final-state-field", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SCartesianIndices2 iterate custom destructuring"],
    statement := "For every custom indexed_iterate method, changing only its final returned second field, including absent or undefined layouts, cannot change destructuring output, error or mutable state.",
    source := "base/reinterpretarray.jl:309-325; doc/src/manual/functions.md:394-410,585-590", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticFinalDestructuringFieldIgnored, thm := some ``Models2Group12.staticFinalDestructuringFieldIgnored_proven },
  { id := "reinterpretarray-static-initial-iteration", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["iterate(iter::SCartesianIndices2{K}) where {K}"],
    statement := "Initial iteration propagates the first range-call error/state, stops immediately on nothing, and returns state channel one with its original item payload; native item payloads yield the exact K-preserving index when the generated constructor is selected.",
    source := "base/reinterpretarray.jl:309-314; doc/src/manual/interfaces.md:8-15", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticInitialIterationContract, thm := none },
  { id := "reinterpretarray-static-stateful-iteration", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}"],
    statement := "When generated construction is selected, stateful iteration with native returned coordinates produces their exact index and interior native channels advance without effects and preserve the outer iteration state, while boundary parent-step failures preserve state2 and the returned world. All custom and malformed state domains remain quantified.",
    source := "base/reinterpretarray.jl:316-325; doc/src/manual/interfaces.md:8-15", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticStatefulIterationContract, thm := none },
  { id := "reinterpretarray-static-iteration-custom-result", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["iterate(iter::SCartesianIndices2{K}) where {K}", "iterate(iter::SCartesianIndices2{K}, (state1, item2, state2)) where {K}"],
    statement := "Both iteration methods preserve any selected constructor result as the item while returning the original pre-conversion channel/outer-item state. Custom calls receive exactly K and the returned state payloads; exhaustion makes no constructor call.",
    source := "base/reinterpretarray.jl:309,316", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticIterationCustomConstructorContract, thm := none },
  { id := "reinterpretarray-static-simd-metadata", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SimdLoop.simd_outer_range(iter::SCartesianIndices2)", "SimdLoop.simd_inner_length(::SCartesianIndices2{K}, ::Any) where K", "SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}"],
    statement := "SIMD metadata methods retain the original outer range and exact K; when generated index construction is selected, the native outer coordinate is preserved and the inner coordinate increments modulo the full signed 64-bit range without effects.",
    source := "base/reinterpretarray.jl:327-331", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticSimdContract, thm := some ``Models2Group12.staticSimdContract_proven },
  { id := "reinterpretarray-static-simd-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["SimdLoop.simd_index(::SCartesianIndices2{K}, Ilast::Int, I1::Int) where {K}"],
    statement := "SIMD index construction passes the exact K, natively wrapped inner coordinate and original outer coordinate to every selected K-specific constructor and preserves its arbitrary actual return or error.",
    source := "base/reinterpretarray.jl:329-331", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticSimdConstructorDispatchContract, thm := some ``Models2Group12.staticSimdConstructorDispatchContract_proven },
  { id := "reinterpretarray-static-maybe-reshape", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_maybe_reshape(::IndexSCartesian2, A::AbstractArray, I...)", "_maybe_reshape(::IndexSCartesian2, A::ReshapedReinterpretArray, I...)"],
    statement := "The generic reshape fallback calls Cartesian dispatch once with every original arbitrary index payload and preserves its actual return/error; the reshaped specialization preserves every observation of the original array.",
    source := "base/reinterpretarray.jl:333,334", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticMaybeReshapeContract, thm := some ``Models2Group12.staticMaybeReshapeContract_proven },
  { id := "reinterpretarray-static-cartesian-fallback", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_getindex(::IndexSCartesian2, A::AbstractArray, I::Vararg{Int, N}) where {N}", "_setindex!(::IndexSCartesian2, A::AbstractArray, v, I::Vararg{Int, N}) where {N}"],
    statement := "The reused native-vararg get/set fallbacks call selected Cartesian dispatch exactly once with unchanged array, value where present, and all machine-sized indices, preserving each actual return or error.",
    source := "base/reinterpretarray.jl:337-344", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticCartesianFallbackContract, thm := some ``Models2Group12.staticCartesianFallbackContract_proven },
  { id := "reinterpretarray-eachindex-abstract-flow", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["eachindex(style::IndexSCartesian2, A::AbstractArray)"],
    statement := "Generic eachindex obtains parent(A) once, passes the exact result and unchanged style to eachindex once, and preserves returned values, exceptions and state transitions.",
    source := "base/reinterpretarray.jl:365; doc/src/manual/interfaces.md:211-233", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.AbstractEachIndexFlow, thm := some ``Models2Group12.abstractEachIndexFlow_proven },
  { id := "reinterpretarray-parent-field-observations", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["parent(a::ReinterpretArray)"],
    statement := "parent(a) preserves every observation of the original stored parent, including reference and alias identity.",
    source := "base/reinterpretarray.jl:369; parent-field invariant", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StoredParentObservations, thm := some ``Models2Group12.storedParentObservations_proven },
  { id := "reinterpretarray-parent-metadata-observations", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["dataids(a::ReinterpretArray)", "has_offset_axes(a::ReinterpretArray)"],
    statement := "dataids and has_offset_axes each invoke the selected parent query exactly once and preserve all result, exception and state observations.",
    source := "base/reinterpretarray.jl:370,401; parent-query invariant", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ParentMetadataObservations, thm := some ``Models2Group12.parentMetadataObservations_proven },
  { id := "reinterpretarray-unaliascopy-flow", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["unaliascopy(a::NonReshapedReinterpretArray{T}) where {T}", "unaliascopy(a::ReshapedReinterpretArray{T}) where {T}"],
    statement := "unaliascopy copies the stored parent once, then reinterprets the actual copy using the original target type and correct plain or reshape overload, preserving outcomes and state transitions.",
    source := "base/reinterpretarray.jl:371-372; ordered-dispatch invariant", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.UnaliasCopyFlow, thm := some ``Models2Group12.unaliasCopyFlow_proven },
  { id := "reinterpretarray-zero-dimensional-shape", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["size(a::NonReshapedReinterpretArray{T,0}) where {T}", "axes(a::NonReshapedReinterpretArray{T,0}) where {T}"],
    statement := "A zero-dimensional nonreshaped view has zero size components and zero axes, independently of its parent and element layouts.",
    source := "base/reinterpretarray.jl:385,399; doc/src/manual/interfaces.md:211-233", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ZeroDimensionalShape, thm := some ``Models2Group12.zeroDimensionalShape_proven },
  { id := "reinterpretarray-cconvert-parent-route", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["cconvert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S}"],
    statement := "cconvert calls the stored parent's selected conversion once for Ptr{S}, retaining its arbitrary returned object, failure and state transitions.",
    source := "base/reinterpretarray.jl:410; doc/src/manual/calling-c-and-fortran-code.md:268-275", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.CconvertParentObservations, thm := some ``Models2Group12.cconvertParentObservations_proven },
  { id := "reinterpretarray-unsafe-convert-view", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr{T}}, a::ReinterpretArray{T,N,S} where N) where {T,S}"],
    statement := "unsafe_convert requests Ptr{S} from the stored parent first, preserves native 64-bit addresses when the Core constructor is selected, and retains every actual target-specific custom constructor argument, arbitrary result, error and state transition even for native input shapes.",
    source := "base/reinterpretarray.jl:411; base/boot.jl:1203; base/pointer.jl:3-9", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.UnsafeConvertViewObservations, thm := none },
  { id := "reinterpretarray-type-element-size", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["elsize(::Type{<:ReinterpretArray{T,<:Any,S,A}}) where {T,S,A}"],
    statement := "For every selected type-size query, scalar equality and parent-type elsize operation, element size queries target then source, preserves actual comparison and Bool assertion effects, calls only parent-type elsize on equality, and otherwise repeats the target-size query while retaining every result, error and state transition.",
    source := "base/reinterpretarray.jl:403-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.DynamicElementSizeProtocol, thm := none },
  { id := "reinterpretarray-wrapper-pointer-route", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["check_ptr_indexable(a::ReshapedArray)", "check_ptr_indexable(a::FastContiguousSubArray)"],
    statement := "Both concrete wrappers project their actual stored parent and preserve exactly one selected query, including its argument, value or error, and entire state transition.",
    source := "base/reinterpretarray.jl:425-426; base/reshapedarray.jl:258; base/subarray.jl:86", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.WrapperPointerProtocol, thm := some ``Models2Group12.wrapperPointerProtocol_proven },
  { id := "reinterpretarray-static-assignment-route", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["isassigned(a::ReinterpretArray, inds::SCartesianIndex2)"],
    statement := "Static assignment queries pass the original parent and outer coordinate exactly once; arbitrary user result types, exception payloads and state changes are retained.",
    source := "base/reinterpretarray.jl:433", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticAssignmentProtocol, thm := some ``Models2Group12.staticAssignmentProtocol_proven },
  { id := "reinterpretarray-assignment-fallback-guard", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_isassigned_ra(a::ReinterpretArray, inds...)"],
    statement := "The internal fallback cannot reject a successful Boolean bounds guard for any accepted heterogeneous vararg tuple or pointer-indexability flag; it does not promise initialized-storage checks.",
    source := "base/reinterpretarray.jl:432-434", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.AssignmentFallbackGuard, thm := some ``Models2Group12.assignmentFallbackGuard_proven },
  { id := "reinterpretarray-padding-display-protocol", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["showerror(io::IO, p::PaddingError)"],
    statement := "Formatting receives the actual Type objects and exact literal segments before printing its actual result to the original IO; arbitrary errors, results and state effects remain in source order.",
    source := "base/reinterpretarray.jl:736-743", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PaddingDisplayProtocol, thm := some ``Models2Group12.paddingDisplayProtocol_proven },
  { id := "reinterpretarray-primitive-width-arithmetic", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_is_scalar_reinterpret_applicable(T, S)"],
    statement := "The concrete Core dependency computes declared width by uint32_t modular size arithmetic and the seven unused-bit flags, independently specified mathematically.",
    source := "Dependency invariant: base/reinterpretarray.jl:470; src/julia.h:1693-1697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PrimitiveWidthArithmetic81, thm := none },
  { id := "reinterpretarray-core-bitsizeof-contract", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_is_scalar_reinterpret_applicable(T, S)"],
    statement := "The Core dependency accepts exactly primitive DataType objects or their primitive instances, returns their mathematical declared width, and raises ErrorException on every other value.",
    source := "base/essentials.jl:844-878; src/builtins.c:680-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.CoreBitSizeContract81, thm := none },
  { id := "reinterpretarray-scalar-applicability-flow", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_is_scalar_reinterpret_applicable(T, S)"],
    statement := "All default and selected primitive predicates are evaluated S before T with short-circuit Bool consumption; arbitrary errors/world changes propagate, and both true predicates lead to equality of the actual primitive declared widths or the native ErrorException.",
    source := "Invariant: base/reinterpretarray.jl:469-471; base/essentials.jl:844-878 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ScalarApplicabilityFlow81, thm := none },
  { id := "reinterpretarray-ispacked-layout-low-bit", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["ispacked(T)"],
    statement := "For a concrete DataTypeLayout, ispacked returns true precisely when its low flags bit is zero and preserves the entire world.",
    source := "Invariant: base/reinterpretarray.jl:827-829; base/runtime_internals.jl:702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PackedLayoutLowBit, thm := some ``Models2Group12.packedLayoutLowBit_proven },
  { id := "reinterpretarray-ispacked-datatype-runtime", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["ispacked(T)"],
    statement := "For any DataType metadata operations, ispacked preserves layout-null UndefRefError, the exact loader failure or divergence, and successful post-load world while returning the complement of the loaded low flags bit.",
    source := "Invariant: base/reinterpretarray.jl:827-829; base/runtime_internals.jl:642-646,701-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PackedDatatypeObservations, thm := some ``Models2Group12.packedDatatypeObservations_proven },
  { id := "reinterpretarray-ispacked-custom-flow", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["ispacked(T)"],
    statement := "Arbitrary selected datatype_haspadding and ! calls occur in the required order with observed intermediate values, exact return/error identity, world continuity and divergence; only actual Bool values use native negation.",
    source := "Invariant: base/reinterpretarray.jl:827-829 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PackedCustomFlow, thm := none },
  { id := "reinterpretarray-struct-padding-comparison", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["struct_subpadding(Out, In)"],
    statement := "For arbitrary selected non-padding queries and equality, struct_subpadding preserves output/input order, exact operands, state continuity and exception precedence, and returns equality's arbitrary result without adding a Bool assertion.",
    source := "base/reinterpretarray.jl:815-817 (internal observation invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StructSubpaddingObservations, thm := some ``Models2Group12.structSubpaddingObservations_proven },
  { id := "reinterpretarray-packed-size-dispatch", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["packedsize(T)"],
    statement := "For arbitrary type/object, metadata, negation, mask, count and sizeof dispatch, packedsize preserves errors and exact arguments, uses native Boolean complement or selected custom negation, rejects non-Bool conditions before either exclusive branch, counts the actual returned mask, and retains the terminal value/error/state.",
    source := "base/reinterpretarray.jl:819-825 (internal branch and argument invariants)", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PackedSizeContract, thm := none },
  { id := "reinterpretarray-array-padding-finite-protocol", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["array_subpadding(S, T)"],
    statement := "Every finite generic array_subpadding execution has the exact target/source packing, source/target mask, target/source emptiness and source/target length prefix; actual intermediate values and callback worlds are retained, first exceptions terminate, and loop returns have concrete mismatch or final modular-reset witnesses.",
    source := "Invariant: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ArrayPaddingFiniteProtocol, thm := none },
  { id := "reinterpretarray-array-padding-counter-advance", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["array_subpadding(S, T)"],
    statement := "For every signed native Int index and arbitrary length, counter advancement satisfies modulo-2^64 increment and signed native comparison, or exactly one selected comparison with actual incremented index, preserving all outcomes, effects and divergence.",
    source := "Invariant: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ArrayPaddingCounterAdvance, thm := none },
  { id := "reinterpretarray-array-padding-boolean-consumption", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["array_subpadding(S, T)"],
    statement := "The source guard preserves every world on native Bool results and raises the modeled TypeError for every non-Bool value.",
    source := "Invariant: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ArrayPaddingBooleanConsumption, thm := some ``Models2Group12.arrayPaddingBooleanConsumption_proven },
  { id := "reinterpretarray-array-padding-entry-transparency", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["array_subpadding(S, T)"],
    statement := "Initial target packing and then source packing preserve their exact failure, divergence, non-Bool TypeError and stopping Bool result with every intermediate world and no later call.",
    source := "Invariant: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ArrayPaddingEntryTransparency, thm := none },
  { id := "reinterpretarray-array-padding-first-read-transparency", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["array_subpadding(S, T)"],
    statement := "At every initial counter pair, the loop preserves first source and conditional target read failures/divergence, native mismatch results and arbitrary selected negation outcomes without mask or length correctness assumptions.",
    source := "Invariant: base/reinterpretarray.jl:775-813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.ArrayPaddingFirstReadTransparency, thm := none },
  { id := "reinterpretarray-permission-checks", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["check_readable(a::ReinterpretArray{T, N, S} where N) where {T,S}", "check_writable(a::ReinterpretArray{T, N, S} where N) where {T,S}"],
    statement := "For arbitrary selected padding, negation, conversion and exception constructors, cached permissions bypass all calls; read/write retain their exact operand orders and errors; non-Bool conditions fail before error construction; generated PaddingError converts both Type fields before final validation; selected constructor results are genuinely thrown with their exact payload and state.",
    source := "base/reinterpretarray.jl:237-254,736-739; base/essentials.jl:1456-1488; doc/src/manual/types.md:1321-1344", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.PermissionContract, thm := none },
  { id := "reinterpretarray-static-mapreduce-routing", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["_mapreduce(f::F, op::OP, style::IndexSCartesian2{K}, A::AbstractArrayOrBroadcasted) where {F,OP,K}"],
    statement := "For arbitrary stateful dispatch and user exception payloads, static Cartesian reduction preserves lookup errors and arguments, performs true native tuple bounds and Boolean checks, isolates empty reductions from endpoints, orders first before last, respects K/R-specific size/first/last methods and their complete iterator arguments, preserves generated native coordinates and arbitrary custom endpoint results, and returns the selected terminal value/error/state unchanged.",
    source := "base/reinterpretarray.jl:946-954; base/tuple.jl:33 (internal routing and evaluation invariants)", status := .todo,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.StaticMapreduceContract, thm := none },
  { id := "reinterpretarray-default-mapreduce-forwarding", juliaFile := "base/reinterpretarray.jl",
    juliaFns := ["mapreduce_impl(f::F, op::OP, A::AbstractArrayOrBroadcasted, ifirst::SCartesianIndex2, ilast::SCartesianIndex2) where {F,OP}"],
    statement := "For arbitrary selected methods and exception payloads, the default reduction helper performs one tuning query and then one worker dispatch; it preserves the original function, operator, array, complete endpoint objects, tuning result, callback state changes and terminal value or error, allowing different endpoint type parameters.",
    source := "base/reinterpretarray.jl:984-985 (internal forwarding invariant)", status := .proven,
    prop := ``JuliaLean.Proofs.base.reinterpretarray.Models2Group12.DefaultMapreduceForwarding, thm := some ``Models2Group12.defaultMapreduceForwarding_proven }
]

end JuliaLean.Proofs.base.reinterpretarray

