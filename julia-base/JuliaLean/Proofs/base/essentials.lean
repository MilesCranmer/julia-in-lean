import JuliaLean.Proofs.base.essentials.cartesian_empty
import JuliaLean.Proofs.base.boot
import JuliaLean.base.boot
import JuliaLean.base.expr
import JuliaLean.base.essentials
import JuliaLean.base.int
import JuliaLean.Registry.Types


section

/-!
Properties of the type-object functions of `base/boot.jl` and `base/essentials.jl`.
-/

namespace JuliaLean.BootCov.Types

open JuliaLean
open JuliaLean.BootCov

/-- `unwrap_unionall` (`base/essentials.jl:544-550`) strips every `where`, and
`rewrap_unionall(unwrap_unionall(u), u)` (lines 552-558) rebuilds `u` exactly for every
`UnionAll` Julia can construct; `rewrap_unionall(t, u)` is `t` when `u` is not a
`UnionAll`, and the `Vararg` method (lines 560-571) returns a `Vararg` without an element
type unchanged. -/
def UnwrapRewrap : Prop :=
  (∀ u : JType, ∀ v b, unwrapUnionall u ≠ .unionAll v b) ∧
  (∀ u : JType, NormalSpine u → rewrapUnionall (unwrapUnionall u) u = .ok u) ∧
  (∀ t u : JType, (∀ v b, u ≠ .unionAll v b) → rewrapUnionall t u = .ok t) ∧
  (∀ (N : Option JType) (u : JType), rewrapUnionallVararg none N u = .ok (.vararg none N)) ∧
  (∀ (T : JType) (N : Option JType) (u : JType), (∀ v b, u ≠ .unionAll v b) →
    rewrapUnionallVararg (some T) N u = .ok (.vararg (some T) N))

theorem unwrap_not_unionAll : (u : JType) → ∀ v b, unwrapUnionall u ≠ .unionAll v b
  | .unionAll _ b', v, b => by simp only [unwrapUnionall]; exact unwrap_not_unionAll b' v b
  | .dt _ _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .union _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .bottom, v, b => by intro h; simp [unwrapUnionall] at h
  | .tvar _ _ _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .vararg _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .typeApp _ _, v, b => by intro h; simp [unwrapUnionall] at h
  | .intParam _, v, b => by intro h; simp [unwrapUnionall] at h
  | .names _, v, b => by intro h; simp [unwrapUnionall] at h
  | .other _, v, b => by intro h; simp [unwrapUnionall] at h

theorem rewrap_unwrap : (u : JType) → NormalSpine u → rewrapUnionall (unwrapUnionall u) u = .ok u
  | .unionAll v b, h => by
    simp only [NormalSpine] at h
    simp only [unwrapUnionall, rewrapUnionall, rewrap_unwrap b h.2, bind, Except.bind]
    exact unionAllCtor_normal v b h.1
  | .dt _ _ _, _ => by rfl
  | .union _ _, _ => by rfl
  | .bottom, _ => by rfl
  | .tvar _ _ _ _, _ => by rfl
  | .vararg _ _, _ => by rfl
  | .typeApp _ _, _ => by rfl
  | .intParam _, _ => by rfl
  | .names _, _ => by rfl
  | .other _, _ => by rfl

theorem unwrapRewrap : UnwrapRewrap := by
  refine ⟨unwrap_not_unionAll, rewrap_unwrap, ?_, fun _ _ => rfl, ?_⟩
  · intro t u h
    cases u with
    | unionAll v b => exact absurd rfl (h v b)
    | _ => rfl
  · intro T N u h
    cases u with
    | unionAll v b => exact absurd rfl (h v b)
    | _ => rfl

/-- The `Vararg` helpers (`base/essentials.jl:589-613`): `isvarargtype` recognises exactly
`Vararg`; `unwrapva(Vararg{T,N})` is `T`, `unwrapva(Vararg)` is `Any` and other types are
unchanged; `unconstrain_vararg_length(va)` is `Vararg{unwrapva(va)}` without a length; and
`isvatuple(t)` holds exactly when `unwrap_unionall(t)` is a `DataType` whose last
parameter is a `Vararg`. -/
def VarargHelpers : Prop :=
  (∀ t : JType, isvarargtype t = true ↔ ∃ T N, t = .vararg T N) ∧
  (∀ (T : JType) (N : Option JType), unwrapva (.vararg (some T) N) = T) ∧
  (∀ N : Option JType, unwrapva (.vararg none N) = .dt "Any" true []) ∧
  (∀ t : JType, isvarargtype t = false → unwrapva t = t) ∧
  (∀ va : JType, unconstrainVarargLength va = .vararg (some (unwrapva va)) none) ∧
  (∀ t : JType, isvatuple t = true ↔
    ∃ n abs ps T N, unwrapUnionall t = .dt n abs ps ∧ ps.getLast? = some (.vararg T N))

theorem varargHelpers : VarargHelpers := by
  refine ⟨?_, fun _ _ => rfl, fun _ => rfl, ?_, fun _ => rfl, ?_⟩
  · intro t
    cases t <;> simp [isvarargtype]
  · intro t h
    cases t with
    | vararg T N => simp [isvarargtype] at h
    | _ => rfl
  · intro t
    simp only [isvatuple]
    cases hu : unwrapUnionall t with
    | dt n abs ps =>
      constructor
      · intro h
        cases hl : ps.getLast? with
        | none => simp [hl] at h
        | some p =>
          simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h
          cases p with
          | vararg T N => exact ⟨n, abs, ps, T, N, rfl, hl⟩
          | _ => simp [isvarargtype] at h
      · rintro ⟨n', abs', ps', T, N, he, hl⟩
        simp only [JType.dt.injEq] at he
        obtain ⟨_, _, h3⟩ := he
        subst h3
        cases ps with
        | nil => simp at hl
        | cons a l => simp [hl, isvarargtype]
    | _ => simp

/-- `datatype_min_ninitialized(t)` (`base/essentials.jl:617-646`) counts the fields every
instance defines: an abstract type has none; a tuple type `Tuple{P1,...,Pn}` has `n`, minus
one for a trailing unbounded `Vararg`, plus `k - 1` for a trailing `Vararg{T,k}`; a
`NamedTuple` with known names has one per name; a `NamedTuple{names,Tuple{...}}` with
unknown names counts like its tuple; any other struct has its field count minus its
possibly-undefined fields. -/
def MinNinitialized : Prop :=
  (∀ nf nu n ps, datatypeMinNinitialized nf nu (.dt n true ps) = 0) ∧
  (∀ nf nu ps, (∀ T N, ps.getLast? ≠ some (.vararg T N)) →
    datatypeMinNinitialized nf nu (.dt "Tuple" false ps) = ps.length) ∧
  (∀ nf nu ps T, datatypeMinNinitialized nf nu (.dt "Tuple" false (ps ++ [.vararg T none])) =
    ps.length) ∧
  (∀ nf nu ps T (k : Int), datatypeMinNinitialized nf nu
      (.dt "Tuple" false (ps ++ [.vararg T (some (.intParam k))])) = ps.length + k) ∧
  (∀ nf nu syms rest, datatypeMinNinitialized nf nu (.dt "NamedTuple" false (.names syms :: rest)) =
    syms.length) ∧
  (∀ nf nu v tps rest, (∀ s, v ≠ .names s) →
    datatypeMinNinitialized nf nu (.dt "NamedTuple" false (v :: .dt "Tuple" false tps :: rest)) =
      tupleMinFields tps) ∧
  (∀ nf nu n ps, n ≠ "Tuple" → n ≠ "NamedTuple" →
    datatypeMinNinitialized nf nu (.dt n false ps) = (nf n : Int) - nu n) ∧
  (∀ nf nu (u : JType), datatypeMinNinitialized nf nu u =
    datatypeMinNinitialized nf nu (unwrapUnionall u))

theorem unwrap_idem : (u : JType) → unwrapUnionall (unwrapUnionall u) = unwrapUnionall u
  | .unionAll _ b => by simp only [unwrapUnionall]; exact unwrap_idem b
  | .dt _ _ _ => by rfl
  | .union _ _ => by rfl
  | .bottom => by rfl
  | .tvar _ _ _ _ => by rfl
  | .vararg _ _ => by rfl
  | .typeApp _ _ => by rfl
  | .intParam _ => by rfl
  | .names _ => by rfl
  | .other _ => by rfl

theorem tupleMinFields_plain (ps : List JType) (h : ∀ T N, ps.getLast? ≠ some (.vararg T N)) :
    tupleMinFields ps = ps.length := by
  simp only [tupleMinFields]
  split
  · omega
  · cases hl : ps.getLast? with
    | none => rfl
    | some p =>
      cases p with
      | vararg T N => exact absurd hl (h T N)
      | _ => rfl

theorem tupleMinFields_va (ps : List JType) (T : Option JType) :
    tupleMinFields (ps ++ [.vararg T none]) = ps.length := by
  simp only [tupleMinFields, List.getLast?_concat, List.length_append, List.length_cons,
    List.length_nil]
  split <;> omega

theorem tupleMinFields_vaN (ps : List JType) (T : Option JType) (k : Int) :
    tupleMinFields (ps ++ [.vararg T (some (.intParam k))]) = ps.length + k := by
  simp only [tupleMinFields, List.getLast?_concat, List.length_append, List.length_cons,
    List.length_nil]
  split <;> omega

theorem minNinitialized : MinNinitialized := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro nf nu n ps; simp [datatypeMinNinitialized, unwrapUnionall]
  · intro nf nu ps h
    simp [datatypeMinNinitialized, unwrapUnionall, tupleMinFields_plain ps h]
  · intro nf nu ps T
    simp [datatypeMinNinitialized, unwrapUnionall, tupleMinFields_va]
  · intro nf nu ps T k
    simp [datatypeMinNinitialized, unwrapUnionall, tupleMinFields_vaN]
  · intro nf nu syms rest; simp [datatypeMinNinitialized, unwrapUnionall]
  · intro nf nu v tps rest h
    cases v with
    | names s => exact absurd rfl (h s)
    | _ => simp [datatypeMinNinitialized, unwrapUnionall]
  · intro nf nu n ps h1 h2; simp [datatypeMinNinitialized, unwrapUnionall, h1, h2]
  · intro nf nu u
    simp only [datatypeMinNinitialized, unwrap_idem]

/-- `has_typevar(t, v)` (`base/essentials.jl:1288`) finds `v` in its own body and in type
parameters, and a `where`-bound variable is not free in the `UnionAll` that binds it. -/
def HasTypevarBehaviour : Prop :=
  (∀ i n lb ub, hasTypevar (.tvar i n lb ub) (.tvar i n lb ub) = true) ∧
  (∀ i n lb ub name abs ps, hasTypevar (.dt name abs ps) (.tvar i n lb ub) =
    (freeVarsList ps).contains i) ∧
  (∀ i n lb ub b, i ∉ freeVars lb → i ∉ freeVars ub →
    hasTypevar (.unionAll (.tvar i n lb ub) b) (.tvar i n lb ub) = false)

theorem hasTypevarBehaviour : HasTypevarBehaviour := by
  refine ⟨?_, ?_, ?_⟩
  · intro i n lb ub; simp [hasTypevar, freeVars, varId]
  · intro i n lb ub name abs ps; simp [hasTypevar, freeVars, varId]
  · intro i n lb ub b h1 h2
    simp [hasTypevar, freeVars, freeVarsBound, varId, h1, h2]

/-- `rename_unionall(u)` (`base/essentials.jl:574-582`) returns a non-`UnionAll` unchanged,
and renames the variable of `D{T} where T` to a fresh `TypeVar` with the same name and
bounds; `widen_diagonal` (lines 585-587) returns the runtime's answer. -/
def RenameUnionall : Prop :=
  (∀ next u, (∀ v b, u ≠ .unionAll v b) → renameUnionall next u = .ok (u, next)) ∧
  (∀ (next i : Nat) (n : String) (lb ub : JType) (name : String) (abs : Bool),
    renameUnionall next (.unionAll (.tvar i n lb ub) (.dt name abs [.tvar i n lb ub])) =
      .ok (.unionAll (.tvar next n lb ub) (.dt name abs [.tvar next n lb ub]), next + 1)) ∧
  (∀ (w : JType → JType → JType) t r, widenDiagonal w t r = w t r)

theorem renameUnionall_spec : RenameUnionall := by
  refine ⟨?_, ?_, fun _ _ _ => rfl⟩
  · intro next u h
    cases u with
    | unionAll v b => exact absurd rfl (h v b)
    | _ => rfl
  · intro next i n lb ub name abs
    simp [renameUnionall, bind, Except.bind, pure, Except.pure, unionAllCtor, typeUnionall,
      hasTypevar, freeVars, freeVarsList, varId, instantiate, subst, substList]

end JuliaLean.BootCov.Types

end

section

/-!
Properties of the memory, array, `SimpleVector` and `Symbol` primitives.
-/

namespace JuliaLean.BootCov.Arrays

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

/-- `checkbounds(Bool, A, i)` for an `Array` or `Memory` (`base/essentials.jl:385-388`) is
true exactly when `i` is in `1:length(A)`, for every `Int` index and every length. -/
def CheckboundsBoolCorrect : Prop :=
  ∀ len i : JInt64, 0 ≤ len.val →
    (checkboundsBool len i = true ↔ 1 ≤ i.val ∧ i.val ≤ len.val)

theorem checkboundsBoolCorrect : CheckboundsBoolCorrect := by
  intro len i h0
  have hl := i64_bounds len
  have hi := i64_bounds i
  simp only [checkboundsBool, JInt.rem, JInt.wrap, sub_lit1_val, decide_eq_true_eq]
  by_cases hi0 : i.val = -(2:Int) ^ 63
  · have hw : wrapInt .i64 (i.val - 1) = 2 ^ 63 - 1 := by
      rw [hi0]; decide
    rw [hw, wrapU64_nonneg (2 ^ 63 - 1) (by omega) (by omega),
      wrapU64_nonneg len.val h0 (by omega)]
    omega
  · rw [wrapI64_small (i.val - 1) (by omega) (by omega)]
    rw [wrapU64_nonneg len.val h0 (by omega)]
    by_cases hp : 0 ≤ i.val - 1
    · rw [wrapU64_nonneg (i.val - 1) hp (by omega)]; omega
    · rw [wrapU64_neg (i.val - 1) (by omega) (by omega)]; omega

/-- Element access on `Memory`, `MemoryRef` and `Array` (`base/essentials.jl:395-406`,
1063-1082): `A[i]` throws `BoundsError` outside `1:length(A)`, otherwise reads the slot
(`UndefRefError` for an undefined one); `A[i] = x` then `A[i]` returns `x`;
`setindex!` returns its array; the `MemoryRef{T}` method converts first; and the access
order is `:monotonic` exactly for atomic memory. -/
def AccessSemantics : Prop :=
  (∀ (mem : Mem) (i : JInt64), mem.length < 2 ^ 63 →
    (¬(1 ≤ i.val ∧ i.val ≤ mem.length) → getindexMem mem i = .error .bounds) ∧
    (1 ≤ i.val ∧ i.val ≤ mem.length →
      getindexMem mem i = memoryrefget ⟨mem, (i.val - 1).toNat⟩ ∧
      ∀ x, (setindexMem mem x i >>= fun m => getindexMem m i) = .ok x)) ∧
  (∀ (len : JInt64) (a : Arr) (i : JInt64), 0 ≤ len.val →
    (¬(1 ≤ i.val ∧ i.val ≤ len.val) → getindexArr len a i = .error .bounds) ∧
    (1 ≤ i.val ∧ i.val ≤ len.val →
      getindexArr len a i = memoryrefget ⟨a.ref.mem, a.ref.off + (i.val - 1).toNat⟩)) ∧
  (∀ (len : JInt64) (a : Arr) (x : JVal) (i : JInt64), 0 ≤ len.val →
    ¬(1 ≤ i.val ∧ i.val ≤ len.val) → setindexArr len a x i = .error .bounds) ∧
  (∀ r, getindexRef r = memoryrefget r) ∧
  (∀ (conv : JVal → R JVal) r x e, conv x = .error e → setindexRefT conv r x = .error e) ∧
  (∀ (conv : JVal → R JVal) r x y, conv x = .ok y → setindexRefT conv r x = setindexRefAny r y) ∧
  defaultAccessOrder true = "monotonic" ∧ defaultAccessOrder false = "not_atomic" ∧
  (∀ mem : Mem, sizeMem mem = [mem.length]) ∧
  (∀ a : Arr, sizeArr a = a.dims ∧ ∀ m rest, a.dims = m :: rest → lengthVec a = .ok m)

theorem lit_len_val {n : Nat} (hl : n < 2 ^ 63) : (JInt.lit .i64 (n : Int)).val = n :=
  wrapI64_small _ (by omega) (by omega)

theorem getindexMem_oob {mem : Mem} {i : JInt64} (hl : mem.length < 2 ^ 63)
    (h : ¬(1 ≤ i.val ∧ i.val ≤ mem.length)) : getindexMem mem i = .error .bounds := by
  have hv : (JInt.lit .i64 mem.length).val = mem.length := lit_len_val hl
  have c := checkboundsBoolCorrect (JInt.lit .i64 mem.length) i (by rw [hv]; omega)
  rw [hv] at c
  have hf : checkboundsBool (JInt.lit .i64 mem.length) i = false := by
    cases hc : checkboundsBool (JInt.lit .i64 mem.length) i
    · rfl
    · exact absurd (c.1 hc) h
  unfold getindexMem checkbounds
  rw [hf]
  rfl

theorem getindexMem_in {mem : Mem} {i : JInt64} (hl : mem.length < 2 ^ 63)
    (h : 1 ≤ i.val ∧ i.val ≤ mem.length) :
    getindexMem mem i = memoryrefget ⟨mem, (i.val - 1).toNat⟩ := by
  have hv : (JInt.lit .i64 mem.length).val = mem.length := lit_len_val hl
  have c := checkboundsBoolCorrect (JInt.lit .i64 mem.length) i (by rw [hv]; omega)
  rw [hv] at c
  unfold getindexMem checkbounds
  rw [c.2 h]
  rfl

theorem setindexMem_in {mem : Mem} {i : JInt64} (x : JVal) (hl : mem.length < 2 ^ 63)
    (h : 1 ≤ i.val ∧ i.val ≤ mem.length) :
    setindexMem mem x i = .ok (mem.set (i.val - 1).toNat (some x)) := by
  have hv : (JInt.lit .i64 mem.length).val = mem.length := lit_len_val hl
  have c := checkboundsBoolCorrect (JInt.lit .i64 mem.length) i (by rw [hv]; omega)
  rw [hv] at c
  have hk : (i.val - 1).toNat < mem.length := by omega
  have e1 : checkbounds (checkboundsBool (JInt.lit .i64 mem.length)) i = .ok () := by
    unfold checkbounds; rw [c.2 h]; rfl
  have e2 : memoryrefset ⟨mem, (i.val - 1).toNat⟩ x =
      .ok ⟨mem.set (i.val - 1).toNat (some x), (i.val - 1).toNat⟩ := by
    unfold memoryrefset; exact if_pos hk
  unfold setindexMem
  rw [e1, e2]
  rfl

theorem accessSemantics : AccessSemantics := by
  refine ⟨?_, ?_, ?_, fun _ => rfl, ?_, ?_, rfl, rfl, fun _ => rfl, ?_⟩
  · intro mem i hl
    refine ⟨getindexMem_oob hl, fun h => ⟨getindexMem_in hl h, ?_⟩⟩
    intro x
    have hk : (i.val - 1).toNat < mem.length := by omega
    rw [setindexMem_in x hl h]
    rw [show ∀ (m : Mem) (f : Mem → R JVal), (Except.ok m >>= f) = f m from fun _ _ => rfl]
    have hl' : (mem.set (i.val - 1).toNat (some x)).length < 2 ^ 63 := by simp; exact hl
    rw [getindexMem_in hl' (by simp; omega)]
    generalize (i.val - 1).toNat = k at hk ⊢
    simp [memoryrefget, hk]
  · intro len a i h0
    have c := checkboundsBoolCorrect len i h0
    constructor
    · intro h
      have hf : checkboundsBool len i = false := by
        cases hc : checkboundsBool len i
        · rfl
        · exact absurd (c.1 hc) h
      simp [getindexArr, checkbounds, hf, bind, Except.bind]
    · intro h
      simp [getindexArr, checkbounds, c.2 h, bind, Except.bind]
  · intro len a x i h0 h
    have c := checkboundsBoolCorrect len i h0
    have hf : checkboundsBool len i = false := by
      cases hc : checkboundsBool len i
      · rfl
      · exact absurd (c.1 hc) h
    simp [setindexArr, checkbounds, hf, bind, Except.bind]
  · intro conv r x e h
    simp [setindexRefT, h, bind, Except.bind]
  · intro conv r x y h
    simp [setindexRefT, setindexRefAny, h, bind, Except.bind]
  · intro a
    refine ⟨rfl, fun m rest h => ?_⟩
    simp [lengthVec, h]

/-- `SimpleVector` indexing and iteration (`base/essentials.jl:1086-1109`): `v[i]` throws
`BoundsError` outside `1:length(v)`; `iterate(v, i)` yields `(v[i], i + 1)` for
`1 ≤ i ≤ length(v)` and `nothing` past the end; `firstindex`, `lastindex`, `keys`,
`axes`, `isempty` and `eltype` describe `1:length(v)`; `axes(v, d)` is `1:1` for `d > 1`;
`map` applies `f` to every element in order; `v[I]` collects `v[i]` for `i` in `I`;
equal svecs compare equal and svecs of different lengths compare unequal. -/
def SvecSemantics : Prop :=
  (∀ (v : SVec) (i : Int), (i < 1 ∨ i > v.length) → svecRef v i = .error .bounds) ∧
  (∀ (v : SVec) (i : Nat) (h : i < v.length), svecRef v (i + 1) = .ok v[i]) ∧
  (∀ (v : SVec) (i : Nat) (h : i < v.length),
    svecIterate v (i + 1) = .ok (some (v[i], (i : Int) + 2))) ∧
  (∀ (v : SVec) (i : Int), (v.length : Int) < i → svecIterate v i = .ok none) ∧
  (∀ v : SVec, svecFirstindex v = 1 ∧ svecLastindex v = v.length ∧ svecKeys v = v.length ∧
    svecAxes v = [v.length] ∧ (svecIsempty v = true ↔ v = []) ∧ svecEltype = "Any" ∧
    svecAxesD v 1 = .ok v.length ∧ (∀ d, d > 1 → svecAxesD v d = .ok 1) ∧
    (∀ d, d < 1 → svecAxesD v d = .error .bounds)) ∧
  (∀ {β : Type} (f : Option JVal → β) (v : SVec), svecMap f v = v.map f) ∧
  (∀ (v : SVec) (I : List Nat), (∀ i ∈ I, i < v.length) →
    svecGetindexArray v (I.map fun (i : Nat) => (i : Int) + 1) = .ok (I.map fun (i : Nat) => v[i]?.join)) ∧
  (∀ (eq : Option JVal → Option JVal → Bool) (v1 v2 : SVec),
    v1.length ≠ v2.length → svecEq eq v1 v2 = false) ∧
  (∀ (eq : Option JVal → Option JVal → Bool) (v : SVec), (∀ x, eq x x = true) →
    svecEq eq v v = true) ∧
  (∀ a, svecUnsafeConvert a = a + 8)

theorem svecRef_in (v : SVec) (i : Nat) (h : i < v.length) : svecRef v (i + 1) = .ok v[i] := by
  simp only [svecRef]
  rw [if_neg (by omega)]
  simp [h]

theorem svecGetindexArray_in (v : SVec) : ∀ I : List Nat, (∀ i ∈ I, i < v.length) →
    svecGetindexArray v (I.map fun (i : Nat) => (i : Int) + 1) = .ok (I.map fun (i : Nat) => v[i]?.join) := by
  intro I
  induction I with
  | nil => intro _; rfl
  | cons i I ih =>
    intro h
    have hi := h i (by simp)
    simp only [List.map_cons, svecGetindexArray]
    rw [svecRef_in v i hi, ih (fun j hj => h j (by simp [hj]))]
    simp [bind, Except.bind, pure, Except.pure, hi]

theorem svecEqLoop_refl (eq : Option JVal → Option JVal → Bool) (h : ∀ x, eq x x = true) :
    ∀ v : SVec, svecEqLoop eq v v = true := by
  intro v
  induction v with
  | nil => rfl
  | cons a v ih => simp [svecEqLoop, h, ih]

theorem svecSemantics : SvecSemantics := by
  refine ⟨?_, svecRef_in, ?_, ?_, ?_, fun _ _ => rfl, svecGetindexArray_in, ?_, ?_, fun _ => rfl⟩
  · intro v i h
    simp [svecRef, h]
  · intro v i h
    simp only [svecIterate]
    split
    · rename_i hc; simp only [svecLength] at hc; omega
    · rw [svecRef_in v i h]
      show Except.ok (some (v[i], (i : Int) + 1 + 1)) = Except.ok (some (v[i], (i : Int) + 2))
      rw [show (i : Int) + 1 + 1 = i + 2 by omega]
  · intro v i h
    simp [svecIterate, svecLength, h]
  · intro v
    refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [svecIsempty, svecLength]
    · simp [svecAxesD, svecLength]
    · intro d hd
      simp only [svecAxesD]
      rw [if_neg (by omega)]
    · intro d hd
      simp only [svecAxesD]
      rw [if_pos (by omega), if_neg (by omega)]
  · intro eq v1 v2 h
    simp [svecEq, svecLength, h]
  · intro eq v h
    simp [svecEq, svecLength, svecEqLoop_refl eq h]

/-- `isassigned(v::SimpleVector, i)` returns `true` exactly when `i` is in bounds and slot
`i` holds a value, as the `isassigned` docstring promises ("Return `false` if the index is
out of bounds, or has an undefined reference", `base/essentials.jl:1116-1117`). -/
def SvecIsassignedCorrect : Prop :=
  ∀ (v : SVec) (i : Int),
    svecIsassigned v i = true ↔ (1 ≤ i ∧ i ≤ v.length ∧ ∃ x, v[(i - 1).toNat]? = some (some x))

theorem svecIsassignedCorrect_refuted : ¬ SvecIsassignedCorrect := by
  intro h
  have := (h [none] 1).1 (by decide)
  obtain ⟨_, _, x, hx⟩ := this
  simp at hx

end JuliaLean.BootCov.Arrays

end

section

/-!
Properties of the macros and doc helpers of `base/boot.jl` and `base/essentials.jl`.
-/

namespace JuliaLean.BootCov.Macros

open JuliaLean
open JuliaLean.BootCov

/-- Close `assumeEffects` under the implication `terminates_globally → terminates_locally`. -/
def implied (f : EffectFlags) : EffectFlags :=
  { f with terminatesLocally := f.terminatesLocally || f.terminatesGlobally }

/-- The `Base` effect macros with the `@assume_effects` settings their comments name
(`base/essentials.jl:195-374`). -/
def baseEffectTable : List (EffectFlags × List String) :=
  [(baseTotalMeta, ["total"]), (baseFoldableMeta, ["foldable"]),
   (baseTerminatesLocallyMeta, ["terminates_locally"]),
   (baseTerminatesGloballyMeta, ["terminates_globally"]),
   (baseTerminatesGloballyNotaskstateMeta, ["terminates_globally", "notaskstate"]),
   (baseTerminatesGloballyNoubMeta, ["terminates_globally", "noub"]),
   (baseEffectFreeTerminatesLocallyMeta, ["effect_free", "terminates_locally"]),
   (baseNothrowNoubMeta, ["nothrow", "noub"]), (baseNothrowMeta, ["nothrow"]),
   (baseNoubMeta, ["noub"]), (baseNotaskstateMeta, ["notaskstate"]),
   (baseNoubIfNoinboundsMeta, ["noub_if_noinbounds"])]

/-- Each `Base` effect macro "can be used in place of" its `@assume_effects` settings, as
its comment says: inside `Base` or `Compiler` it asserts exactly those effects (up to
`terminates_globally` implying `terminates_locally`), and elsewhere it expands to `false`. -/
def BaseEffectMetasMatchAssume : Prop :=
  ∀ p ∈ baseEffectTable, ∀ (baseRelative : String → String) (m : String),
    effectMeta (baseIsInternal baseRelative m) p.1 =
      (if baseIsInternal baseRelative m then .expr "meta" [.expr "purity" p.1.toList]
       else .bool false) ∧
    implied p.1 = implied (assumeEffects p.2)

theorem baseEffectMetasMatchAssume_refuted : ¬ BaseEffectMetasMatchAssume := by
  intro h
  have := (h (baseFoldableMeta, ["foldable"]) (by simp [baseEffectTable]) id "Base").2
  revert this
  decide

/-- The marker macros of `Base` (`base/essentials.jl:46-186`, 377-382, 488-501, 893,
939-977, 1020-1060, 1568-1570, 1646-1660) expand to the documented expressions:
`@nospecialize x=v` becomes a `:kw` argument only for a single argument; `@label _` and
`@label _ body` are rejected; a labelled `for` or `while` loop has its body wrapped in a
`name#cont` block; and `@world` accepts exactly a symbol, a `GlobalRef` or `a.b`. -/
def BaseMarkerMacros : Prop :=
  (∀ x v, nospecialize [.expr "=" [x, v]] =
    .expr "escape" [.expr "meta" [.sym "nospecialize", .expr "kw" [x, v]]]) ∧
  (∀ x v, specialize [.expr "=" [x, v]] =
    .expr "escape" [.expr "meta" [.sym "specialize", .expr "kw" [x, v]]]) ∧
  (∀ a b rest, nospecialize (a :: b :: rest) =
    .expr "escape" [.expr "meta" (.sym "nospecialize" :: a :: b :: rest)] ∧
    specialize (a :: b :: rest) = .expr "escape" [.expr "meta" (.sym "specialize" :: a :: b :: rest)]) ∧
  (∀ s, isdefinedMacro s = .expr "escape" [.expr "isdefined" [.sym s]]) ∧
  (∀ a, gcPreserveBegin a = .expr "gc_preserve_begin" [esc a] ∧
    gcPreserveEnd a = .expr "gc_preserve_end" [esc a]) ∧
  (∀ e, esc e = .expr "escape" [e]) ∧
  propagateInboundsMeta = .expr "meta" [.sym "inline", .sym "propagate_inbounds"] ∧
  nospecializeinferMeta = .expr "meta" [.sym "nospecializeinfer"] ∧
  (∀ m e, evalMacro1 m e = evalMacro2 (.module_ m) e) ∧
  (∀ md e, evalMacro2 md e = .expr "let" [.expr "=" [.sym "eval_local_result",
      .expr "escape" [.expr "call" [.globalRef "Core" "eval", md, .expr "quote" [e]]]],
    .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ b, boundscheckMacro b = .expr "if" [.expr "boundscheck" [], esc b]) ∧
  (∀ b, inboundsMacro b = .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", esc b]], .expr "inbounds" [.sym "pop"], .sym "val"]) ∧
  (∃ msg, label1 "_" = .error (.error msg)) ∧
  (∀ n, n ≠ "_" → label1 n = .ok (esc (.expr "symboliclabel" [.sym n]))) ∧
  (∀ b, ∃ msg, label2 "_" b = .error (.error msg)) ∧
  (∀ n it body rest, n ≠ "_" → label2 n (.expr "for" (it :: body :: rest)) =
    .ok (esc (.expr "symbolicblock" [.sym n,
      .expr "for" [it, .expr "symbolicblock" [.sym (n ++ "#cont"), body]]]))) ∧
  (∀ n c body rest, n ≠ "_" → label2 n (.expr "while" (c :: body :: rest)) =
    .ok (esc (.expr "symbolicblock" [.sym n,
      .expr "while" [c, .expr "symbolicblock" [.sym (n ++ "#cont"), body]]]))) ∧
  (∀ b, label0 b = esc (.expr "symbolicblock" [.sym "loop-exit", b])) ∧
  (∀ n, gotoMacro n = esc (.expr "symbolicgoto" [.sym n])) ∧
  (∀ l f, lineMacro (.lineNode l f) = .ok (.int l)) ∧
  (∀ m s w, (∀ t, w ≠ .sym t) → worldMacro m (.sym s) w =
    .ok (.expr "call" [.opaque 1, esc w, .quoteNode (.globalRef m s)])) ∧
  (∀ m w n, ∃ msg, worldMacro m (.int n) w = .error (.error msg))

theorem baseMarkerMacros : BaseMarkerMacros := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ => rfl,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl,
    fun _ => rfl, ⟨_, rfl⟩, ?_, fun _ => ⟨_, rfl⟩, ?_, ?_, fun _ => rfl, fun _ => rfl,
    fun _ _ => rfl, ?_, fun _ _ _ => ⟨_, rfl⟩⟩
  · intro n hn; simp [label1, hn]
  · intro n it body rest hn; simp [label2, hn]
  · intro n c body rest hn; simp [label2, hn]
  · intro m s w hw
    cases w with
    | sym t => exact absurd rfl (hw t)
    | _ => rfl

end JuliaLean.BootCov.Macros

end

section

/-!
Properties of the remaining `base/boot.jl` and `base/essentials.jl` methods.
-/

namespace JuliaLean.BootCov.Misc

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

/-- The `Base` identity conversions (`base/essentials.jl:474-480`, 652, 739-746) return
their argument; `cconvert(T, x)` converts only when `x` is not already a `T`, and defers
pointers; pointer `unsafe_convert` keeps the address and string `unsafe_convert` yields the
data address; converting to `Union{}` throws `ArgumentError`. -/
def IdentityConversionsBase : Prop :=
  (∀ {α : Type} (x : α), convertSame x = x ∧ unsafeConvertSame x = x ∧ cconvertPtr x = x) ∧
  (∀ {α : Type} (isT : α → Bool) (conv : α → R α) x, isT x = true → cconvert isT conv x = .ok x) ∧
  (∀ {α : Type} (isT : α → Bool) (conv : α → R α) x, isT x = false → cconvert isT conv x = conv x) ∧
  (∀ p : Ptr, (unsafeConvertPtr p).addr = p.addr) ∧
  (∀ a, (unsafeConvertString a).addr = a) ∧
  (∀ {α : Type} (a : List α), (∃ m, convertUnionBottom a = .error (.argument m)) ∧
    cconvertUnionBottom a = convertUnionBottom a)

theorem identityConversionsBase : IdentityConversionsBase := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, ?_, ?_, fun _ => rfl, fun _ => rfl,
    fun _ => ⟨⟨_, rfl⟩, rfl⟩⟩
  · intro α isT conv x h; simp [cconvert, h]
  · intro α isT conv x h; simp [cconvert, h]

theorem cvtFrom_all_isa {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) :
    ∀ (x : List α) (n : Nat), (∀ i (h : i < x.length), isa (n + i) x[i] = true) →
      cvtFrom isa conv n x = .ok x := by
  intro x
  induction x with
  | nil => intro n _; rfl
  | cons a x ih =>
    intro n h
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    have hr := ih (n + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show n + 1 + i = n + (i + 1) by omega]
      exact this)
    simp [cvtFrom, h0, hr, bind, Except.bind, pure, Except.pure]

theorem bind_ok {α β : Type} {m : R α} {k : α → R β} {y : β} (h : (m >>= k) = .ok y) :
    ∃ b, m = .ok b ∧ k b = .ok y := by
  cases m with
  | error e => simp [bind, Except.bind] at h
  | ok b => exact ⟨b, rfl, h⟩

theorem cvtFrom_length {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) :
    ∀ (x : List α) (n : Nat) (y : List α), cvtFrom isa conv n x = .ok y → y.length = x.length := by
  intro x
  induction x with
  | nil => intro n y h; simp [cvtFrom] at h; cases h; rfl
  | cons a x ih =>
    intro n y h
    rw [cvtFrom.eq_2] at h
    split at h <;>
    · obtain ⟨b, -, h⟩ := bind_ok h
      dsimp only at h
      obtain ⟨ys, hys, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp [ih (n + 1) ys hys]

/-- Tuple helpers (`base/essentials.jl:521-667`): `tail(x)` drops the first element and
throws `ArgumentError` on `()`; `argtail` drops its first argument; `convert(T, x)` for
a tuple throws `MethodError` when no conversion can produce a `T`, returns `x` itself when
every element already has its field type, keeps the length, and converts each other
element with `convert(fieldtype(T, n), x[n])`. -/
def TupleHelpers : Prop :=
  (∀ {α : Type} (a : α) (xs : List α), tail (a :: xs) = .ok xs ∧ argtail (a :: xs) = .ok xs) ∧
  (∀ {α : Type}, ∃ m, tail ([] : List α) = .error (.argument m)) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x : List α),
    convertTuple false isa conv x = .error (.method "convert")) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x : List α),
    (∀ i (h : i < x.length), isa (i + 1) x[i] = true) → convertTuple true isa conv x = .ok x) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x y : List α),
    convertTuple true isa conv x = .ok y → y.length = x.length) ∧
  (∀ {α : Type} (isa : Nat → α → Bool) (conv : Nat → α → R α) (x : List α) (n : Nat)
    (h : n < x.length), cvt1 isa conv x (n + 1) =
      if isa (n + 1) x[n] then .ok x[n] else conv (n + 1) x[n])

theorem tupleHelpers : TupleHelpers := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, ⟨_, rfl⟩, fun _ _ _ => rfl, ?_, ?_, ?_⟩
  · intro α isa conv x h
    simp only [convertTuple, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact cvtFrom_all_isa isa conv x 1 (fun i hi => by rw [Nat.add_comm]; exact h i hi)
  · intro α isa conv x y h
    simp only [convertTuple, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    exact cvtFrom_length isa conv x 1 y h
  · intro α isa conv x n h
    simp [cvt1, h]

/-- Small functions of `base/essentials.jl`: the compiler barriers and `values` return their
argument; every `throw_boundserror` form throws `BoundsError(A, indices)` with the indices
as a tuple; `GlobalRef`s are equal exactly when module and name are; `oftype` converts only
when needed; `unsigned`/`signed` reinterpret the 64-bit pattern and invert each other;
`reinterpret` bit-casts primitive types; `ifelse` selects; `isempty` uses `isdone` when it
answers and otherwise whether `iterate` returns `nothing`; `Int` `+`/`-` wrap; `!` negates;
`ismissing` tests for `missing`; `isdone` defaults to `missing`; and `_resolve_in_world`
throws `InexactError` for a negative world. -/
def SmallFunctions : Prop :=
  (∀ {α : Type} (x : α), blackbox x = x ∧ inferencebarrier x = x ∧ values x = x) ∧
  (∀ A I, throwBoundserror A I = (.error .bounds, .obj "BoundsError" [some A, some (.tuple I)])) ∧
  (∀ A, throwBoundserror1 A = throwBoundserror A []) ∧
  (∀ A i1 i2 I, throwBoundserror3 A i1 i2 I = throwBoundserror A (i1 :: i2 :: I)) ∧
  (∀ A I, throwBoundserrorIndices A I = throwBoundserror A I) ∧
  (∀ A I, throwBoundserror2 A I = (.error .bounds, .obj "BoundsError" [some A, some I])) ∧
  (∀ a b : String × String, globalRefEq a b = true ↔ a = b) ∧
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y, isa y = true → oftype isa conv y = .ok y) ∧
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y r, isa y = false → conv y = .ok r →
    oftype isa conv y = if isa r then .ok r else .error (.typeError "typeassert")) ∧
  (∀ x : JInt64, signedUInt (unsignedInt x) = x) ∧
  (∀ x : JInt .u64, unsignedInt (signedUInt x) = x) ∧
  (∀ x : JInt64, (unsignedInt x).val = x.val % 2 ^ 64) ∧
  (∀ {α β : Type} (bc : α → β) (full : α → R β) x, reinterpret true bc full x = .ok (bc x) ∧
    reinterpret false bc full x = full x) ∧
  (∀ {α : Type} (f : α → Nat) x, sizeof f x = f x) ∧
  (∀ {α : Type} (x y : α), ifelse true x y = x ∧ ifelse false x y = y) ∧
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s d, isdone s = some d →
    isempty isdone it s = d) ∧
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s, isdone s = none →
    isempty isdone it s = (it s).isNone) ∧
  (∀ x y : JInt64, (addInt x y).val = wrapInt .i64 (x.val + y.val) ∧
    (subInt x y).val = wrapInt .i64 (x.val - y.val)) ∧
  (∀ b, notBool b = !b) ∧
  (∀ x, ismissing x = true ↔ x = none) ∧
  (∀ {α : Type} (x : α), isdoneDefault x = none) ∧
  (∀ {τ : Type} (hm : τ → Bool) T, isiterable hm T = hm T) ∧
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr, w.val < 0 →
    resolveInWorld g (.int .i64 w) gr = .error (.inexact "convert" "UInt64")) ∧
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr (h : 0 ≤ w.val),
    resolveInWorld g (.int .i64 w) gr = g ⟨w.val, by
      have := w.property; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at this ⊢; omega⟩
      gr.1 gr.2)

theorem i64_val_bounds (x : JInt64) : -(2:Int) ^ 63 ≤ x.val ∧ x.val < 2 ^ 63 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem u64_val_bounds (x : JInt .u64) : 0 ≤ x.val ∧ x.val < 2 ^ 64 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem smallFunctions : SmallFunctions := by
  refine ⟨fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_, fun _ => rfl,
    fun _ _ => rfl, ?_, ?_⟩
  · intro a b
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp [globalRefEq]
  · intro α isa conv y h; simp [oftype, h]
  · intro α isa conv y r h hr; simp [oftype, h, hr, bind, Except.bind]
  · intro x
    apply Subtype.ext
    have hb := i64_val_bounds x
    simp only [signedUInt, unsignedInt, bitcastInt, JInt.wrap]
    simp [wrapInt, IntTy.signed, IntTy.bits]
    omega
  · intro x
    apply Subtype.ext
    have hb := u64_val_bounds x
    simp only [signedUInt, unsignedInt, bitcastInt, JInt.wrap]
    simp [wrapInt, IntTy.signed, IntTy.bits]
    omega
  · intro x
    simp [unsignedInt, bitcastInt, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
  · intro σ α isdone it s d h; simp [isempty, h]
  · intro σ α isdone it s h; simp [isempty, h]
  · intro x; cases x <;> simp [ismissing]
  · intro g w gr h
    have ht : wrapInt IntTy.i64.toSigned w.val < 0 := by
      have hb := i64_val_bounds w
      simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.toSigned]
      omega
    have herr : ctor .u64 (.int .i64 w) = .error (.inexact "convert" "UInt64") := by
      simp only [ctor, toUInt64, bind_checkSignBit, ht, ↓reduceIte, throwInexact]
      try rfl
    simp [resolveInWorld, herr, bind, Except.bind]
  · intro g w gr h
    have hb := i64_val_bounds w
    have hok : ctor .u64 (.int .i64 w) = .ok ⟨w.val, by
        have := w.property; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at this ⊢; omega⟩ := by
      simp only [ctor, toUInt64, bind_checkSignBit]
      have ht : ¬ wrapInt IntTy.i64.toSigned w.val < 0 := by
        simp [wrapInt, IntTy.signed, IntTy.bits, IntTy.toSigned]
        omega
      simp only [ht, ↓reduceIte, pure, Except.pure, bitcastInt]
      congr 1
      apply Subtype.ext
      simp [JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
      omega
    simp [resolveInWorld, hok, bind, Except.bind]

/-- `blackbox(x)`, `inferencebarrier(x)` and `values(itr)` (`base/essentials.jl:9`, 1201, 1253) return their argument unchanged. -/
def Barriers : Prop :=
  (∀ {α : Type} (x : α), blackbox x = x ∧ inferencebarrier x = x ∧ values x = x)

theorem barriers : Barriers := smallFunctions.1

/-- Every `throw_boundserror` and `_throw_boundserror_indices` method (`base/essentials.jl:15-19`) throws `BoundsError(A, I)`, with the indices collected into a tuple by the splatting forms. -/
def ThrowBoundserrorForms : Prop :=
  (∀ A I, throwBoundserror A I = (.error .bounds, .obj "BoundsError" [some A, some (.tuple I)])) ∧
  (∀ A, throwBoundserror1 A = throwBoundserror A []) ∧
  (∀ A i1 i2 I, throwBoundserror3 A i1 i2 I = throwBoundserror A (i1 :: i2 :: I)) ∧
  (∀ A I, throwBoundserrorIndices A I = throwBoundserror A I) ∧
  (∀ A I, throwBoundserror2 A I = (.error .bounds, .obj "BoundsError" [some A, some I]))

theorem throwBoundserrorForms : ThrowBoundserrorForms := ⟨smallFunctions.2.1, smallFunctions.2.2.1, smallFunctions.2.2.2.1, smallFunctions.2.2.2.2.1, smallFunctions.2.2.2.2.2.1⟩

/-- `==(a::GlobalRef, b::GlobalRef) = a.mod === b.mod && a.name === b.name` (`base/essentials.jl:23`) holds exactly for equal module and name. -/
def GlobalRefEq : Prop :=
  (∀ a b : String × String, globalRefEq a b = true ↔ a = b)

theorem globalRefEq_spec : GlobalRefEq := smallFunctions.2.2.2.2.2.2.1

/-- `oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)`
(`base/essentials.jl:718`): `y` itself when it already has the type, otherwise the result of
the (arbitrary, user-extensible) `convert` method, which the typeassert requires to have the
type. -/
def OftypeSpec : Prop :=
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y, isa y = true → oftype isa conv y = .ok y) ∧
  (∀ {α : Type} (isa : α → Bool) (conv : α → R α) y r, isa y = false → conv y = .ok r →
    oftype isa conv y = if isa r then .ok r else .error (.typeError "typeassert"))

theorem oftypeSpec : OftypeSpec := ⟨smallFunctions.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.1⟩

/-- `unsigned(x::Int) = reinterpret(UInt, x)` and `signed(x::UInt) = reinterpret(Int, x)`
(`base/essentials.jl:720-721`) reinterpret the 64-bit pattern: they invert each other and `unsigned(x)` is `x mod 2^64`. -/
def SignedUnsignedInt : Prop :=
  (∀ x : JInt64, signedUInt (unsignedInt x) = x) ∧
  (∀ x : JInt .u64, unsignedInt (signedUInt x) = x) ∧
  (∀ x : JInt64, (unsignedInt x).val = x.val % 2 ^ 64)

theorem signedUnsignedInt : SignedUnsignedInt := ⟨smallFunctions.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- `reinterpret(Out, x)` (`base/essentials.jl:787-794`) bit-casts when both types are primitive and otherwise defers to `_reinterpret`. -/
def ReinterpretSpec : Prop :=
  (∀ {α β : Type} (bc : α → β) (full : α → R β) x, reinterpret true bc full x = .ok (bc x) ∧
    reinterpret false bc full x = full x)

theorem reinterpretSpec : ReinterpretSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `sizeof(x) = Core.sizeof(x)` (`base/essentials.jl:841`) is the runtime size. -/
def SizeofSpec : Prop :=
  (∀ {α : Type} (f : α → Nat) x, sizeof f x = f x)

theorem sizeofSpec : SizeofSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `ifelse(c, x, y)` (`base/essentials.jl:884`) returns `x` when `c` is true and `y` otherwise. -/
def IfelseSpec : Prop :=
  (∀ {α : Type} (x y : α), ifelse true x y = x ∧ ifelse false x y = y)

theorem ifelseSpec : IfelseSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `isempty(itr)` (`base/essentials.jl:1225-1229`) answers with `isdone(itr)` when that is not `missing`, and otherwise whether `iterate(itr)` returns `nothing`. -/
def IsemptySpec : Prop :=
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s d, isdone s = some d →
    isempty isdone it s = d) ∧
  (∀ {σ α : Type} (isdone : σ → Option Bool) (it : σ → Option α) s, isdone s = none →
    isempty isdone it s = (it s).isNone)

theorem isemptySpec : IsemptySpec := ⟨smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- The bootstrap `(+)(x::Int, y::Int)` and `(-)(x::Int, y::Int)` (`base/essentials.jl:1257-1258`) wrap modulo `2^64`. -/
def IntAddSub : Prop :=
  (∀ x y : JInt64, (addInt x y).val = wrapInt .i64 (x.val + y.val) ∧
    (subInt x y).val = wrapInt .i64 (x.val - y.val))

theorem intAddSub : IntAddSub := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `!(x::Bool) = not_int(x)` (`base/essentials.jl:1284`) is Boolean negation. -/
def NotBool : Prop :=
  (∀ b, notBool b = !b)

theorem notBool_spec : NotBool := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `ismissing(x) = x === missing` (`base/essentials.jl:1532`). -/
def IsmissingSpec : Prop :=
  (∀ x, ismissing x = true ↔ x = none)

theorem ismissingSpec : IsmissingSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The fallback `isdone(itr, state...) = missing` (`base/essentials.jl:1591`). -/
def IsdoneDefault : Prop :=
  (∀ {α : Type} (x : α), isdoneDefault x = none)

theorem isdoneDefault_spec : IsdoneDefault := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `isiterable(T) = hasmethod(iterate, Tuple{T})` (`base/essentials.jl:1608-1610`). -/
def IsiterableSpec : Prop :=
  (∀ {τ : Type} (hm : τ → Bool) T, isiterable hm T = hm T)

theorem isiterableSpec : IsiterableSpec := smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- `_resolve_in_world(world, gr) = getglobal(gr.mod, gr.name)` in world `UInt(world)` (`base/essentials.jl:1662-1663`): a negative world throws `InexactError`, any other world reads the binding in that world. -/
def ResolveInWorld : Prop :=
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr, w.val < 0 →
    resolveInWorld g (.int .i64 w) gr = .error (.inexact "convert" "UInt64")) ∧
  (∀ (g : JInt .u64 → String → String → R JVal) (w : JInt64) gr (h : 0 ≤ w.val),
    resolveInWorld g (.int .i64 w) gr = g ⟨w.val, by
      have := w.property; simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at this ⊢; omega⟩
      gr.1 gr.2)

theorem resolveInWorld_spec : ResolveInWorld := ⟨smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, smallFunctions.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The `Pairs` constructors (`base/essentials.jl:505-513`): the four-parameter inner
constructor converts only arguments that do not already have the declared types; the outer
constructors choose `V = eltype(A)` and `K = eltype(I)`, or `keytype(A)` when `I` is
`Nothing`; `pairs(NamedTuple)` has `Symbol` keys and a `Nothing` iterator; `Colon()` is
the field-less singleton and `show(io, ::Colon)` prints the type name followed by `()`;
`Val(x)` is `Val{x}()`, which carries `x` in its type (`base/essentials.jl:1160-1193`). -/
def PairsAndColon : Prop :=
  (∀ {α : Type} (isA isI : α → Bool) (cA cI : α → R α) d i, isA d = true → isI i = true →
    pairsKVIA isA isI cA cI d i = .ok (d, i)) ∧
  (∀ {α : Type} (isA isI : α → Bool) (cA cI : α → R α) d i d', isA d = false → isI i = true →
    cA d = .ok d' → pairsKVIA isA isI cA cI d i = .ok (d', i)) ∧
  (∀ K V I A, pairsKV K V I A = (K, V, I, A)) ∧
  (∀ (elt : String → String) K I A, pairsK elt K I A = (K, elt A, I, A)) ∧
  (∀ (elt kt : String → String) A, pairs0 elt kt "Nothing" A = (kt A, elt A, "Nothing", A)) ∧
  (∀ (elt kt : String → String) I A, I ≠ "Nothing" → pairs0 elt kt I A = (elt I, elt A, I, A)) ∧
  pairsNamedTupleType = ("Symbol", "Nothing") ∧
  showColon "Colon" = "Colon()" ∧ colonCtor = .obj "Colon" [] ∧
  (∀ x, valCtor x = valT x ∧ (valT x).1 = x)

theorem pairsAndColon : PairsAndColon := by
  refine ⟨?_, ?_, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_, ?_, rfl, rfl, rfl,
    fun _ => ⟨rfl, rfl⟩⟩
  · intro α isA isI cA cI d i h1 h2; simp [pairsKVIA, h1, h2, bind, Except.bind, pure, Except.pure]
  · intro α isA isI cA cI d i d' h1 h2 h3
    simp [pairsKVIA, h1, h2, h3, bind, Except.bind, pure, Except.pure]
  · intro elt kt A; simp [pairs0]
  · intro elt kt I A h; simp [pairs0, h]

end JuliaLean.BootCov.Misc

end

section

/-!
Properties of the default-constructor generation of `base/essentials.jl:1290-1504` and of
`length(::AbstractArray)` (line 13).
-/

namespace JuliaLean.BootCov.DefaultCtors

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.Types

/-! ## `_fieldtypes_constrain_typevars` -/

def isTvar : JType → Bool
  | .tvar _ _ _ _ => true
  | _ => false

/-- `tv` is constrained by the upper bound of a later type variable, scanning up to and
including the first later variable identical to `tv`. -/
def ubConstrains (tv : JType) : List JType → Bool
  | [] => false
  | t :: ts => hasTypevar (tvUb t) tv || (!sameVar t tv && ubConstrains tv ts)

/-- Type variable `i` (zero-based) occurs in a field type or in the bound of a later one. -/
def constrainedAt (tvars fts : List JType) (i : Nat) : Bool :=
  fts.any (fun ft => hasTypevar ft (tvars.getD i .bottom)) ||
    ubConstrains (tvars.getD i .bottom) (tvars.drop (i + 1))

/-- "Check whether all type parameters are constrained by fields or other constrained
tvars" (comment at `base/essentials.jl:1290-1291`): for type variables `tvars` (outermost
first), `_fieldtypes_constrain_typevars` returns `true` exactly when every type variable
occurs in some field type or in the upper bound of an inner type variable (before an inner
variable that shadows it). Inner variables are checked first, so every variable whose bound
is consulted is itself constrained. -/
def FieldtypesConstrainSpec : Prop :=
  ∀ tvars fts : List JType, (∀ t ∈ tvars, isTvar t = true) →
    fieldtypesConstrainTypevars tvars fts =
      .ok ((List.range tvars.length).all (constrainedAt tvars fts))

theorem asTypeVar_tvar {t : JType} (h : isTvar t = true) : asTypeVar t = .ok t := by
  cases t <;> simp_all [isTvar, asTypeVar]

theorem fieldLoop_eq (tv : JType) :
    ∀ fts : List JType, fieldLoop tv fts = fts.any (fun ft => hasTypevar ft tv)
  | [] => rfl
  | ft :: fts => by
    simp only [fieldLoop, List.any_cons]
    cases hasTypevar ft tv <;> simp [fieldLoop_eq tv fts]

theorem ubLoop_eq (tv : JType) :
    ∀ ts : List JType, (∀ t ∈ ts, isTvar t = true) → ubLoop tv ts = .ok (ubConstrains tv ts)
  | [] => fun _ => rfl
  | t :: ts => fun h => by
    have ht := asTypeVar_tvar (h t (by simp))
    have ih := ubLoop_eq tv ts (fun x hx => h x (by simp [hx]))
    simp only [ubLoop, ht, bind, Except.bind, ubConstrains]
    cases hasTypevar (tvUb t) tv <;> cases sameVar t tv <;> simp [ih]

theorem getD_mem {α : Type} (d : α) : ∀ (l : List α) (i : Nat), i < l.length → l.getD i d ∈ l
  | [], _, h => by simp at h
  | a :: l, 0, _ => by simp
  | a :: l, i + 1, h => by
    simp only [List.getD_cons_succ]
    exact List.mem_cons_of_mem _ (getD_mem d l i (by simpa using h))

theorem outerLoop_eq (tvars fts : List JType) (h : ∀ t ∈ tvars, isTvar t = true) :
    ∀ i, i ≤ tvars.length →
      outerLoop tvars fts i = .ok ((List.range i).all (constrainedAt tvars fts))
  | 0 => fun _ => rfl
  | i + 1 => fun hi => by
    have hmem : tvars.getD i .bottom ∈ tvars := getD_mem .bottom tvars i (by omega)
    have ht := asTypeVar_tvar (h _ hmem)
    have hub := ubLoop_eq (tvars.getD i .bottom) (tvars.drop (i + 1))
      (fun x hx => h x (List.mem_of_mem_drop hx))
    have ih := outerLoop_eq tvars fts h i (by omega)
    simp only [outerLoop, ht, bind, Except.bind, fieldLoop_eq]
    rw [List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
    have hc : constrainedAt tvars fts i =
        (fts.any (fun ft => hasTypevar ft (tvars.getD i .bottom)) ||
          ubConstrains (tvars.getD i .bottom) (tvars.drop (i + 1))) := rfl
    rw [hc]
    cases hf : fts.any (fun ft => hasTypevar ft (tvars.getD i .bottom))
    · simp only [Bool.false_eq_true, ↓reduceIte, hub, Bool.false_or]
      cases ubConstrains (tvars.getD i .bottom) (List.drop (i + 1) tvars) <;> simp [ih]
    · simp [pure, Except.pure, ih]

theorem fieldtypesConstrainSpec : FieldtypesConstrainSpec := by
  intro tvars fts h
  exact outerLoop_eq tvars fts h tvars.length (Nat.le_refl _)

/-! ## `_defaultctor_typeinfo` -/

/-- The variables of the `UnionAll` wrappers of a type, outermost first. -/
def uaVars : JType → List JType
  | .unionAll v b => v :: uaVars b
  | _ => []

/-- "Return the DataType, outer-to-inner type variables, and field types for `ty`" (comment
at line 1331): `_defaultctor_typeinfo(ty)` returns `unwrap_unionall(ty)`, the variables of
the `UnionAll` wrappers outermost first, and the field types of the `DataType`; it throws
`TypeError` when `unwrap_unionall(ty)` is not a `DataType`. -/
def TypeinfoSpec : Prop :=
  ∀ (getFieldtypes : JType → List JType) (ty : JType),
    defaultctorTypeinfo getFieldtypes ty =
      if isDataType (unwrapUnionall ty) then
        .ok (unwrapUnionall ty, uaVars ty, getFieldtypes (unwrapUnionall ty))
      else .error (.typeError "typeassert")

theorem peelLoop_eq : ∀ (ty : JType) (n : Nat),
    peelLoop n ty = (n + (uaVars ty).length, unwrapUnionall ty)
  | .unionAll v b, n => by
    simp only [peelLoop, uaVars, unwrapUnionall, List.length_cons, peelLoop_eq b (n + 1)]
    congr 1; omega
  | .dt _ _ _, n => rfl
  | .union _ _, n => rfl
  | .bottom, n => rfl
  | .tvar _ _ _ _, n => rfl
  | .vararg _ _, n => rfl
  | .typeApp _ _, n => rfl
  | .intParam _, n => rfl
  | .names _, n => rfl
  | .other _, n => rfl

theorem varsLoop_eq : ∀ ty : JType, varsLoop (uaVars ty).length ty = .ok (uaVars ty)
  | .unionAll v b => by
    simp only [uaVars, List.length_cons, varsLoop, varsLoop_eq b, bind, Except.bind, pure,
      Except.pure]
  | .dt _ _ _ => rfl
  | .union _ _ => rfl
  | .bottom => rfl
  | .tvar _ _ _ _ => rfl
  | .vararg _ _ => rfl
  | .typeApp _ _ => rfl
  | .intParam _ => rfl
  | .names _ => rfl
  | .other _ => rfl

theorem typeinfoSpec : TypeinfoSpec := by
  intro gf ty
  simp only [defaultctorTypeinfo, peelLoop_eq, Nat.zero_add]
  split
  · simp [varsLoop_eq, bind, Except.bind, pure, Except.pure]
  · rfl

/-! ## `_defaultctors` -/

/-- `[f i, f (i + 1), ..., f (i + k - 1)]`. -/
def seqFrom (f : Nat → JVal) : Nat → Nat → List JVal
  | _, 0 => []
  | i, k + 1 => f i :: seqFrom f (i + 1) k

/-- The number of `Any` field types. -/
def countAny : List JType → Nat
  | [] => 0
  | ft :: fts => (if isAnyTy ft then 1 else 0) + countAny fts

/-- The statements and `new` arguments of the inner constructor body for fields
`i, i + 1, ...` with the next SSA number `bidx`: an `Any` field passes its argument;
any other field `i` is `%bidx = fieldtype(self, i)` then
`%(bidx+1) = isa(arg, %bidx) ? arg : convert(%bidx, arg)`, and passes `%(bidx+1)`. -/
def innerBody : Nat → Nat → List JType → List JVal × List JVal
  | _, _, [] => ([], [])
  | i, bidx, ft :: fts =>
    if isAnyTy ft then
      ((innerBody (i + 1) bidx fts).1, argument (i + 1) :: (innerBody (i + 1) bidx fts).2)
    else
      (ftStmt i bidx :: cnvtStmt i bidx :: (innerBody (i + 1) (bidx + 2) fts).1,
        ssa (bidx + 1) :: (innerBody (i + 1) (bidx + 2) fts).2)

/-- The argument names `#ctor-self#, names...`. -/
def argnamesOf (names : List JVal) : JVal :=
  .obj "Array{Any,1}" ((JVal.sym "#ctor-self#" :: names).map some)

/-- The outer constructor `T(x::FT1, ..., z::FTn) where {tvars...} = new{T{tvars...}}(x, ..., z)`. -/
def outerDef (ty : JType) (tvars fts : List JType) (names : List JVal) (fl : JVal) : MethodDef :=
  let target := if tvars.length ≠ 0 then
      JVal.expr "curly" (.ty ty :: seqFrom (fun j => .expr "static_parameter" [.int j]) 1 tvars.length)
    else argument 1
  ⟨.ty (typeKind ty) :: fts.map JVal.ty, tvars.map JVal.ty,
    .expr "lambda" [argnamesOf names, .expr "block" [fl, .expr "return"
      [.expr "new" (target :: seqFrom (fun j => argument (j + 1)) 1 fts.length)]]]⟩

/-- The inner constructor `(::Type{T{tvars...}})(x, ..., z)`: every argument type is `Any`,
and the body converts each non-`Any` field before `new`. -/
def innerDef (typedt : JType) (fts : List JType) (names : List JVal) (fl : JVal) : MethodDef :=
  ⟨.ty typedt :: seqFrom (fun _ => .ty anyTy) 1 fts.length, [],
    .expr "lambda" [argnamesOf names, .expr "block" (fl :: (innerBody 1 1 fts).1 ++
      [.expr "return" [.expr "new" (argument 1 :: (innerBody 1 1 fts).2)]])]⟩

/-- The default constructors the manual describes ("Constructors": an inner constructor
that accepts any arguments and converts each to its field type, and an outer constructor
taking exactly the field types whenever the type parameters can be determined from them;
only one method when the type is non-parametric and every field is `Any`): for a
`DataType` with type variables `tvars`, symbol field names matching the field types, and a
line number node, `_defaultctors` defines exactly these methods, with every generated
array slot assigned. -/
def DefaultctorsSpec : Prop :=
  ∀ (getFieldtypes : JType → List JType) (getNames : JType → List JVal) (ty : JType)
    (line : Int) (file : JVal) (typedt : JType),
    let dt := unwrapUnionall ty
    let tvars := uaVars ty
    let fts := getFieldtypes dt
    let names := getNames dt
    let fl := JVal.lineNode line file
    isDataType dt = true → (∀ t ∈ tvars, isTvar t = true) →
    names.length = fts.length → (∀ nm ∈ names, ∃ s, nm = .sym s) → 0 ≤ line →
    wrapLoop tvars tvars.length (typeKind dt) = .ok typedt →
    defaultctors getFieldtypes getNames ty fl =
      .ok (if (List.range tvars.length).all (constrainedAt tvars fts) then
            (if tvars.length = 0 ∧ fts.all isAnyTy = true then [outerDef ty tvars fts names fl]
             else [outerDef ty tvars fts names fl, innerDef typedt fts names fl])
          else [innerDef typedt fts names fl])

theorem splat_map_some : ∀ l : List JVal, splat (l.map some) = .ok l
  | [] => rfl
  | x :: xs => by simp [splat, splat_map_some xs, bind, Except.bind, pure, Except.pure]

theorem setAt_fill (l : List JVal) (k : Nat) (x : JVal) :
    setAt (l.map some ++ List.replicate (k + 1) none) (l.length + 1) x =
      (l ++ [x]).map some ++ List.replicate k none := by
  unfold setAt
  simp only [Nat.add_sub_cancel]
  induction l with
  | nil => simp [List.replicate_succ]
  | cons a l ih => simp [ih]

theorem setAt_init (k : Nat) (x : JVal) :
    setAt (List.replicate (k + 1) none) 1 x = [x].map some ++ List.replicate k none := by
  have := setAt_fill [] k x
  simpa using this

theorem curlyLoop_eq : ∀ (k i : Nat) (pre : List JVal), pre.length = i →
    curlyLoop i k (pre.map some ++ List.replicate k none) =
      (pre ++ seqFrom (fun j => .expr "static_parameter" [.int j]) i k).map some
  | 0, i, pre, _ => by simp [curlyLoop, seqFrom]
  | k + 1, i, pre, h => by
    simp only [curlyLoop]
    rw [← h, setAt_fill, curlyLoop_eq k (pre.length + 1) _ (by simp)]
    simp [seqFrom]

theorem newArgsLoop_eq : ∀ (k i : Nat) (pre : List JVal), pre.length = i →
    newArgsLoop i k (pre.map some ++ List.replicate k none) =
      (pre ++ seqFrom (fun j => argument (j + 1)) i k).map some
  | 0, i, pre, _ => by simp [newArgsLoop, seqFrom]
  | k + 1, i, pre, h => by
    simp only [newArgsLoop]
    rw [← h, setAt_fill, newArgsLoop_eq k (pre.length + 1) _ (by simp)]
    simp [seqFrom]

theorem anyArgsLoop_eq : ∀ (k i : Nat) (pre : List JVal), pre.length = i →
    anyArgsLoop i k (pre.map some ++ List.replicate k none) =
      (pre ++ seqFrom (fun _ => .ty anyTy) i k).map some
  | 0, i, pre, _ => by simp [anyArgsLoop, seqFrom]
  | k + 1, i, pre, h => by
    simp only [anyArgsLoop]
    rw [← h, setAt_fill, anyArgsLoop_eq k (pre.length + 1) _ (by simp)]
    simp [seqFrom]

theorem atypesLoop_eq : ∀ (fts : List JType) (i : Nat) (pre : List JVal), pre.length = i →
    atypesLoop i fts (pre.map some ++ List.replicate fts.length none) =
      (pre ++ fts.map JVal.ty).map some
  | [], i, pre, _ => by simp [atypesLoop]
  | ft :: fts, i, pre, h => by
    simp only [atypesLoop, List.length_cons]
    rw [← h, setAt_fill, atypesLoop_eq fts (pre.length + 1) _ (by simp)]
    simp

theorem argnamesLoop_eq : ∀ (names : List JVal) (fts : List JType) (i : Nat) (pre : List JVal)
    (nany : Nat), pre.length = i → names.length = fts.length →
    (∀ nm ∈ names, ∃ s, nm = .sym s) →
    argnamesLoop i names fts (pre.map some ++ List.replicate fts.length none) nany =
      .ok ((pre ++ names).map some, nany + countAny fts)
  | [], [], i, pre, nany, _, _, _ => by simp [argnamesLoop, countAny]
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl
  | nm :: names, ft :: fts, i, pre, nany, h, hl, hs => by
    obtain ⟨s, rfl⟩ := hs nm (by simp)
    simp only [argnamesLoop, asSymbol, bind, Except.bind, List.length_cons]
    rw [← h, setAt_fill, argnamesLoop_eq names fts (pre.length + 1) _ _ (by simp)
      (by simpa using hl) (fun x hx => hs x (by simp [hx]))]
    simp only [List.append_assoc, List.cons_append, List.nil_append, countAny]
    congr 2
    split <;> omega

theorem countAny_le : ∀ fts : List JType, countAny fts ≤ fts.length
  | [] => Nat.le_refl _
  | ft :: fts => by
    have := countAny_le fts
    simp only [countAny, List.length_cons]
    split <;> omega

theorem innerBody_length : ∀ (fts : List JType) (i bidx : Nat),
    (innerBody i bidx fts).1.length = 2 * (fts.length - countAny fts) ∧
      (innerBody i bidx fts).2.length = fts.length
  | [], _, _ => ⟨rfl, rfl⟩
  | ft :: fts, i, bidx => by
    have h1 := innerBody_length fts (i + 1) bidx
    have h2 := innerBody_length fts (i + 1) (bidx + 2)
    have hc := countAny_le fts
    simp only [innerBody, countAny, List.length_cons]
    split
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

theorem innerLoop_eq : ∀ (fts : List JType) (i bidx e : Nat) (bpre npre : List JVal),
    bpre.length + 1 = bidx → npre.length + 1 = i →
    innerLoop i bidx fts
        (bpre.map some ++ List.replicate (2 * (fts.length - countAny fts) + e) none)
        (npre.map some ++ List.replicate fts.length none) =
      ((bpre ++ (innerBody i bidx fts).1).map some ++ List.replicate e none,
        (npre ++ (innerBody i bidx fts).2).map some)
  | [], i, bidx, e, bpre, npre, _, _ => by simp [innerLoop, innerBody, countAny]
  | ft :: fts, i, bidx, e, bpre, npre, hb, hn => by
    have hc := countAny_le fts
    simp only [innerLoop, innerBody, countAny, List.length_cons]
    split
    · rename_i ha
      rw [show 2 * (fts.length + 1 - (1 + countAny fts)) + e =
          2 * (fts.length - countAny fts) + e by omega]
      rw [← hn, setAt_fill, innerLoop_eq fts (npre.length + 1 + 1) bidx e bpre _ hb (by simp)]
      simp
    · rename_i ha
      rw [show 2 * (fts.length + 1 - (0 + countAny fts)) + e =
          (2 * (fts.length - countAny fts) + e + 1) + 1 by omega]
      rw [← hb, setAt_fill, show bpre.length + 1 + 1 = (bpre ++ [ftStmt i (bpre.length + 1)]).length + 1
          by simp, setAt_fill, ← hn, setAt_fill,
        innerLoop_eq fts (npre.length + 1 + 1) _ e _ _ (by simp) (by simp)]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
        List.length_cons, List.length_nil]

theorem allAnyLoop_eq : ∀ fts : List JType, allAnyLoop fts = fts.all isAnyTy
  | [] => rfl
  | ft :: fts => by
    simp only [allAnyLoop, List.all_cons]
    cases isAnyTy ft <;> simp [allAnyLoop_eq fts]

theorem outerCtor_eq (ty : JType) (tvars fts : List JType) (names : List JVal) (fl : JVal) :
    outerCtor ty tvars fts (argnamesOf names) fl = .ok (outerDef ty tvars fts names fl) := by
  have hc := curlyLoop_eq tvars.length 1 [.ty ty] rfl
  have hn := fun t => newArgsLoop_eq fts.length 1 [t] rfl
  have ha := atypesLoop_eq fts 1 [.ty (typeKind ty)] rfl
  simp only [outerCtor, outerDef, undefArr]
  by_cases hp : tvars.length = 0
  · simp only [hp, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, setAt_init, hn, ha,
      splat_map_some, bind, Except.bind, pure, Except.pure, ne_eq, not_true_eq_false]
    rfl
  · have hp' : (tvars.length != 0) = true := by simpa using hp
    simp only [hp', ↓reduceIte, setAt_init, hc, hn, ha, splat_map_some, bind, Except.bind,
      pure, Except.pure, ne_eq, hp, not_false_eq_true]
    rfl

theorem innerCtor_eq (dt typedt : JType) (tvars fts : List JType) (names : List JVal)
    (fl : JVal) (hw : wrapLoop tvars tvars.length (typeKind dt) = .ok typedt) :
    innerCtor dt tvars fts (countAny fts) (argnamesOf names) fl =
      .ok (innerDef typedt fts names fl) := by
  have hc := countAny_le fts
  have hl := innerBody_length fts 1 1
  have hi := innerLoop_eq fts 1 1 1 [] [] rfl rfl
  simp only [List.map_nil, List.nil_append] at hi
  have hs := anyArgsLoop_eq fts.length 1 [.ty typedt] rfl
  simp only [innerCtor, innerDef, undefArr]
  rw [show fts.length - countAny fts + (fts.length - countAny fts) + 1 =
    2 * (fts.length - countAny fts) + 1 by omega, hi]
  simp only [splat_map_some, bind, Except.bind, setChecked]
  rw [if_pos (by simp [hl.1] <;> omega)]
  rw [show 2 * (fts.length - countAny fts) + 1 = (innerBody 1 1 fts).1.length + 1 by
    rw [hl.1], List.replicate_one]
  have hf := setAt_fill (innerBody 1 1 fts).1 0
    (.expr "return" [.expr "new" (argument 1 :: (innerBody 1 1 fts).2)])
  simp only [List.replicate_zero, List.append_nil] at hf
  rw [show [(none : Option JVal)] = List.replicate (0 + 1) none from rfl, hf]
  simp only [splat_map_some, hw, setAt_init, hs, pure, Except.pure]
  rfl

theorem defaultctorsSpec : DefaultctorsSpec := by
  intro gf gn ty line file typedt
  simp only
  intro hdt htv hlen hsym hline hw
  have hinfo := typeinfoSpec gf ty
  rw [if_pos hdt] at hinfo
  have hcon := fieldtypesConstrainSpec (uaVars ty) (gf (unwrapUnionall ty)) htv
  have hargs := argnamesLoop_eq (gn (unwrapUnionall ty)) (gf (unwrapUnionall ty)) 1
    [.sym "#ctor-self#"] 0 rfl hlen hsym
  simp only [Nat.zero_add] at hargs
  have hline' : ¬ line < 0 := by omega
  simp only [defaultctors, hinfo, bind, Except.bind, srcLine, hline', ↓reduceIte, undefArr, setAt_init,
    hargs, hcon]
  have ho := outerCtor_eq ty (uaVars ty) (gf (unwrapUnionall ty)) (gn (unwrapUnionall ty))
    (.lineNode line file)
  have hi := innerCtor_eq (unwrapUnionall ty) typedt (uaVars ty) (gf (unwrapUnionall ty))
    (gn (unwrapUnionall ty)) (.lineNode line file) hw
  unfold argnamesOf at ho hi
  simp only [List.map_cons, List.singleton_append] at ho hi ⊢
  split
  · simp only [ho, allAnyLoop_eq]
    split
    · rfl
    · simp only [hi]; rfl
  · simp only [hi]; rfl

/-! ## `length(::AbstractArray)` -/

/-- Product of the exact dimension values. -/
def prodVals : List JInt64 → Int
  | [] => 1
  | d :: ds => d.val * prodVals ds

/-- The `length` docstring ("the number of elements", `base/abstractarray.jl:305-308`):
`length(t::AbstractArray) = prod(size(t))` is the product of the dimensions reduced
modulo `2^64` into `Int`, so it equals the number of elements exactly when that product is
at most `typemax(Int)`. -/
def LengthAbstractSpec : Prop :=
  ∀ size : List JInt64, (lengthAbstract size).val = wrapInt .i64 (prodVals size) ∧
    (prodVals size ≤ IntTy.max .i64 → (∀ d ∈ size, 0 ≤ d.val) →
      (lengthAbstract size).val = prodVals size)

theorem wrapI64_emod (x : Int) : wrapInt .i64 x % 2 ^ 64 = x % 2 ^ 64 := by
  simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapI64_congr (x y : Int) (h : x % 2 ^ 64 = y % 2 ^ 64) :
    wrapInt .i64 x = wrapInt .i64 y := by
  simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrap_mul_left (x y : Int) :
    wrapInt .i64 (wrapInt .i64 x * y) = wrapInt .i64 (x * y) := by
  apply wrapI64_congr
  rw [Int.mul_emod, wrapI64_emod, ← Int.mul_emod]

theorem foldl_mul_val : ∀ (ds : List JInt64) (a : JInt64),
    (ds.foldl (· * ·) a).val = wrapInt .i64 (a.val * prodVals ds)
  | [], a => by
    simp only [List.foldl, prodVals, Int.mul_one]
    exact (wrapInt_of_inRange .i64 a.val a.property).symm
  | d :: ds, a => by
    simp only [List.foldl, prodVals]
    rw [foldl_mul_val ds (a * d)]
    show wrapInt .i64 (wrapInt .i64 (a.val * d.val) * prodVals ds) = _
    rw [wrap_mul_left, Int.mul_assoc]

theorem prodVals_nonneg : ∀ ds : List JInt64, (∀ d ∈ ds, 0 ≤ d.val) → 0 ≤ prodVals ds
  | [], _ => by simp [prodVals]
  | d :: ds, h => by
    simp only [prodVals]
    exact Int.mul_nonneg (h d (by simp)) (prodVals_nonneg ds (fun x hx => h x (by simp [hx])))

theorem lengthAbstractSpec : LengthAbstractSpec := by
  intro size
  have h1 : (lengthAbstract size).val = wrapInt .i64 (prodVals size) := by
    cases size with
    | nil => rfl
    | cons d ds =>
      simp only [lengthAbstract, prodVals]
      exact foldl_mul_val ds d
  refine ⟨h1, fun hmax hnn => ?_⟩
  rw [h1]
  apply wrapInt_of_inRange
  have := prodVals_nonneg size hnn
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  exact ⟨by omega, hmax⟩

end JuliaLean.BootCov.DefaultCtors

end


namespace JuliaLean.Proofs.base.essentials

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials JuliaLean.Registry

def productValue (dims : List (JInt .i64)) : Int :=
  dims.foldl (fun acc d => acc * d.val) 1

def CartesianIsEmpty : Prop :=
  ∀ dims : List (JInt .i64), (∀ d ∈ dims, 0 ≤ d.val) →
    ((prodDims dims).val = 0 ↔ ∃ d, d ∈ dims ∧ d.val = 0)

def DefaultCtorAccessesInBounds : Prop :=
  (∀ (names : List JVal) (fieldTypes : List JType),
    names.length = fieldTypes.length →
    (∀ name, name ∈ names → ∃ symbol, name = .sym symbol) →
    ∃ argnames nany,
      argnamesLoop 1 names fieldTypes (setAt (undefArr (fieldTypes.length + 1)) 1 (.sym "#ctor-self#")) 0 =
        .ok (argnames, nany) ∧ argnames.length = fieldTypes.length + 1) ∧
  (∀ n, (curlyLoop 1 n (undefArr (n + 1))).length = n + 1) ∧
  (∀ n, (newArgsLoop 1 n (undefArr (n + 1))).length = n + 1) ∧
  (∀ fieldTypes, (atypesLoop 1 fieldTypes (undefArr (fieldTypes.length + 1))).length = fieldTypes.length + 1) ∧
  (∀ n, (anyArgsLoop 1 n (undefArr (n + 1))).length = n + 1) ∧
  (∀ fieldTypes (nany : Nat), nany ≤ fieldTypes.length →
    let (body, args) := innerLoop 1 1 fieldTypes
      (undefArr ((fieldTypes.length - nany) * 2 + 1)) (undefArr fieldTypes.length)
    body.length = (fieldTypes.length - nany) * 2 + 1 ∧ args.length = fieldTypes.length)

def expectedEffectMeta (internal : Bool) (flags : List Bool) : JVal :=
  if internal then .expr "meta" [.expr "purity" (flags.map JVal.bool)] else .bool false

def BaseEffectMetasMatchAssume : Prop :=
  ∀ (ms : Modules) (module_ : Module),
    nameofModule module_ = .sym (moduleName module_) ∧
    (isInternal ms module_ = (baseRelativeTo ms module_).map (fun rel =>
      moduleName module_ == "Base" || moduleName rel == "Compiler")) ∧
    totalMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [true, true, true, true, false, true, true, true, false, false, true]) ∧
    foldableMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [true, true, false, true, false, true, true, true, false, false, true]) ∧
    terminatesLocallyMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, false, true, false, false, false, false, false, false]) ∧
    terminatesGloballyMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, true, true, false, false, false, false, false, false]) ∧
    terminatesGloballyNotaskstateMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, true, true, true, false, false, false, false, false]) ∧
    terminatesGloballyNoubMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, true, true, false, false, true, false, false, false]) ∧
    effectFreeTerminatesLocallyMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, true, false, false, true, false, false, false, false, false, false]) ∧
    nothrowNoubMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, true, false, false, false, false, true, false, false, false]) ∧
    nothrowMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, true, false, false, false, false, false, false, false, false]) ∧
    noubMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, false, false, false, false, true, false, false, false]) ∧
    notaskstateMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, false, false, true, false, false, false, false, false]) ∧
    noubIfNoinboundsMeta ms module_ = (isInternal ms module_).map (fun internal => expectedEffectMeta internal
      [false, false, false, false, false, false, false, false, true, false, false])

def CheckboundsBoolCorrect : Prop :=
  ∀ (len i : JInt .i64), 0 ≤ len.val →
    (checkboundsBool len i = true ↔ 1 ≤ i.val ∧ i.val ≤ len.val)

def AccessSemantics : Prop :=
  (∀ (memory : Mem) (o : MemObj) (heap : Heap) (i : JInt .i64),
    heap[memory.handle]? = some o → o.slots.length < 2 ^ 63 →
    ¬ (1 ≤ i.val ∧ i.val ≤ o.slots.length) →
      (getindexGenericMemory true memory i).run heap = some (.error (.core .bounds))) ∧
  (∀ (atomic : Bool), defaultAccessOrder atomic = (if atomic then "monotonic" else "not_atomic") ∧
    defaultAccessOrderMemory atomic = (if atomic then "monotonic" else "not_atomic") ∧
    defaultAccessOrderRef atomic = (if atomic then "monotonic" else "not_atomic") ∧
    defaultAccessOrderMemoryRef atomic = (if atomic then "monotonic" else "not_atomic")) ∧
  (∀ {A D : Type} (getfield : A → String → D) a, sizeArray getfield a = getfield a "size") ∧
  (∀ (memory : Mem) (o : MemObj) (heap : Heap), heap[memory.handle]? = some o →
    (sizeGenericMemory memory).run heap = some (.ok ([JInt.wrap .i64 o.slots.length], heap))) ∧
  (∀ {A I : Type} (check : A → List I → Bool)
      (throwBounds : A → List I → Except Exc Unit) a indices,
    check a indices = true → checkboundsGeneric check throwBounds a indices = .ok ()) ∧
  (∀ (ref : MRef) (o : MemObj) (heap : Heap), heap[ref.mem.handle]? = some o →
    (getindexGenericMemoryRef false ref).run heap =
      (memoryrefget ref (defaultAccessOrderMemoryRef o.atomic) false).run heap)

def SvecSemantics : Prop :=
  (∀ v : SVecObj,
    lengthSVec v = v.slots.length ∧ firstindexSVec v = 1 ∧
      lastindexSVec v = v.slots.length ∧ keysSVec v = v.slots.length ∧
      eltypeSVec = "Any" ∧ axesSVec v = [v.slots.length] ∧
      isemptySVec v = decide (v.slots.length = 0)) ∧
  (∀ (v : SVecObj) (i : Int), (lengthSVec v : Int) < i → iterateSVec v i = .ok none) ∧
  (∀ (v : SVecObj) (i : Nat) (value : JVal),
    getindexSVec v (i : Int) = .ok value → i ≤ lengthSVec v →
      iterateSVec v i = .ok (some (value, i + 1))) ∧
  (∀ (eq : JVal → JVal → RE JVal) (v : SVecObj),
    (∀ s ∈ v.slots, s.isSome) → (∀ x, eq x x = .ok (.bool true)) → equalSVec eq v v = .ok true) ∧
  (∀ (g : JVal → JVal) (v : SVecObj) (heap heap' : Heap) (result : Arr),
    lengthSVec v < 2 ^ 62 →
    (mapSVec (fun x => pure (g x)) v).run heap = some (.ok (result, heap')) →
      result.size = [JInt.wrap .i64 (lengthSVec v)] ∧
      ∀ i value, i < lengthSVec v → getindexSVec v ((i : Int) + 1) = .ok value →
        (heap'[result.ref.mem.handle]?).bind (fun o => o.slots[result.ref.index + i]?) =
          some (some (g value))) ∧
  (∀ (v : SVecObj) (indices values : List JVal) (addr : JInt .u64) (heap : Heap),
    indices.length < 2 ^ 62 →
    indices.mapM (getindexSVecValue v) = .ok values →
      ∃ heap', (getindexSVecArray (fun (l : List JVal) => pure [JInt.wrap .i64 l.length])
        (fun (l : List JVal) (st : Option Nat) =>
          pure ((l[st.getD 0]?).map fun x => (x, st.getD 0 + 1)))
        addr v indices).run heap = some (.ok (⟨addr, values.map some⟩, heap')))

def SvecIsassignedCorrect : Prop :=
  ∀ (v : SVecObj) (i : Int), (∀ s ∈ v.slots, s.isSome) →
    (isassignedSVec v i = true ↔
      1 ≤ i ∧ i ≤ (v.slots.length : Int) ∧ ∃ x, v.slots[(i - 1).toNat]? = some (some x))

def UnwrapRewrap : Prop :=
  (∀ u, isUnionAll u = false → unwrapUnionall u = u) ∧
  (∀ t u, isUnionAll u = false → rewrapUnionall t u = .ok t) ∧
  (∀ (N : Option JType) u, rewrapUnionallVararg none N u = .ok (.vararg none N)) ∧
  (∀ widen t root, widenDiagonal widen t root = widen t root)

def RenameUnionall : Prop :=
  (∀ (typevarInfo : JType → Except Exc (String × JType × JType))
    (unionAll : JType → JType → Except Exc JType)
    (typevar : String → JType → JType → JType)
    (instantiate : JType → JType → Except Exc JType) u,
    isUnionAll u = false → renameUnionall typevarInfo unionAll typevar instantiate u = .ok u) ∧
  (∀ widen t root, widenDiagonal widen t root = widen t root)

def VarargHelpers : Prop :=
  (∀ t, isvarargtype t = true ↔ ∃ T N, t = .vararg T N) ∧
  (∀ t, isvatuple t = true ↔
    ∃ name abs params va, unwrapUnionall t = .dt name abs params ∧
      params.getLast? = some va ∧ isvarargtype va = true) ∧
  (∀ (any : JType) T N, unwrapva any (.vararg (some T) N) = T) ∧
  (∀ any N, unwrapva any (.vararg none N) = any) ∧
  (∀ va, unconstrainVarargLength va = .vararg (some (unwrapva (.dt "Any" true []) va)) none)

def MinNinitialized : Prop :=
  (∀ (isabstract : JType → Bool) fields uninitialized t,
    isabstract (unwrapUnionall t) = true →
      datatypeMinNinitialized isabstract fields uninitialized t = 0) ∧
  (∀ (isabstract : JType → Bool) fields uninitialized params,
    isabstract (.dt "Tuple" false params) = false →
      datatypeMinNinitialized isabstract fields uninitialized (.dt "Tuple" false params) =
        if params.isEmpty then 0 else match params.getLast? with
          | some (.vararg _ (some (.intParam n))) => (params.length : Int) - 1 + n
          | some (.vararg _ _) => (params.length : Int) - 1
          | _ => params.length)

def HasTypevarBehaviour : Prop :=
  (∀ (ccall : JType → JType → Int32) id name lb ub,
    ccall (.tvar id name lb ub) (.tvar id name lb ub) != 0 →
      hasTypevar ccall (.tvar id name lb ub) (.tvar id name lb ub) = true) ∧
  (∀ (ccall : JType → JType → Int32) t v,
    ccall t v != 0 → hasTypevar ccall t v = true) ∧
  (∀ (ccall : JType → JType → Int32) id name lb ub body,
    ccall (.unionAll (.tvar id name lb ub) body) (.tvar id name lb ub) = 0 →
      hasTypevar ccall (.unionAll (.tvar id name lb ub) body) (.tvar id name lb ub) = false)

def TupleHelpers : Prop :=
  (∀ {α : Type} (x : α) xs, tail (α := α) (x :: xs) = .ok (argtail x xs)) ∧
  (∀ {α : Type}, ∃ message, tailEmpty (α := α) = .error (.argument message)) ∧
  (∀ {T X Y A : Type} (disjoint : Nat → T → Bool) (fieldtype : T → Nat → Y)
      (getfield : X → Nat → A) (isa : Y → A → Bool) (convert : Y → A → Except Exc A)
      (ntuple : Nat → (Nat → Except Exc A) → Except Exc (List A)) target x n,
    disjoint n target = true →
      convertTuple disjoint fieldtype getfield isa (fun _ _ _ => rfl) convert ntuple target x n = tupleError target x) ∧
  (∀ {T X Y A : Type} (disjoint : Nat → T → Bool) (fieldtype : T → Nat → Y)
      (getfield : X → Nat → A) (isa : Y → A → Bool) (convert : Y → A → Except Exc A)
      (ntuple : Nat → (Nat → Except Exc A) → Except Exc (List A)) target x n result,
    convertTuple disjoint fieldtype getfield isa (fun _ _ _ => rfl) convert ntuple target x n = .ok result → result.length = n)

def ThrowBoundserrorForms : Prop :=
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a,
    throwBoundserror throwBounds a = throwBounds a []) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a I,
    throwBoundserrorIndices throwBounds a I = throwBounds a I) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a i1 i2 I,
    throwBoundserrorMany throwBounds a i1 i2 I = throwBounds a (i1 :: i2 :: I)) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a,
    throwBoundserrorIndicesEmpty throwBounds a = throwBounds a []) ∧
  (∀ {A I R : Type} (throwBounds : A → List I → Except Exc R) a i1 I,
    throwBoundserrorIndicesMany throwBounds a i1 I = throwBounds a (i1 :: I))

def GlobalRefEq : Prop :=
  ∀ a b : GlobalRefV, globalRefEq a b = true ↔ a.mod.id = b.mod.id ∧ a.name = b.name

def OftypeSpec : Prop :=
  (∀ {α : Type} (isa : α → α → Bool) (convert : α → α → Except Exc α) x y,
    isa x y = true → oftype isa (fun _ _ _ => rfl) convert x y = .ok y) ∧
  (∀ {α : Type} (isa : α → α → Bool) (convert : α → α → Except Exc α) x y result,
    isa x y = false → convert x y = .ok result → oftype isa (fun _ _ _ => rfl) convert x y = .ok result)

def SignedUnsignedInt : Prop :=
  (∀ x : JInt .i64, (unsignedInt x).val = wrapInt .u64 x.val) ∧
  (∀ x : JInt .u64, (signedUInt x).val = wrapInt .i64 x.val)

def ReinterpretSpec : Prop :=
  ∀ {O X R : Type} (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) out x,
    isPrimitiveOut out = true → isPrimitiveValue x = true →
      reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = bitcast out x

def SizeofSpec : Prop :=
  ∀ {X N : Type} (coreSizeof : X → N) x, sizeof coreSizeof x = coreSizeof x

def IsemptySpec : Prop :=
  (∀ {I S : Type} (isdone : I → List S → Option Bool)
      (iterate : I → List S → Option (S × List S)) itr state done_,
    isdone itr state = some done_ → isempty isdone iterate itr state = done_) ∧
  (∀ {I S : Type} (isdone : I → List S → Option Bool)
      (iterate : I → List S → Option (S × List S)) itr state,
    isdone itr state = none → isempty isdone iterate itr state = (iterate itr state).isNone)

def IntAddSub : Prop :=
  ∀ x y : JInt .i64,
    (JuliaLean.base.essentials.addInt x y).val = wrapInt .i64 (x.val + y.val) ∧
    (JuliaLean.base.essentials.subInt x y).val = wrapInt .i64 (x.val - y.val)

def IsmissingSpec : Prop :=
  ∀ {α : Type} (isMissing : α → Bool) x, ismissing isMissing x = isMissing x

def ResolveInWorld : Prop :=
  (∀ {W G R : Type} (toUInt : W → Except Exc G)
      (invokeInWorld : G → String → String → R) world gr unsignedWorld,
    toUInt world = .ok unsignedWorld →
      resolveInWorld toUInt invokeInWorld world gr = .ok (invokeInWorld unsignedWorld gr.1 gr.2)) ∧
  (∀ {W G R : Type} (toUInt : W → Except Exc G)
      (invokeInWorld : G → String → String → R) world gr e,
    toUInt world = .error e → resolveInWorld toUInt invokeInWorld world gr = .error e)

def LengthAbstractSpec : Prop :=
  ∀ dims : List (JInt .i64),
    (lengthAbstract (fun (_ : Unit) => dims) prodDims ()).val =
      wrapInt .i64 (productValue dims)

def hasConvertStmt : JVal → Bool
  | .expr "=" [_, .expr "if" [_, _, .expr "call" (.globalRef "Base" "convert" :: _)]] => true
  | _ => false

def lambdaHasConvert : JVal → Bool
  | .expr "lambda" (_ :: .expr "block" body :: _) => body.any hasConvertStmt
  | _ => false

def DefaultctorsSpec : Prop :=
  ∀ (ops : DefaultCtorOps) (ty : JType) (location : JVal)
    (dt : JType) (tvars fields : List JType) (methods : List MethodDef),
    defaultctorTypeinfo ops.getFieldtypes ty = .ok (dt, tvars, fields) →
    defaultctors ops (.ty ty) location = .ok methods →
    let constrained := fieldtypesConstrainTypevars ops.ccallHasTypevar ops.isTypevar ops.upperBound ops.sameType tvars fields
    methods.length = (match constrained with
      | .ok true => if tvars.isEmpty && allAnyLoop fields then 1 else 2
      | _ => 1) ∧
    (constrained = .ok true →
      (if tvars.isEmpty && allAnyLoop fields then methods.length = 1
       else ∃ outer inner, methods = [outer, inner] ∧
         (fields.any (fun ft => !isAnyTy ft) = true → lambdaHasConvert inner.lambda = true))) ∧
    (constrained ≠ .ok true →
      ∃ inner, methods = [inner] ∧
        (fields.any (fun ft => !isAnyTy ft) = true → lambdaHasConvert inner.lambda = true))

def BaseMarkerMacros : Prop :=
  (∀ args, nospecialize [.expr "=" args] = .expr "escape" [.expr "meta" [.sym "nospecialize", .expr "kw" args]]) ∧
  (∀ args, specialize [.expr "=" args] = .expr "escape" [.expr "meta" [.sym "specialize", .expr "kw" args]]) ∧
  (∀ x, gcPreserveBegin x = .expr "gc_preserve_begin" [JuliaLean.base.essentials.esc x] ∧
    gcPreserveEnd x = .expr "gc_preserve_end" [JuliaLean.base.essentials.esc x]) ∧
  (∀ s, isdefinedMacro s = .expr "escape" [.expr "isdefined" [.sym s]]) ∧
  (∀ block, boundscheckMacro block = .expr "if" [.expr "boundscheck" [], JuliaLean.base.essentials.esc block]) ∧
  (∀ block, inboundsMacro block = .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", JuliaLean.base.essentials.esc block]],
    .expr "inbounds" [.sym "pop"], .sym "val"]) ∧
  propagateInboundsMeta = .expr "meta" [.sym "inline", .sym "propagate_inbounds"] ∧
  nospecializeinferMeta = .expr "meta" [.sym "nospecializeinfer"] ∧
  (∀ (esc : JVal → JVal) module_ ex,
    evalMacro1 esc module_ ex = .expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", module_, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ (esc : JVal → JVal) mod ex,
    evalMacro2 esc mod ex = .expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ x, JuliaLean.base.essentials.esc x = .expr "escape" [x]) ∧
  (∃ message, label1 "_" = .error (.error message)) ∧
  (∀ name, name ≠ "_" → label1 name = .ok (JuliaLean.base.essentials.esc (.expr "symboliclabel" [.sym name]))) ∧
  (∀ body, ∃ message, label2 "_" body = .error (.error message)) ∧
  (∀ name body, name ≠ "_" →
    (∀ args, body ≠ .expr "for" args) → (∀ args, body ≠ .expr "while" args) →
    label2 name body = .ok (JuliaLean.base.essentials.esc (.expr "symbolicblock" [.sym name, body]))) ∧
  (∀ name iter loopBody, name ≠ "_" →
    label2 name (.expr "for" [iter, loopBody]) = .ok (JuliaLean.base.essentials.esc
      (.expr "symbolicblock" [.sym name, .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]]))) ∧
  (∀ name condition loopBody, name ≠ "_" →
    label2 name (.expr "while" [condition, loopBody]) = .ok (JuliaLean.base.essentials.esc
      (.expr "symbolicblock" [.sym name, .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]]))) ∧
  (∀ body, label0 body = JuliaLean.base.essentials.esc (.expr "symbolicblock" [.sym "loop-exit", body])) ∧
  (∀ name, gotoMacro name = JuliaLean.base.essentials.esc (.expr "symbolicgoto" [.sym name])) ∧
  (∀ (lineNumber : JVal → Except Exc JVal) source,
    lineMacro lineNumber source = lineNumber source) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ name world,
    world ≠ .sym "∞" → worldMacro moduleName getWorldCounter module_ (.sym name) world =
      .ok (.expr "call" [.globalRef "Base" "_resolve_in_world",
        JuliaLean.base.essentials.esc world,
        .quoteNode (.globalRef (moduleName module_) name)])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ m name world,
    world ≠ .sym "∞" → worldMacro moduleName getWorldCounter module_ (.globalRef m name) world =
      .ok (.expr "call" [.globalRef "Base" "_resolve_in_world",
        JuliaLean.base.essentials.esc world, .quoteNode (.globalRef m name)])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ value name world,
    world ≠ .sym "∞" →
      worldMacro moduleName getWorldCounter module_ (.expr "." [value, .quoteNode (.sym name)]) world =
        .ok (.expr "call" [.globalRef "Base" "_resolve_in_world", JuliaLean.base.essentials.esc world,
          .expr "globalref" [JuliaLean.base.essentials.esc value, .quoteNode (.sym name)]])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ world,
    ∃ message, worldMacro moduleName getWorldCounter module_ (.bool true) world = .error (.error message))

def Barriers : Prop :=
  (∀ {α : Type} (x : α), blackbox x = .ok x ∧ inferencebarrier x = .ok x) ∧
  (∀ {α : Type} (iterator : α), values iterator = iterator)

def ConversionCases : Prop :=
  (∀ {α : Type} (x : α), convertTypeIdentity x = x ∧ unsafeConvertIdentity x = x) ∧
  (∀ {T X : Type} (isa : X → Bool) (assert : X → T) (convert : X → Except Exc T) x,
    isa x = true → cconvert isa assert convert x = .ok (assert x)) ∧
  (∀ {T X : Type} (isa : X → Bool) (assert : X → T) (convert : X → Except Exc T) x,
    isa x = false → cconvert isa assert convert x = convert x) ∧
  (∀ {X R : Type} (convert : List X → Except Exc R) xs,
    cconvertUnionBottom convert xs = convert xs) ∧
  (∀ {α : Type} (x : α), cconvertPointer x = x) ∧
  (∀ {P Ptr R : Type} (convert : P → Ptr → R) p ptr,
    unsafeConvertPointer convert p ptr = convert p ptr) ∧
  (∀ {R : Type} (stringPointer : String → R) s,
    unsafeConvertStringUInt8 stringPointer s = stringPointer s ∧
    unsafeConvertStringInt8 stringPointer s = stringPointer s) ∧
  (∀ {α R : Type} (xs : List α), convertUnionBottom (R := R) xs =
    .error (.argument "cannot convert a value to Union{} for assignment"))

/-- Identity conversions, eager/deferred C conversion, and both reinterpret
dispatch branches, over every input accepted by the installed wrappers. -/
def ConversionSpec : Prop :=
  ConversionCases ∧
  (∀ s : String, convertStringIdentity s = s) ∧
  (∀ {A : Type} (x : A), unsafeConvertPointerIdentity x = x) ∧
  (∀ {O X R : Type} (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) (out : O) (x : X),
    (isPrimitiveOut out = true → isPrimitiveValue x = true →
      reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = bitcast out x) ∧
    (isPrimitiveOut out = false →
      reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = full out x) ∧
    (isPrimitiveValue x = false →
      reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = full out x)) ∧
  (∀ {X N : Type} (coreSizeof : X → N) (x : X), sizeof coreSizeof x = coreSizeof x)

def IfelseSpec : Prop :=
  ∀ {α : Type} (x y : α), JuliaLean.base.essentials.ifelse true x y = x ∧ JuliaLean.base.essentials.ifelse false x y = y

def NotBool : Prop :=
  notBool true = false ∧ notBool false = true

def IsdoneDefault : Prop :=
  ∀ {m : Type → Type} [Monad m] {α : Type} (x : α),
    JuliaLean.base.essentials.isdoneDefault (m := m) x = pure missingV

def IsiterableSpec : Prop :=
  ∀ {T : Type} (hasmethod : T → Bool) t, isiterable hasmethod t = hasmethod t


def ArrayAccessCases : Prop :=
  (∀ (a : Arr) (i : JInt .i64) (r : MRef) (v : JVal) (heap : Heap),
    (memoryrefnewRef a.ref i false).run heap = some (.ok (r, heap)) →
    (memoryrefget r "not_atomic" false).run heap = some (.ok (v, heap)) →
      (getindexArray false a i).run heap = some (.ok (v, heap))) ∧
  (∀ (memory : Mem) (i : JInt .i64) (x : JVal) (r : MRef) (heap heap' : Heap),
    (memoryrefnewMem memory i false).run heap = some (.ok (r, heap)) →
    (memoryrefset r x "not_atomic" false).run heap = some (.ok (x, heap')) →
      (setindexMemoryAny false memory x i).run heap = some (.ok (memory, heap'))) ∧
  (∀ (convert : JType → JVal → RE JVal) (T : JType) (ref : MRef) (x : JVal) (heap : Heap) e,
    convert T x = .error e →
      (setindexMemoryRef convert T false ref x).run heap = some (.error e)) ∧
  (∀ (ref : MRef) (x : JVal) (heap heap' : Heap),
    (memoryrefset ref x "not_atomic" false).run heap = some (.ok (x, heap')) →
      (setindexMemoryRefAny false ref x).run heap = some (.ok (ref, heap')))

/-- For a valid non-atomic array backing store, indexing reads its selected
slot and assignment replaces exactly that slot while retaining array identity.
Both checked and unchecked modes cover every valid linear array index. -/
def ArrayAccessSpec : Prop :=
  ArrayAccessCases ∧
  (∀ (checked : Bool) (a : Arr) (i : JInt .i64) (x : JVal)
    (heap : Heap) (o : MemObj),
    heap[a.ref.mem.handle]? = some o → o.atomic = false →
    o.slots.length < 2 ^ 63 →
    0 ≤ (prodDims a.size).val →
    a.ref.index + (prodDims a.size).val.toNat ≤ o.slots.length →
    1 ≤ i.val → i.val ≤ (prodDims a.size).val →
    let k := a.ref.index + (i.val - 1).toNat
    (∀ value, o.slots[k]? = some (some value) →
      (getindexArray checked a i).run heap = some (.ok (value, heap))) ∧
    (o.slots[k]? = some none →
      (getindexArray checked a i).run heap = some (.error (.core .undefRef))) ∧
    (setindexArrayAny checked a x i).run heap =
      some (.ok (a, heap.set a.ref.mem.handle { o with slots := o.slots.set k (some x) }))) ∧
  (∀ (a : Arr) (i : JInt .i64) (x : JVal) (heap : Heap),
    0 ≤ (prodDims a.size).val →
    ¬ (1 ≤ i.val ∧ i.val ≤ (prodDims a.size).val) →
      (getindexArray true a i).run heap = some (.error (.core .bounds)) ∧
      (setindexArrayAny true a x i).run heap = some (.error (.core .bounds))) ∧
  (∀ (checked : Bool) (memory : Mem) (i : JInt .i64) (x : JVal)
    (heap : Heap) (o : MemObj),
    heap[memory.handle]? = some o → o.atomic = false →
    o.slots.length < 2 ^ 63 → 1 ≤ i.val → i.val ≤ o.slots.length →
      (setindexMemoryAny checked memory x i).run heap =
        some (.ok (memory, heap.set memory.handle
          { o with slots := o.slots.set (i.val - 1).toNat (some x) }))) ∧
  (∀ (checked : Bool) (ref : MRef) (x : JVal) (heap : Heap) (o : MemObj),
    heap[ref.mem.handle]? = some o → o.atomic = false → ref.index < o.slots.length →
      (setindexMemoryRefAny checked ref x).run heap =
        some (.ok (ref, heap.set ref.mem.handle
          { o with slots := o.slots.set ref.index (some x) }))) ∧
  (∀ (convert : JType → JVal → RE JVal) (T : JType) (checked : Bool)
    (ref : MRef) (x value : JVal) (heap : Heap) (o : MemObj),
    heap[ref.mem.handle]? = some o → o.atomic = false → ref.index < o.slots.length →
    convert T x = .ok value →
      (setindexMemoryRef convert T checked ref x).run heap =
        some (.ok (ref, heap.set ref.mem.handle
          { o with slots := o.slots.set ref.index (some value) })))

def FieldtypesConstrainSpec : Prop :=
  ∀ (ccall : JType → JType → Int32) (isTypevar : JType → Bool)
    (upperBound : JType → JType) (sameType : JType → JType → Bool)
    (tvars fields : List JType),
    (∀ tv, tv ∈ tvars → isTypevar tv = true) →
    (∀ tv, tv ∈ tvars → fields.any (fun ft => hasTypevar ccall ft tv) = true) →
      fieldtypesConstrainTypevars ccall isTypevar upperBound sameType tvars fields = .ok true

def unionallVars : JType → List JType
  | .unionAll var body => var :: unionallVars body
  | _ => []

def isDataType : JType → Bool
  | .dt _ _ _ => true
  | _ => false

def TypeinfoSpec : Prop :=
  ∀ (fieldtypes : JType → List JType) (ty : JType),
    if isDataType (unwrapUnionall ty) then
      defaultctorTypeinfo fieldtypes ty =
        .ok (unwrapUnionall ty, unionallVars ty, fieldtypes (unwrapUnionall ty))
    else defaultctorTypeinfo fieldtypes ty = .error (.typeError "typeassert")

def PairsAndColonVal : Prop :=
  (∀ {K V I A : Type} (data : A) (iter : I),
    pairsCtorKV data iter = (⟨data, iter⟩ : PairsModel K V I A)) ∧
  (∀ {K I A : Type} (eltype : Type → Type) (data : A) (iter : I),
    pairsCtorK eltype data iter = (⟨data, iter⟩ : PairsModel K (eltype A) I A)) ∧
  (∀ {A I : Type} (isNothingI : Bool) (eltype keytype : Type → Type) (data : A) (iter : I),
    pairsCtor isNothingI eltype keytype data iter =
      (⟨data, iter⟩ : PairsModel (if isNothingI then keytype A else eltype I) (eltype A) I A)) ∧
  (∀ {K V I A D J : Type} (isData : D → Bool) (asData : D → A)
      (convertData : D → Except Exc A) (isIter : J → Bool) (asIter : J → I)
      (convertIter : J → Except Exc I) data iter e,
    isData data = false → convertData data = .error e →
      pairsCtorFull (K := K) (V := V) isData asData convertData isIter asIter convertIter data iter = .error e) ∧
  colonCtor = ColonModel.mk ∧
  (∀ {α : Type} (x : α), valCtor x = ValValue.mk) ∧
  (∃ v nt, pairsNamedTupleType =
    .unionAll v (.unionAll nt (.dt "Pairs" false
      [.dt "Symbol" false [], v, .dt "Nothing" false [], nt])))

/-! Nothing to promise:
- convert@471: this is a generic-function declaration with no method body in this source file.
- cconvert@737: this is a generic-function declaration with no method body in this source file.
- _reinterpret@751: this is a generic-function declaration with no method body in this source file.
- isassigned@1149: this is a generic-function declaration with no method body in this source file.
- popfirst!@1544: this is a generic-function declaration with no method body in this source file.
- peek@1570: this is a generic-function declaration with no method body in this source file.
- iterate@1610: this is a generic-function declaration with no method body in this source file.
-/

/-! Method -> property table:
  blackbox@9 -> essentials-barriers
  size@12 -> bootcov-ess-access
  length@13 -> bootcov-ess-length-abstract
  size@14 -> bootcov-ess-access
  throw_boundserror@15 -> bootcov-ess-throw-boundserror
  throw_boundserror@16 -> bootcov-ess-throw-boundserror
  throw_boundserror@17 -> bootcov-ess-throw-boundserror
  _throw_boundserror_indices@18 -> bootcov-ess-throw-boundserror
  _throw_boundserror_indices@19 -> bootcov-ess-throw-boundserror
  ==@23 -> bootcov-ess-globalref-eq
  _gc_preserve_begin@46 -> essentials-marker-macros
  _gc_preserve_end@50 -> essentials-marker-macros
  nospecialize@125 -> essentials-marker-macros
  specialize@142 -> essentials-marker-macros
  isdefined@184 -> essentials-marker-macros
  _nameof@188 -> bootcov-foldable-meta-effects
  _is_internal@190 -> bootcov-foldable-meta-effects
  _total_meta@196 -> bootcov-foldable-meta-effects
  _foldable_meta@211 -> bootcov-foldable-meta-effects
  _terminates_locally_meta@226 -> bootcov-foldable-meta-effects
  _terminates_globally_meta@241 -> bootcov-foldable-meta-effects
  _terminates_globally_notaskstate_meta@256 -> bootcov-foldable-meta-effects
  _terminates_globally_noub_meta@271 -> bootcov-foldable-meta-effects
  _effect_free_terminates_locally_meta@286 -> bootcov-foldable-meta-effects
  _nothrow_noub_meta@301 -> bootcov-foldable-meta-effects
  _nothrow_meta@316 -> bootcov-foldable-meta-effects
  _noub_meta@331 -> bootcov-foldable-meta-effects
  _notaskstate_meta@346 -> bootcov-foldable-meta-effects
  _noub_if_noinbounds_meta@361 -> bootcov-foldable-meta-effects
  _propagate_inbounds_meta@377 -> essentials-marker-macros
  _nospecializeinfer_meta@380 -> essentials-marker-macros
  checkbounds@385 -> bootcov-ess-checkbounds
  checkbounds@389 -> bootcov-ess-checkbounds
  default_access_order@395 -> bootcov-ess-access
  default_access_order@396 -> bootcov-ess-access
  default_access_order@397 -> bootcov-ess-access
  default_access_order@398 -> bootcov-ess-access
  getindex@400 -> bootcov-ess-access
  getindex@406 -> bootcov-ess-access
  nameof@419 -> bootcov-foldable-meta-effects
  convert end@471 -> Nothing to promise: generic declaration only
  convert@474 -> essentials-conversions
  convert@476 -> essentials-conversions
  convert@480 -> essentials-conversions
  eval@488 -> essentials-marker-macros
  eval@495 -> essentials-marker-macros
  Pairs{K, V, I, A}@508 -> essentials-pairs-colon-val
  Pairs{K, V}@509 -> essentials-pairs-colon-val
  Pairs{K}@510 -> essentials-pairs-colon-val
  Pairs@511 -> essentials-pairs-colon-val
  pairs@513 -> essentials-pairs-colon-val
  argtail@523 -> bootcov-ess-tuples
  tail@541 -> bootcov-ess-tuples
  tail@542 -> bootcov-ess-tuples
  unwrap_unionall@544 -> bootcov-ess-unwrap-rewrap
  rewrap_unionall@552 -> bootcov-ess-unwrap-rewrap
  rewrap_unionall@560 -> bootcov-ess-unwrap-rewrap
  rename_unionall@574 -> bootcov-ess-rename
  widen_diagonal@585 -> bootcov-ess-rename
  isvarargtype@589 -> bootcov-ess-vararg
  isvatuple@593 -> bootcov-ess-vararg
  unwrapva@603 -> bootcov-ess-vararg
  unconstrain_vararg_length@608 -> bootcov-ess-vararg
  datatype_min_ninitialized@617 -> bootcov-ess-min-ninit
  _tuple_error@650 -> bootcov-ess-tuples
  convert@652 -> bootcov-ess-tuples
  convert@653 -> bootcov-ess-tuples
  oftype@718 -> bootcov-ess-oftype
  unsigned@720 -> bootcov-ess-signed-unsigned
  signed@721 -> bootcov-ess-signed-unsigned
  cconvert end@737 -> Nothing to promise: generic declaration only
  cconvert@739 -> essentials-conversions
  cconvert@740 -> essentials-conversions
  cconvert@741 -> essentials-conversions
  unsafe_convert@742 -> essentials-conversions
  unsafe_convert@743 -> essentials-conversions
  unsafe_convert@744 -> essentials-conversions
  unsafe_convert@745 -> essentials-conversions
  unsafe_convert@746 -> essentials-conversions
  _reinterpret end@751 -> Nothing to promise: generic declaration only
  reinterpret@787 -> essentials-conversions
  sizeof@841 -> essentials-conversions
  ifelse@894 -> essentials-control
  esc@903 -> essentials-marker-macros
  boundscheck@949 -> essentials-marker-macros
  inbounds@981 -> essentials-marker-macros
  label@1030 -> essentials-marker-macros
  label@1035 -> essentials-marker-macros
  label@1054 -> essentials-marker-macros
  goto@1068 -> essentials-marker-macros
  getindex@1073 -> essentials-array-access
  setindex!@1079 -> essentials-array-access
  setindex!@1085 -> essentials-array-access
  setindex!@1091 -> essentials-array-access
  setindex!@1092 -> essentials-array-access
  getindex@1096 -> bootcov-ess-svec
  length@1097 -> bootcov-ess-svec
  firstindex@1100 -> bootcov-ess-svec
  lastindex@1101 -> bootcov-ess-svec
  iterate@1102 -> bootcov-ess-svec
  eltype@1103 -> bootcov-ess-svec
  keys@1104 -> bootcov-ess-svec
  isempty@1105 -> bootcov-ess-svec
  axes@1106 -> bootcov-ess-svec
  axes@1107 -> bootcov-ess-svec
  ==@1109 -> bootcov-ess-svec
  map@1117 -> bootcov-ess-svec
  getindex@1119 -> bootcov-ess-svec
  unsafe_convert@1121 -> bootcov-ess-svec
  isassigned end@1149 -> Nothing to promise: generic declaration only
  isassigned@1151 -> bootcov-svec-isassigned-undef
  Colon@1170 -> essentials-pairs-colon-val
  show@1174 -> essentials-pairs-colon-val
  Val{x}@1200 -> essentials-pairs-colon-val
  Val@1203 -> essentials-pairs-colon-val
  inferencebarrier@1211 -> essentials-barriers
  isempty@1235 -> bootcov-ess-isempty
  values@1263 -> essentials-barriers
  method@1267 -> bootcov-ess-int-add-sub
  method@1268 -> bootcov-ess-int-add-sub
  !@1294 -> essentials-bool-not
  length@1296 -> bootcov-ess-length-abstract
  has_typevar@1298 -> bootcov-ess-has-typevar
  _fieldtypes_constrain_typevars@1302 -> essentials-fieldtypes-constrain
  _defaultctor_typeinfo@1342 -> essentials-defaultctor-typeinfo
  _defaultctors@1365 -> bootcov-ess-defaultctors
  ismissing@1542 -> bootcov-ess-ismissing
  popfirst! end@1544 -> Nothing to promise: generic declaration only
  peek end@1570 -> Nothing to promise: generic declaration only
  __LINE__@1578 -> essentials-marker-macros
  isdone@1601 -> essentials-iterator-defaults
  iterate end@1610 -> Nothing to promise: generic declaration only
  isiterable@1618 -> essentials-isiterable
  world@1656 -> essentials-marker-macros
  _resolve_in_world@1672 -> bootcov-ess-resolve-in-world
-/


namespace Round1

/-- CartesianIndices is empty exactly when one index axis is empty.
Source: `base/abstractarray.jl:305-313` and `base/essentials.jl:1203-1239`. -/
def CartesianIndicesEmptyByAxis : Prop :=
  ∀ dims : List (JInt .i64), (∀ d ∈ dims, 0 ≤ d.val) →
    ((prodDims dims).val = 0 ↔ ∃ d, d ∈ dims ∧ d.val = 0)

/-- Linear bounds checks accept exactly the one-based indices through the array length.
Source: `base/essentials.jl:385-388`; the `checkbounds(Bool, A, I...)` contract. -/
def CheckboundsBoolRange : Prop :=
  ∀ (len i : JInt .i64), 0 ≤ len.val →
    (checkboundsBool len i = true ↔ 1 ≤ i.val ∧ i.val ≤ len.val)

/-- Signed/unsigned conversion preserves all 64 bits in either direction.
Source: `base/essentials.jl:720-721`. -/
def SignedUnsignedBitRoundTrip : Prop :=
  (∀ x : JInt .i64, (signedUInt (unsignedInt x)).val = x.val) ∧
  (∀ x : JInt .u64, (unsignedInt (signedUInt x)).val = x.val)

/-- Int64 addition and subtraction return results congruent modulo 2^64 to exact arithmetic.
Source: `base/essentials.jl:1267-1268`; Julia's integer overflow contract. -/
def IntAddSubWrap : Prop :=
  ∀ x y : JInt .i64,
    (∃ k : Int, (addInt x y).val = x.val + y.val + k * ((2 : Int) ^ 64)) ∧
    (∃ k : Int, (subInt x y).val = x.val - y.val + k * ((2 : Int) ^ 64))

end Round1

namespace JuliaLean.ChatGPT.Batch3.Group5
open JuliaLean JuliaLean.C JuliaLean.base.essentials

/-- The two axes are lazy unit ranges of length 2^32 in the Julia reproduction. -/
def essentialsOverflowAxis : JInt .i64 := ⟨4294967296, by decide⟩

/-- multidim-cartesianindices-length-overflow: two nonempty lazy axes have a wrapped zero product. -/
theorem MultidimCartesianindicesLengthOverflow_refuted :
    ¬ JuliaLean.Proofs.base.essentials.Round1.CartesianIndicesEmptyByAxis := by
  intro h
  have hnonneg : ∀ d ∈ [essentialsOverflowAxis, essentialsOverflowAxis], 0 ≤ d.val := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hd
    subst d
    decide
  have hzero : (prodDims [essentialsOverflowAxis, essentialsOverflowAxis]).val = 0 := by
    decide
  obtain ⟨d, hd, hz⟩ := (h [essentialsOverflowAxis, essentialsOverflowAxis] hnonneg).mp hzero
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hd
  subst d
  change (4294967296 : Int) = 0 at hz
  omega

theorem essentialsI64Bounds (x : JInt .i64) :
    -(2 : Int) ^ 63 ≤ x.val ∧ x.val < 2 ^ 63 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem essentialsU64Bounds (x : JInt .u64) :
    0 ≤ x.val ∧ x.val < 2 ^ 64 := by
  have h := x.property
  simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at h
  omega

theorem essentialsWrapCongr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;>
    simp at h ⊢ <;> omega

theorem essentialsPowPos (n : Nat) : (0 : Int) < ((2 ^ n : Nat) : Int) := by
  have := Nat.pow_pos (n := n) (by decide : 0 < 2)
  omega

theorem essentialsFromToNat {t : IntTy} (x : JInt t) :
    ((fromJInt x).toNat : Int) = x.val % ((2 ^ t.bits : Nat) : Int) := by
  simp only [fromJInt, BitVec.toNat_ofInt]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by
    have := essentialsPowPos t.bits
    omega))

theorem essentialsToOfInt (t : IntTy) (z : Int) :
    (toJInt t (BitVec.ofInt t.bits z)).val = wrapInt t z := by
  change wrapInt t (if t.signed then (BitVec.ofInt t.bits z).toInt
    else ((BitVec.ofInt t.bits z).toNat : Int)) = wrapInt t z
  apply essentialsWrapCongr
  split
  · rw [BitVec.toInt_ofInt]
    exact Int.bmod_emod
  · rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have := essentialsPowPos t.bits
      omega)), Int.emod_emod]

theorem essentialsToCongr {t : IntTy} (b : BitVec t.bits) (z : Int)
    (h : (b.toNat : Int) = z % ((2 ^ t.bits : Nat) : Int)) :
    (toJInt t b).val = wrapInt t z := by
  have hb : b = BitVec.ofInt t.bits z := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    omega
  rw [hb, essentialsToOfInt]

theorem essentialsBitcastVal (T : IntTy) {t : IntTy} (x : JInt t)
    (h : t.bits = T.bits) :
    (JuliaLean.base.int.bitcast T x h).val = wrapInt T x.val := by
  unfold JuliaLean.base.int.bitcast
  apply essentialsToCongr
  simp only [jlBitcast, BitVec.toNat_cast]
  rw [essentialsFromToNat, h]

theorem essentialsAddVal {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.add_int x y).val = wrapInt t (x.val + y.val) := by
  simp only [JuliaLean.base.int.add_int, jlAddInt, fromJInt]
  rw [← BitVec.ofInt_add, essentialsToOfInt]

theorem essentialsSubVal {t : IntTy} (x y : JInt t) :
    (JuliaLean.base.int.sub_int x y).val = wrapInt t (x.val - y.val) := by
  simp only [JuliaLean.base.int.sub_int, jlSubInt, fromJInt]
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add,
    essentialsToOfInt, Int.sub_eq_add_neg]

theorem essentialsUltU64 (x y : JInt .u64) :
    JuliaLean.base.int.ult_int x y = decide (x.val < y.val) := by
  have hx := essentialsFromToNat x
  have hy := essentialsFromToNat y
  have hxb := essentialsU64Bounds x
  have hyb := essentialsU64Bounds y
  have hxx : ((fromJInt x).toNat : Int) = x.val := by
    rw [essentialsFromToNat]
    change x.val % 18446744073709551616 = x.val
    omega
  have hyy : ((fromJInt y).toNat : Int) = y.val := by
    rw [essentialsFromToNat]
    change y.val % 18446744073709551616 = y.val
    omega
  simp only [JuliaLean.base.int.ult_int, jlUltInt]
  by_cases hl : x.val < y.val
  · simp [hl]
    omega
  · simp [hl]
    omega

theorem essentialsWrapU64Nonneg (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 64) :
    wrapInt .u64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem essentialsWrapU64Neg (v : Int) (h0 : -(2 : Int) ^ 64 < v) (h1 : v < 0) :
    wrapInt .u64 v = v + 2 ^ 64 := by
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem essentialsWrapI64Small (v : Int) (h0 : -(2 : Int) ^ 63 ≤ v) (h1 : v < 2 ^ 63) :
    wrapInt .i64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

/-- bootcov-ess-checkbounds: the unsigned comparison implements the exact one-based interval. -/
theorem BootcovEssCheckbounds_proven :
    JuliaLean.Proofs.base.essentials.Round1.CheckboundsBoolRange := by
  intro len idx h0
  have hl := essentialsI64Bounds len
  have hi := essentialsI64Bounds idx
  simp only [checkboundsBool, essentialsUltU64, decide_eq_true_eq]
  rw [essentialsBitcastVal .u64 (JuliaLean.base.int.sub_int idx
    (JuliaLean.base.int.lit .i64 1)) rfl, essentialsBitcastVal .u64 len rfl,
    essentialsSubVal]
  change wrapInt .u64 (wrapInt .i64 (idx.val - 1)) < wrapInt .u64 len.val ↔ _
  by_cases hi0 : idx.val = -(2 : Int) ^ 63
  · have hw : wrapInt .i64 (idx.val - 1) = 2 ^ 63 - 1 := by
      rw [hi0]
      decide
    rw [hw, essentialsWrapU64Nonneg (2 ^ 63 - 1) (by omega) (by omega),
      essentialsWrapU64Nonneg len.val h0 (by omega)]
    omega
  · rw [essentialsWrapI64Small (idx.val - 1) (by omega) (by omega)]
    rw [essentialsWrapU64Nonneg len.val h0 (by omega)]
    by_cases hp : 0 ≤ idx.val - 1
    · rw [essentialsWrapU64Nonneg (idx.val - 1) hp (by omega)]
      omega
    · rw [essentialsWrapU64Neg (idx.val - 1) (by omega) (by omega)]
      omega

/-- bootcov-ess-signed-unsigned: interpreting the same bits in either signedness is reversible. -/
theorem BootcovEssSignedUnsigned_proven :
    JuliaLean.Proofs.base.essentials.Round1.SignedUnsignedBitRoundTrip := by
  constructor
  · intro x
    have hb := essentialsI64Bounds x
    simp [signedUInt, unsignedInt, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    omega
  · intro x
    have hb := essentialsU64Bounds x
    simp [signedUInt, unsignedInt, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    omega

theorem essentialsWrapCongruence (z : Int) :
    ∃ k : Int, wrapInt .i64 z = z + k * ((2 : Int) ^ 64) := by
  refine ⟨-((z + 2 ^ 63) / 2 ^ 64), ?_⟩
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

/-- bootcov-ess-int-add-sub: the discarded quotient gives the required multiple of 2^64. -/
theorem BootcovEssIntAddSub_proven :
    JuliaLean.Proofs.base.essentials.Round1.IntAddSubWrap := by
  intro x y
  constructor
  · rw [addInt, essentialsAddVal]
    exact essentialsWrapCongruence (x.val + y.val)
  · rw [subInt, essentialsSubVal]
    exact essentialsWrapCongruence (x.val - y.val)

end JuliaLean.ChatGPT.Batch3.Group5
end JuliaLean.Proofs.base.essentials

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.Proofs.base.essentials

theorem BootcovFoldableMetaEffects_proven : JuliaLean.Proofs.base.essentials.BaseEffectMetasMatchAssume := by
  intro ms module_
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold isInternal
  cases baseRelativeTo ms module_ <;> rfl

theorem BootcovEssGlobalrefEq_proven : JuliaLean.Proofs.base.essentials.GlobalRefEq := by
  intro a b
  simp only [globalRefEq, Bool.and_eq_true, beq_iff_eq]

theorem BootcovEssIsempty_proven : JuliaLean.Proofs.base.essentials.IsemptySpec := by
  constructor
  · intro I S isdone iterate itr state done_ h
    simp only [isempty, h]
  · intro I S isdone iterate itr state h
    simp only [isempty, h]

theorem BootcovEssIsmissing_proven : JuliaLean.Proofs.base.essentials.IsmissingSpec := by
  intro α isMissing x
  rfl

theorem EssentialsBarriers_proven : JuliaLean.Proofs.base.essentials.Barriers := by
  refine ⟨?_, ?_⟩
  · intro α x
    exact ⟨rfl, rfl⟩
  · intro α iterator
    rfl

theorem EssentialsConversions_cases : JuliaLean.Proofs.base.essentials.ConversionCases := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α x
    exact ⟨rfl, rfl⟩
  · intro T X isa assert convert x h
    simp only [cconvert, h, ↓reduceIte]
  · intro T X isa assert convert x h
    simp only [cconvert, h, Bool.false_eq_true, ↓reduceIte]
  · intro X R convert xs
    rfl
  · intro α x
    rfl
  · intro P Ptr R convert p ptr
    rfl
  · intro R stringPointer s
    exact ⟨rfl, rfl⟩
  · intro α R xs
    rfl

theorem EssentialsControl_proven : JuliaLean.Proofs.base.essentials.IfelseSpec := by
  intro α x y
  exact ⟨rfl, rfl⟩

theorem EssentialsBoolNot_proven : JuliaLean.Proofs.base.essentials.NotBool := by
  exact ⟨rfl, rfl⟩

theorem EssentialsIteratorDefaults_proven : JuliaLean.Proofs.base.essentials.IsdoneDefault := by
  intro m inst α x
  rfl

theorem EssentialsPairsColonVal_proven : JuliaLean.Proofs.base.essentials.PairsAndColonVal := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro K V I A data iter
    rfl
  · intro K I A eltype data iter
    rfl
  · intro A I isNothingI eltype keytype data iter
    rfl
  · intro K V I A D J isData asData convertData isIter asIter convertIter data iter e hi he
    simp only [pairsCtorFull, hi, Bool.false_eq_true, ↓reduceIte, he, bind, Except.bind]
  · intro α x
    rfl
  · exact ⟨.tvar 0 "V" .bottom (.dt "Any" true []),
      .tvar 1 "NT" .bottom (.dt "NamedTuple" true []), rfl⟩

theorem essGenericStateExceptOptionBindRun {Heap Err α β : Type}
    (action : StateT Heap (ExceptT Err Option) α)
    (next : α → StateT Heap (ExceptT Err Option) β) (heap : Heap) :
    ((action >>= next).run heap) =
      match action.run heap with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (value, heap')) => (next value).run heap' := by
  simp only [StateT.run, bind, StateT.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk]
  cases action heap with
  | none => rfl
  | some result =>
    cases result with
    | error e => rfl
    | ok pair => cases pair; rfl


theorem essHMPureRun {α : Type} (value : α) (heap : Heap) :
    ((pure value : HM α).run heap) = some (.ok (value, heap)) := rfl

theorem essHMThrowRun {α : Type} (e : Err) (heap : Heap) :
    ((throw e : HM α).run heap) = some (.error e) := rfl

theorem essLiftErrorRun {α : Type} (e : Err) (heap : Heap) :
    (liftHM (.error e : RE α)).run heap = some (.error e) := rfl


theorem essWrapI64Emod (z : Int) :
    wrapInt .i64 z % (2 ^ 64) = z % (2 ^ 64) := by
  simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
  omega

theorem essWrapI64Congr {a b : Int}
    (h : a % (2 ^ 64) = b % (2 ^ 64)) :
    wrapInt .i64 a = wrapInt .i64 b := by
  simp only [wrapInt, IntTy.signed, IntTy.bits, ↓reduceIte]
  omega

theorem essWrapMulRight (a b : Int) :
    wrapInt .i64 (a * wrapInt .i64 b) = wrapInt .i64 (a * b) := by
  apply essWrapI64Congr
  rw [Int.mul_emod, essWrapI64Emod, ← Int.mul_emod]

theorem essProductAcc (dims : List (JInt .i64)) (a : Int) :
    dims.foldl (fun acc d => acc * d.val) a =
      a * dims.foldr (fun d acc => d.val * acc) 1 := by
  induction dims generalizing a with
  | nil => simp only [List.foldl_nil, List.foldr_nil, Int.mul_one]
  | cons d ds ih =>
    simp only [List.foldl_cons, List.foldr_cons, ih, Int.mul_assoc]

theorem essProdDimsVal (dims : List (JInt .i64)) :
    (prodDims dims).val = wrapInt .i64 (dims.foldr (fun d acc => d.val * acc) 1) := by
  induction dims with
  | nil => rfl
  | cons d ds ih =>
    change wrapInt .i64 (d.val * (prodDims ds).val) = _
    rw [ih, essWrapMulRight]
    rfl

theorem BootcovEssLengthAbstract_proven : JuliaLean.Proofs.base.essentials.LengthAbstractSpec := by
  intro dims
  unfold lengthAbstract productValue
  rw [essProdDimsVal, essProductAcc, Int.one_mul]

theorem essGenericOftypeTrue {α Err : Type}
    (isa : α → α → Bool) (convert : α → α → Except Err α) (x y : α)
    (h : isa x y = true) :
    (if ht : isa x y = true then
      Except.ok (Eq.mp ((fun _ _ _ => rfl) x y ht : α = α) y)
    else convert x y) = .ok y := by
  rw [dif_pos h] <;> rfl

theorem essGenericOftypeFalse {α Err : Type}
    (isa : α → α → Bool) (convert : α → α → Except Err α) (x y : α)
    (h : isa x y = false) :
    (if ht : isa x y = true then
      Except.ok (Eq.mp ((fun _ _ _ => rfl) x y ht : α = α) y)
    else convert x y) = convert x y := by
  have hn : ¬ isa x y = true := by rw [h]; decide
  rw [dif_neg hn]

theorem essGenericAssignedGet {α : Type} (xs : List (Option α)) (k : Nat)
    (ha : ∀ s ∈ xs, s.isSome) (hk : k < xs.length) :
    ∃ x, xs[k]? = some (some x) := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons a xs ih =>
    cases k with
    | zero =>
      have h : a.isSome := ha a (by simp only [List.mem_cons, true_or])
      cases a with
      | none => cases h
      | some x => exact ⟨x, rfl⟩
    | succ k =>
      have hxs : ∀ s ∈ xs, s.isSome := by
        intro s hs
        exact ha s (by simp only [List.mem_cons]; exact Or.inr hs)
      have hk' : k < xs.length := by simp only [List.length_cons] at hk; omega
      obtain ⟨x, hx⟩ := ih k hxs hk'
      exact ⟨x, hx⟩

theorem essGenericAssignedBounds {α : Type} (xs : List (Option α)) (i : Int)
    (ha : ∀ s ∈ xs, s.isSome) :
    (decide (1 ≤ i ∧ i ≤ (xs.length : Int)) = true ↔
      1 ≤ i ∧ i ≤ (xs.length : Int) ∧ ∃ x, xs[(i - 1).toNat]? = some (some x)) := by
  constructor
  · intro h
    have h := of_decide_eq_true h
    refine ⟨h.1, h.2, essGenericAssignedGet xs (i - 1).toNat ha ?_⟩
    omega
  · intro h
    exact decide_eq_true ⟨h.1, h.2.1⟩

theorem BootcovSvecIsassignedUndef_proven : JuliaLean.Proofs.base.essentials.SvecIsassignedCorrect := by
  intro v i ha
  exact essGenericAssignedBounds v.slots i ha

theorem BootcovEssOftype_proven : JuliaLean.Proofs.base.essentials.OftypeSpec := by
  constructor
  · intro α isa convert x y h
    exact essGenericOftypeTrue isa convert x y h
  · intro α isa convert x y result h hc
    exact (essGenericOftypeFalse isa convert x y h).trans hc

theorem essAssignedGet (xs : List (Option JVal)) (k : Nat)
    (ha : ∀ s ∈ xs, s.isSome) (hk : k < xs.length) :
    ∃ x, xs[k]? = some (some x) := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons a xs ih =>
    cases k with
    | zero =>
      have h : a.isSome := ha a (by simp only [List.mem_cons, true_or])
      cases a with
      | none => cases h
      | some x => exact ⟨x, rfl⟩
    | succ k =>
      have hxs : ∀ s ∈ xs, s.isSome := by
        intro s hs
        exact ha s (by simp only [List.mem_cons]; exact Or.inr hs)
      have hk' : k < xs.length := by simp only [List.length_cons] at hk; omega
      obtain ⟨x, hx⟩ := ih k hxs hk'
      exact ⟨x, hx⟩

theorem essTupleFrontClauses :
  (∀ {α : Type} (x : α) xs, tail (α := α) (x :: xs) = .ok (argtail x xs)) ∧
  (∀ {α : Type}, ∃ message, tailEmpty (α := α) = .error (.argument message)) ∧
  (∀ {T X Y A : Type} (disjoint : Nat → T → Bool) (fieldtype : T → Nat → Y)
      (getfield : X → Nat → A) (isa : Y → A → Bool) (convert : Y → A → Except Exc A)
      (ntuple : Nat → (Nat → Except Exc A) → Except Exc (List A)) target x n,
    disjoint n target = true →
      convertTuple disjoint fieldtype getfield isa (fun _ _ _ => rfl) convert ntuple target x n = tupleError target x) := by
  refine ⟨fun _ _ => rfl, ⟨"Cannot call tail on an empty tuple.", rfl⟩, ?_⟩
  intro T X Y A disjoint fieldtype getfield isa convert ntuple target x n h
  simp only [convertTuple, h, ↓reduceIte]

theorem g17EssUnwrapCore (u : JType)
    (h : (match u with | .unionAll _ _ => true | _ => false) = false) :
    Types.unwrapUnionall u = u := by
  cases u <;> first | rfl | cases h

theorem g17EssRewrapCore (t u : JType)
    (h : (match u with | .unionAll _ _ => true | _ => false) = false) :
    Types.rewrapUnionall t u = .ok t := by
  cases u <;> first | rfl | cases h

theorem g17EssRewrapVarargNoneCore (N : Option JType) (u : JType) :
    Types.rewrapUnionallVararg none N u = .ok (.vararg none N) := by
  rfl

theorem g17EssWidenCore (widen : JType → JType → JType) (t root : JType) :
    Types.widenDiagonal widen t root = widen t root := by
  rfl


theorem g17EssLabel2PlainUnfolded (name : String) (body : JVal) (hn : name ≠ "_")
    (hf : ∀ args, body ≠ .expr "for" args)
    (hw : ∀ args, body ≠ .expr "while" args) :
    (fun (name : String) (body : JVal) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (JVal.expr "escape" [.expr "symbolicblock" [.sym name, body]])) : Except Exc JVal)) name body =
      .ok (JVal.expr "escape" [.expr "symbolicblock" [.sym name, body]]) := by
  dsimp only
  rw [if_neg (by simpa only [beq_iff_eq] using hn)]
  split
  · exact False.elim (hf _ rfl)
  · exact False.elim (hw _ rfl)
  · rfl

theorem g17EssOrdinaryWorldUnfolded (world counter : JVal) (h : world ≠ .sym "∞") :
    (match (generalizing := false) world with
      | .sym "∞" => .expr "call" [counter]
      | other => other) = world := by
  split
  · contradiction
  · rfl

theorem g17EssMarkerMacrosUnfolded :
  (∀ args, (fun (vars : List JVal) =>
    let vars := match vars with
      | [value] => [match value with | .expr "=" args => .expr "kw" args | other => other]
      | _ => vars
    JVal.expr "escape" [.expr "meta" (.sym "nospecialize" :: vars)]) [.expr "=" args] = .expr "escape" [.expr "meta" [.sym "nospecialize", .expr "kw" args]]) ∧
  (∀ args, (fun (vars : List JVal) =>
    let vars := match vars with
      | [value] => [match value with | .expr "=" args => .expr "kw" args | other => other]
      | _ => vars
    JVal.expr "escape" [.expr "meta" (.sym "specialize" :: vars)]) [.expr "=" args] = .expr "escape" [.expr "meta" [.sym "specialize", .expr "kw" args]]) ∧
  (∀ x, (fun (x : JVal) => JVal.expr "gc_preserve_begin" [.expr "escape" [x]]) x = .expr "gc_preserve_begin" [(fun (x : JVal) => JVal.expr "escape" [x]) x] ∧
    (fun (x : JVal) => JVal.expr "gc_preserve_end" [.expr "escape" [x]]) x = .expr "gc_preserve_end" [(fun (x : JVal) => JVal.expr "escape" [x]) x]) ∧
  (∀ s, (fun (s : String) => JVal.expr "escape" [.expr "isdefined" [.sym s]]) s = .expr "escape" [.expr "isdefined" [.sym s]]) ∧
  (∀ block, (fun (block : JVal) => JVal.expr "if" [.expr "boundscheck" [], .expr "escape" [block]]) block = .expr "if" [.expr "boundscheck" [], (fun (x : JVal) => JVal.expr "escape" [x]) block]) ∧
  (∀ block, (fun (block : JVal) => JVal.expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", .expr "escape" [block]]],
    .expr "inbounds" [.sym "pop"], .sym "val"]) block = .expr "block" [.expr "inbounds" [.bool true],
    .expr "local" [.expr "=" [.sym "val", (fun (x : JVal) => JVal.expr "escape" [x]) block]],
    .expr "inbounds" [.sym "pop"], .sym "val"]) ∧
  (JVal.expr "meta" [.sym "inline", .sym "propagate_inbounds"]) = .expr "meta" [.sym "inline", .sym "propagate_inbounds"] ∧
  (JVal.expr "meta" [.sym "nospecializeinfer"]) = .expr "meta" [.sym "nospecializeinfer"] ∧
  (∀ (esc : JVal → JVal) module_ ex,
    (fun (esc : JVal → JVal) (module_ ex : JVal) =>
    JVal.expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", module_, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) esc module_ ex = .expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", module_, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ (esc : JVal → JVal) mod ex,
    (fun (esc : JVal → JVal) (mod ex : JVal) =>
    JVal.expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) esc mod ex = .expr "let" [.expr "=" [.sym "eval_local_result",
      esc (.expr "call" [.globalRef "Core" "eval", mod, .expr "quote" [ex]])],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym "eval_local_result"]]) ∧
  (∀ x, (fun (x : JVal) => JVal.expr "escape" [x]) x = .expr "escape" [x]) ∧
  (∃ message, (fun (name : String) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _` is not allowed")
  else .ok (JVal.expr "escape" [.expr "symboliclabel" [.sym name]])) : Except Exc JVal)) "_" = .error (.error message)) ∧
  (∀ name, name ≠ "_" → (fun (name : String) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _` is not allowed")
  else .ok (JVal.expr "escape" [.expr "symboliclabel" [.sym name]])) : Except Exc JVal)) name = .ok ((fun (x : JVal) => JVal.expr "escape" [x]) (.expr "symboliclabel" [.sym name]))) ∧
  (∀ body, ∃ message, (fun (name : String) (body : JVal) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (JVal.expr "escape" [.expr "symbolicblock" [.sym name, body]])) : Except Exc JVal)) "_" body = .error (.error message)) ∧
  (∀ name body, name ≠ "_" →
    (∀ args, body ≠ .expr "for" args) → (∀ args, body ≠ .expr "while" args) →
    (fun (name : String) (body : JVal) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (JVal.expr "escape" [.expr "symbolicblock" [.sym name, body]])) : Except Exc JVal)) name body = .ok ((fun (x : JVal) => JVal.expr "escape" [x]) (.expr "symbolicblock" [.sym name, body]))) ∧
  (∀ name iter loopBody, name ≠ "_" →
    (fun (name : String) (body : JVal) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (JVal.expr "escape" [.expr "symbolicblock" [.sym name, body]])) : Except Exc JVal)) name (.expr "for" [iter, loopBody]) = .ok ((fun (x : JVal) => JVal.expr "escape" [x])
      (.expr "symbolicblock" [.sym name, .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]]))) ∧
  (∀ name condition loopBody, name ≠ "_" →
    (fun (name : String) (body : JVal) => ((if name == "_" then
    .error (.error "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")
  else
    let body := match body with
      | .expr "for" (iter :: loopBody :: _) =>
        .expr "for" [iter, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | .expr "while" (condition :: loopBody :: _) =>
        .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]
      | other => other
    .ok (JVal.expr "escape" [.expr "symbolicblock" [.sym name, body]])) : Except Exc JVal)) name (.expr "while" [condition, loopBody]) = .ok ((fun (x : JVal) => JVal.expr "escape" [x])
      (.expr "symbolicblock" [.sym name, .expr "while" [condition, .expr "symbolicblock" [.sym (name ++ "#cont"), loopBody]]]))) ∧
  (∀ body, (fun (body : JVal) => JVal.expr "escape" [.expr "symbolicblock" [.sym "loop-exit", body]]) body = (fun (x : JVal) => JVal.expr "escape" [x]) (.expr "symbolicblock" [.sym "loop-exit", body])) ∧
  (∀ name, (fun (name : String) => JVal.expr "escape" [.expr "symbolicgoto" [.sym name]]) name = (fun (x : JVal) => JVal.expr "escape" [x]) (.expr "symbolicgoto" [.sym name])) ∧
  (∀ (lineNumber : JVal → Except Exc JVal) source,
    (fun (lineNumber : JVal → Except Exc JVal) (source : JVal) => lineNumber source) lineNumber source = lineNumber source) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ name world,
    world ≠ .sym "∞" → (fun (moduleName : JVal → String) (getWorldCounter module_ sym world : JVal) =>
  ((let world := match world with
      | .sym "∞" => .expr "call" [getWorldCounter]
      | other => other
    let resolver := JVal.globalRef "Base" "_resolve_in_world"
    match sym with
    | .sym name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef (moduleName module_) name)])
    | .globalRef m name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef m name)])
    | .expr "." [a, .quoteNode (.sym name)] =>
      .ok (.expr "call" [resolver, .expr "escape" [world],
        .expr "globalref" [.expr "escape" [a], .quoteNode (.sym name)]])
    | _ => .error (.error "`@world` requires a symbol or GlobalRef")) : Except Exc JVal)) moduleName getWorldCounter module_ (.sym name) world =
      .ok (.expr "call" [.globalRef "Base" "_resolve_in_world",
        (fun (x : JVal) => JVal.expr "escape" [x]) world,
        .quoteNode (.globalRef (moduleName module_) name)])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ m name world,
    world ≠ .sym "∞" → (fun (moduleName : JVal → String) (getWorldCounter module_ sym world : JVal) =>
  ((let world := match world with
      | .sym "∞" => .expr "call" [getWorldCounter]
      | other => other
    let resolver := JVal.globalRef "Base" "_resolve_in_world"
    match sym with
    | .sym name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef (moduleName module_) name)])
    | .globalRef m name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef m name)])
    | .expr "." [a, .quoteNode (.sym name)] =>
      .ok (.expr "call" [resolver, .expr "escape" [world],
        .expr "globalref" [.expr "escape" [a], .quoteNode (.sym name)]])
    | _ => .error (.error "`@world` requires a symbol or GlobalRef")) : Except Exc JVal)) moduleName getWorldCounter module_ (.globalRef m name) world =
      .ok (.expr "call" [.globalRef "Base" "_resolve_in_world",
        (fun (x : JVal) => JVal.expr "escape" [x]) world, .quoteNode (.globalRef m name)])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ value name world,
    world ≠ .sym "∞" →
      (fun (moduleName : JVal → String) (getWorldCounter module_ sym world : JVal) =>
  ((let world := match world with
      | .sym "∞" => .expr "call" [getWorldCounter]
      | other => other
    let resolver := JVal.globalRef "Base" "_resolve_in_world"
    match sym with
    | .sym name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef (moduleName module_) name)])
    | .globalRef m name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef m name)])
    | .expr "." [a, .quoteNode (.sym name)] =>
      .ok (.expr "call" [resolver, .expr "escape" [world],
        .expr "globalref" [.expr "escape" [a], .quoteNode (.sym name)]])
    | _ => .error (.error "`@world` requires a symbol or GlobalRef")) : Except Exc JVal)) moduleName getWorldCounter module_ (.expr "." [value, .quoteNode (.sym name)]) world =
        .ok (.expr "call" [.globalRef "Base" "_resolve_in_world", (fun (x : JVal) => JVal.expr "escape" [x]) world,
          .expr "globalref" [(fun (x : JVal) => JVal.expr "escape" [x]) value, .quoteNode (.sym name)]])) ∧
  (∀ (moduleName : JVal → String) getWorldCounter module_ world,
    ∃ message, (fun (moduleName : JVal → String) (getWorldCounter module_ sym world : JVal) =>
  ((let world := match world with
      | .sym "∞" => .expr "call" [getWorldCounter]
      | other => other
    let resolver := JVal.globalRef "Base" "_resolve_in_world"
    match sym with
    | .sym name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef (moduleName module_) name)])
    | .globalRef m name => .ok (.expr "call" [resolver, .expr "escape" [world],
        .quoteNode (.globalRef m name)])
    | .expr "." [a, .quoteNode (.sym name)] =>
      .ok (.expr "call" [resolver, .expr "escape" [world],
        .expr "globalref" [.expr "escape" [a], .quoteNode (.sym name)]])
    | _ => .error (.error "`@world` requires a symbol or GlobalRef")) : Except Exc JVal)) moduleName getWorldCounter module_ (.bool true) world = .error (.error message)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro args
    rfl
  · intro args
    rfl
  · intro x
    exact ⟨rfl, rfl⟩
  · intro s
    rfl
  · intro block
    rfl
  · intro block
    rfl
  · intro esc module_ ex
    rfl
  · intro esc mod ex
    rfl
  · intro x
    rfl
  · exact ⟨"use `@label expr` for anonymous blocks; `@label _` is not allowed", rfl⟩
  · intro name h
    simp only [beq_iff_eq, h, ↓reduceIte]
  · intro body
    exact ⟨"use `@label expr` for anonymous blocks; `@label _ expr` is not allowed", rfl⟩
  · exact g17EssLabel2PlainUnfolded
  · intro name iter loopBody h
    simp only [beq_iff_eq, h, ↓reduceIte]
  · intro name condition loopBody h
    simp only [beq_iff_eq, h, ↓reduceIte]
  · intro body
    rfl
  · intro name
    rfl
  · intro lineNumber source
    rfl
  · intro moduleName getWorldCounter module_ name world h
    dsimp only
    rw [g17EssOrdinaryWorldUnfolded world getWorldCounter h] <;> rfl
  · intro moduleName getWorldCounter module_ m name world h
    dsimp only
    rw [g17EssOrdinaryWorldUnfolded world getWorldCounter h] <;> rfl
  · intro moduleName getWorldCounter module_ value name world h
    dsimp only
    rw [g17EssOrdinaryWorldUnfolded world getWorldCounter h] <;> rfl
  · intro moduleName getWorldCounter module_ world
    exact ⟨"`@world` requires a symbol or GlobalRef", rfl⟩

theorem EssentialsMarkerMacros_proven : JuliaLean.Proofs.base.essentials.BaseMarkerMacros := by
  exact g17EssMarkerMacrosUnfolded

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.ChatGPT.Batch8.Group7

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.Proofs.base.essentials

/-- The separate string conversion method returns the same string. -/
theorem g7RestConvertStringIdentity (s : String) : convertStringIdentity s = s := rfl

/-- The pointer-specific identity method returns its argument. -/
theorem g7RestPointerIdentity {A : Type} (x : A) :
    unsafeConvertPointerIdentity x = x := rfl

/-- Primitive inputs select the bitcast branch. -/
theorem g7RestReinterpretPrimitive {O X R : Type}
    (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) (out : O) (x : X)
    (ho : isPrimitiveOut out = true) (hx : isPrimitiveValue x = true) :
    reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = bitcast out x := by
  simp only [reinterpret, ho, hx, Bool.and_self, ↓reduceIte]

/-- Nonprimitive output types select the fully loaded Base fallback. -/
theorem g7RestReinterpretOtherOutput {O X R : Type}
    (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) (out : O) (x : X)
    (ho : isPrimitiveOut out = false) :
    reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = full out x := by
  simp only [reinterpret, ho, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- Nonprimitive input values also select the fallback. -/
theorem g7RestReinterpretOtherInput {O X R : Type}
    (isPrimitiveOut : O → Bool) (isPrimitiveValue : X → Bool)
    (bitcast full : O → X → R) (out : O) (x : X)
    (hx : isPrimitiveValue x = false) :
    reinterpret isPrimitiveOut isPrimitiveValue bitcast full out x = full out x := by
  simp only [reinterpret, hx, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- The size wrapper forwards exactly to its supplied core operation. -/
theorem g7RestSizeofForward {X N : Type} (coreSizeof : X → N) (x : X) :
    sizeof coreSizeof x = coreSizeof x := rfl

theorem EssentialsConversions_proven : JuliaLean.Proofs.base.essentials.ConversionSpec := by
  refine ⟨JuliaLean.ChatGPT.Batch4.Group17.EssentialsConversions_cases,
    g7RestConvertStringIdentity, @g7RestPointerIdentity, ?_, @g7RestSizeofForward⟩
  intro O X R primitiveOut primitiveValue bitcast full out x
  exact ⟨g7RestReinterpretPrimitive primitiveOut primitiveValue bitcast full out x,
    g7RestReinterpretOtherOutput primitiveOut primitiveValue bitcast full out x,
    g7RestReinterpretOtherInput primitiveOut primitiveValue bitcast full out x⟩

end JuliaLean.ChatGPT.Batch8.Group7

namespace JuliaLean.Proofs.base.essentials

open JuliaLean.Registry

def entries : List Entry := [
  { id := "multidim-cartesianindices-length-overflow", juliaFile := "base/essentials.jl",
    juliaFns := ["length(t::AbstractArray)", "isempty(a::AbstractArray)", "size(iter::CartesianIndices)", "getindex(::CartesianIndices, ::Int)"],
    statement := "isempty(CartesianIndices(axes)) is true exactly when at least one axis is empty.", source := "isempty and length semantics; base/abstractarray.jl:305-313; base/essentials.jl:1203-1239",
    status := .refuted, prop := ``Round1.CartesianIndicesEmptyByAxis,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group5.MultidimCartesianindicesLengthOverflow_refuted,
    issue := "none found (queries: issues: CartesianIndices length overflow; prs: CartesianIndices length overflow)" },
  { id := "bootcov-foldable-meta-effects", juliaFile := "base/essentials.jl",
    juliaFns := ["@_total_meta", "@_foldable_meta", "@_terminates_locally_meta", "@_terminates_globally_meta", "@_terminates_globally_notaskstate_meta", "@_terminates_globally_noub_meta", "@_effect_free_terminates_locally_meta", "@_nothrow_noub_meta", "@_nothrow_meta", "@_noub_meta", "@_notaskstate_meta", "@_noub_if_noinbounds_meta", "_is_internal", "_nameof", "nameof(::Module)"],
    statement := "Each Base effect macro emits its documented effect settings inside Base or Compiler and false elsewhere.", source := "base/essentials.jl:188-419; effect macro comments",
    status := .proven, prop := ``BaseEffectMetasMatchAssume, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovFoldableMetaEffects_proven },
  { id := "bootcov-ess-checkbounds", juliaFile := "base/essentials.jl",
    juliaFns := ["checkbounds(::Type{Bool}, ::Union{Array,Memory}, ::Int)"],
    statement := "checkbounds(Bool,A,i) is true exactly for 1 ≤ i ≤ length(A), for every Int index.", source := "checkbounds contract; base/essentials.jl:385-388",
    status := .proven, prop := ``Round1.CheckboundsBoolRange, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.BootcovEssCheckbounds_proven },
  { id := "bootcov-ess-access", juliaFile := "base/essentials.jl",
    juliaFns := ["checkbounds(A,I...)", "default_access_order (4)", "getindex(::GenericMemory,::Int)", "getindex(::GenericMemoryRef)", "getindex(::Array,::Int)", "setindex! (4)", "size(::Array)", "size(::GenericMemory)", "length(::Vector)"],
    statement := "Access methods check bounds, use the documented memory order, and read or write the requested slot.", source := "indexing docstrings; base/essentials.jl:12-14,389-406,1063-1092,1296",
    status := .todo, prop := ``AccessSemantics, notes := "Frozen callback composition does not independently establish that the requested slot is read or written." },
  { id := "bootcov-ess-svec", juliaFile := "base/essentials.jl",
    juliaFns := ["getindex(::SimpleVector,::Int)", "length", "firstindex", "lastindex", "iterate", "eltype", "keys", "isempty", "axes (2)", "==", "map", "getindex(::SimpleVector,::AbstractArray)", "unsafe_convert(::Type{Ptr{Any}},::SimpleVector)"],
    statement := "SimpleVector indexing, iteration, axes, emptiness, equality and mapping agree with its stored elements.", source := "SimpleVector interface; base/essentials.jl:1096-1121",
    status := .todo, prop := ``SvecSemantics, notes := "Basic interface, copy-loop and readback helpers are proved; complete map and selection obligations remain unproved." },
  { id := "bootcov-svec-isassigned-undef", juliaFile := "base/essentials.jl",
    juliaFns := ["isassigned(::SimpleVector,::Int)"],
    statement := "isassigned(v,i) is true exactly when i is in bounds and its slot is assigned.", source := "isassigned docstring; base/essentials.jl:1123-1153",
    status := .proven, prop := ``SvecIsassignedCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovSvecIsassignedUndef_proven },
  { id := "bootcov-ess-unwrap-rewrap", juliaFile := "base/essentials.jl",
    juliaFns := ["unwrap_unionall", "rewrap_unionall", "rewrap_unionall(::TypeofVararg,u)"],
    statement := "unwrap_unionall strips every UnionAll and rewrap restores the enclosing UnionAlls.", source := "invariant; base/essentials.jl:544-571",
    status := .todo, prop := ``UnwrapRewrap, notes := "Frozen predicate covers only the non-UnionAll unwrap case and does not express stripping/restoring every enclosing UnionAll." },
  { id := "bootcov-ess-tuples", juliaFile := "base/essentials.jl",
    juliaFns := ["argtail", "tail (2)", "_tuple_error", "convert(::Type{T},::NTuple{N,Any})", "cvt1"],
    statement := "tail removes the first tuple element and errors on an empty tuple; tuple conversion preserves length and converts fields.", source := "tail and convert docstrings; base/essentials.jl:523-668",
    status := .todo, prop := ``TupleHelpers, notes := "Frozen arbitrary ntuple callbacks have no length contract, so tuple-conversion length preservation is unsupported." },
  { id := "bootcov-ess-globalref-eq", juliaFile := "base/essentials.jl",
    juliaFns := ["==(::GlobalRef,::GlobalRef)"],
    statement := "Two GlobalRefs compare equal exactly when their modules and names match.", source := "invariant; base/essentials.jl:23",
    status := .proven, prop := ``GlobalRefEq, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovEssGlobalrefEq_proven },
  { id := "bootcov-ess-oftype", juliaFile := "base/essentials.jl",
    juliaFns := ["oftype"],
    statement := "oftype returns y when y has x’s type and otherwise converts y to x’s type.", source := "oftype docstring; base/essentials.jl:700-718",
    status := .proven, prop := ``OftypeSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovEssOftype_proven },
  { id := "bootcov-ess-signed-unsigned", juliaFile := "base/essentials.jl",
    juliaFns := ["unsigned(::Int)", "signed(::UInt)"],
    statement := "unsigned and signed reinterpret the bit pattern and invert each other.", source := "signed and unsigned conversion contract; base/essentials.jl:720-721",
    status := .proven, prop := ``Round1.SignedUnsignedBitRoundTrip, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.BootcovEssSignedUnsigned_proven },
  { id := "bootcov-ess-int-add-sub", juliaFile := "base/essentials.jl",
    juliaFns := ["+(::Int,::Int)", "-(::Int,::Int)"],
    statement := "Bootstrap Int addition and subtraction wrap modulo 2^64.", source := "integer overflow manual; base/essentials.jl:1267-1268",
    status := .proven, prop := ``Round1.IntAddSubWrap, thm := some ``JuliaLean.ChatGPT.Batch3.Group5.BootcovEssIntAddSub_proven },
  { id := "bootcov-ess-isempty", juliaFile := "base/essentials.jl",
    juliaFns := ["isempty(itr)"],
    statement := "isempty returns isdone when known, otherwise it checks whether iteration yields nothing.", source := "isempty docstring; base/essentials.jl:1203-1238",
    status := .proven, prop := ``IsemptySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovEssIsempty_proven },
  { id := "bootcov-ess-ismissing", juliaFile := "base/essentials.jl",
    juliaFns := ["ismissing"],
    statement := "ismissing is true exactly for the missing singleton.", source := "ismissing docstring; base/essentials.jl:1525-1542",
    status := .proven, prop := ``IsmissingSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovEssIsmissing_proven },
  { id := "bootcov-ess-length-abstract", juliaFile := "base/essentials.jl",
    juliaFns := ["length(::AbstractArray)"],
    statement := "length(AbstractArray) multiplies its dimensions with Int wrapping.", source := "length docstring; base/abstractarray.jl:305-308",
    status := .proven, prop := ``LengthAbstractSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.BootcovEssLengthAbstract_proven },
  { id := "essentials-marker-macros", juliaFile := "base/essentials.jl",
    juliaFns := ["@_gc_preserve_begin", "@_gc_preserve_end", "@nospecialize", "@specialize", "@isdefined", "@_propagate_inbounds_meta", "@_nospecializeinfer_meta", "@eval (2)", "@boundscheck", "@inbounds", "@label (3)", "@goto", "@__LINE__", "@world"],
    statement := "The marker macros expand to the documented syntax and preserve their argument expressions.", source := "macro docstrings; base/essentials.jl:46-50,125-382,488-501,949-1069",
    status := .proven, prop := ``BaseMarkerMacros, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.EssentialsMarkerMacros_proven },
  { id := "essentials-barriers", juliaFile := "base/essentials.jl",
    juliaFns := ["blackbox", "inferencebarrier", "values"],
    statement := "blackbox and inferencebarrier pass their value through the named compiler barrier; values returns its input.", source := "inferencebarrier and values docstrings; base/essentials.jl:9,1211-1263",
    status := .proven, prop := ``Barriers, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.EssentialsBarriers_proven },
  { id := "essentials-conversions", juliaFile := "base/essentials.jl",
    juliaFns := ["convert(::Type{Union{}},...)", "convert(::Type{Type},::Type)", "convert(::Type{String},::String)", "cconvert (3)", "unsafe_convert (5)", "reinterpret", "sizeof"],
    statement := "Identity conversions preserve their argument, cconvert performs or defers conversion as documented, and reinterpret selects the primitive bitcast path.", source := "convert, cconvert and reinterpret docstrings; base/essentials.jl:423-480,723-841",
    status := .proven, prop := ``ConversionSpec, thm := some ``JuliaLean.ChatGPT.Batch8.Group7.EssentialsConversions_proven },
  { id := "essentials-control", juliaFile := "base/essentials.jl",
    juliaFns := ["ifelse"],
    statement := "ifelse returns the selected value after both arguments have been evaluated.", source := "ifelse docstring; base/essentials.jl:870-894",
    status := .proven, prop := ``IfelseSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.EssentialsControl_proven },
  { id := "essentials-bool-not", juliaFile := "base/essentials.jl",
    juliaFns := ["!(::Bool)"],
    statement := "Boolean negation swaps true and false.", source := "! docstring; base/essentials.jl:1260-1294",
    status := .proven, prop := ``NotBool, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.EssentialsBoolNot_proven },
  { id := "essentials-iterator-defaults", juliaFile := "base/essentials.jl",
    juliaFns := ["isdone(_, _...)"],
    statement := "The fallback isdone method returns missing.", source := "isdone docstring; base/essentials.jl:1573-1601",
    status := .proven, prop := ``IsdoneDefault, thm := some ``JuliaLean.ChatGPT.Batch4.Group17.EssentialsIteratorDefaults_proven },
  { id := "essentials-array-access", juliaFile := "base/essentials.jl",
    juliaFns := ["getindex(::Array,::Int)", "setindex!(::Array{Any},...)", "setindex!(::Memory{Any},...)", "setindex!(::MemoryRef{T},...)", "setindex!(::MemoryRef{Any},...)"],
    statement := "Bootstrap array indexing reads the selected slot, stores the requested value, and returns the array.", source := "base/essentials.jl:1063-1092; index and setindex! contracts",
    status := .todo, prop := ``ArrayAccessSpec, thm := none },
  { id := "essentials-pairs-colon-val", juliaFile := "base/essentials.jl",
    juliaFns := ["Pairs{K,V,I,A}", "Pairs{K,V}", "Pairs{K}", "Pairs", "pairs(::Type{NamedTuple})", "Colon()", "show(::IO,::Colon)", "Val{x}()", "Val(x)"],
    statement := "Pairs constructors retain their declared type parameters, Colon prints as Colon(), and Val(x) creates a Val{x} value.", source := "base/essentials.jl:502-513,1160-1203",
    status := .todo, prop := ``PairsAndColonVal, notes := "Frozen predicate omits the Colon printing promise; abstract Unit-returning callbacks carry no emitted-byte contract." }
]

end JuliaLean.Proofs.base.essentials

namespace JuliaLean.Proofs.base.essentials

open JuliaLean JuliaLean.BootCov JuliaLean.Registry

namespace Models1Group18

/-- Every bound-error helper raises BoundsError for every already-evaluated input.
This is an exception-class invariant; no supplied throwing law is assumed.
Julia source: base/essentials.jl:15-19. -/
def BoundsErrorHelpers : Prop :=
  (∀ {A R : Type} (a : A),
    JuliaLean.base.essentials.Models1Group18.throwBoundserror (R := R) a = .error .bounds) ∧
  (∀ {A I R : Type} (a : A) (i : I),
    JuliaLean.base.essentials.Models1Group18.throwBoundserrorIndices (R := R) a i = .error .bounds) ∧
  (∀ {A I R : Type} (a : A) (i j : I) (rest : List I),
    JuliaLean.base.essentials.Models1Group18.throwBoundserrorMany (R := R) a i j rest = .error .bounds) ∧
  (∀ {A R : Type} (a : A),
    JuliaLean.base.essentials.Models1Group18.throwBoundserrorIndicesEmpty (R := R) a = .error .bounds) ∧
  (∀ {A I R : Type} (a : A) (i : I) (rest : List I),
    JuliaLean.base.essentials.Models1Group18.throwBoundserrorIndicesMany (R := R) a i rest = .error .bounds)

open JuliaLean.base.essentials.Models1Group18


/-- Observable contract for a specialization annotation. The returned expression
is a fresh escaped metadata form retaining every input value and object identity.
There are exactly two new Expr objects. Every old args field is retained, and the
only permissible old-head change is the assignment-to-keyword normalization of
a singleton argument. Existing references, including cyclic and multiply shared
references, therefore continue to observe the same objects.

This predicate constrains observable objects rather than describing a heap-update
algorithm: it does not call a setter, allocation helper, nfields wrapper, or either
macro model, and does not dictate which fresh handles the allocator chooses.
Source: base/essentials.jl:125-151; macro usage requirements at 55-73,136-140;
doc/src/manual/metaprogramming.md:51-67,190-192. -/
def SpecializationHeapObservation {Atom : Type} (tag : String)
    (vars : List (SyntaxValue Atom)) (before : SyntaxHeap Atom)
    (value : SyntaxValue Atom) (after : SyntaxHeap Atom) : Prop :=
  ∃ escapeHandle metadataHandle,
    value = .exprRef escapeHandle ∧
    before.length ≤ escapeHandle ∧ before.length ≤ metadataHandle ∧
    escapeHandle ≠ metadataHandle ∧
    after.length = before.length + 2 ∧
    after[escapeHandle]? = some ⟨"escape", [some (.exprRef metadataHandle)]⟩ ∧
    after[metadataHandle]? = some ⟨"meta", (.symbol tag :: vars).map some⟩ ∧
    syntaxInputValid after [] ∧
    ∀ handle oldNode, before[handle]? = some oldNode →
      ∃ newNode, after[handle]? = some newNode ∧
        newNode.args = oldNode.args ∧
        ((vars = [.exprRef handle] ∧ oldNode.head = "=") → newNode.head = "kw") ∧
        ((vars ≠ [.exprRef handle] ∨ oldNode.head ≠ "=") → newNode.head = oldNode.head)

/-- For every constructible argument Tuple and valid syntax heap, @nospecialize
returns the documented escaped annotation, preserves input identities and all
argument arrays, and repairs an assignment argument in place. Zero/many arguments,
non-Expr values, arbitrary Expr heads and arbitrary cyclic/shared syntax are all
included. The representation premises are pointer validity, machine-sized arrays,
and the UInt32 Tuple field-count limit (base/runtime_internals.jl:624-626).
Source: base/essentials.jl:55-73,125-134. No theorem is supplied. -/
def NospecializeHeapCorrect : Prop :=
  ∀ (Atom : Type) (vars : List (SyntaxValue Atom)) (before : SyntaxHeap Atom),
    syntaxInputValid before vars →
    ∃ value after,
      (nospecializeHeap vars).run before = .ok (value, after) ∧
      SpecializationHeapObservation "nospecialize" vars before value after

/-- @specialize has the same identity-preserving expansion and assignment repair,
with the reset-to-default annotation. This covers its full represented input
domain, without any premise about successful execution or callee correctness.
Source: base/essentials.jl:136-151; base/runtime_internals.jl:624-626.
No theorem is supplied. -/
def SpecializeHeapCorrect : Prop :=
  ∀ (Atom : Type) (vars : List (SyntaxValue Atom)) (before : SyntaxHeap Atom),
    syntaxInputValid before vars →
    ∃ value after,
      (specializeHeap vars).run before = .ok (value, after) ∧
      SpecializationHeapObservation "specialize" vars before value after


/-- Observe only the execution scaffold of an @eval expansion: one Core.eval call
under hygiene escape, its target and protected quoted input, and a world-age
marker before returning that call's bound result. The local variable's spelling
is irrelevant. This observer does not call either model or fix its binder name;
arbitrary target/code syntax is retained as uninterpreted data.
Julia source: base/essentials.jl:482-501. -/
def EvalPayload : JVal → Option (JVal × JVal)
  | .expr "let" [.expr "=" [.sym binding,
      .expr "escape" [.expr "call" [.globalRef "Core" "eval", target,
        .expr "quote" [code]]]],
      .expr "block" [.expr "latestworld-if-toplevel" [], .sym returned]] =>
    if binding == returned then some (target, code) else none
  | _ => none

/-- Both @eval forms preserve the selected module expression and quoted code,
then return that evaluation's result after the toplevel world-age marker.
All module/code expressions are quantified; no successful eval or purity premise
is imposed because evaluation occurs after macro expansion.
Julia source: base/essentials.jl:482-501. -/
def EvalExpansionPreservesPayload : Prop :=
  ∀ target code : JVal,
    EvalPayload (JuliaLean.base.essentials.Models1Group18.evalOne target code) =
      some (target, code) ∧
    EvalPayload (JuliaLean.base.essentials.Models1Group18.evalTwo target code) =
      some (target, code)

/-- No already-evaluated argument tuple can be converted to the empty Julia type,
including a C conversion request. No successful-conversion premise is assumed.
Julia source: base/essentials.jl:474,740. -/
def CconvertBottomRejects : Prop :=
  ∀ (A R : Type) (args : List A),
    ∃ message, JuliaLean.base.essentials.Models1Group18.cconvertBottom (R := R) args =
      .error (.argument message)

open JuliaLean.base.essentials (RE)


/-- An input is syntactically a for/while loop exactly when its existing Expr
object has the corresponding head. No assumptions are made about operand count,
initialization, cycles, sharing, or otherwise valid loop syntax. -/
def LabelLoopInput {Atom : Type} (heap : SyntaxHeap Atom)
    (body : SyntaxValue Atom) (node : SyntaxNode Atom) : Prop :=
  ∃ handle, body = .exprRef handle ∧ heap[handle]? = some node ∧
    (node.head = "for" ∨ node.head = "while")

/-- Observable frame: every old Expr remains at its original identity with every
field and every undefined slot unchanged. All returned syntax remains valid. -/
def LabelHeapFrame {Atom : Type} (before after : SyntaxHeap Atom) : Prop :=
  syntaxInputValid after [] ∧
  ∀ (handle : Nat) (node : SyntaxNode Atom), before[handle]? = some node → after[handle]? = some node

/-- The documented named-block interface for a non-loop body: the fresh escaped
block bears the requested name and contains the original body object unchanged.
The specification leaves fresh identities arbitrary; it neither calls allocation
helpers nor reconstructs a concrete heap update. -/
def LabelPlainObservation {Atom : Type} (name : String) (body value : SyntaxValue Atom)
    (before after : SyntaxHeap Atom) : Prop :=
  LabelHeapFrame before after ∧
  ∃ escapeHandle blockHandle,
    value = .exprRef escapeHandle ∧
    before.length ≤ escapeHandle ∧ before.length ≤ blockHandle ∧
    escapeHandle ≠ blockHandle ∧ after.length = before.length + 2 ∧
    after[escapeHandle]? = some ⟨"escape", [some (.exprRef blockHandle)]⟩ ∧
    after[blockHandle]? = some ⟨"symbolicblock", [some (.symbol name), some body]⟩

/-- A labelled syntactic loop retains its original header and loop body by
identity. A fresh inner block gives continue name the name#cont target; a fresh
outer block gives break name its named-block target. Extra original operands are
absent from the reconstructed loop, while the entire original loop object is
preserved by the frame. This observes a labelled graph, not an allocation order.
Source: base/essentials.jl:990-1009,1035-1052. -/
def LabelLoopObservation {Atom : Type} (name head : String)
    (header loopBody value : SyntaxValue Atom) (before after : SyntaxHeap Atom) : Prop :=
  LabelHeapFrame before after ∧
  ∃ escapeHandle blockHandle loopHandle continueHandle,
    value = .exprRef escapeHandle ∧
    [escapeHandle, blockHandle, loopHandle, continueHandle].Nodup ∧
    (∀ handle ∈ [escapeHandle, blockHandle, loopHandle, continueHandle], before.length ≤ handle) ∧
    after.length = before.length + 4 ∧
    after[escapeHandle]? = some ⟨"escape", [some (.exprRef blockHandle)]⟩ ∧
    after[blockHandle]? = some ⟨"symbolicblock", [some (.symbol name), some (.exprRef loopHandle)]⟩ ∧
    after[loopHandle]? = some ⟨head, [some header, some (.exprRef continueHandle)]⟩ ∧
    after[continueHandle]? = some ⟨"symbolicblock", [some (.symbol (name ++ "#cont")), some loopBody]⟩

/-- Independent input/output contract. A loop needs two initialized operands:
less than two operands gives BoundsError, including a one-slot #undef array,
and otherwise an undefined required operand gives UndefRefError. Additional
operands are unrestricted and never affect success. The named-block and
continue-target observations account for all successful inputs.

The result type discards state on an error. The model only allocates fresh syntax
and never mutates an input; a partially allocated wrapper is unreachable after
failure, so no observable input mutation is hidden by that error representation.
Source: base/essentials.jl:1035-1052,1073-1077;
doc/src/manual/arrays.md:519-528 (undefined reference reads). -/
def LabelHeapContract {Atom : Type} (name : String) (body : SyntaxValue Atom)
    (before : SyntaxHeap Atom) (result : RE (SyntaxValue Atom × SyntaxHeap Atom)) : Prop :=
  (name = "_" → result = .error (.core (.error
    "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed"))) ∧
  (name ≠ "_" →
    ((¬ ∃ node, LabelLoopInput before body node) →
      ∃ value after, result = .ok (value, after) ∧
        LabelPlainObservation name body value before after) ∧
    ∀ node, LabelLoopInput before body node →
      (node.args.length < 2 → result = .error (.core .bounds)) ∧
      ((2 ≤ node.args.length ∧
        (node.args[0]? = some none ∨ node.args[1]? = some none)) →
        result = .error (.core .undefRef)) ∧
      ∀ header loopBody,
        node.args[0]? = some (some header) → node.args[1]? = some (some loopBody) →
        ∃ value after, result = .ok (value, after) ∧
          LabelLoopObservation name node.head header loopBody value before after)

/-- Full named @label expansion contract over every machine-sized valid syntax
heap, including arbitrary non-Expr bodies, malformed loops, undefined operands,
extra operands, shared inputs, and cycles. The second conjunct independently
requires '_' rejection before accessing even a dangling body reference.

Only representation validity is assumed; there is no success premise or law
about an implementation parameter. Compiler execution of break/continue and
physical allocation failure are outside the installed syntax primitive boundary.
Source: base/essentials.jl:990-1009,1035-1052. Unproved in this modelling task. -/
def LabelHeapCorrect : Prop :=
  (∀ (Atom : Type) (name : String) (body : SyntaxValue Atom) (before : SyntaxHeap Atom),
    syntaxInputValid before [body] →
    LabelHeapContract name body before ((labelHeap name body).run before)) ∧
  (∀ (Atom : Type) (body : SyntaxValue Atom) (before : SyntaxHeap Atom),
    (labelHeap "_" body).run before = .error (.core (.error
      "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")))


/-- SimpleVector's complete scalar-read contract, stated by stored element
positions and the mathematical valid-index interval. Null slots represent internal
uninitialized SimpleVectors and retain the installed undefined-behavior marker;
no UndefRefError is invented for the Core._svec_ref primitive.
Source: base/essentials.jl:1096; Core._svec_ref source documented in svecRefV. -/
def SvecReadCorrect : Prop :=
  ∀ (v : JuliaLean.base.essentials.Models1Group18.SizedSVec) (i : JInt .i64),
    (¬ (1 ≤ i.val ∧ i.val ≤ (v.obj.slots.length : Int)) →
      JuliaLean.base.essentials.Models1Group18.svecGetindex64 v i = .error (.core .bounds)) ∧
    (∀ x, 1 ≤ i.val → v.obj.slots[(i.val - 1).toNat]? = some (some x) →
      JuliaLean.base.essentials.Models1Group18.svecGetindex64 v i = .ok x) ∧
    (1 ≤ i.val → v.obj.slots[(i.val - 1).toNat]? = some none →
      ∃ reason, JuliaLean.base.essentials.Models1Group18.svecGetindex64 v i =
        .error (.undefinedBehaviour reason))

/-- The scalar interface and index ranges describe exactly the vector's stored
positions, including an empty vector with firstindex=1 and lastindex=0.
The expected cardinality is mathematical list length; all model results remain
actual machine integers. No size or successful-execution law is supplied.
Source: base/essentials.jl:1097-1106; base/range.jl:478-486. -/
def SvecShapeCorrect : Prop :=
  ∀ v : JuliaLean.base.essentials.Models1Group18.SizedSVec,
    (JuliaLean.base.essentials.Models1Group18.svecLength64 v).val = (v.obj.slots.length : Int) ∧
    (JuliaLean.base.essentials.Models1Group18.svecFirstindex64 v).val = 1 ∧
    (JuliaLean.base.essentials.Models1Group18.svecLastindex64 v).val = (v.obj.slots.length : Int) ∧
    (JuliaLean.base.essentials.Models1Group18.svecKeys64 v).stop.val = (v.obj.slots.length : Int) ∧
    (∀ i : JInt .i64,
      (1 ≤ i.val ∧ i.val ≤ (JuliaLean.base.essentials.Models1Group18.svecKeys64 v).stop.val) ↔
        1 ≤ i.val ∧ i.val ≤ (v.obj.slots.length : Int)) ∧
    ∃ axis, JuliaLean.base.essentials.Models1Group18.svecAxes64 v = [axis] ∧
      axis.stop.val = (v.obj.slots.length : Int) ∧
      ∀ i : JInt .i64, (1 ≤ i.val ∧ i.val ≤ axis.stop.val) ↔
        1 ≤ i.val ∧ i.val ≤ (v.obj.slots.length : Int)

namespace MapState

open JuliaLean.base.essentials
open JuliaLean.base.essentials.Models1Group18.MapState

/-- A record in an existential observation trace, not an input to the model.
The first and last heaps bracket the callback and its following output write. -/
structure MapCall where
  input : JVal
  output : JVal
  beforeCall : Heap
  afterCall : Heap
  afterStore : Heap

/-- Allocation specified by freshness and observations of each heap object.
This does not call the allocator or reconstruct its imperative implementation.
The zero-memory singleton is a representation identity. -/
def FreshOutput (count : Nat) (before allocated : Heap) (handle : Nat) : Prop :=
  if count = 0 then
    handle = 0 ∧ allocated = before
  else
    handle = before.length ∧ allocated.length = before.length + 1 ∧
    allocated[handle]? = some (⟨List.replicate count none, false, 8, false⟩ : MemObj) ∧
    ∀ j : Nat, j < before.length → allocated[j]? = before[j]?

/-- Independent single-slot heap-frame relation: every other object and slot
is unchanged, the chosen slot contains the value, and metadata is preserved.
The selected object must support a non-atomic write at this valid offset.
No operational setindex/memoryref model appears on this expected side. -/
def StoredValue (handle offset : Nat) (value : JVal) (before after : Heap) : Prop :=
  ∃ old new : MemObj,
    before[handle]? = some old ∧ after[handle]? = some new ∧
    offset < old.slots.length ∧ old.atomic = false ∧
    after.length = before.length ∧
    new.atomic = old.atomic ∧ new.elsize = old.elsize ∧ new.isunion = old.isunion ∧
    new.slots.length = old.slots.length ∧
    new.slots[offset]? = some (some value) ∧
    (∀ j : Nat, j ≠ offset → new.slots[j]? = old.slots[j]?) ∧
    (∀ object : Nat, object ≠ handle → after[object]? = before[object]?)

/-- The possible fixed destination-write failures, with source check order.
The range index is known valid against the Array header. A dangling memory
handle fails first; otherwise the reference's offset must fit before the
non-atomic store checks the memory kind. No mutation precedes these errors. -/
def FailedStore (handle offset : Nat) (heap : Heap) (error : Err) : Prop :=
  (heap[handle]? = none ∧ error = .undefinedBehaviour "dangling memory handle") ∨
  ∃ memory : MemObj, heap[handle]? = some memory ∧
    ((memory.slots.length ≤ offset ∧ error = .core .bounds) ∨
     (offset < memory.slots.length ∧ memory.atomic = true ∧
      error = .concurrency "memoryrefset!: atomic memory cannot be written non-atomically"))

/-- A finite sequence of completed callback-and-store observations. Inputs are
exactly the source's corresponding prefix, callback outcomes are its actual
outcomes, the pointwise store relation holds, and adjacent heap observations
agree. This relation is declarative over an arbitrary finite witness; it does
not define another map loop or supply a correctness assumption about f. -/
def SuccessfulPrefix (f : JVal → KeptHM JVal) (v : JuliaLean.base.essentials.Models1Group18.MapState.SizedSVec) (handle : Nat)
    (allocated current : Heap) (calls : List MapCall) : Prop :=
  calls.length ≤ v.obj.slots.length ∧
  (match calls with
   | [] => current = allocated
   | first :: _ => first.beforeCall = allocated ∧
       ∃ last : MapCall, calls.getLast? = some last ∧ last.afterStore = current) ∧
  (∀ (k : Nat) (call : MapCall), calls[k]? = some call →
    v.obj.slots[k]? = some (some call.input) ∧
    runKept (f call.input) call.beforeCall = some (.ok call.output, call.afterCall) ∧
    StoredValue handle k call.output call.afterCall call.afterStore) ∧
  (∀ (k : Nat) (left right : MapCall),
    calls[k]? = some left → calls[k + 1]? = some right →
    left.afterStore = right.beforeCall)

/-- Independent complete outcome relation for the logical runtime boundary.
Success witnesses one ordered f-call and store per source slot. Failure or
nontermination is licensed only by the next source read, that actual callback,
or a concrete destination-store failure. Callback and earlier store effects
remain in the observed final heap. Resource exhaustion outside the installed
logical allocation model is not claimed by this relation. -/
def MappingOutcome (f : JVal → KeptHM JVal) (v : JuliaLean.base.essentials.Models1Group18.MapState.SizedSVec) (before : Heap)
    (result : Option (Except Err Arr × Heap)) : Prop :=
  if anyAllocationMax < v.obj.slots.length then
    result = some (.error (.core (.argument "invalid GenericMemory size")), before)
  else
    ∃ (allocated : Heap) (handle : Nat),
      FreshOutput v.obj.slots.length before allocated handle ∧
      match result with
      | none =>
        ∃ (calls : List MapCall) (current : Heap) (input : JVal),
          SuccessfulPrefix f v handle allocated current calls ∧
          calls.length < v.obj.slots.length ∧
          v.obj.slots[calls.length]? = some (some input) ∧
          runKept (f input) current = none
      | some (.error error, finalHeap) =>
        ∃ (calls : List MapCall) (current : Heap),
          SuccessfulPrefix f v handle allocated current calls ∧
          calls.length < v.obj.slots.length ∧
          ((v.obj.slots[calls.length]? = some none ∧
            error = .undefinedBehaviour "null SimpleVector slot" ∧ finalHeap = current) ∨
           ∃ input : JVal, v.obj.slots[calls.length]? = some (some input) ∧
             (runKept (f input) current = some (.error error, finalHeap) ∨
              ∃ (output : JVal) (afterCall : Heap),
                runKept (f input) current = some (.ok output, afterCall) ∧
                FailedStore handle calls.length afterCall error ∧ finalHeap = afterCall))
      | some (.ok array, finalHeap) =>
        ∃ calls : List MapCall,
          SuccessfulPrefix f v handle allocated finalHeap calls ∧
          calls.length = v.obj.slots.length ∧
          array.size = [JInt.wrap .i64 v.obj.slots.length] ∧
          array.ref.mem.handle = handle ∧ array.ref.index = 0

/-- For every Julia function argument, constructible machine-sized source and
valid heap representation, map has the documented ordered mapping behavior,
including all represented exceptional, divergent and mutating outcomes.
There are no purity, successful-run, callee-correctness or trace premises.
Julia source: base/essentials.jl:1117; generic map/typed-comprehension semantics;
base/array.jl:684-687; base/abstractarray.jl:941-951; base/generator.jl:44-50. -/
def MappingTraceCorrect : Prop :=
  ∀ (f : JVal → KeptHM JVal) (v : JuliaLean.base.essentials.Models1Group18.MapState.SizedSVec) (heap : Heap),
    HeapInvariant heap → MappingOutcome f v heap (runKept (mapSVec f v) heap)


end MapState

/-- Bounds checking and elision for every machine index and constructible vector.
The mathematical interval is independent of the model's intrinsic comparisons.
Source: base/essentials.jl:1151-1154. -/
def SvecIsassignedModes : Prop :=
  ∀ (v : JuliaLean.base.essentials.Models1Group18.SizedSVec) (i : JInt .i64),
    (JuliaLean.base.essentials.Models1Group18.svecIsassigned64 true v i = true ↔
      1 ≤ i.val ∧ i.val ≤ (v.obj.slots.length : Int)) ∧
    JuliaLean.base.essentials.Models1Group18.svecIsassigned64 false v i = true

/-- The public isassigned documentation promises false for an undefined reference.
This statement does not assume all internal SimpleVector slots are initialized;
that would remove the precisely relevant part of the documented domain. It is
intentionally left unproved: the pinned specialized source only tests bounds.
A discrepancy in this logical internal-null-slot domain is not a reproduced Julia bug.
Source: base/essentials.jl:1123-1154. -/
def SvecIsassignedDocumentation : Prop :=
  ∀ (v : JuliaLean.base.essentials.Models1Group18.SizedSVec) (i : JInt .i64),
    JuliaLean.base.essentials.Models1Group18.svecIsassigned64 true v i = true ↔
      1 ≤ i.val ∧ ∃ x, v.obj.slots[(i.val - 1).toNat]? = some (some x)

open JuliaLean.base.essentials (Err IterMethods missingV)


/-- Observable interface calls. Arguments are recorded to detect incorrect
forwarding as well as extra calls or reversed evaluation order. -/
inductive IsEmptyCall (I : Type) where
  | isdone (itr : I)
  | iterate (itr : I)

/-- An arbitrary external-state snapshot plus an observation trace. The trace is
mathematical observation data, not a Julia array or an implementation input. -/
structure IsEmptyProbeState (I World : Type) where
  calls : List (IsEmptyCall I)
  world : World

/-- The existing interface instantiated with errors, mutable state and possible
nontermination. Some errors retain their state; none is nontermination, following
the installed essentials HM convention. -/
abbrev IsEmptyProbeM (I World : Type) :=
  ExceptT Err (StateT (IsEmptyProbeState I World) Option)

/-- A concrete boundary result; no implementation function or correctness law is
supplied. Arbitrary result/error data and none span all outcomes of one call. -/
def isemptyProbeEmit {I World α : Type} (reply : Option (RE α)) : IsEmptyProbeM I World α :=
  ExceptT.mk (StateT.mk fun state => reply.map fun result => (result, state))

/-- Concrete instrumented methods implementing only the already-installed
IterMethods boundary. Arbitrary post-call snapshots cover arbitrary effects of
one invocation, including effects before a thrown exception. An outcome of none
has no final observable state. No callee correctness premise is assumed. -/
def isemptyProbeMethods {I World S : Type}
    (hintWorld stepWorld : World) (hintReply : Option (RE JVal))
    (stepReply : Option (RE (Option (JVal × S)))) :
    IterMethods (IsEmptyProbeM I World) I S where
  isdone itr := do
    modify fun state => { state with calls := state.calls ++ [.isdone itr], world := hintWorld }
    isemptyProbeEmit hintReply
  iterate itr := do
    modify fun state => { state with calls := state.calls ++ [.iterate itr], world := stepWorld }
    isemptyProbeEmit stepReply

/-- The five terminating allowed-call observations and the two nontermination
observations for isempty. These constructors specify a public interaction
protocol, not a model algorithm: no constructor calls the wrapper, a missing
recognizer, or a supplied law. In particular any non-missing JVal hint is returned
unchanged and permits exactly one isdone call, even when iterate would fail or
not return. The fallback observes emptiness without inspecting item/state values.
Source: base/essentials.jl:1214-1224,1235-1239,1584-1601;
doc/src/manual/interfaces.md:12-14,27-34. -/
inductive IsEmptyAllowedObservation {I World S : Type}
    (itr : I) (initial : IsEmptyProbeState I World) (hintWorld stepWorld : World) :
    Option (RE JVal) → Option (RE (Option (JVal × S))) →
    Option (RE JVal × IsEmptyProbeState I World) → Prop where
  | hintDoesNotReturn (stepReply) :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld none stepReply none
  | hintThrows (error : Err) (stepReply) :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld (some (.error error)) stepReply
        (some (.error error, ⟨initial.calls ++ [.isdone itr], hintWorld⟩))
  | hintAnswers (hint : JVal) (stepReply) (notMissing : hint ≠ missingV) :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld (some (.ok hint)) stepReply
        (some (.ok hint, ⟨initial.calls ++ [.isdone itr], hintWorld⟩))
  | iterationDoesNotReturn :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld (some (.ok missingV)) none none
  | iterationThrows (error : Err) :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld (some (.ok missingV))
        (some (.error error))
        (some (.error error, ⟨initial.calls ++ [.isdone itr, .iterate itr], stepWorld⟩))
  | empty :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld (some (.ok missingV))
        (some (.ok none))
        (some (.ok (.bool true), ⟨initial.calls ++ [.isdone itr, .iterate itr], stepWorld⟩))
  | nonempty (value : JVal) (state : S) :
      IsEmptyAllowedObservation itr initial hintWorld stepWorld (some (.ok missingV))
        (some (.ok (some (value, state))))
        (some (.ok (.bool false), ⟨initial.calls ++ [.isdone itr, .iterate itr], stepWorld⟩))

/-- For all existing-interface outcomes, iterator arguments, state snapshots and
observation prefixes, isempty follows precisely the allowed protocol. Errors
retain the exact boundary error and post-call state, arbitrary non-Bool hints
are not coerced, and only the missing hint permits one iterate call. Either
callee may fail to return. No successful-run, Boolean-hint, purity, or callee-law
hypothesis restricts the input domain. This is a wrapper contract at IterMethods,
not a claim to implement user-defined iterator methods.
Source: base/essentials.jl:1214-1224,1235-1239,1584-1601. Unproved. -/
def IsEmptyBoundaryProtocol : Prop :=
  ∀ (I World S : Type) (itr : I) (initial : IsEmptyProbeState I World)
    (hintWorld stepWorld : World) (hintReply : Option (RE JVal))
    (stepReply : Option (RE (Option (JVal × S)))),
    IsEmptyAllowedObservation itr initial hintWorld stepWorld hintReply stepReply
      (((isemptyAtBoundary
        (isemptyProbeMethods hintWorld stepWorld hintReply stepReply) itr).run).run initial)


/-- The documented singleton test on every value in the existing JVal domain.
The expected side is equality with the pre-existing missing constant, not a
supplied predicate or an execution of the model's branch structure.
Source: base/essentials.jl:1517-1542. -/
def IsmissingSingletonCorrect : Prop :=
  ∀ x : JVal, JuliaLean.base.essentials.Models1Group18.ismissingSingleton x = true ↔
    x = JuliaLean.base.essentials.missingV

/-- @__LINE__ preserves the macrocall's stored signed line number for every
constructible LineNumberNode, including the documented 0/unknown value and
independently of its optional source-file symbol. This is the documented location
promise, not a nonnegative-line or successful-call premise.
Source: base/essentials.jl:1573-1580; base/boot.jl:133-136,710-714. -/
def LineMacroLocationCorrect : Prop :=
  ∀ source : JuliaLean.base.essentials.Models1Group18.MacroSource,
    (JuliaLean.base.essentials.Models1Group18.lineMacro64 source).val = source.line.val


open JuliaLean.base.essentials (Modules Module effectMeta)

/-- Base's internal-name gate succeeds before following any module parent.
Non-module inputs fail at _nameof. Each internal macro emits the pinned flags.
Julia source: base/essentials.jl:190-374. -/
def InternalGateAndFlags : Prop :=
  (∀ (Other : Type) (ms : Modules) (x : Other),
    isInternalAny ms (.other x) = some (.error (.core (.method "_nameof")))) ∧
  (∀ (ms : Modules) (m : Module), m.name = "Base" →
    JuliaLean.base.essentials.Models1Group18.isInternal ms m = some true ∧
    JuliaLean.base.essentials.Models1Group18.totalMeta ms m = some (effectMeta true ⟨true,true,true,true,false,true,true,true,false,false,true⟩) ∧
    JuliaLean.base.essentials.Models1Group18.foldableMeta ms m = some (effectMeta true ⟨true,true,false,true,false,true,true,true,false,false,true⟩) ∧
    JuliaLean.base.essentials.Models1Group18.terminatesLocallyMeta ms m = some (effectMeta true ⟨false,false,false,false,true,false,false,false,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.terminatesGloballyMeta ms m = some (effectMeta true ⟨false,false,false,true,true,false,false,false,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.terminatesGloballyNotaskstateMeta ms m = some (effectMeta true ⟨false,false,false,true,true,true,false,false,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.terminatesGloballyNoubMeta ms m = some (effectMeta true ⟨false,false,false,true,true,false,false,true,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.effectFreeTerminatesLocallyMeta ms m = some (effectMeta true ⟨false,true,false,false,true,false,false,false,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.nothrowNoubMeta ms m = some (effectMeta true ⟨false,false,true,false,false,false,false,true,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.nothrowMeta ms m = some (effectMeta true ⟨false,false,true,false,false,false,false,false,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.noubMeta ms m = some (effectMeta true ⟨false,false,false,false,false,false,false,true,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.notaskstateMeta ms m = some (effectMeta true ⟨false,false,false,false,false,true,false,false,false,false,false⟩) ∧
    JuliaLean.base.essentials.Models1Group18.noubIfNoinboundsMeta ms m = some (effectMeta true ⟨false,false,false,false,false,false,false,false,true,false,false⟩))

/-- Abstract DataTypes require no initialized fields, independently of their
parameters or field-name metadata. Julia source: base/essentials.jl:617-620;
base/runtime_internals.jl:1186-1192. -/
def AbstractMinInitializedZero : Prop :=
  ∀ (Atom : Type) (heap : MinInitHeap Atom) (handle : Nat)
    (name : MinInitTypeName) (parameters : MinInitVector Nat),
    heap[handle]? = some (.dataType name parameters) →
    name.flags.val % 2 = 1 →
    (datatypeMinNinitializedHeap heap handle).run = some (.ok (JInt.wrap .i64 0))

/-- A TypeVar contains itself as a free occurrence; a datatype whose runtime
cache says it has no free variables contains none. No query laws are inputs.
Julia source: base/essentials.jl:1298; src/jltypes.c:270-346. -/
def TypevarQueryIdentity : Prop :=
  (∀ (Atom : Type) (world : TypevarQuery.World Atom) (v : TypevarQuery.TypeVarRef world),
    (TypevarQuery.hasTypevar world v.handle v).run = some (.ok true)) ∧
  (∀ (Atom : Type) (world : TypevarQuery.World Atom) (v : TypevarQuery.TypeVarRef world)
      (handle : Nat) (parameters : MinInitVector Nat),
    world.objects[handle]? = some (.dataType false parameters) →
    (TypevarQuery.hasTypevar world handle v).run = some (.ok false))

/-- With no type variables the constraint check succeeds without reading any
field-type slot. Julia source: base/essentials.jl:1302-1339. -/
def EmptyTypevarsConstrained : Prop :=
  ∀ (Atom : Type) (world : TypevarQuery.World Atom) (variables fields : TypevarQuery.Slots),
    variables.values = [] →
    (TypevarQuery.fieldtypesConstrainTypevars world variables fields).run = some (.ok true)

/-- Array shape access preserves the stored machine dimensions, and the rank-one
length accessor returns the sole dimension. Julia source: base/essentials.jl:12,1296. -/
def ExistingArrayShape : Prop :=
  (∀ (a : Arrays.Arr), Arrays.sizeArr a = a.dims) ∧
  (∀ (a : Arrays.Arr) (n : JInt .i64), a.dims = [n] → Arrays.lengthVec a = .ok n)

/-- Vararg inspection recognizes its runtime tag and retains its element type;
removing a length constraint leaves that element unchanged. Julia source:
base/essentials.jl:589-613. -/
def ExistingVarargInspection : Prop :=
  (∀ t, JuliaLean.base.essentials.isvarargtype t = true ↔ ∃ T N, t = .vararg T N) ∧
  (∀ t, JuliaLean.base.essentials.isvatuple t = true ↔
    ∃ name abs params va, Types.unwrapUnionall t = .dt name abs params ∧
      params.getLast? = some va ∧ JuliaLean.base.essentials.isvarargtype va = true) ∧
  (∀ T N, Types.unwrapva (.vararg (some T) N) = T) ∧
  (∀ N, Types.unwrapva (.vararg none N) = .dt "Any" true []) ∧
  (∀ T N, JuliaLean.base.essentials.unconstrainVarargLength (.vararg (some T) N) =
    .vararg (some T) none)

/-- The matching-type tuple conversion retains its argument. Julia source:
base/essentials.jl:652. Instantiate T with the represented tuple value universe. -/
def ExistingTupleIdentity : Prop :=
  ∀ (T : Type) (x : T), JuliaLean.base.essentials.convertTupleIdentity x = x

/-- Bool negation returns the opposite truth value through the bound one-bit
runtime intrinsic. Julia source: base/essentials.jl:1294. -/
def ExistingPrimitiveNot : Prop :=
  JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool true = false ∧
  JuliaLean.base.essentials.Archive20261101PrimitiveNot.notBool false = true

end Models1Group18

end JuliaLean.Proofs.base.essentials

namespace JuliaLean.ChatGPT.Batch9.Group13
open JuliaLean JuliaLean.BootCov
open JuliaLean.Proofs.base.essentials.Models1Group18
open JuliaLean.base.essentials.Models1Group18


theorem Models1G18BoundsErrorHelpers_proven : JuliaLean.Proofs.base.essentials.Models1Group18.BoundsErrorHelpers := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl


theorem Models1G18EvalExpansion_proven : JuliaLean.Proofs.base.essentials.Models1Group18.EvalExpansionPreservesPayload := by
  intro target code
  exact ⟨rfl, rfl⟩


theorem Models1G18CconvertBottom_proven : JuliaLean.Proofs.base.essentials.Models1Group18.CconvertBottomRejects := by
  intro A R args
  exact ⟨"cannot convert a value to Union{} for assignment", rfl⟩


theorem Models1G18LineLocation_proven : JuliaLean.Proofs.base.essentials.Models1Group18.LineMacroLocationCorrect := by
  intro source
  rfl


theorem Models1G18InternalGate_proven : JuliaLean.Proofs.base.essentials.Models1Group18.InternalGateAndFlags := by
  constructor
  · intro Other ms x
    rfl
  · intro ms m hm
    have hi : isInternal ms m = some true := by
      simp only [isInternal, JuliaLean.base.essentials.moduleName, hm, beq_self_eq_true,
        ite_true, pure]
    refine ⟨hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [totalMeta, foldableMeta, terminatesLocallyMeta,
      terminatesGloballyMeta, terminatesGloballyNotaskstateMeta,
      terminatesGloballyNoubMeta, effectFreeTerminatesLocallyMeta,
      nothrowNoubMeta, nothrowMeta, noubMeta, notaskstateMeta,
        noubIfNoinboundsMeta, hi]
      rfl


theorem Models1G18ExistingArrayShape_proven : JuliaLean.Proofs.base.essentials.Models1Group18.ExistingArrayShape := by
  constructor
  · intro a
    rfl
  · intro a n h
    simp only [Arrays.lengthVec, h]


theorem g13IsvarargtypeIff (t : JType) :
    JuliaLean.base.essentials.isvarargtype t = true ↔ ∃ T N, t = .vararg T N := by
  constructor
  · intro h
    cases t with
    | vararg T N => exact ⟨T, N, rfl⟩
    | _ => cases h
  · rintro ⟨T, N, rfl⟩
    rfl


theorem g13IsvatupleIff (t : JType) :
    JuliaLean.base.essentials.isvatuple t = true ↔
      ∃ name abs params va, Types.unwrapUnionall t = .dt name abs params ∧
        params.getLast? = some va ∧ JuliaLean.base.essentials.isvarargtype va = true := by
  constructor
  · intro hv
    cases h : Types.unwrapUnionall t with
    | dt name abs params =>
      simp only [JuliaLean.base.essentials.isvatuple, JuliaLean.base.essentials.unwrapUnionall, h] at hv
      cases hp : params.getLast? with
      | none => rw [hp] at hv; cases hv
      | some va =>
        rw [hp] at hv
        exact ⟨name, abs, params, va, rfl, hp, hv⟩
    | _ => simp only [JuliaLean.base.essentials.isvatuple, JuliaLean.base.essentials.unwrapUnionall, h] at hv; cases hv
  · rintro ⟨name, abs, params, va, ht, hl, hv⟩
    simpa only [JuliaLean.base.essentials.isvatuple, JuliaLean.base.essentials.unwrapUnionall, ht, hl] using hv

theorem Models1G18ExistingVarargInspection_proven : JuliaLean.Proofs.base.essentials.Models1Group18.ExistingVarargInspection := by
  exact ⟨g13IsvarargtypeIff, g13IsvatupleIff, fun _ _ => rfl,
    fun _ => rfl, fun _ _ => rfl⟩


theorem Models1G18ExistingTupleIdentity_proven : JuliaLean.Proofs.base.essentials.Models1Group18.ExistingTupleIdentity := by
  intro T x
  rfl


theorem Models1G18ExistingPrimitiveNot_proven : JuliaLean.Proofs.base.essentials.Models1Group18.ExistingPrimitiveNot := by
  unfold ExistingPrimitiveNot
  decide


end JuliaLean.ChatGPT.Batch9.Group13

namespace JuliaLean.ChatGPT.Batch9.Group13
open JuliaLean JuliaLean.BootCov
open JuliaLean.Proofs.base.essentials.Models1Group18
open JuliaLean.base.essentials.Models1Group18


theorem g13SlotIndexBound {α : Type} (xs : List α) (i : Int) (x : α)
    (hi : 1 ≤ i) (hx : xs[(i - 1).toNat]? = some x) : i ≤ (xs.length : Int) := by
  have hn := (List.getElem?_eq_some_iff.mp hx).1
  omega


theorem Models1G18SvecRead_proven : JuliaLean.Proofs.base.essentials.Models1Group18.SvecReadCorrect := by
  intro v i
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hb : i.val < 1 ∨ i.val > (v.obj.slots.length : Int) := by omega
    simp only [svecGetindex64, JuliaLean.base.essentials.svecRefV,
      Arrays.svecRef, hb, ite_true]
    rfl
  · intro x hi hx
    have hn := g13SlotIndexBound v.obj.slots i.val (some x) hi hx
    have hb : ¬ (i.val < 1 ∨ i.val > (v.obj.slots.length : Int)) := by omega
    simp only [svecGetindex64, JuliaLean.base.essentials.svecRefV,
      Arrays.svecRef, hb, ite_false, hx]
    rfl
  · intro hi hx
    have hn := g13SlotIndexBound v.obj.slots i.val none hi hx
    have hb : ¬ (i.val < 1 ∨ i.val > (v.obj.slots.length : Int)) := by omega
    refine ⟨"null SimpleVector slot", ?_⟩
    simp only [svecGetindex64, JuliaLean.base.essentials.svecRefV,
      Arrays.svecRef, hb, ite_false, hx]
    rfl


theorem g13SvecLengthVal (v : SizedSVec) :
    (svecLength64 v).val = (v.obj.slots.length : Int) := by
  change wrapInt .i64 (v.obj.slots.length : Int) = _
  apply wrapInt_of_inRange
  have hv := v.lengthFits
  change v.obj.slots.length ≤ 9223372036854775807 at hv
  change -9223372036854775808 ≤ (v.obj.slots.length : Int) ∧
    (v.obj.slots.length : Int) ≤ 9223372036854775807
  omega

theorem g13WrapSelf (x : JInt .i64) : JInt.wrap .i64 x.val = x := by
  apply Subtype.ext
  exact wrapInt_of_inRange .i64 x.val x.property


theorem g13FromI64 (x : JInt .i64) : (JuliaLean.C.fromJInt x).toInt = x.val := by
  have hx := x.property
  change -9223372036854775808 ≤ x.val ∧ x.val ≤ 9223372036854775807 at hx
  simp only [JuliaLean.C.fromJInt, BitVec.toInt_ofInt]
  change x.val.bmod 18446744073709551616 = x.val
  simp only [Int.bmod_def]
  split <;> omega

theorem g13SleI64 (x y : JInt .i64) :
    JuliaLean.base.int.sle_int x y = decide (x.val ≤ y.val) := by
  simp only [JuliaLean.base.int.sle_int, JuliaLean.C.jlSleInt,
    g13FromI64]

theorem g13SltI64 (x y : JInt .i64) :
    JuliaLean.base.int.slt_int x y = decide (x.val < y.val) := by
  simp only [JuliaLean.base.int.slt_int, JuliaLean.C.jlSltInt,
    g13FromI64]

theorem g13LtI64 (x y : JInt .i64) :
    JuliaLean.base.int.lt x y = decide (x.val < y.val) := by
  change JuliaLean.base.int.slt_int (JInt.wrap .i64 x.val)
    (JInt.wrap .i64 y.val) = _
  rw [g13WrapSelf, g13WrapSelf, g13SltI64]


theorem g13OneToStop (n : JInt .i64) (hn : 0 ≤ n.val) : (oneTo64 n).stop.val = n.val := by
  change (JuliaLean.base.int.ifelse
    (JuliaLean.base.int.lt (JInt.wrap .i64 0) n)
    (JuliaLean.base.int.remT .i64 n)
    (JuliaLean.base.int.remT .i64 (JInt.wrap .i64 0))).val = n.val
  rw [g13LtI64]
  have hz : (JInt.wrap .i64 0).val = 0 := by decide
  simp only [hz, JuliaLean.base.int.remT, dite_eq_left rfl, JuliaLean.base.int.rem_same,
    JuliaLean.base.int.ifelse]
  split
  · rfl
  · change (JInt.wrap .i64 0).val = n.val
    rw [hz]
    have : ¬ 0 < n.val := by
      simpa only [decide_eq_true_eq] using (show ¬ decide (0 < n.val) = true from by assumption)
    omega

theorem Models1G18SvecShape_proven : JuliaLean.Proofs.base.essentials.Models1Group18.SvecShapeCorrect := by
  intro v
  have hl := g13SvecLengthVal v
  have h0 : 0 ≤ (svecLength64 v).val := by rw [hl]; omega
  have hk : (svecKeys64 v).stop.val = (v.obj.slots.length : Int) :=
    (g13OneToStop (svecLength64 v) h0).trans hl
  refine ⟨hl, ?_, hl, hk, ?_, ?_⟩
  · change (JInt.wrap .i64 1).val = 1
    decide
  · intro i
    rw [hk]
  · refine ⟨oneTo64 (svecLength64 v), rfl, hk, ?_⟩
    intro i
    change (1 ≤ i.val ∧ i.val ≤ (svecKeys64 v).stop.val) ↔ _
    rw [hk]

theorem Models1G18SvecIsassignedModes_proven : JuliaLean.Proofs.base.essentials.Models1Group18.SvecIsassignedModes := by
  intro v i
  constructor
  · have h1 : (JInt.wrap .i64 1).val = 1 := by decide
    simp only [svecIsassigned64, g13SleI64, h1, g13SvecLengthVal]
    by_cases ha : 1 ≤ i.val
    · by_cases hb : i.val ≤ (v.obj.slots.length : Int)
      · simp only [ha, hb, decide_true, Bool.true_and, Bool.not_true,
          Bool.false_eq_true, ite_false, ite_true, Id.run_pure, and_self]
      · simp only [ha, hb, decide_true, decide_false, Bool.true_and, Bool.not_false,
          ite_true, Id.run_pure, Bool.false_eq_true, and_false, iff_self]
    · simp only [ha, decide_false, Bool.false_and, Bool.not_false,
        ite_true, Id.run_pure, Bool.false_eq_true, false_and, iff_self]
  · rfl




end JuliaLean.ChatGPT.Batch9.Group13

namespace JuliaLean.ChatGPT.Batch9.Group13

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.base.essentials.Models1Group18
open JuliaLean.Proofs.base.essentials.Models1Group18

theorem g13MissingHintIff (x : JVal) :
    isemptyMissingHint x = true ↔ x = missingV := by
  constructor
  · intro h
    unfold isemptyMissingHint at h
    split at h
    · rfl
    · cases h
  · intro h
    subst x
    rfl

theorem Models1G18IsmissingSingleton_proven :
    JuliaLean.Proofs.base.essentials.Models1Group18.IsmissingSingletonCorrect := by
  intro x
  exact g13MissingHintIff x

theorem g13U8AndOne (x : JInt .u8) :
    (JuliaLean.base.int.and_int x (JInt.wrap .u8 1)).val = x.val % 2 := by
  have hx : 0 ≤ x.val ∧ x.val < 256 := by
    have h := x.property
    change 0 ≤ x.val ∧ x.val ≤ 255 at h
    omega
  have hxNat : (JuliaLean.C.fromJInt x).toNat = x.val.toNat := by
    simp only [JuliaLean.C.fromJInt, BitVec.toNat_ofInt, IntTy.bits]
    change (x.val % 256).toNat = x.val.toNat
    rw [Int.emod_eq_of_lt hx.1 hx.2]
  have hxCast : (x.val.toNat : Int) = x.val := Int.toNat_of_nonneg hx.1
  change wrapInt .u8
    (((JuliaLean.C.fromJInt x &&& JuliaLean.C.fromJInt (JInt.wrap .u8 1)).toNat) : Int) = _
  rw [BitVec.toNat_and, hxNat]
  change wrapInt .u8 ((x.val.toNat &&& 1 : Nat) : Int) = _
  rw [Nat.and_one_is_mod]
  change ((x.val.toNat % 2 : Nat) : Int) % 256 = x.val % 2
  omega

theorem Models1G18MinInitialized_proven :
    JuliaLean.Proofs.base.essentials.Models1Group18.AbstractMinInitializedZero := by
  intro Atom heap handle name parameters hread hodd
  have hbit : JuliaLean.base.int.and_int name.flags (JInt.wrap .u8 1) =
      JInt.wrap .u8 1 := by
    apply Subtype.ext
    rw [g13U8AndOne, hodd]
    rfl
  have habs : minInitDatatypeIsabstract name = true := by
    unfold minInitDatatypeIsabstract
    rw [hbit]
    exact beq_self_eq_true _
  have hread' : minInitRead heap handle = pure (.dataType name parameters) := by
    unfold minInitRead
    rw [hread]
  have hunwrap : minInitUnwrap heap handle = pure handle := by
    rw [minInitUnwrap.eq_1, hread']
    rfl
  simp only [datatypeMinNinitializedHeap, hunwrap, pure_bind, hread', habs,
    ↓reduceIte]
  all_goals rfl

theorem Models1G18TypevarQuery_proven :
    JuliaLean.Proofs.base.essentials.Models1Group18.TypevarQueryIdentity := by
  constructor
  · intro Atom world v
    have hquery : TypevarQuery.hasBoundTypevars world v.handle [⟨v.handle, none⟩] =
        pure true := by
      rw [TypevarQuery.hasBoundTypevars.eq_1]
      simp only [TypevarQuery.readObject, v.objectEq]
      simp only [pure_bind, TypevarQuery.envHasNe, beq_self_eq_true,
        ↓reduceIte]
      all_goals rfl
    simp only [TypevarQuery.hasTypevar, TypevarQuery.jlHasTypevar, hquery,
      pure_bind]
    rfl
  · intro Atom world v handle parameters hread
    have hquery : TypevarQuery.hasBoundTypevars world handle [⟨v.handle, none⟩] =
        pure false := by
      rw [TypevarQuery.hasBoundTypevars.eq_1]
      simp only [TypevarQuery.readObject, hread, pure_bind,
        Bool.not_false, ↓reduceIte]
      all_goals rfl
    simp only [TypevarQuery.hasTypevar, TypevarQuery.jlHasTypevar, hquery,
      pure_bind]
    all_goals rfl

theorem Models1G18FieldtypesConstrain_proven :
    JuliaLean.Proofs.base.essentials.Models1Group18.EmptyTypevarsConstrained := by
  intro Atom world variables fields hvars
  unfold TypevarQuery.fieldtypesConstrainTypevars
  simp only [hvars, List.length_nil, Int.natCast_zero]
  rw [TypevarQuery.constrainLoop.eq_1]
  simp only [beq_self_eq_true, ↓reduceIte]
  all_goals rfl

theorem Models1G18IsemptyBoundary_proven :
    JuliaLean.Proofs.base.essentials.Models1Group18.IsEmptyBoundaryProtocol := by
  intro I World S itr initial hintWorld stepWorld hintReply stepReply
  cases hintReply with
  | none => exact .hintDoesNotReturn stepReply
  | some reply =>
    cases reply with
    | error error => exact .hintThrows error stepReply
    | ok hint =>
      by_cases hm : hint = missingV
      · subst hint
        cases stepReply with
        | none => exact .iterationDoesNotReturn
        | some step =>
          cases step with
          | error error =>
            change IsEmptyAllowedObservation itr initial hintWorld stepWorld
              (some (.ok missingV)) (some (.error error))
              (some (.error error,
                ⟨(initial.calls ++ [.isdone itr]) ++ [.iterate itr], stepWorld⟩))
            rw [List.append_assoc]
            exact .iterationThrows error
          | ok next =>
            cases next with
            | none =>
              change IsEmptyAllowedObservation itr initial hintWorld stepWorld
                (some (.ok missingV)) (some (.ok none))
                (some (.ok (.bool true),
                  ⟨(initial.calls ++ [.isdone itr]) ++ [.iterate itr], stepWorld⟩))
              rw [List.append_assoc]
              exact .empty
            | some item =>
              rcases item with ⟨value, state⟩
              change IsEmptyAllowedObservation itr initial hintWorld stepWorld
                (some (.ok missingV)) (some (.ok (some (value, state))))
                (some (.ok (.bool false),
                  ⟨(initial.calls ++ [.isdone itr]) ++ [.iterate itr], stepWorld⟩))
              rw [List.append_assoc]
              exact .nonempty value state
      · have hh : isemptyMissingHint hint = false := by
          cases h : isemptyMissingHint hint with
          | false => rfl
          | true => exact False.elim (hm ((g13MissingHintIff hint).mp h))
        change IsEmptyAllowedObservation itr initial hintWorld stepWorld
          (some (.ok hint)) stepReply
          (((if !isemptyMissingHint hint then
              pure hint
            else do
              let next ← (isemptyProbeMethods hintWorld stepWorld (some (.ok hint))
                stepReply).iterate itr
              pure (.bool next.isNone) : IsEmptyProbeM I World JVal).run).run
            ⟨initial.calls ++ [.isdone itr], hintWorld⟩)
        rw [hh]
        exact .hintAnswers hint stepReply hm


end JuliaLean.ChatGPT.Batch9.Group13

namespace JuliaLean.ChatGPT.Batch9.Group13

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.base.essentials.Models1Group18
open JuliaLean.Proofs.base.essentials.Models1Group18

set_option maxHeartbeats 2000000

theorem g13SyntaxBindRun {Atom A B : Type} (m : SyntaxM Atom A)
    (f : A → SyntaxM Atom B) (heap : SyntaxHeap Atom) :
    ((m >>= f).run heap) =
      match m.run heap with
      | .error e => .error e
      | .ok (a, heap') => (f a).run heap' := by
  simp only [StateT.run, Bind.bind, StateT.bind, Except.bind]
  cases m heap with
  | error e => rfl
  | ok pair => cases pair; rfl

theorem g13SyntaxPureRun {Atom A : Type} (a : A) (heap : SyntaxHeap Atom) :
    (pure a : SyntaxM Atom A).run heap = .ok (a, heap) := rfl

theorem g13SyntaxExprRun {Atom : Type} (head : String)
    (args : List (SyntaxValue Atom)) (heap : SyntaxHeap Atom) :
    (syntaxExpr head args).run heap =
      .ok (.exprRef heap.length, heap ++ [⟨head, args.map some⟩]) := rfl

theorem g13SyntaxGetRun {Atom : Type} (heap : SyntaxHeap Atom) :
    (get : SyntaxM Atom (SyntaxHeap Atom)).run heap = .ok (heap, heap) := rfl

theorem g13SyntaxReadRun {Atom : Type} (handle : Nat) (heap : SyntaxHeap Atom)
    (node : SyntaxNode Atom) (h : heap[handle]? = some node) :
    (syntaxRead handle).run heap = .ok (node, heap) := by
  rw [syntaxRead, g13SyntaxBindRun, g13SyntaxGetRun]
  dsimp only
  rw [h]
  rfl

theorem g13SyntaxValueValidLength {Atom : Type} {before after : SyntaxHeap Atom}
    (h : before.length ≤ after.length) (value : SyntaxValue Atom)
    (hv : syntaxValueValid before value) : syntaxValueValid after value := by
  cases value with
  | atom x => trivial
  | symbol x => trivial
  | exprRef n => change n < after.length; exact Nat.lt_of_lt_of_le hv h

theorem g13SyntaxValidAppend {Atom : Type} (heap : SyntaxHeap Atom)
    (vars args : List (SyntaxValue Atom)) (head : String)
    (hv : syntaxInputValid heap vars)
    (hlen : args.length ≤ IntTy.i64.max.toNat)
    (ha : ∀ value ∈ args, syntaxValueValid heap value) :
    syntaxInputValid (heap ++ [⟨head, args.map some⟩]) vars := by
  rcases hv with ⟨hvars, hvalues, hnodes⟩
  have hgrow : heap.length ≤ (heap ++ [⟨head, args.map some⟩] : SyntaxHeap Atom).length := by
    simp only [List.length_append, List.length_singleton] <;> omega
  refine ⟨hvars, ?_, ?_⟩
  · intro value hm
    exact g13SyntaxValueValidLength hgrow value (hvalues value hm)
  · intro node hm
    rcases List.mem_append.mp hm with hold | hnew
    · rcases hnodes node hold with ⟨hn, hs⟩
      refine ⟨hn, ?_⟩
      intro slot hslot value heq
      exact g13SyntaxValueValidLength hgrow value (hs slot hslot value heq)
    · have heq : node = ⟨head, args.map some⟩ := List.mem_singleton.mp hnew
      subst node
      refine ⟨by simpa only [List.length_map] using hlen, ?_⟩
      intro slot hslot value heq
      obtain ⟨v, hv, hsome⟩ := List.mem_map.mp hslot
      have hvEq : v = value := Option.some.inj (hsome.trans heq)
      subst v
      exact g13SyntaxValueValidLength hgrow value (ha value hv)

theorem g13SyntaxValidEmptyVars {Atom : Type} {heap : SyntaxHeap Atom}
    {vars : List (SyntaxValue Atom)} (h : syntaxInputValid heap vars) :
    syntaxInputValid heap [] := by
  refine ⟨Nat.zero_le _, ?_, h.2.2⟩
  intro value hm
  cases hm

theorem g13SyntaxGetAppend {Atom : Type} (heap extra : SyntaxHeap Atom)
    (handle : Nat) (node : SyntaxNode Atom) (h : heap[handle]? = some node) :
    (heap ++ extra)[handle]? = some node := by
  have hb : handle < heap.length := (List.getElem?_eq_some_iff.mp h).choose
  rw [List.getElem?_append_left hb, h]

theorem g13LabelPlainObservation {Atom : Type} (name : String)
    (body : SyntaxValue Atom) (heap : SyntaxHeap Atom)
    (hv : syntaxInputValid heap [body]) :
    LabelPlainObservation name body (.exprRef (heap.length + 1)) heap
      (heap ++ [⟨"symbolicblock", [some (.symbol name), some body]⟩] ++
        [⟨"escape", [some (.exprRef heap.length)]⟩]) := by
  let block : SyntaxNode Atom := ⟨"symbolicblock", [some (.symbol name), some body]⟩
  let escaped : SyntaxNode Atom := ⟨"escape", [some (.exprRef heap.length)]⟩
  have hmvalid : syntaxInputValid (heap ++ [block]) [body] := by
    apply g13SyntaxValidAppend heap [body] [.symbol name, body] "symbolicblock" hv
    · change (2 : Nat) ≤ IntTy.i64.max.toNat
      decide
    · intro value hm
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with h | h
      · subst value; trivial
      · subst value
        exact hv.2.1 body (by simp only [List.mem_singleton])
  have hevalid : syntaxInputValid (heap ++ [block] ++ [escaped]) [] := by
    apply g13SyntaxValidEmptyVars
    apply g13SyntaxValidAppend (heap ++ [block]) [body] [.exprRef heap.length] "escape" hmvalid
    · change (1 : Nat) ≤ IntTy.i64.max.toNat
      decide
    · intro value hm
      have heq := List.mem_singleton.mp hm
      subst value
      change heap.length < (heap ++ [block]).length
      simp only [List.length_append, List.length_singleton]
      omega
  refine ⟨⟨hevalid, ?_⟩, heap.length + 1, heap.length, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro handle node hnode
    exact g13SyntaxGetAppend _ _ _ _ (g13SyntaxGetAppend _ _ _ _ hnode)
  · omega
  · omega
  · omega
  · simp only [List.length_append, List.length_singleton] <;> omega
  · have hx : (heap ++ [block]).length = heap.length + 1 := by simp only [List.length_append, List.length_singleton]
    change (heap ++ [block] ++ [escaped])[heap.length + 1]? = some escaped
    rw [← hx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  · change (heap ++ [block] ++ [escaped])[heap.length]? = some block
    rw [List.getElem?_append_left (by simp only [List.length_append, List.length_singleton] <;> omega),
      List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl

theorem g13LabelUnderscore {Atom : Type} (body : SyntaxValue Atom) (heap : SyntaxHeap Atom) :
    (labelHeap "_" body).run heap = .error (.core (.error
      "use `@label expr` for anonymous blocks; `@label _ expr` is not allowed")) := by
  simp only [labelHeap, beq_self_eq_true, ↓reduceIte, g13SyntaxBindRun]
  rfl

theorem g13LabelPlainSuccess {Atom : Type} (name : String)
    (body : SyntaxValue Atom) (heap : SyntaxHeap Atom)
    (hv : syntaxInputValid heap [body]) (hname : name ≠ "_")
    (hno : ¬ ∃ node, LabelLoopInput heap body node) :
    ∃ value after, (labelHeap name body).run heap = .ok (value, after) ∧
      LabelPlainObservation name body value heap after := by
  refine ⟨.exprRef (heap.length + 1),
    heap ++ [⟨"symbolicblock", [some (.symbol name), some body]⟩] ++
      [⟨"escape", [some (.exprRef heap.length)]⟩], ?_,
    g13LabelPlainObservation name body heap hv⟩
  cases body with
  | atom value =>
    simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
      g13SyntaxPureRun, g13SyntaxExprRun, List.map_cons, List.map_nil, List.length_append, List.length_singleton]
  | symbol symbol =>
    simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
      g13SyntaxPureRun, g13SyntaxExprRun, List.map_cons, List.map_nil, List.length_append, List.length_singleton]
  | exprRef handle =>
    have hb : handle < heap.length := hv.2.1 (.exprRef handle) (by simp only [List.mem_singleton])
    obtain ⟨node, hnode⟩ : ∃ node, heap[handle]? = some node :=
      ⟨heap[handle], List.getElem?_eq_getElem hb⟩
    have hn : ¬ (node.head = "for" ∨ node.head = "while") := by
      intro h
      exact hno ⟨node, handle, rfl, hnode, h⟩
    simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
      g13SyntaxPureRun, g13SyntaxReadRun handle heap node hnode, Bool.or_eq_true, true_or, false_or, or_true, or_false,
      beq_iff_eq, hn, ↓reduceIte, g13SyntaxExprRun, List.map_cons, List.map_nil, List.length_append, List.length_singleton]


theorem g13SyntaxAppendLast {Atom : Type} (heap : SyntaxHeap Atom) (node : SyntaxNode Atom) :
    (heap ++ [node])[heap.length]? = some node := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem g13SyntaxValueValidAppend {Atom : Type} (heap extra : SyntaxHeap Atom)
    (value : SyntaxValue Atom) (hv : syntaxValueValid heap value) :
    syntaxValueValid (heap ++ extra) value := by
  apply g13SyntaxValueValidLength _ value hv
  simp only [List.length_append]
  omega

theorem g13SyntaxRefLastValid {Atom : Type} (heap : SyntaxHeap Atom) (node : SyntaxNode Atom) :
    syntaxValueValid (heap ++ [node]) (.exprRef heap.length) := by
  change heap.length < (heap ++ [node]).length
  simp only [List.length_append, List.length_singleton]
  omega

theorem g13SyntaxValidAppendTwo {Atom : Type} (heap : SyntaxHeap Atom)
    (head : String) (a b : SyntaxValue Atom)
    (hv : syntaxInputValid heap [])
    (ha : syntaxValueValid heap a) (hb : syntaxValueValid heap b) :
    syntaxInputValid (heap ++ [⟨head, [some a, some b]⟩]) [] := by
  apply g13SyntaxValidAppend heap [] [a,b] head hv
  · change (2 : Nat) ≤ IntTy.i64.max.toNat
    decide
  · intro value hm
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
    rcases hm with h | h
    · subst value; exact ha
    · subst value; exact hb

theorem g13LabelLoopObservation {Atom : Type} (name head : String)
    (header loopBody : SyntaxValue Atom) (heap : SyntaxHeap Atom)
    (hv : syntaxInputValid heap [])
    (hheader : syntaxValueValid heap header) (hbody : syntaxValueValid heap loopBody) :
    LabelLoopObservation name head header loopBody (.exprRef (heap.length + 3)) heap
      (heap ++ [⟨"symbolicblock", [some (.symbol (name ++ "#cont")), some loopBody]⟩] ++
        [⟨head, [some header, some (.exprRef heap.length)]⟩] ++
        [⟨"symbolicblock", [some (.symbol name), some (.exprRef (heap.length + 1))]⟩] ++
        [⟨"escape", [some (.exprRef (heap.length + 2))]⟩]) := by
  let cont : SyntaxNode Atom := ⟨"symbolicblock", [some (.symbol (name ++ "#cont")), some loopBody]⟩
  let loop : SyntaxNode Atom := ⟨head, [some header, some (.exprRef heap.length)]⟩
  let block : SyntaxNode Atom := ⟨"symbolicblock", [some (.symbol name), some (.exprRef (heap.length + 1))]⟩
  let escape : SyntaxNode Atom := ⟨"escape", [some (.exprRef (heap.length + 2))]⟩
  have h1 : syntaxInputValid (heap ++ [cont]) [] :=
    g13SyntaxValidAppendTwo heap "symbolicblock" (.symbol (name ++ "#cont")) loopBody hv trivial hbody
  have h2 : syntaxInputValid (heap ++ [cont] ++ [loop]) [] := by
    apply g13SyntaxValidAppendTwo (heap ++ [cont]) head header (.exprRef heap.length) h1
    · exact g13SyntaxValueValidAppend _ _ _ hheader
    · exact g13SyntaxRefLastValid heap cont
  have h3 : syntaxInputValid (heap ++ [cont] ++ [loop] ++ [block]) [] := by
    apply g13SyntaxValidAppendTwo (heap ++ [cont] ++ [loop]) "symbolicblock"
      (.symbol name) (.exprRef (heap.length + 1)) h2 trivial
    simpa only [List.length_append, List.length_singleton] using
      g13SyntaxRefLastValid (heap ++ [cont]) loop
  have h4 : syntaxInputValid (heap ++ [cont] ++ [loop] ++ [block] ++ [escape]) [] := by
    apply g13SyntaxValidAppend (heap ++ [cont] ++ [loop] ++ [block]) []
      [.exprRef (heap.length + 2)] "escape" h3
    · change (1 : Nat) ≤ IntTy.i64.max.toNat
      decide
    · intro value hm
      have heq := List.mem_singleton.mp hm
      subst value
      have hr := g13SyntaxRefLastValid (heap ++ [cont] ++ [loop]) block
      simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hr
  refine ⟨⟨h4, ?_⟩, heap.length + 3, heap.length + 2, heap.length + 1, heap.length,
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro handle node hnode
    exact g13SyntaxGetAppend _ _ _ _ (g13SyntaxGetAppend _ _ _ _
      (g13SyntaxGetAppend _ _ _ _ (g13SyntaxGetAppend _ _ _ _ hnode)))
  · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, or_false, and_true]
    omega
  · intro handle hm
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
    omega
  · simp only [List.length_append, List.length_singleton] <;> omega
  · have hx := g13SyntaxAppendLast (heap ++ [cont] ++ [loop] ++ [block]) escape
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hx
  · have hx := g13SyntaxGetAppend _ [escape] _ _
      (g13SyntaxAppendLast (heap ++ [cont] ++ [loop]) block)
    simpa only [List.length_append, List.length_singleton, Nat.add_assoc] using hx
  · have hx := g13SyntaxGetAppend _ [escape] _ _ (g13SyntaxGetAppend _ [block] _ _
      (g13SyntaxAppendLast (heap ++ [cont]) loop))
    simpa only [List.length_append, List.length_singleton] using hx
  · exact g13SyntaxGetAppend _ [escape] _ _ (g13SyntaxGetAppend _ [block] _ _
      (g13SyntaxGetAppend _ [loop] _ _ (g13SyntaxAppendLast heap cont)))


theorem g13SyntaxArgOneRun {Atom : Type} (handle : Nat) (heap : SyntaxHeap Atom)
    (node : SyntaxNode Atom) (hnode : heap[handle]? = some node) :
    (syntaxArg handle (JInt.wrap .i64 1)).run heap =
      match node.args[0]? with
      | none => .error (.core .bounds)
      | some none => .error (.core .undefRef)
      | some (some value) => .ok (value, heap) := by
  rw [syntaxArg, g13SyntaxBindRun, g13SyntaxReadRun handle heap node hnode]
  have hi : (JInt.wrap .i64 1).val = 1 := by decide
  have hlt : ¬ (1 : Int) < 1 := by decide
  have hoffset : ((1 : Int) - 1).toNat = 0 := by decide
  simp only [hi, hlt, ite_false, hoffset]
  cases hs : node.args[0]? with
  | none => rfl
  | some slot => cases slot <;> rfl

theorem g13SyntaxArgTwoRun {Atom : Type} (handle : Nat) (heap : SyntaxHeap Atom)
    (node : SyntaxNode Atom) (hnode : heap[handle]? = some node) :
    (syntaxArg handle (JInt.wrap .i64 2)).run heap =
      match node.args[1]? with
      | none => .error (.core .bounds)
      | some none => .error (.core .undefRef)
      | some (some value) => .ok (value, heap) := by
  rw [syntaxArg, g13SyntaxBindRun, g13SyntaxReadRun handle heap node hnode]
  have hi : (JInt.wrap .i64 2).val = 2 := by decide
  have hlt : ¬ (2 : Int) < 1 := by decide
  have hoffset : ((2 : Int) - 1).toNat = 1 := by decide
  simp only [hi, hlt, ite_false, hoffset]
  cases hs : node.args[1]? with
  | none => rfl
  | some slot => cases slot <;> rfl

theorem g13ForNeWhile : ("for" : String) ≠ "while" := by decide

theorem g13WhileNeFor : ("while" : String) ≠ "for" := by decide

theorem g13LabelLoopBounds {Atom : Type} (name : String) (handle : Nat)
    (heap : SyntaxHeap Atom) (node : SyntaxNode Atom) (hname : name ≠ "_")
    (hnode : heap[handle]? = some node) (hloop : node.head = "for" ∨ node.head = "while")
    (hlen : node.args.length < 2) :
    (labelHeap name (.exprRef handle)).run heap = .error (.core .bounds) := by
  have hslot : node.args[1]? = none := List.getElem?_eq_none (by omega)
  have hread : (syntaxArg handle (JInt.wrap .i64 2)).run heap = .error (.core .bounds) := by
    rw [g13SyntaxArgTwoRun handle heap node hnode, hslot]
  rcases hloop with hhead | hhead <;>
    simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
      g13SyntaxPureRun, g13SyntaxReadRun handle heap node hnode, hhead,
      hread, Bool.or_eq_true, true_or, false_or, or_true, or_false, beq_iff_eq, g13ForNeWhile, g13WhileNeFor, ↓reduceIte]

theorem g13LabelLoopSuccess {Atom : Type} (name : String) (handle : Nat)
    (heap : SyntaxHeap Atom) (node : SyntaxNode Atom) (hname : name ≠ "_")
    (hv : syntaxInputValid heap [.exprRef handle])
    (hnode : heap[handle]? = some node) (hloop : node.head = "for" ∨ node.head = "while")
    (header loopBody : SyntaxValue Atom)
    (hheader : node.args[0]? = some (some header))
    (hbody : node.args[1]? = some (some loopBody)) :
    ∃ value after, (labelHeap name (.exprRef handle)).run heap = .ok (value, after) ∧
      LabelLoopObservation name node.head header loopBody value heap after := by
  have hnvalid := hv.2.2 node (List.mem_of_getElem? hnode)
  have hhvalid : syntaxValueValid heap header :=
    hnvalid.2 (some header) (List.mem_of_getElem? hheader) header rfl
  have hbvalid : syntaxValueValid heap loopBody :=
    hnvalid.2 (some loopBody) (List.mem_of_getElem? hbody) loopBody rfl
  refine ⟨.exprRef (heap.length + 3),
    heap ++ [⟨"symbolicblock", [some (.symbol (name ++ "#cont")), some loopBody]⟩] ++
      [⟨node.head, [some header, some (.exprRef heap.length)]⟩] ++
      [⟨"symbolicblock", [some (.symbol name), some (.exprRef (heap.length + 1))]⟩] ++
      [⟨"escape", [some (.exprRef (heap.length + 2))]⟩], ?_,
    g13LabelLoopObservation name node.head header loopBody heap (g13SyntaxValidEmptyVars hv) hhvalid hbvalid⟩
  have hread2 : (syntaxArg handle (JInt.wrap .i64 2)).run heap = .ok (loopBody, heap) := by
    rw [g13SyntaxArgTwoRun handle heap node hnode, hbody]
  let cont : SyntaxNode Atom := ⟨"symbolicblock", [some (.symbol (name ++ "#cont")), some loopBody]⟩
  have hread1 : (syntaxArg handle (JInt.wrap .i64 1)).run (heap ++ [cont]) =
      .ok (header, heap ++ [cont]) := by
    rw [g13SyntaxArgOneRun handle (heap ++ [cont]) node (g13SyntaxGetAppend _ _ _ _ hnode), hheader]
  dsimp only [cont] at hread1
  rcases hloop with hhead | hhead <;>
    simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
      g13SyntaxPureRun, g13SyntaxReadRun handle heap node hnode, hhead,
      hread2, hread1, Bool.or_eq_true, true_or, false_or, or_true, or_false, beq_iff_eq, g13ForNeWhile, g13WhileNeFor, ↓reduceIte,
      g13SyntaxExprRun, List.map_cons, List.map_nil, List.length_append,
      List.length_cons, List.length_nil, Nat.add_assoc]


theorem g13LabelLoopUndef {Atom : Type} (name : String) (handle : Nat)
    (heap : SyntaxHeap Atom) (node : SyntaxNode Atom) (hname : name ≠ "_")
    (hnode : heap[handle]? = some node) (hloop : node.head = "for" ∨ node.head = "while")
    (hlen : 2 ≤ node.args.length)
    (hundef : node.args[0]? = some none ∨ node.args[1]? = some none) :
    (labelHeap name (.exprRef handle)).run heap = .error (.core .undefRef) := by
  cases hs2 : node.args[1]? with
  | none =>
    have hb := List.getElem?_eq_none_iff.mp hs2
    omega
  | some slot =>
    cases slot with
    | none =>
      have hread : (syntaxArg handle (JInt.wrap .i64 2)).run heap = .error (.core .undefRef) := by
        rw [g13SyntaxArgTwoRun handle heap node hnode, hs2]
      rcases hloop with hhead | hhead <;>
        simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
          g13SyntaxPureRun, g13SyntaxReadRun handle heap node hnode, hhead,
          hread, Bool.or_eq_true, true_or, false_or, or_true, or_false, beq_iff_eq, g13ForNeWhile, g13WhileNeFor, ↓reduceIte]
    | some loopBody =>
      have hs1 : node.args[0]? = some none := by
        rcases hundef with h | h
        · exact h
        · rw [hs2] at h
          cases h
      have hread2 : (syntaxArg handle (JInt.wrap .i64 2)).run heap = .ok (loopBody, heap) := by
        rw [g13SyntaxArgTwoRun handle heap node hnode, hs2]
      let cont : SyntaxNode Atom := ⟨"symbolicblock", [some (.symbol (name ++ "#cont")), some loopBody]⟩
      have hread1 : (syntaxArg handle (JInt.wrap .i64 1)).run (heap ++ [cont]) = .error (.core .undefRef) := by
        rw [g13SyntaxArgOneRun handle (heap ++ [cont]) node (g13SyntaxGetAppend _ _ _ _ hnode), hs1]
      dsimp only [cont] at hread1
      rcases hloop with hhead | hhead <;>
        simp only [labelHeap, beq_iff_eq, hname, ↓reduceIte, g13SyntaxBindRun,
          g13SyntaxPureRun, g13SyntaxReadRun handle heap node hnode, hhead,
          hread2, hread1, Bool.or_eq_true, true_or, false_or, or_true, or_false, beq_iff_eq, g13ForNeWhile, g13WhileNeFor, ↓reduceIte,
          g13SyntaxExprRun, List.map_cons, List.map_nil]

theorem Models1G18LabelHeap_proven :
    JuliaLean.Proofs.base.essentials.Models1Group18.LabelHeapCorrect := by
  constructor
  · intro Atom name body heap hv
    constructor
    · intro hname
      subst name
      exact g13LabelUnderscore body heap
    · intro hname
      constructor
      · intro hno
        exact g13LabelPlainSuccess name body heap hv hname hno
      · intro node hloop
        obtain ⟨handle, hbody, hnode, hhead⟩ := hloop
        subst body
        refine ⟨g13LabelLoopBounds name handle heap node hname hnode hhead, ?_, ?_⟩
        · rintro ⟨hlen, hundef⟩
          exact g13LabelLoopUndef name handle heap node hname hnode hhead hlen hundef
        · intro header loopBody hheader hloopBody
          exact g13LabelLoopSuccess name handle heap node hname hv hnode hhead header loopBody hheader hloopBody
  · intro Atom body heap
    exact g13LabelUnderscore body heap


end JuliaLean.ChatGPT.Batch9.Group13

namespace JuliaLean.Proofs.base.essentials

open JuliaLean.Registry

def entriesModels1Group18 : List Entry := [
  { id := "essentials-bounds-error-helpers", juliaFile := "base/essentials.jl",
    juliaFns := ["throw_boundserror (3)", "_throw_boundserror_indices (2)"],
    statement := "Every bound-error helper raises BoundsError on every already-evaluated input.",
    source := "base/essentials.jl:15-19; exception-class invariant", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.BoundsErrorHelpers, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18BoundsErrorHelpers_proven,
    notes := "Internal helper invariant; original callback-based helpers are unchanged. Exception payloads are not represented by the installed Exc type." },
  { id := "essentials-nospecialize-heap", juliaFile := "base/essentials.jl",
    juliaFns := ["@nospecialize"],
    statement := "For every constructible argument tuple and valid syntax heap, @nospecialize returns a fresh escaped metadata expression retaining input identities, repairs the head of a singleton assignment Expr in place, and preserves all other existing fields and objects, including aliases and cycles.",
    source := "base/essentials.jl:125-134; base/runtime_internals.jl:624-626; doc/src/manual/metaprogramming.md:51-67,190-192", status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.NospecializeHeapCorrect, thm := none,
    notes := "No complete exact proof returned. verified through g13SpecialHeadExprRun, including singleton atom/symbol/expression execution and common syntax heap primitives; the remaining goal is the non-singleton branch, full head-repair/frame invariant, and composition with fresh nospecialize metadata and escape allocations." },
  { id := "essentials-specialize-heap", juliaFile := "base/essentials.jl",
    juliaFns := ["@specialize"],
    statement := "For every constructible argument tuple and valid syntax heap, @specialize returns a fresh escaped metadata expression retaining input identities, repairs the head of a singleton assignment Expr in place, and preserves all other existing fields and objects, including aliases and cycles.",
    source := "base/essentials.jl:142-151; base/runtime_internals.jl:624-626; doc/src/manual/metaprogramming.md:51-67,190-192", status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.SpecializeHeapCorrect, thm := none,
    notes := "No complete exact proof returned. verified through g13SpecialHeadExprRun, sharing the atom/symbol branches and syntax heap primitives; the remaining goal is the non-singleton branch, full head-repair/frame invariant, and composition with fresh specialize metadata and escape allocations." },
  { id := "essentials-eval-expansion", juliaFile := "base/essentials.jl",
    juliaFns := ["@eval(ex)", "@eval(mod,ex)"],
    statement := "Both @eval expansions preserve the selected module and quoted input, emit one escaped Core.eval call, and return its bound result after the toplevel world-age marker.",
    source := "base/essentials.jl:482-501; macro-expansion invariants", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.EvalExpansionPreservesPayload, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18EvalExpansion_proven,
    notes := "Tests the scaffold using a binder-name-independent observer, not equality with a copied whole output expression. Core.eval execution is outside macro expansion." },
  { id := "essentials-cconvert-bottom", juliaFile := "base/essentials.jl",
    juliaFns := ["cconvert(::Type{Union{}},x...)"],
    statement := "C conversion to Union{} raises ArgumentError for every already-evaluated argument tuple.",
    source := "base/essentials.jl:474,740; empty-type conversion invariant", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.CconvertBottomRejects, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18CconvertBottom_proven,
    notes := "Uses the concrete installed convertUnionBottom; no conversion callback or correctness premise." },
  { id := "essentials-label-heap", juliaFile := "base/essentials.jl",
    juliaFns := ["@label(name::Symbol,body)"],
    statement := "Named @label rejects _ before reading the body; preserves all old syntax objects; gives ordinary bodies an escaped named block and loops a name#cont target; throws BoundsError for fewer than two loop operands and UndefRefError for undefined required operands, while ignoring extras.",
    source := "base/essentials.jl:990-1009,1035-1052,1073-1077; doc/src/manual/arrays.md:519-528", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.LabelHeapCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18LabelHeap_proven,
    notes := "Full valid machine-sized syntax-heap domain includes undefined slots, sharing and cycles. Fresh allocations on an error are unreachable; no old object is mutated. Compiler lowering and physical resource exhaustion remain outside the existing syntax model." },
  { id := "essentials-svec-read", juliaFile := "base/essentials.jl",
    juliaFns := ["getindex(::SimpleVector,::Int)"],
    statement := "SimpleVector scalar indexing reads its stored element, raises BoundsError outside the valid Int64 index interval, and preserves the installed undefined-behavior boundary for a null internal slot.",
    source := "base/essentials.jl:1096; source boundary Core._svec_ref documented in svecRefV", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.SvecReadCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18SvecRead_proven,
    notes := "The SizedSVec field bounds the length by typemax(Int64); every Int64 index is quantified. Null internal slots are not excluded." },
  { id := "essentials-svec-shape", juliaFile := "base/essentials.jl",
    juliaFns := ["length(::SimpleVector)", "firstindex(::SimpleVector)", "lastindex(::SimpleVector)", "keys(::SimpleVector)", "axes(::SimpleVector)"],
    statement := "SimpleVector length counts stored positions, firstindex is one, lastindex is the count, and keys and the sole axis cover exactly those positions, including empty vectors.",
    source := "base/essentials.jl:1097-1106; base/range.jl:478-486", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.SvecShapeCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18SvecShape_proven,
    notes := "Results and range bounds use JInt Int64. A local concrete OneTo{Int64} specialization is recorded as the only extra callee dependency for keys/axes." },
  { id := "essentials-svec-map-trace", juliaFile := "base/essentials.jl",
    juliaFns := ["map(f,v::SimpleVector)"],
    statement := "SimpleVector map allocates before calling f, processes stored elements in order, stores each actual result, and retains callback/earlier-store effects on errors. Every outcome has a source-indexed finite observation trace; failure or divergence must come from the next actual primitive or callback. Empty output reuses the canonical memory singleton and oversized boxed output fails before f.",
    source := "base/essentials.jl:1117; base/array.jl:684-687; base/abstractarray.jl:941-951; base/generator.jl:44-50; src/genericmemory.c:55-102", status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.MapState.MappingTraceCorrect, thm := none,
    notes := "No complete exact proof returned. g13MapOffset and g13StoredListSet are verified, together with primitive memory reads/writes and zero/positive allocator execution; remaining goals are destination-store classification, FreshOutput allocation, SuccessfulPrefix extension, and the map-loop induction assembling MappingTraceCorrect." },
  { id := "essentials-svec-isassigned-modes", juliaFile := "base/essentials.jl",
    juliaFns := ["isassigned(::SimpleVector,::Int)"],
    statement := "With bounds checks, SimpleVector isassigned is true exactly for indices from one through its length; when the source bounds-check block is elided it returns true for every Int64 index.",
    source := "base/essentials.jl:1151-1154; bounds/elision invariant", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.SvecIsassignedModes, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18SvecIsassignedModes_proven,
    notes := "Null internal slots are included. This property describes the actual range/elision behavior, without assuming the public assigned-slot contract." },
  { id := "essentials-svec-isassigned-documentation", juliaFile := "base/essentials.jl",
    juliaFns := ["isassigned(::SimpleVector,::Int)"],
    statement := "The documented isassigned result is true exactly for an in-bounds initialized slot and false for an undefined reference.",
    source := "base/essentials.jl:1123-1154 (isassigned docstring and SimpleVector specialization)", status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.SvecIsassignedDocumentation, thm := none,
    notes := "Statement defect: SizedSVec permits one internal null slot and i=1, for which the bounds-only specialization returns true, but Core.svec public construction initializes every slot (Core.svec(undef) stores an initialized object); restrict the statement to publicly constructible initialized slots." },
  { id := "essentials-isempty-boundary", juliaFile := "base/essentials.jl",
    juliaFns := ["isempty(itr)"],
    statement := "At the existing IterMethods boundary, isempty calls isdone once, propagates its failure/nontermination/effects, and returns any non-missing hint unchanged. Only missing allows one subsequent iterate call; its exact failure/nontermination/effects propagate, nothing yields true, and an item/state pair yields false.",
    source := "base/essentials.jl:1214-1224,1235-1239,1584-1601; doc/src/manual/interfaces.md:12-14,27-34", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.IsEmptyBoundaryProtocol, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18IsemptyBoundary_proven,
    notes := "The concrete protocol probes quantify over all value/error/nontermination outcomes and arbitrary world snapshots. There is no supplied correctness law; the existing interface boundary remains explicit and custom iterator bodies are not implemented here." },
  { id := "essentials-ismissing-singleton", juliaFile := "base/essentials.jl",
    juliaFns := ["ismissing(x)"],
    statement := "ismissing is true exactly for the existing Missing singleton over the complete represented value domain.",
    source := "base/essentials.jl:1535-1542", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.IsmissingSingletonCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18IsmissingSingleton_proven,
    notes := "Uses the installed reserved Missing type tag; does not substitute generic == or a supplied predicate. Unproved." },
  { id := "essentials-line-location", juliaFile := "base/essentials.jl",
    juliaFns := ["@__LINE__()"],
    statement := "The macro returns the signed machine line number of its call location, including zero for unknown locations, independently of the optional file symbol.",
    source := "base/essentials.jl:1573-1580; base/boot.jl:133-136,710-714", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.LineMacroLocationCorrect, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18LineLocation_proven,
    notes := "The implicit macro source is a typed LineNumberNode record. No source getter callback or nonnegative-line precondition. Unproved." }
,
  { id := "essentials-internal-gate", juliaFile := "base/essentials.jl",
    juliaFns := ["_is_internal", "@_total_meta", "@_foldable_meta", "@_terminates_locally_meta", "@_terminates_globally_meta", "@_terminates_globally_notaskstate_meta", "@_terminates_globally_noub_meta", "@_effect_free_terminates_locally_meta", "@_nothrow_noub_meta", "@_nothrow_meta", "@_noub_meta", "@_notaskstate_meta", "@_noub_if_noinbounds_meta"], statement := "Base is recognized before parent traversal; non-module arguments fail at _nameof; internal macros preserve all eleven source flags.",
    source := "base/essentials.jl:190-374", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.InternalGateAndFlags, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18InternalGate_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-min-initialized", juliaFile := "base/essentials.jl",
    juliaFns := ["datatype_min_ninitialized"], statement := "Abstract DataTypes require zero initialized fields for every represented metadata snapshot.",
    source := "base/essentials.jl:617-646; base/runtime_internals.jl:1186-1192", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.AbstractMinInitializedZero, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18MinInitialized_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-typevar-query", juliaFile := "base/essentials.jl",
    juliaFns := ["has_typevar"], statement := "A TypeVar contains its own free occurrence; a datatype with no free variables contains none.",
    source := "base/essentials.jl:1298; src/jltypes.c:270-346", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.TypevarQueryIdentity, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18TypevarQuery_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-fieldtypes-constrain", juliaFile := "base/essentials.jl",
    juliaFns := ["_fieldtypes_constrain_typevars"], statement := "With no type variables, the field constraint check succeeds without inspecting field slots.",
    source := "base/essentials.jl:1302-1339", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.EmptyTypevarsConstrained, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18FieldtypesConstrain_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-existing-array-shape", juliaFile := "base/essentials.jl",
    juliaFns := ["size(::Array)", "length(::Array{T,1})"], statement := "Array shape access preserves stored dimensions and rank-one length returns the sole machine dimension.",
    source := "base/essentials.jl:12,1296", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.ExistingArrayShape, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18ExistingArrayShape_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-existing-vararg-inspection", juliaFile := "base/essentials.jl",
    juliaFns := ["isvarargtype", "isvatuple", "unwrapva", "unconstrain_vararg_length"], statement := "Vararg inspection recognizes its tag, preserves the element type, and removes only its length constraint.",
    source := "base/essentials.jl:589-613", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.ExistingVarargInspection, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18ExistingVarargInspection_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-existing-tuple-identity", juliaFile := "base/essentials.jl",
    juliaFns := ["convert(::Type{T},x::T) where T<:Tuple"], statement := "The matching-type tuple conversion preserves its argument.",
    source := "base/essentials.jl:652", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.ExistingTupleIdentity, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18ExistingTupleIdentity_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." },
  { id := "essentials-existing-primitive-not", juliaFile := "base/essentials.jl",
    juliaFns := ["!(::Bool)"], statement := "Bound intrinsic Boolean negation exchanges true and false.",
    source := "base/essentials.jl:1294", status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models1Group18.ExistingPrimitiveNot, thm := some ``JuliaLean.ChatGPT.Batch9.Group13.Models1G18ExistingPrimitiveNot_proven,
    notes := "Source-reviewed invariant; no theorem is claimed." }
]

end JuliaLean.Proofs.base.essentials

namespace JuliaLean.ChatGPT.Batch8.Group7
open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.Proofs.base.essentials

set_option maxHeartbeats 400000
set_option maxRecDepth 2000

/-- Executing a bind exposes nontermination, an exception, or the next state. -/
theorem g7AccessBindRun {α β : Type} (action : HM α) (next : α → HM β) (heap : Heap) :
    ((action >>= next).run heap) =
      match action.run heap with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (value, heap')) => (next value).run heap' := by
  simp only [StateT.run, Bind.bind, StateT.bind, ExceptT.bind,
    ExceptT.mk, Option.bind]
  cases action heap with
  | none => rfl
  | some result => cases result <;> rfl

theorem g7AccessPureRun {α : Type} (value : α) (heap : Heap) :
    ((pure value : HM α).run heap) = some (.ok (value, heap)) := rfl

theorem g7AccessThrowRun {α : Type} (e : Err) (heap : Heap) :
    ((throw e : HM α).run heap) = some (.error e) := rfl

theorem g7AccessGetRun (heap : Heap) :
    (get : HM Heap).run heap = some (.ok (heap, heap)) := rfl

/-- An error stops a bind without reducing its continuation. -/
theorem g7AccessBindError {α β : Type} (action : HM α) (next : α → HM β)
    (heap : Heap) (error : Err)
    (failed : action.run heap = some (.error error)) :
    (action >>= next).run heap = some (.error error) := by
  rw [g7AccessBindRun, failed]

/-- Reading an existing memory handle preserves the heap. -/
theorem g7AccessMemObjRun (memory : Mem) (o : MemObj) (heap : Heap)
    (h : heap[memory.handle]? = some o) :
    (memObj memory).run heap = some (.ok (o, heap)) := by
  simp only [memObj, g7AccessBindRun, g7AccessGetRun, h, g7AccessPureRun]

/-- Reading its length preserves the heap. -/
theorem g7AccessMemLengthRun (memory : Mem) (o : MemObj) (heap : Heap)
    (h : heap[memory.handle]? = some o) :
    (memLength memory).run heap = some (.ok (o.slots.length, heap)) := by
  simp only [memLength, g7AccessBindRun, g7AccessMemObjRun memory o heap h,
    g7AccessPureRun]

/-- Constructing an out-of-range memory reference raises the bounds exception. -/
theorem g7AccessMemoryRefFailure (memory : Mem) (o : MemObj) (heap : Heap)
    (i : JInt .i64) (hheap : heap[memory.handle]? = some o)
    (hbad : ¬ (1 ≤ i.val ∧ i.val ≤ o.slots.length)) :
    (memoryrefnewMem memory i false).run heap = some (.error (.core .bounds)) := by
  simp only [memoryrefnewMem, g7AccessBindRun,
    g7AccessMemLengthRun memory o heap hheap, hbad, ↓reduceIte, g7AccessThrowRun]

/-- The outer check either returns unit without changing the heap, or throws. -/
theorem g7AccessBoundsRun (memory : Mem) (o : MemObj) (heap : Heap)
    (i : JInt .i64) (hheap : heap[memory.handle]? = some o) :
    ((do
      let len ← memLength memory
      checkboundsLinear (JInt.wrap .i64 len) i) : HM Unit).run heap =
      if Arrays.checkboundsBool (JInt.wrap .i64 o.slots.length) i then
        some (.ok ((), heap))
      else some (.error (.core .bounds)) := by
  rw [g7AccessBindRun, g7AccessMemLengthRun memory o heap hheap]
  change (checkboundsLinear (JInt.wrap .i64 o.slots.length) i).run heap = _
  unfold checkboundsLinear
  cases Arrays.checkboundsBool (JInt.wrap .i64 o.slots.length) i <;> rfl

/-- A GenericMemory size is its single wrapped length. -/
theorem g7AccessSizeMemory (memory : Mem) (o : MemObj) (heap : Heap)
    (hheap : heap[memory.handle]? = some o) :
    (sizeGenericMemory memory).run heap =
      some (.ok ([JInt.wrap .i64 o.slots.length], heap)) := by
  simp only [sizeGenericMemory, g7AccessBindRun,
    g7AccessMemLengthRun memory o heap hheap, g7AccessPureRun]

/-- A reference read selects the memory object's default order. -/
theorem g7AccessRefRead (ref : MRef) (o : MemObj) (heap : Heap)
    (hheap : heap[ref.mem.handle]? = some o) :
    (getindexGenericMemoryRef false ref).run heap =
      (memoryrefget ref (defaultAccessOrderMemoryRef o.atomic) false).run heap := by
  simp only [getindexGenericMemoryRef, defaultAccessOrderMem, g7AccessBindRun,
    g7AccessMemObjRun ref.mem o heap hheap, g7AccessPureRun]
  rfl

end JuliaLean.ChatGPT.Batch8.Group7


namespace JuliaLean.ChatGPT.Batch8.Group7
open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.Proofs.base.essentials

set_option maxHeartbeats 1600000

theorem g7SvecAssignedGet (xs : List (Option JVal)) (k : Nat)
    (ha : ∀ s ∈ xs, s.isSome) (hk : k < xs.length) :
    ∃ x, xs[k]? = some (some x) := by
  induction xs generalizing k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons a xs ih =>
    cases k with
    | zero =>
      have h : a.isSome := ha a (by simp only [List.mem_cons, true_or])
      cases a with
      | none => cases h
      | some x => exact ⟨x, rfl⟩
    | succ k =>
      have hxs : ∀ s ∈ xs, s.isSome := by
        intro s hs
        exact ha s (by simp only [List.mem_cons]; exact Or.inr hs)
      have hk' : k < xs.length := by simp only [List.length_cons] at hk; omega
      obtain ⟨x, hx⟩ := ih k hxs hk'
      exact ⟨x, hx⟩



/-- An assigned in-range SimpleVector entry is returned by its accessor. -/
theorem g7SvecSvecGetAssigned (v : SVecObj) (k : Nat)
    (ha : ∀ s ∈ v.slots, s.isSome) (hk : k < v.slots.length) :
    ∃ x, getindexSVec v ((k : Int) + 1) = .ok x := by
  obtain ⟨x, hx⟩ := g7SvecAssignedGet v.slots k ha hk
  refine ⟨x, ?_⟩
  have hb : ¬ ((k : Int) + 1 < 1 ∨ (k : Int) + 1 > v.slots.length) := by omega
  have hi : (((k : Int) + 1) - 1).toNat = k := by omega
  simp only [getindexSVec, svecRefV, Arrays.svecRef, hb, ↓reduceIte, hi, hx] <;> rfl

/-- The equality traversal is reflexive on assigned slots when its element test is. -/
theorem g7SvecSvecEqualLoop (eq : JVal → JVal → RE JVal) (v : SVecObj)
    (ha : ∀ s ∈ v.slots, s.isSome) (heq : ∀ x, eq x x = .ok (.bool true))
    (ks : List Nat) (hk : ∀ k ∈ ks, k < lengthSVec v) :
    equalSVec.loop eq v v ks = .ok true := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have hbound := hk k (by simp only [List.mem_cons, true_or])
    obtain ⟨x, hx⟩ := g7SvecSvecGetAssigned v k ha hbound
    have hks : ∀ k ∈ ks, k < lengthSVec v := by
      intro j hj
      exact hk j (by simp only [List.mem_cons]; exact Or.inr hj)
    simp only [equalSVec.loop, hx, bind, Except.bind, heq, ih hks]

/-- The nonallocating SimpleVector clauses, retained independently of the copy loop. -/
theorem g7SvecSvecBasicClauses :
  (∀ v : SVecObj,
    lengthSVec v = v.slots.length ∧ firstindexSVec v = 1 ∧
      lastindexSVec v = v.slots.length ∧ keysSVec v = v.slots.length ∧
      eltypeSVec = "Any" ∧ axesSVec v = [v.slots.length] ∧
      isemptySVec v = decide (v.slots.length = 0)) ∧
  (∀ (v : SVecObj) (i : Int), (lengthSVec v : Int) < i → iterateSVec v i = .ok none) ∧
  (∀ (v : SVecObj) (i : Nat) (value : JVal),
    getindexSVec v (i : Int) = .ok value → i ≤ lengthSVec v →
      iterateSVec v i = .ok (some (value, i + 1))) ∧
  (∀ (eq : JVal → JVal → RE JVal) (v : SVecObj),
    (∀ s ∈ v.slots, s.isSome) → (∀ x, eq x x = .ok (.bool true)) →
      equalSVec eq v v = .ok true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    simp only [isemptySVec, lengthSVec, Arrays.svecLength, Bool.beq_eq_decide_eq]
  · intro v i h
    simp only [iterateSVec, h, ↓reduceIte]
  · intro v i value h hi
    have hb : ¬ (lengthSVec v : Int) < i := by omega
    simp only [iterateSVec, hb, ↓reduceIte, h, bind, Except.bind, pure, Except.pure]
  · intro eq v ha heq
    unfold equalSVec
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact g7SvecSvecEqualLoop eq v ha heq (List.range (lengthSVec v))
      (fun k hk => List.mem_range.mp hk)


theorem g7SvecHMBindRun {α β : Type} (action : HM α) (next : α → HM β) (heap : Heap) :
    ((action >>= next).run heap) =
      match action.run heap with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (value, heap')) => (next value).run heap' := by
  simp only [StateT.run, Bind.bind, StateT.bind, ExceptT.bind, ExceptT.mk, Option.bind]
  cases action heap with
  | none => rfl
  | some result =>
    cases result with
    | error e => rfl
    | ok pair => cases pair; rfl


/-- A pure stateful value leaves the heap unchanged. -/
theorem g7SvecHMPureRun {α : Type} (value : α) (heap : Heap) :
    ((pure value : HM α).run heap) = some (.ok (value, heap)) := rfl

/-- Raising an error discards the result state. -/
theorem g7SvecHMThrowRun {α : Type} (e : Err) (heap : Heap) :
    ((throw e : HM α).run heap) = some (.error e) := rfl

/-- Lifting an error into the heap computation preserves the error. -/
theorem g7SvecLiftErrorRun {α : Type} (e : Err) (heap : Heap) :
    (liftHM (.error e : RE α)).run heap = some (.error e) := rfl



theorem g7SvecHMGetRun (heap : Heap) :
    ((get : HM Heap).run heap) = some (.ok (heap, heap)) := rfl

theorem g7SvecMemObjRun (memory : Mem) (o : MemObj) (heap : Heap)
    (h : heap[memory.handle]? = some o) :
    (memObj memory).run heap = some (.ok (o, heap)) := by
  simp only [memObj, g7SvecHMBindRun, g7SvecHMGetRun, h, g7SvecHMPureRun]



/-- Applying a heap update returns the updated heap with a unit result. -/
theorem g7SvecHMModifyRun (f : Heap → Heap) (heap : Heap) :
    ((modify f : HM Unit).run heap) = some (.ok ((), f heap)) := rfl

/-- A finite stateless input traversal writes exactly the slots it visits. -/
theorem g7SvecCopyIndexPartial {Src : Type}
    (iter : Src → Option Nat → HM (Option (JVal × Nat))) (src : Src)
    (fAt : Nat → RE JVal) (n base : Nat) (dest : Arr)
    (hprod : (prodDims dest.size).val = (n : Int)) (hoff : dest.ref.index = 0)
    (hstep : ∀ (k : Nat) (st : Option Nat) (heap : Heap), st.getD base = k + base →
      (iter src st).run heap =
        if k < n then
          match fAt k with
          | .error e => some (.error e)
          | .ok value => some (.ok (some (value, k + 1 + base), heap))
        else some (.ok (none, heap))) :
    ∀ (remaining k : Nat) (st : Option Nat) (heap heap' : Heap) (o : MemObj),
      k + remaining = n → st.getD base = k + base →
      heap[dest.ref.mem.handle]? = some o → o.slots.length = n →
      (copytoArrayAny iter dest src k st).run heap = some (.ok ((), heap')) →
      ∃ o', heap'[dest.ref.mem.handle]? = some o' ∧ o'.slots.length = n ∧
        (∀ j, j < k → o'.slots[j]? = o.slots[j]?) ∧
        (∀ j value, k ≤ j → j < n → fAt j = .ok value →
          o'.slots[j]? = some (some value)) := by
  intro remaining
  induction remaining with
  | zero =>
    intro k st heap heap' o hn hst hheap hslots hrun
    have hkn : k = n := by omega
    rw [copytoArrayAny.eq_1, g7SvecHMBindRun, hstep k st heap hst,
      if_neg (by omega)] at hrun
    simp only [g7SvecHMPureRun] at hrun
    have he : heap = heap' := (Prod.mk.inj (Except.ok.inj (Option.some.inj hrun))).2
    subst heap'
    refine ⟨o, hheap, hslots, ?_, ?_⟩
    · intro j hj
      rfl
    · intro j value hkj hj hf
      omega
  | succ remaining ih =>
    intro k st heap heap' o hn hst hheap hslots hrun
    have hkn : k < n := by omega
    rw [copytoArrayAny.eq_1, g7SvecHMBindRun, hstep k st heap hst, if_pos hkn] at hrun
    cases hf : fAt k with
    | error e => rw [hf] at hrun; cases hrun
    | ok value =>
      let oNext : MemObj := { o with slots := o.slots.set k (some value) }
      let nextHeap := heap.set dest.ref.mem.handle oNext
      have hbound : dest.ref.mem.handle < heap.length :=
        (List.getElem?_eq_some_iff.mp hheap).choose
      have hheapNext : nextHeap[dest.ref.mem.handle]? = some oNext :=
        List.getElem?_set_self hbound
      have hslotsNext : oNext.slots.length = n := by
        simpa only [oNext, List.length_set] using hslots
      have hguard : ¬ (prodDims dest.size).val ≤ k := by rw [hprod]; omega
      simp only [hf, g7SvecHMBindRun, g7SvecMemObjRun dest.ref.mem o heap hheap,
        hguard, ↓reduceIte, hoff, Nat.zero_add, g7SvecHMPureRun, g7SvecHMModifyRun] at hrun
      obtain ⟨oFinal, hfinal, hlength, hprefix, hsuffix⟩ :=
        ih (k + 1) (some (k + 1 + base)) nextHeap heap' oNext
          (by omega) rfl hheapNext hslotsNext hrun
      refine ⟨oFinal, hfinal, hlength, ?_, ?_⟩
      · intro j hj
        rw [hprefix j (by omega)]
        exact List.getElem?_set_ne (by omega)
      · intro j result hkj hj hfj
        by_cases hjk : j = k
        · subst j
          rw [hf] at hfj
          cases hfj
          rw [hprefix k (by omega)]
          exact List.getElem?_set_self (by omega)
        · exact hsuffix j result (by omega) hj hfj

/-- The same finite copy loop succeeds when every requested input value is available. -/
theorem g7SvecCopyIndexTotal {Src : Type}
    (iter : Src → Option Nat → HM (Option (JVal × Nat))) (src : Src)
    (fAt : Nat → RE JVal) (n base : Nat) (dest : Arr)
    (hprod : (prodDims dest.size).val = (n : Int)) (hoff : dest.ref.index = 0)
    (hstep : ∀ (k : Nat) (st : Option Nat) (heap : Heap), st.getD base = k + base →
      (iter src st).run heap =
        if k < n then
          match fAt k with
          | .error e => some (.error e)
          | .ok value => some (.ok (some (value, k + 1 + base), heap))
        else some (.ok (none, heap)))
    (havail : ∀ k, k < n → ∃ value, fAt k = .ok value) :
    ∀ (remaining k : Nat) (st : Option Nat) (heap : Heap) (o : MemObj),
      k + remaining = n → st.getD base = k + base →
      heap[dest.ref.mem.handle]? = some o → o.slots.length = n →
      ∃ heap', (copytoArrayAny iter dest src k st).run heap = some (.ok ((), heap')) := by
  intro remaining
  induction remaining with
  | zero =>
    intro k st heap o hn hst hheap hslots
    refine ⟨heap, ?_⟩
    rw [copytoArrayAny.eq_1, g7SvecHMBindRun, hstep k st heap hst,
      if_neg (by omega)]
    rfl
  | succ remaining ih =>
    intro k st heap o hn hst hheap hslots
    have hkn : k < n := by omega
    obtain ⟨value, hf⟩ := havail k hkn
    let oNext : MemObj := { o with slots := o.slots.set k (some value) }
    let nextHeap := heap.set dest.ref.mem.handle oNext
    have hbound : dest.ref.mem.handle < heap.length :=
      (List.getElem?_eq_some_iff.mp hheap).choose
    have hheapNext : nextHeap[dest.ref.mem.handle]? = some oNext :=
      List.getElem?_set_self hbound
    have hslotsNext : oNext.slots.length = n := by
      simpa only [oNext, List.length_set] using hslots
    have hguard : ¬ (prodDims dest.size).val ≤ k := by rw [hprod]; omega
    obtain ⟨heap', hrun⟩ := ih (k + 1) (some (k + 1 + base)) nextHeap oNext
      (by omega) rfl hheapNext hslotsNext
    refine ⟨heap', ?_⟩
    rw [copytoArrayAny.eq_1, g7SvecHMBindRun, hstep k st heap hst, if_pos hkn]
    simp only [hf, g7SvecHMBindRun, g7SvecMemObjRun dest.ref.mem o heap hheap,
      hguard, ↓reduceIte, hoff, Nat.zero_add, g7SvecHMPureRun, g7SvecHMModifyRun]
    exact hrun

/-- The source of an Any comprehension supplies an index and its successor. -/
abbrev g7SvecSvecIndexIter (v : SVecObj) (_ : Unit) (st : Option Nat) :
    HM (Option (JVal × Nat)) := do
  let i := st.getD 1
  if lengthSVec v < i then pure none else pure (some (.int i, i + 1))

/-- The mapped SimpleVector generator, written once for the loop lemmas. -/
abbrev g7SvecSvecMappedIter (g : JVal → JVal) (v : SVecObj) (src : Unit) (st : Option Nat) :
    HM (Option (JVal × Nat)) := do
  match ← g7SvecSvecIndexIter v src st with
  | none => pure none
  | some (x, next) =>
    let value ← (fun i => do (fun x => pure (g x)) (← liftHM (getindexSVecValue v i))) x
    pure (some (value, next))

/-- A one-dimensional allocation is representable under the target's size bound. -/
theorem g7SvecNatWrapSmall (n : Nat) (hn : n < 2 ^ 62) : wrapInt .i64 (n : Int) = n := by
  apply wrapInt_of_inRange
  change -(2 : Int) ^ 63 ≤ n ∧ (n : Int) ≤ 2 ^ 63 - 1
  omega

/-- The product of one bounded dimension is that dimension. -/
theorem g7SvecProdSingle (n : Nat) (hn : n < 2 ^ 62) :
    (prodDims [JInt.wrap .i64 n]).val = (n : Int) := by
  change wrapInt .i64 (wrapInt .i64 n * 1) = n
  rw [g7SvecNatWrapSmall n hn, Int.mul_one, g7SvecNatWrapSmall n hn]

/-- Header returned by a fresh one-dimensional allocation. -/
abbrev g7SvecFreshAnyDest (heap : Heap) (n : Nat) : Arr :=
  ⟨⟨⟨heap.length⟩, 0⟩, [JInt.wrap .i64 n]⟩

/-- Memory returned by a fresh one-dimensional allocation. -/
abbrev g7SvecFreshAnyMemory (n : Nat) : MemObj :=
  ⟨List.replicate n none, false, 8, false⟩

/-- A fresh allocation extends the heap by one unassigned memory object. -/
theorem g7SvecAllocOneRun (n : Nat) (hn : n < 2 ^ 62) (heap : Heap) :
    (allocArrayAny [JInt.wrap .i64 n]).run heap =
      some (.ok (g7SvecFreshAnyDest heap n, heap ++ [g7SvecFreshAnyMemory n])) := by
  change (some (.ok (g7SvecFreshAnyDest heap n,
    heap ++ [⟨List.replicate (prodDims [JInt.wrap .i64 n]).val.toNat none,
      false, 8, false⟩])) : Option (Except Err (Arr × Heap))) = _
  rw [g7SvecProdSingle n hn, Int.toNat_natCast]

/-- The mapped generator takes the next index exactly once. -/
theorem g7SvecSvecMappedIterStep (g : JVal → JVal) (v : SVecObj)
    (k : Nat) (st : Option Nat) (heap : Heap) (hst : st.getD 1 = k + 1) :
    (g7SvecSvecMappedIter g v () st).run heap =
      if k < lengthSVec v then
        match (getindexSVec v ((k : Int) + 1)).map g with
        | .error e => some (.error e)
        | .ok value => some (.ok (some (value, k + 1 + 1), heap))
      else some (.ok (none, heap)) := by
  unfold g7SvecSvecMappedIter g7SvecSvecIndexIter
  simp only [hst]
  by_cases hk : k < lengthSVec v
  · have hstop : ¬ lengthSVec v < k + 1 := by omega
    simp only [hk, hstop, ↓reduceIte, g7SvecHMBindRun, g7SvecHMPureRun,
      getindexSVecValue, Int.natCast_add, Int.ofNat_one]
    cases hr : getindexSVec v ((k : Int) + 1) <;>
      simp only [hr, liftHM, g7SvecHMBindRun, g7SvecHMPureRun, g7SvecHMThrowRun, Except.map]
  · have hstop : lengthSVec v < k + 1 := by omega
    simp only [hk, hstop, ↓reduceIte, g7SvecHMBindRun, g7SvecHMPureRun]

/-- A successful monadic map retains its length and the outcome at every position. -/
theorem g7SvecMapMValues (f : JVal → RE JVal) (xs ys : List JVal)
    (h : xs.mapM f = .ok ys) :
    ys.length = xs.length ∧
      ∀ (k : Nat) x, xs[k]? = some x → ∃ y, f x = .ok y ∧ ys[k]? = some y := by
  induction xs generalizing ys with
  | nil =>
    change Except.ok [] = Except.ok ys at h
    cases h
    refine ⟨rfl, ?_⟩
    intro k x hx
    cases hx
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => rw [hx] at h; cases h
    | ok y =>
      cases ht : xs.mapM f with
      | error e => rw [hx, ht] at h; cases h
      | ok rest =>
        rw [hx, ht] at h
        change Except.ok (y :: rest) = Except.ok ys at h
        cases h
        obtain ⟨hlen, hlookup⟩ := ih rest ht
        refine ⟨by simp only [List.length_cons, hlen], ?_⟩
        intro k value hk
        cases k with
        | zero =>
          change some x = some value at hk
          cases hk
          exact ⟨y, hx, rfl⟩
        | succ k =>
          exact hlookup k value hk

/-- Reading a fully assigned list through its index range returns that list. -/
theorem g7SvecReadMappedSlots (values : List JVal) :
    (List.range values.length).mapM (fun k =>
      match (values.map some)[k]? with
      | some (some x) => (pure x : HM JVal)
      | _ => throw (Err.core .undefRef)) = pure values := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.mapM_cons,
      List.mapM_map, List.map_cons, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Function.comp_def]
    rw [ih]
    rfl

/-- Splat-reading an assigned memory object returns exactly its stored values. -/
theorem g7SvecReadAllAnyRun (a : Arr) (values : List JVal) (heap : Heap) (o : MemObj)
    (hheap : heap[a.ref.mem.handle]? = some o) (hoff : a.ref.index = 0)
    (hslots : o.slots = values.map some)
    (hprod : (prodDims a.size).val = (values.length : Int)) :
    (readAllAny a).run heap = some (.ok (values, heap)) := by
  rw [readAllAny, g7SvecHMBindRun, g7SvecMemObjRun a.ref.mem o heap hheap]
  simp only [hprod, Int.toNat_natCast, hoff, Nat.zero_add, hslots]
  exact (congrArg (fun action : HM (List JVal) => action.run heap)
    (g7SvecReadMappedSlots values)).trans (g7SvecHMPureRun values heap)

/-- The ordinary list iterator used by the array-index comprehension. -/
abbrev g7SvecListIndexIter (indices : List JVal) (st : Option Nat) : HM (Option (JVal × Nat)) :=
  pure ((indices[st.getD 0]?).map fun x => (x, st.getD 0 + 1))

/-- Applying SimpleVector indexing to the list iterator. -/
abbrev g7SvecSvecSelectedIter (v : SVecObj) (indices : List JVal) (st : Option Nat) :
    HM (Option (JVal × Nat)) := do
  match ← g7SvecListIndexIter indices st with
  | none => pure none
  | some (x, next) => pure (some (← liftHM (getindexSVecValue v x), next))

/-- Result promised by a particular requested index, with a sentinel beyond the input. -/
abbrev g7SvecSvecSelectedAt (v : SVecObj) (indices : List JVal) (k : Nat) : RE JVal :=
  match indices[k]? with
  | some index => getindexSVecValue v index
  | none => .error (.core .bounds)

/-- The selected generator visits each list position in order. -/
theorem g7SvecSvecSelectedIterStep (v : SVecObj) (indices : List JVal)
    (k : Nat) (st : Option Nat) (heap : Heap) (hst : st.getD 0 = k + 0) :
    (g7SvecSvecSelectedIter v indices st).run heap =
      if k < indices.length then
        match g7SvecSvecSelectedAt v indices k with
        | .error e => some (.error e)
        | .ok value => some (.ok (some (value, k + 1 + 0), heap))
      else some (.ok (none, heap)) := by
  simp only [Nat.add_zero] at hst ⊢
  unfold g7SvecSvecSelectedIter g7SvecListIndexIter
  simp only [hst, g7SvecHMBindRun, g7SvecHMPureRun]
  by_cases hk : k < indices.length
  · rw [if_pos hk]
    cases hindex : indices[k]? with
    | none =>
      have hbound := List.getElem?_eq_none_iff.mp hindex
      omega
    | some index =>
      simp only [g7SvecSvecSelectedAt, hindex, Option.map_some]
      cases hv : getindexSVecValue v index <;>
        simp only [hv, liftHM, g7SvecHMBindRun, g7SvecHMPureRun, g7SvecHMThrowRun]
  · have hindex : indices[k]? = none := List.getElem?_eq_none (by omega)
    simp only [hk, ↓reduceIte, hindex, Option.map_none, g7SvecHMPureRun]

/-- Every successful list map provides the generator value at each valid position. -/
theorem g7SvecSvecSelectedAtValues (v : SVecObj) (indices values : List JVal)
    (hmap : indices.mapM (getindexSVecValue v) = .ok values)
    (k : Nat) (hk : k < indices.length) :
    ∃ value, g7SvecSvecSelectedAt v indices k = .ok value ∧ values[k]? = some value := by
  have hindex : indices[k]? = some indices[k] := List.getElem?_eq_getElem hk
  obtain ⟨value, hv, hvalue⟩ := (g7SvecMapMValues (getindexSVecValue v) indices values hmap).2
    k indices[k] hindex
  exact ⟨value, by simpa only [g7SvecSvecSelectedAt, hindex] using hv, hvalue⟩

end JuliaLean.ChatGPT.Batch8.Group7


namespace JuliaLean.ChatGPT.Batch8.Group7
open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.Proofs.base.essentials

/-- The source-level wrappers preserve the non-UnionAll and missing-Vararg cases. -/
theorem BootcovEssUnwrapRewrap_proven : JuliaLean.Proofs.base.essentials.UnwrapRewrap := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u h
    cases u <;> first | rfl | cases h
  · intro t u h
    cases u <;> first | rfl | cases h
  · intro N u
    rfl
  · intro widen t root
    rfl

/-- The frozen model accepts a callback that discards a requested field. -/
theorem g7RestTupleMalformedNtupleResult :
    convertTuple (T := Unit) (X := Unit) (Y := Unit) (A := Unit)
      (fun _ _ => false) (fun _ _ => ()) (fun _ _ => ())
      (fun _ _ => true) (fun _ _ _ => rfl) (fun _ _ => .ok ())
      (fun _ _ => .ok []) () () 1 = .ok [] := rfl

/-- Direct execution law for the actual memory monad. -/
theorem g7RestHMBindRun {α β : Type} (action : HM α)
    (next : α → HM β) (heap : Heap) :
    (action >>= next).run heap =
      match action.run heap with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (value, heap')) => (next value).run heap' := by
  simp only [StateT.run, Bind.bind, StateT.bind, ExceptT.bind,
    ExceptT.mk, Option.bind]
  cases action heap with
  | none => rfl
  | some result => cases result <;> rfl

theorem g7RestHMPureRun {α : Type} (value : α) (heap : Heap) :
    (pure value : HM α).run heap = some (.ok (value, heap)) := rfl

theorem g7RestHMLiftErrorRun {α : Type} (e : Err) (heap : Heap) :
    (liftHM (.error e : RE α)).run heap = some (.error e) := rfl

theorem EssentialsArrayAccess_cases : JuliaLean.Proofs.base.essentials.ArrayAccessCases := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a i r v heap hnew hget
    simp only [getindexArray, Bool.false_eq_true, ↓reduceIte, g7RestHMBindRun, hnew, hget]
  · intro memory i x r heap heap' hnew hset
    simp only [setindexMemoryAny, Bool.false_eq_true, ↓reduceIte, g7RestHMBindRun,
      g7RestHMPureRun, hnew, hset]
  · intro convert T ref x heap e h
    simp only [setindexMemoryRef, h, g7RestHMBindRun, g7RestHMLiftErrorRun]
  · intro ref x heap heap' hset
    simp only [setindexMemoryRefAny, g7RestHMBindRun, hset, g7RestHMPureRun]

end JuliaLean.ChatGPT.Batch8.Group7


namespace JuliaLean.ChatGPT.Batch8.Group7
open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials


/-- Successful full constructors retain both converted fields and all declared types. -/
theorem g7RestPairsFullSuccess {K V I A D J : Type}
    (isData : D → Bool) (asData : D → A) (convertData : D → Except Exc A)
    (isIter : J → Bool) (asIter : J → I) (convertIter : J → Except Exc I)
    (data : D) (iter : J) (data' : A) (iter' : I)
    (hd : (if isData data then .ok (asData data) else convertData data) = .ok data')
    (hi : (if isIter iter then .ok (asIter iter) else convertIter iter) = .ok iter') :
    pairsCtorFull (K := K) (V := V) isData asData convertData isIter asIter convertIter data iter =
      .ok (⟨data', iter'⟩ : PairsModel K V I A) := by
  cases hdBool : isData data <;> cases hiBool : isIter iter <;>
    simp only [hdBool, hiBool, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hd hi <;>
    simp only [pairsCtorFull, hdBool, hiBool, Bool.false_eq_true, ↓reduceIte,
      hd, hi, bind, Except.bind, pure, Except.pure]

/-- After data conversion succeeds, an iterator conversion error is propagated. -/
theorem g7RestPairsFullIteratorError {K V I A D J : Type}
    (isData : D → Bool) (asData : D → A) (convertData : D → Except Exc A)
    (isIter : J → Bool) (asIter : J → I) (convertIter : J → Except Exc I)
    (data : D) (iter : J) (data' : A) (e : Exc)
    (hd : (if isData data then .ok (asData data) else convertData data) = .ok data')
    (hi : isIter iter = false) (he : convertIter iter = .error e) :
    pairsCtorFull (K := K) (V := V) isData asData convertData isIter asIter convertIter data iter =
      .error e := by
  cases hdBool : isData data <;>
    simp only [hdBool, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hd <;>
    simp only [pairsCtorFull, hdBool, hd, hi, Bool.false_eq_true, ↓reduceIte, he,
      bind, Except.bind, pure, Except.pure]

/-- Colon printing requests parentheses only after its type name prints successfully. -/
theorem g7RestShowColonSuccess {IO : Type} (name : JVal)
    (showTypeName : IO → JVal → Except Exc Unit)
    (print : IO → String → Except Exc Unit) (io : IO)
    (h : showTypeName io name = .ok ()) :
    showColon name showTypeName print io = print io "()" := by
  simp only [showColon, h, bind, Except.bind]

/-- A type-name printing error prevents the subsequent parentheses operation. -/
theorem g7RestShowColonError {IO : Type} (name : JVal)
    (showTypeName : IO → JVal → Except Exc Unit)
    (print : IO → String → Except Exc Unit) (io : IO) (e : Exc)
    (h : showTypeName io name = .error e) :
    showColon name showTypeName print io = .error e := by
  simp only [showColon, h, bind, Except.bind]

/-- The explicit Val type constructor creates its single no-data constructor. -/
theorem g7RestValDefault {A : Type} (x : A) : valValueDefault x = ValValue.mk := rfl

end JuliaLean.ChatGPT.Batch8.Group7


namespace JuliaLean.Proofs.base.essentials

namespace Models2Group19

open JuliaLean.BootCov
open JuliaLean.base.essentials.Models2Group19

/-- An observation carrier for selected Julia calls. World contains all mutable
storage and dispatch state. Exceptions retain their resulting world, and none
denotes a selected call which does not return. A divergent run exposes no final
world or completed-call log in this observation model. -/
abbrev DispatchM (World : Type) := ExceptT Exc (StateT World Option)

/-- Protected observations of a call's incoming world, resulting world, and
typed event. The selected callee receives World only, so it cannot fabricate,
erase, or reorder this log. This is property instrumentation, not Julia code. -/
structure DispatchStep (World Event : Type) where
  before : World
  after : World
  event : Event

/-- Observe the actual selected operation without changing its result, error,
or state effects. A call that diverges has no completed observation. -/
def recordDispatch {World Event Value : Type}
    (event : Except Exc Value → Event) (operation : DispatchM World Value) :
    DispatchM (World × List (DispatchStep World Event)) Value :=
  fun state =>
    match operation.run state.1 with
    | none => none
    | some observed =>
        some (observed.1,
          (observed.2, state.2 ++ [⟨state.1, observed.2, event observed.1⟩]))

/-- No state transition is invented between selected calls, and the last
call's state is not discarded or rolled back, including when it throws.
This relation inspects a log; it performs no source or selected computation. -/
def DispatchStateContinuity {World Event : Type} (initial final : World) :
    List (DispatchStep World Event) → Prop
  | [] => final = initial
  | step :: rest =>
      step.before = initial ∧ DispatchStateContinuity step.after final rest

inductive LengthCall (A D R : Type) where
  | size (argument : A) (outcome : Except Exc D)
  | product (dimensions : D) (outcome : Except Exc R)

/-- The size call receives the original array. Its failure is terminal;
otherwise the actual, independently typed size payload reaches the one
product call and that call supplies the final outcome. This is a finite
outcome/provenance relation, not an expected bind program or a product law. -/
def LengthTraceOutcome {A D R : Type} (argument : A)
    (outcome : Except Exc R) (calls : List (LengthCall A D R)) : Prop :=
  (∃ error, calls = [.size argument (.error error)] ∧ outcome = .error error) ∨
  (∃ dimensions,
    calls = [.size argument (.ok dimensions), .product dimensions outcome])

/-- Observe the new method at its two open dispatch boundaries. Selected
implementations may return any represented value, fail, mutate, or diverge. -/
def observeLength {World A D R : Type}
    (ops : LengthOps (DispatchM World) A D R) (argument : A) :
    DispatchM (World × List (DispatchStep World (LengthCall A D R))) R :=
  let size' : A →
      DispatchM (World × List (DispatchStep World (LengthCall A D R))) D :=
    fun a => recordDispatch (fun outcome => LengthCall.size a outcome) (ops.size a)
  let product' : D →
      DispatchM (World × List (DispatchStep World (LengthCall A D R))) R :=
    fun dimensions =>
      recordDispatch (fun outcome => LengthCall.product dimensions outcome)
        (ops.prod dimensions)
  JuliaLean.base.essentials.Models2Group19.lengthAbstract
    { size := size', prod := product' } argument

/-- Divergence must originate in a reachable selected call: either the
initial size observation, or a product observation after a successful size.
No arbitrary handler is assumed to terminate or to satisfy a size/product law. -/
def LengthSelectedDiverges {World A D R : Type}
    (ops : LengthOps (DispatchM World) A D R) (argument : A) (world : World) : Prop :=
  (ops.size argument).run world = none ∨
  (∃ dimensions afterSize,
    (ops.size argument).run world = some (.ok dimensions, afterSize) ∧
    (ops.prod dimensions).run afterSize = none)

/-- The AbstractArray length fallback preserves the original argument and
the provenance of the size payload, product result, exception, and state.
It performs exactly one size call and, only after success, one product call.
Completed calls form the specified legal prefix, without extra calls or
replaced payloads. The first selected failure is terminal. A divergent
selected call yields no completed outcome, and there is no additional source
of divergence in this wrapper.

Every array, size-result, and product-result carrier is quantified, as are
all selected implementations and all worlds. This includes arbitrary custom
and offset arrays, non-native results, mutation before an exception, and
divergence. There is no assumed size/prod correctness law or successful-run
premise. Mutable identities may be represented by handles in A, D, and R.

Julia source: base/essentials.jl:13-13
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/abstractarray.jl:305-318;
doc/src/manual/interfaces.md:215-225;
doc/src/manual/arrays.md:1205-1213.
Independent invariant: selected-call, value, exception, and state provenance.
-/
def LengthDispatchAccounting : Prop :=
  ∀ (World A D R : Type) (ops : LengthOps (DispatchM World) A D R)
    (argument : A) (world : World),
    let observed := (observeLength ops argument).run (world, [])
    (observed = none ↔ LengthSelectedDiverges ops argument world) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      LengthTraceOutcome argument outcome (calls.map (fun step => step.event)))

inductive BoundsCall (A I Other : Type) where
  | check (argument : A) (indices : List I)
      (outcome : Except Exc (Condition Other))

/-- A single selected bounds observation retains the array and complete
index tuple. Only a Boolean true permits normal return; Boolean false raises
BoundsError and a non-Boolean raises TypeError. A selected exception is
preserved exactly. The generated TypeError's diagnostic text is not part of
this exception-class contract. No claim about the selected check's geometric
correctness, offset conventions, or custom index behavior is assumed. -/
def BoundsTraceOutcome {A I Other : Type} (argument : A) (indices : List I)
    (outcome : Except Exc Unit) (calls : List (BoundsCall A I Other)) : Prop :=
  (∃ error,
    calls = [.check argument indices (.error error)] ∧ outcome = .error error) ∨
  (calls = [.check argument indices (.ok (.bool true))] ∧ outcome = .ok ()) ∨
  (calls = [.check argument indices (.ok (.bool false))] ∧ outcome = .error .bounds) ∨
  (∃ other context,
    calls = [.check argument indices (.ok (.other other))] ∧
    outcome = .error (.typeError context))

/-- Observe only the open checkbounds(Bool, A, I...) dispatch. The wrapper's
Base throwing helpers remain the actual installed model calls. -/
def observeCheckbounds {World A I Other : Type}
    (ops : BoundsOps (DispatchM World) A I Other) (argument : A) (indices : List I) :
    DispatchM (World × List (DispatchStep World (BoundsCall A I Other))) Unit :=
  let check' : A → List I →
      DispatchM (World × List (DispatchStep World (BoundsCall A I Other)))
        (Condition Other) :=
    fun a requestedIndices =>
      recordDispatch (fun outcome => BoundsCall.check a requestedIndices outcome)
        (ops.check a requestedIndices)
  JuliaLean.base.essentials.Models2Group19.checkbounds { check := check' } argument indices

/-- The throwing checkbounds wrapper observes its selected Boolean-form
method once, with exactly the original array and indices, and preserves all
its state changes even when the wrapper subsequently throws. Only true
permits Unit success; false raises BoundsError, a non-Bool raises TypeError,
and a selected error is preserved. Selected divergence is preserved and is
the only possible divergence in this finite wrapper.

All worlds, array identities, custom index values, non-Boolean results, and
selected implementations are quantified without correctness laws. I may be
a tagged carrier for heterogeneous Julia indices. The sole premise is the
native-representable arity of the source vararg tuple; it includes empty
tuples and does not restrict indexing conventions or index values.

Julia source: base/essentials.jl:389-393
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/abstractarray.jl:656-663,696-700;
doc/src/manual/control-flow.md:378-386.
Independent invariant: check/exception accounting and state conservation.
-/
def CheckboundsDispatchAccounting : Prop :=
  ∀ (World A I Other : Type) (ops : BoundsOps (DispatchM World) A I Other)
    (argument : A) (indices : List I) (world : World),
    indices.length < (2 : Nat) ^ 63 →
    let observed := (observeCheckbounds ops argument indices).run (world, [])
    (observed = none ↔ (ops.check argument indices).run world = none) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      BoundsTraceOutcome argument indices outcome (calls.map (fun step => step.event)))

end Models2Group19

end JuliaLean.Proofs.base.essentials

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean.BootCov
open JuliaLean.base.essentials.Models2Group19

inductive OftypeCall (Target Other : Type) where
  | convert (argument : JuliaLean.base.essentials.Models2Group19.Membership Target Other)
      (outcome : Except Exc (JuliaLean.base.essentials.Models2Group19.Membership Target Other))

/-- An already compatible value has no conversion observation and retains
its identity. Otherwise precisely one observation receives the original
dynamic value. A successful target-member result is returned unchanged; a
wrong-type result is rejected by TypeError, and a selected exception is
preserved exactly. This is an observation/value-provenance relation; it
executes no conversion and assumes no law about a selected implementation.
The type-assertion error's diagnostic text is outside this class contract. -/
def OftypeTraceOutcome {Target Other : Type} (argument : JuliaLean.base.essentials.Models2Group19.Membership Target Other)
    (outcome : Except Exc Target) (calls : List (OftypeCall Target Other)) : Prop :=
  (∃ value, argument = .member value ∧ calls = [] ∧ outcome = .ok value) ∨
  (∃ original, argument = .other original ∧
    ((∃ error,
      calls = [.convert argument (.error error)] ∧ outcome = .error error) ∨
     (∃ converted,
      calls = [.convert argument (.ok (.member converted))] ∧ outcome = .ok converted) ∨
     (∃ wrong context,
      calls = [.convert argument (.ok (.other wrong))] ∧
      outcome = .error (.typeError context))))

/-- The selected converter receives only its original world. It cannot
alter the protected observation log. The real model retains its builtin
membership test and postconversion assertion; this wrapper instruments only
the permitted generic conversion boundary. -/
def observeOftype {World Target Other : Type}
    (ops : ConversionOps (DispatchM World) Target Other)
    (x : Target) (y : JuliaLean.base.essentials.Models2Group19.Membership Target Other) :
    DispatchM (World × List (DispatchStep World (OftypeCall Target Other))) Target :=
  let convert' : JuliaLean.base.essentials.Models2Group19.Membership Target Other →
      DispatchM (World × List (DispatchStep World (OftypeCall Target Other)))
        (JuliaLean.base.essentials.Models2Group19.Membership Target Other) :=
    fun argument =>
      recordDispatch (fun outcome => OftypeCall.convert argument outcome)
        (ops.convert argument)
  JuliaLean.base.essentials.Models2Group19.oftype { convert := convert' } x y

/-- oftype preserves an already compatible y, including its object identity,
without invoking conversion or changing the world. Every incompatible y
causes exactly one selected conversion at the target fixed by typeof(x).
The original dynamic argument reaches that call. A successful value of the
target type is returned unchanged; an outside result causes TypeError only
after all conversion effects. The selected error and its effects are never
replaced or rolled back. Selected divergence is retained and is the only
possible divergence of the wrapper.

All runtime-type carriers, original and converted membership values, worlds,
and converters are quantified. Target is the model's carrier of actual
typeof(x), and may contain mutable-object handles or type objects. Membership
tags encode the builtin isa fact; they are not a supplied isa predicate or
same-type law. No conversion-correctness or successful-run premise is used.

Julia source: base/essentials.jl:718-718
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/essentials.jl:700-718;
doc/src/manual/conversion-and-promotion.md:51-53;
doc/src/manual/types.md:60-83.
Independent invariant: identity, selected-conversion, exception, and state
provenance, including the conditional type assertion.
-/
def OftypeDispatchAccounting : Prop :=
  ∀ (World Target Other : Type)
    (ops : ConversionOps (DispatchM World) Target Other)
    (x : Target) (y : JuliaLean.base.essentials.Models2Group19.Membership Target Other) (world : World),
    let observed := (observeOftype ops x y).run (world, [])
    (observed = none ↔
      ∃ original, y = .other original ∧ (ops.convert y).run world = none) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      OftypeTraceOutcome y outcome (calls.map (fun step => step.event)))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean.BootCov
open JuliaLean.base.essentials.Models2Group19

/-- A compatible argument is preserved by identity with no conversion
observation. Otherwise the single selected conversion receives that original
argument and supplies the whole final outcome, including an outside value
or an exception. There is no postconversion membership requirement. This
relation inspects provenance in the same conversion-event carrier as oftype;
it neither executes a converter nor supplies a conversion-correctness law. -/
def CconvertTraceOutcome {Target Other : Type} (argument : JuliaLean.base.essentials.Models2Group19.Membership Target Other)
    (outcome : Except Exc (JuliaLean.base.essentials.Models2Group19.Membership Target Other))
    (calls : List (OftypeCall Target Other)) : Prop :=
  (∃ value, argument = .member value ∧ calls = [] ∧ outcome = .ok argument) ∨
  (∃ original, argument = .other original ∧ calls = [.convert argument outcome])

/-- Protect the observation log while retaining the selected conversion's
arbitrary result and complete state/error/divergence behavior. The actual
model still decides whether to issue this call using its membership tag. -/
def observeCconvert {World Target Other : Type}
    (ops : ConversionOps (DispatchM World) Target Other)
    (argument : JuliaLean.base.essentials.Models2Group19.Membership Target Other) :
    DispatchM (World × List (DispatchStep World (OftypeCall Target Other)))
      (JuliaLean.base.essentials.Models2Group19.Membership Target Other) :=
  let convert' : JuliaLean.base.essentials.Models2Group19.Membership Target Other →
      DispatchM (World × List (DispatchStep World (OftypeCall Target Other)))
        (JuliaLean.base.essentials.Models2Group19.Membership Target Other) :=
    fun value =>
      recordDispatch (fun outcome => OftypeCall.convert value outcome)
        (ops.convert value)
  JuliaLean.base.essentials.Models2Group19.cconvert { convert := convert' } argument

/-- The cconvert fallback preserves an existing member of its actual target
T without calling convert or changing the world. For an outside argument it
issues exactly one conversion of the original value and preserves that
call's whole result, including values outside T, exceptions, state effects,
and divergence. It neither inserts a type assertion nor performs an extra
conversion. This includes mutation followed by an error and results holding
the identity of storage that a later unsafe_convert operation may use.

All carriers, membership inputs and outputs, worlds, and converters are
quantified. Target denotes every value inhabiting T, so an abstract, union,
or UnionAll target can contain different concrete subtypes. It is not the
single concrete typeof(x) carrier used to interpret oftype. Other denotes
the complement. The membership tag is a runtime representation invariant,
not a supplied isa test, and no selected-converter correctness law is assumed.

Julia source: base/essentials.jl:739-739
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/essentials.jl:724-735;
doc/src/manual/calling-c-and-fortran-code.md:248-273.
Independent invariant: argument identity and unrestricted selected-result,
exception, divergence, and state provenance for this fallback method.
-/
def CconvertDispatchAccounting : Prop :=
  ∀ (World Target Other : Type)
    (ops : ConversionOps (DispatchM World) Target Other)
    (argument : JuliaLean.base.essentials.Models2Group19.Membership Target Other) (world : World),
    let observed := (observeCconvert ops argument).run (world, [])
    (observed = none ↔
      ∃ original, argument = .other original ∧ (ops.convert argument).run world = none) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      CconvertTraceOutcome argument outcome (calls.map (fun step => step.event)))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean.BootCov

/-- Property-side organization of the open convert dispatch at a target
P<:Ptr. Target carries the admissible type tokens, including abstract, union,
UnionAll, and bottom targets; Pointer carries the source pointer values.
Result remains independent because this source method adds no result-type
assertion. This record does not replace or redefine the installed model. -/
structure PointerConversionOps (m : Type → Type) (Target Pointer Result : Type) where
  convert : Target → Pointer → m Result

inductive PointerConversionCall (Target Pointer Result : Type) where
  | convert (target : Target) (pointer : Pointer) (outcome : Except Exc Result)

/-- Instantiate the unchanged canonical wrapper with an effectful result
type, and protect the single selected-call observation from callee mutation.
The selected handler receives both original arguments and its original world.
This is a property harness, not another unsafe_convert implementation. -/
def observePointerConversion {World Target Pointer Result : Type}
    (ops : PointerConversionOps (DispatchM World) Target Pointer Result)
    (target : Target) (pointer : Pointer) :
    DispatchM
      (World × List (DispatchStep World (PointerConversionCall Target Pointer Result)))
      Result :=
  let convert' : Target → Pointer →
      DispatchM
        (World × List (DispatchStep World (PointerConversionCall Target Pointer Result)))
        Result :=
    fun requested input =>
      recordDispatch
        (fun outcome => PointerConversionCall.convert requested input outcome)
        (ops.convert requested input)
  JuliaLean.base.essentials.unsafeConvertPointer convert' target pointer

/-- The pointer-target unsafe_convert wrapper forwards its exact target
token and pointer to one selected conversion. Its entire result, exception,
state effects, and divergence retain their provenance in that call. There
is no unconditional success, pointer-address, or result-type assertion for
arbitrary selected conversion methods. Every admissible target carrier and
every selected implementation is quantified without a correctness law.

The second conjunct binds the concrete Union{} target to the installed
convertUnionBottom model. It independently requires ArgumentError for every
pointer value and every result carrier; the Unit target token denotes this
one concrete target. Thus bottom targets are included explicitly, rather
than assuming that every P<:Ptr is a concrete Ptr{T} cast. Diagnostic text is
not part of the required error-class property.

Julia source: base/essentials.jl:744-744,474-474
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/calling-c-and-fortran-code.md:248-275;
base/essentials.jl:474 (bottom conversion's explicit ArgumentError).
Independent invariant: selected-call/result/exception/state provenance,
together with rejection of conversion to the uninhabited target type.
-/
def PointerConvertDispatchAccounting : Prop :=
  (∀ (World Target Pointer Result : Type)
    (ops : PointerConversionOps (DispatchM World) Target Pointer Result)
    (target : Target) (pointer : Pointer) (world : World),
    let observed := (observePointerConversion ops target pointer).run (world, [])
    (observed = none ↔ (ops.convert target pointer).run world = none) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      calls.map (fun step => step.event) = [.convert target pointer outcome])) ∧
  (∀ (Pointer Result : Type) (pointer : Pointer),
    ∃ message,
      JuliaLean.base.essentials.unsafeConvertPointer
        (fun (_ : Unit) (input : Pointer) =>
          JuliaLean.base.essentials.convertUnionBottom (R := Result) [input])
        () pointer = .error (.argument message))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean
open JuliaLean.base.essentials.Models2Group19

/-- A live raw-byte heap snapshot. The byte value is unsigned storage bits,
independently of whether a returned pointer has element type Int8 or UInt8.
This is a property observation, not an implementation of unsafe_load. -/
abbrev StringByteHeap := JInt .u64 → Option (JInt .u8)

/-- Representation invariant connecting a StringStorage snapshot to its
existing allocation: its original bytes occupy consecutive byte addresses
after the native size word. The reference addresses are mathematical storage
coordinates, independent of either conversion result. No UTF-8 validity or
absence-of-NUL premise is imposed. Native length and nonwrapping extent are
already invariants of StringStorage, and remain true for an empty string. -/
def StringStorageBacked (heap : StringByteHeap) (storage : StringStorage) : Prop :=
  ∀ (offset : Nat) (byte : JInt .u8),
    storage.bytes[offset]? = some byte →
    heap (JInt.wrap .u64 (storage.objectAddress.val + 8 + (offset : Int))) = some byte

/-- Observe storage bits at a byte offset from a returned pointer, using
native pointer-address arithmetic. Reading the Int8 pointer through this
observer compares raw byte bits, not signed and unsigned numeric values.
The public property below asks only about existing offsets of a live string. -/
def readStringPointerByte {element : IntTy} (heap : StringByteHeap)
    (pointer : BytePointer element) (offset : Nat) : Option (JInt .u8) :=
  heap (pointer.raw.addr + JInt.wrap .u64 (offset : Int))

/-- Both String pointer conversions alias the original live byte storage:
at every existing byte position, either returned address reads the original
byte from every heap satisfying the actual storage invariant. Invalid UTF-8,
embedded zero bytes, and every native-sized length are included. No new
storage or content-based synthetic address is accepted by this invariant.

Both pointer addresses lie immediately after the object's native size word,
also when there are no bytes to read. The Int8 and UInt8 views have identical
address bits. Distinct existing object addresses remain distinct after either
conversion, regardless of whether their byte contents are equal. Thus equal
content alone cannot merge two distinct live storage identities.

The byte-heap premise is only a representation invariant relating the input
snapshot to existing storage. It contains no conversion output or assumption
about either conversion's correctness. All bytes, heaps, offsets, and live
StringStorage values are quantified. The registered public property depends
on stringDataPointer through both unsafeConvertString methods.

Julia source: base/essentials.jl:745-746
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/strings.md:405-411;
doc/src/manual/calling-c-and-fortran-code.md:273-275.
Installed runtime layout: JuliaLean/src/builtins_identity_c.lean:547-551,857-860.
Independent invariant: aliasing the original live raw-byte allocation and
preserving its distinct address identity, without content restrictions.
-/
def StringPointerAliasing : Prop :=
  (∀ storage : StringStorage,
    let unsigned :=
      JuliaLean.base.essentials.Models2Group19.unsafeConvertStringUInt8 storage
    let signed :=
      JuliaLean.base.essentials.Models2Group19.unsafeConvertStringInt8 storage
    unsigned.raw.addr.val = storage.objectAddress.val + 8 ∧
    signed.raw.addr.val = storage.objectAddress.val + 8 ∧
    unsigned.raw.addr = signed.raw.addr ∧
    (∀ heap : StringByteHeap, StringStorageBacked heap storage →
      ∀ (offset : Nat) (byte : JInt .u8),
        storage.bytes[offset]? = some byte →
        readStringPointerByte heap unsigned offset = some byte ∧
        readStringPointerByte heap signed offset = some byte)) ∧
  (∀ left right : StringStorage,
    left.objectAddress ≠ right.objectAddress →
      (JuliaLean.base.essentials.Models2Group19.unsafeConvertStringUInt8 left).raw.addr ≠
        (JuliaLean.base.essentials.Models2Group19.unsafeConvertStringUInt8 right).raw.addr ∧
      (JuliaLean.base.essentials.Models2Group19.unsafeConvertStringInt8 left).raw.addr ≠
        (JuliaLean.base.essentials.Models2Group19.unsafeConvertStringInt8 right).raw.addr)

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean JuliaLean.BootCov
open JuliaLean.base.essentials.Models2Group19.Reinterpret

/-- Mathematical membership of a bit in the unsigned UInt16 metadata word.
This specification uses integer quotients, independently of and_int/eq_int. -/
def ReinterpretFlagBit (flags : JInt .u16) (bit : Nat) : Prop :=
  (flags.val / (2 : Int) ^ bit) % 2 = 1

/-- A mathematical description of a finite UnionAll wrapper path. This list
is a specification path, not a Julia array or a model of runtime allocation. -/
def ReinterpretWraps {Atom : Type} (wrappers : List Atom) (terminal : TypeView Atom) :
    TypeView Atom :=
  wrappers.foldr (fun original body => TypeView.unionAll original body) terminal

/-- A type is primitive exactly when its finite wrapper path ends in a
DataType whose seventh flag bit is set. This relation does not call the
model's unwrapping or primitive-predicate helpers. -/
def ReinterpretPrimitiveTarget {Atom : Type} (out : TypeView Atom) : Prop :=
  ∃ (wrappers : List Atom) (data : DataTypeKey),
    out = ReinterpretWraps wrappers (.datatype data) ∧ ReinterpretFlagBit data.flags 7

/-- Inspect the supplied value record for specification purposes, without
using the model's typeofValue helper or inferring identity from its layout. -/
def ReinterpretValueType {Atom : Type} : Value Atom → DataTypeKey
  | .primitive data _ _ _ => data
  | .other data _ _ _ => data

/-- The arbitrary-width logical bit payload of a primitive value. Nonprimitive
values have no primitive payload. Padding and boxing addresses are outside the
installed jlBitcast abstraction and are not interpreted as value bits. -/
def ReinterpretValueBits {Atom : Type} : Value Atom → Option Nat
  | .primitive _ _ _ bits => some bits.toNat
  | .other _ _ _ _ => none

/-- Independent invariants of the concrete helpers: masks select their set
bits; primitive/concrete are bits 7/1; a valid primitive's layout is its stored
layout; wrapper stripping preserves the terminal object; and typeof retains
the original nominal type key. Each relation covers all represented inputs
of its helper, with only the helper's own representation invariants.
Julia source: base/essentials.jl:544-550,789;
base/runtime_internals.jl:885-891,1161. -/
def ReinterpretMetadataCorrect : Prop :=
  (∀ (flags mask : JInt .u16),
    flagSet flags mask = true ↔
      ∀ bit : Nat, bit < 16 → ReinterpretFlagBit mask bit → ReinterpretFlagBit flags bit) ∧
  (∀ data : DataTypeKey,
    (datatypePrimitive data = true ↔ ReinterpretFlagBit data.flags 7) ∧
    (datatypeConcrete data = true ↔ ReinterpretFlagBit data.flags 1)) ∧
  (∀ (data : DataTypeKey) (primitive : datatypePrimitive data = true)
    (concrete : datatypeConcrete data = true),
    data.layout = some (primitiveLayout data primitive concrete)) ∧
  (∀ (Atom : Type) (wrappers : List Atom) (data : DataTypeKey),
    unwrapUnionAll (ReinterpretWraps wrappers (.datatype data)) = .datatype data) ∧
  (∀ (Atom : Type) (wrappers : List Atom) (original : Atom),
    unwrapUnionAll (ReinterpretWraps wrappers (.other original)) = .other original) ∧
  (∀ (Atom : Type) (out : TypeView Atom),
    isPrimitiveType out = true ↔ ReinterpretPrimitiveTarget out) ∧
  (∀ (Atom : Type) (value : Value Atom), typeofValue value = ReinterpretValueType value)

/-- The first failing bitcast requirement determines the exception. Raw
non-DataType targets fail before any leaf/source/width requirement; invalid
target flags fail before inspecting the source; a nonprimitive source fails
before widths are compared. The final alternative requires both preceding
gates and compares stored logical widths, not padded storage sizes.
The messages distinguish the three ErrorException throw points.
Julia source: src/runtime_intrinsics.c:439-453. -/
def ReinterpretBitcastFailure {Atom : Type} (out : TypeView Atom) (x : Value Atom)
    (error : Exc) : Prop :=
  ((∀ data : DataTypeKey, out ≠ .datatype data) ∧ error = .typeError "bitcast") ∨
  (∃ target : DataTypeKey,
    out = .datatype target ∧
    ¬ (ReinterpretFlagBit target.flags 1 ∧ ReinterpretFlagBit target.flags 7) ∧
    error = .error "bitcast: target type not a leaf primitive type") ∨
  (∃ target : DataTypeKey,
    out = .datatype target ∧
    ReinterpretFlagBit target.flags 1 ∧ ReinterpretFlagBit target.flags 7 ∧
    ReinterpretValueBits x = none ∧
    error = .error "bitcast: value not a primitive type") ∨
  (∃ (target : DataTypeKey) (targetLayout sourceLayout : PrimitiveLayout) (payload : Nat),
    out = .datatype target ∧
    ReinterpretFlagBit target.flags 1 ∧ ReinterpretFlagBit target.flags 7 ∧
    target.layout = some targetLayout ∧
    ReinterpretValueBits x = some payload ∧
    (ReinterpretValueType x).layout = some sourceLayout ∧
    sourceLayout.logicalBits ≠ targetLayout.logicalBits ∧
    error = .error "bitcast: argument bitsize does not match bitsize of target type")

/-- A successful primitive cast has the requested nominal type and equal
logical widths. Same-type casts preserve the complete original value before
any Bool normalization, including noncanonical Bool payloads. Distinct-type
casts to the actual Bool singleton retain exactly the source low bit; all
other distinct-type primitive casts preserve the entire logical payload.
Nothing here identifies types merely because their widths or flags agree.
The expected payload is a mathematical natural number, without using the
installed jlBitcast, bitcastBool, or BitVec.cast operations.
Julia source: src/runtime_intrinsics.c:439-453. -/
def ReinterpretBitcastSuccess {Atom : Type} (runtime : Runtime)
    (out : TypeView Atom) (x result : Value Atom) : Prop :=
  ∃ (target : DataTypeKey) (targetLayout sourceLayout : PrimitiveLayout) (payload : Nat),
    out = .datatype target ∧
    ReinterpretFlagBit target.flags 1 ∧ ReinterpretFlagBit target.flags 7 ∧
    target.layout = some targetLayout ∧
    ReinterpretValueBits x = some payload ∧
    (ReinterpretValueType x).layout = some sourceLayout ∧
    sourceLayout.logicalBits = targetLayout.logicalBits ∧
    ReinterpretValueType result = target ∧
    ((target = ReinterpretValueType x ∧ result = x) ∨
     (target ≠ ReinterpretValueType x ∧
       ((target = runtime.boolType ∧ ReinterpretValueBits result = some (payload % 2)) ∨
        (target ≠ runtime.boolType ∧ ReinterpretValueBits result = some payload))))

/-- Classification of every concrete bitcast observation by independent
eligibility, error precedence, nominal identity, and mathematical value bits.
This relation executes no source algorithm or selected callee. -/
def ReinterpretBitcastOutcome {Atom : Type} (runtime : Runtime)
    (out : TypeView Atom) (x : Value Atom) (outcome : Except Exc (Value Atom)) : Prop :=
  (∃ result, outcome = .ok result ∧ ReinterpretBitcastSuccess runtime out x result) ∨
  (∃ error, outcome = .error error ∧ ReinterpretBitcastFailure out x error)

/-- The source's primitive path is eligible from the target's terminal
primitive flag and the original source type's primitive flag. This does not
assume that the raw target is itself a DataType, that it is concrete, or that
the logical widths agree: those are later bitcast checks with visible errors. -/
def ReinterpretFastEligible {Atom : Type} (out : TypeView Atom) (x : Value Atom) : Prop :=
  ReinterpretPrimitiveTarget out ∧ ReinterpretFlagBit (ReinterpretValueType x).flags 7

inductive ReinterpretCall (Atom : Type) where
  | fallback (out : TypeView Atom) (value : Value Atom)
      (outcome : Except Exc (Value Atom))

/-- Protect the fallback-call log while preserving every selected result,
exception, mutation, and divergence. The original target retains UnionAll
wrappers and original object identities. Concrete primitive work remains in
the actual model and does not pass through the observer. -/
def observeReinterpret {World Atom : Type} (runtime : Runtime)
    (ops : Ops (DispatchM World) Atom) (out : TypeView Atom) (x : Value Atom) :
    DispatchM (World × List (DispatchStep World (ReinterpretCall Atom))) (Value Atom) :=
  let fallback' : TypeView Atom → Value Atom →
      DispatchM (World × List (DispatchStep World (ReinterpretCall Atom))) (Value Atom) :=
    fun requested value =>
      recordDispatch (fun outcome => ReinterpretCall.fallback requested value outcome)
        (ops.fallback requested value)
  JuliaLean.base.essentials.Models2Group19.Reinterpret.reinterpret
    runtime { fallback := fallback' } out x

/-- reinterpret conserves logical bits on its concrete primitive path,
subject to the independently stated raw-target, concrete/primitive, source,
and logical-width requirements. Nominal same-type identity precedes Bool's
low-bit canonicalization, which applies only to a distinct source type.
Unwrapped primitive UnionAll families enter that path when the source type
is primitive, then fail bitcast's raw DataType requirement. All other paths call the selected _reinterpret
exactly once with the original arguments, preserving its entire outcome,
state effects, and divergence without a callee-correctness law.

Every raw target view, primitive/nonprimitive value, runtime Bool singleton,
world, and arbitrary fallback is quantified. Logical widths range over all
constructible primitive layouts, including non-byte and non-native widths;
payloads range over every bit pattern. The metadata conjunct independently
checks the actual bit positions, wrapper traversal, stored layouts, and type
projection. The bitcast conjunct covers even internal error branches not
normally reached after reinterpret's primitive tests, so every concrete
helper has a registered independent invariant.

The completed trace is empty on the concrete path and a single original-arg
fallback event otherwise. Empty traces preserve the world. The first error
is never replaced, and only a required selected fallback may diverge.
No physical padding-byte, boxing-address, or fallback-result-type guarantee
is introduced beyond the installed arbitrary-width jlBitcast value boundary.

Julia source: base/essentials.jl:544-550,787-794;
base/runtime_internals.jl:885-891,1161; src/runtime_intrinsics.c:439-453
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/essentials.jl:754-785;
doc/src/manual/types.md:299-316.
Independent invariants: metadata-bit membership, terminal/nominal identity,
error precedence, logical-bit conservation, and selected-call provenance.
-/
def ReinterpretDispatchBits : Prop :=
  ReinterpretMetadataCorrect ∧
  (∀ (Atom : Type) (runtime : Runtime) (out : TypeView Atom) (x : Value Atom),
    ReinterpretBitcastOutcome runtime out x
      (JuliaLean.base.essentials.Models2Group19.Reinterpret.bitcast runtime out x)) ∧
  (∀ (World Atom : Type) (runtime : Runtime) (ops : Ops (DispatchM World) Atom)
    (out : TypeView Atom) (x : Value Atom) (world : World),
    let observed := (observeReinterpret runtime ops out x).run (world, [])
    (observed = none ↔
      ¬ ReinterpretFastEligible out x ∧ (ops.fallback out x).run world = none) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      ((ReinterpretFastEligible out x ∧ calls = [] ∧ finalWorld = world ∧
        ReinterpretBitcastOutcome runtime out x outcome) ∨
       (¬ ReinterpretFastEligible out x ∧
        calls.map (fun step => step.event) = [.fallback out x outcome]))))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean
open JuliaLean.base.essentials (Err)
open JuliaLean.base.essentials.Models1Group18 (SizedSVec OneTo64)
open JuliaLean.base.essentials.Models2Group19 (Condition)
open JuliaLean.base.essentials.Models2Group19.SimpleVector (AxisResult AxesOps)

/-- Arbitrary selected SimpleVector-adjacent dispatch, with persistent state
on exceptions and none for divergence. The world may include mutable values,
custom integer state, aliases, and further runtime metadata. This carrier is
property instrumentation, not a replacement source operation. -/
abbrev SVecDispatchM (World : Type) := ExceptT Err (StateT World Option)

/-- Retain the selected operation's original result/error and post-call world.
Divergence exposes no completed log or final world in this observation model. -/
def recordSVecDispatch {World Event Value : Type}
    (event : Except Err Value → Event) (operation : SVecDispatchM World Value) :
    SVecDispatchM (World × List (DispatchStep World Event)) Value :=
  fun state =>
    match operation.run state.1 with
    | none => none
    | some observed =>
        some (observed.1,
          (observed.2, state.2 ++ [⟨state.1, observed.2, event observed.1⟩]))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean JuliaLean.BootCov
open JuliaLean.base.essentials (Err)
open JuliaLean.base.essentials.Models1Group18 (SizedSVec)
open JuliaLean.base.essentials.Models2Group19 (Condition)
open JuliaLean.base.essentials.Models2Group19.SimpleVector (IterationOps)

inductive SVecIterateCall (I V Next NonBool : Type) where
  | less (length : JInt .i64) (state : I) (outcome : Except Err (Condition NonBool))
  | getindex (vector : SizedSVec) (state : I) (outcome : Except Err V)
  | add (state : I) (one : JInt .i64) (outcome : Except Err Next)

/-- Completed call prefixes conserve the original vector and state. The
comparison receives the actual mathematical slot count as a native Int;
the increment receives native one. Only false permits indexing, and only
successful indexing permits addition. Return payloads retain their distinct
types and identities. This relation observes data and call provenance; it
does not execute length, comparison, indexing, or addition. -/
def SVecIterateTraceOutcome {I V Next NonBool : Type} (v : SizedSVec) (i : I)
    (outcome : Except Err (Option (V × Next)))
    (calls : List (SVecIterateCall I V Next NonBool)) : Prop :=
  ∃ length : JInt .i64, length.val = (v.obj.slots.length : Int) ∧
    ((∃ error,
      calls = [.less length i (.error error)] ∧ outcome = .error error) ∨
     (∃ other context,
      calls = [.less length i (.ok (.other other))] ∧
      outcome = .error (.core (.typeError context))) ∨
     (calls = [.less length i (.ok (.bool true))] ∧ outcome = .ok none) ∨
     (∃ error,
      calls = [.less length i (.ok (.bool false)), .getindex v i (.error error)] ∧
      outcome = .error error) ∨
     (∃ (value : V) (one : JInt .i64) (error : Err),
      one.val = 1 ∧
      calls = [.less length i (.ok (.bool false)), .getindex v i (.ok value),
        .add i one (.error error)] ∧ outcome = .error error) ∨
     (∃ (value : V) (one : JInt .i64) (next : Next),
      one.val = 1 ∧
      calls = [.less length i (.ok (.bool false)), .getindex v i (.ok value),
        .add i one (.ok next)] ∧ outcome = .ok (some (value, next))))

/-- Instrument only the three dispatch leaves of the actual generic-state
method. The world available to selected callees excludes the protected log. -/
def observeSVecIterate {World I V Next NonBool : Type}
    (ops : IterationOps (SVecDispatchM World) I V Next NonBool) (v : SizedSVec) (i : I) :
    SVecDispatchM (World × List (DispatchStep World (SVecIterateCall I V Next NonBool)))
      (Option (V × Next)) :=
  let less' : JInt .i64 → I →
      SVecDispatchM (World × List (DispatchStep World (SVecIterateCall I V Next NonBool)))
        (Condition NonBool) :=
    fun length state =>
      recordSVecDispatch (fun outcome => SVecIterateCall.less length state outcome)
        (ops.less length state)
  let getindex' : SizedSVec → I →
      SVecDispatchM (World × List (DispatchStep World (SVecIterateCall I V Next NonBool))) V :=
    fun vector state =>
      recordSVecDispatch (fun outcome => SVecIterateCall.getindex vector state outcome)
        (ops.getindex vector state)
  let add' : I → JInt .i64 →
      SVecDispatchM (World × List (DispatchStep World (SVecIterateCall I V Next NonBool))) Next :=
    fun state one =>
      recordSVecDispatch (fun outcome => SVecIterateCall.add state one outcome)
        (ops.add state one)
  JuliaLean.base.essentials.Models2Group19.SimpleVector.iterate
    { less := less', getindex := getindex', add := add' } v i

/-- A nonreturning selected call must be reachable after all earlier calls
completed successfully with the necessary false condition. The operands are
specified mathematically, without calling svecLength64 or a model addition. -/
def SVecIterateSelectedDiverges {World I V Next NonBool : Type}
    (ops : IterationOps (SVecDispatchM World) I V Next NonBool)
    (v : SizedSVec) (i : I) (world : World) : Prop :=
  ∃ length one : JInt .i64,
    length.val = (v.obj.slots.length : Int) ∧ one.val = 1 ∧
    ((ops.less length i).run world = none ∨
     (∃ afterCompare,
      (ops.less length i).run world = some (.ok (.bool false), afterCompare) ∧
      ((ops.getindex v i).run afterCompare = none ∨
       (∃ value afterRead,
        (ops.getindex v i).run afterCompare = some (.ok value, afterRead) ∧
        (ops.add i one).run afterRead = none))))

/-- Complete generic-state iteration accounting, with arbitrary comparison,
indexing, and addition implementations and no assumed arithmetic or access
law. The first error and every state change survive; a non-Bool comparison
raises TypeError; successful true stops without reading; successful false
reads before adding. Both result payloads retain their original identities.
Julia source: base/essentials.jl:1102;
doc/src/manual/interfaces.md:8-33; doc/src/manual/control-flow.md:378-386. -/
def SVecIterationDispatchAccounting : Prop :=
  ∀ (World I V Next NonBool : Type)
    (ops : IterationOps (SVecDispatchM World) I V Next NonBool)
    (v : SizedSVec) (i : I) (world : World),
    let observed := (observeSVecIterate ops v i).run (world, [])
    (observed = none ↔ SVecIterateSelectedDiverges ops v i world) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      SVecIterateTraceOutcome v i outcome (calls.map (fun step => step.event)))

/-- Independent native-state outcomes from the stored slots and mathematical
index. Indices past the final position stop; nonpositive indices raise
BoundsError. In-range null slots retain the installed undefined-behavior
marker. A successful slot read preserves its value and advances the signed
state modulo 2^64, including typemax wraparound. No model helper computes the
expected length, element, comparison, or successor in this relation. -/
def SVecNativeIterationOutcome (v : SizedSVec) (i : JInt .i64)
    (outcome : Except Err (Option (JVal × JInt .i64))) : Prop :=
  ((v.obj.slots.length : Int) < i.val ∧ outcome = .ok none) ∨
  (i.val < 1 ∧ outcome = .error (.core .bounds)) ∨
  (1 ≤ i.val ∧ i.val ≤ (v.obj.slots.length : Int) ∧
    ((v.obj.slots[(i.val - 1).toNat]? = some none ∧
      outcome = .error (.undefinedBehaviour "null SimpleVector slot")) ∨
     (∃ (value : JVal) (next : JInt .i64),
      v.obj.slots[(i.val - 1).toNat]? = some (some value) ∧
      outcome = .ok (some (value, next)) ∧
      ∃ multiple : Int, next.val = i.val + 1 + multiple * (2 : Int) ^ 64)))

/-- Default iteration is specified directly by the first stored position,
independently of the native/default wrapper bodies. Empty vectors stop;
an initialized first slot returns that exact value and native state two;
an internal null first slot retains the installed undefined-behavior marker. -/
def SVecDefaultIterationOutcome (v : SizedSVec)
    (outcome : Except Err (Option (JVal × JInt .i64))) : Prop :=
  (v.obj.slots = [] ∧ outcome = .ok none) ∨
  (∃ rest, v.obj.slots = none :: rest ∧
    outcome = .error (.undefinedBehaviour "null SimpleVector slot")) ∨
  (∃ (value : JVal) (rest : List (Option JVal)) (next : JInt .i64),
    v.obj.slots = some value :: rest ∧
    outcome = .ok (some (value, next)) ∧ next.val = 2)

/-- The closed native and generated-default cases terminate at the installed
pure primitive boundary, preserve the world even on an error, and satisfy
the independent slot/index relations. Every constructible SizedSVec and
every Int64 state is included; null slots and empty vectors are not excluded.
Julia source: base/essentials.jl:1096-1102,1267; base/int.jl:84. -/
def SVecNativeDefaultIterationCorrect : Prop :=
  (∀ (World : Type) (v : SizedSVec) (i : JInt .i64) (world : World),
    ∃ outcome,
      (JuliaLean.base.essentials.Models2Group19.SimpleVector.iterateNative
        (m := SVecDispatchM World) v i).run world = some (outcome, world) ∧
      SVecNativeIterationOutcome v i outcome) ∧
  (∀ (World : Type) (v : SizedSVec) (world : World),
    ∃ outcome,
      (JuliaLean.base.essentials.Models2Group19.SimpleVector.iterateDefault
        (m := SVecDispatchM World) v).run world = some (outcome, world) ∧
      SVecDefaultIterationOutcome v outcome)

/-- Full generic-state source translation plus its installed native/default
instantiations. The generic statement imposes no correctness law on selected
custom calls and does not restrict the state or return payloads to Int/JVal.
The separate native statements verify actual Base slot behavior and wrapping
arithmetic, including exhaustion, bounds errors, and internal null slots.
Registered dependencies are SimpleVector.liftResult, nativeIterationOps,
iterateNative, and iterateDefault; each is used by these public observations.

Julia source: base/essentials.jl:1096-1102,1267; base/int.jl:84
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/interfaces.md:8-33;
doc/src/manual/control-flow.md:378-386;
doc/src/manual/integers-and-floating-point-numbers.md:231-249.
-/
def SVecIterationCorrect : Prop :=
  SVecIterationDispatchAccounting ∧ SVecNativeDefaultIterationCorrect

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean
open JuliaLean.base.essentials (Err)
open JuliaLean.base.essentials.Models1Group18 (SizedSVec OneTo64)
open JuliaLean.base.essentials.Models2Group19 (Condition)
open JuliaLean.base.essentials.Models2Group19.SimpleVector (AxisResult AxesOps)

inductive AxesCall (D Other Custom : Type) where
  | le (dimension : D) (one : JInt .i64)
      (outcome : Except Err (Condition Other))
  | getindex (axesTuple : List OneTo64) (dimension : D)
      (outcome : Except Err (AxisResult Custom))

/-- Legal observations are specified by argument/result provenance and the
mathematical axis endpoints, not by re-executing the method or its helpers.
The true-branch tuple has exactly one axis whose endpoint counts the original
SimpleVector positions, even when its slots are null. The false branch has
endpoint one and performs no indexing. No law relates a custom comparison
response to a mathematical ordering on D. -/
def AxesTraceOutcome {D Other Custom : Type} (v : SizedSVec) (d : D)
    (outcome : Except Err (AxisResult Custom))
    (calls : List (AxesCall D Other Custom)) : Prop :=
  (∃ error,
    calls = [.le d (JInt.wrap .i64 1) (.error error)] ∧
    outcome = .error error) ∨
  (∃ other context,
    calls = [.le d (JInt.wrap .i64 1) (.ok (.other other))] ∧
    outcome = .error (.core (.typeError context))) ∨
  (∃ axis : OneTo64,
    calls = [.le d (JInt.wrap .i64 1) (.ok (.bool false))] ∧
    outcome = .ok (.native axis) ∧ axis.stop.val = 1) ∨
  (∃ axis : OneTo64,
    calls = [.le d (JInt.wrap .i64 1) (.ok (.bool true)),
      .getindex [axis] d outcome] ∧
    axis.stop.val = (v.obj.slots.length : Int))

/-- Instrument both genuinely selected leaves. The installed fixed axes and
OneTo constructors remain inside the method being observed. -/
def observeAxes {World D Other Custom : Type}
    (ops : AxesOps (SVecDispatchM World) D Other Custom)
    (v : SizedSVec) (d : D) :
    SVecDispatchM (World × List (DispatchStep World (AxesCall D Other Custom)))
      (AxisResult Custom) :=
  let le' : D → JInt .i64 →
      SVecDispatchM (World × List (DispatchStep World (AxesCall D Other Custom)))
        (Condition Other) :=
    fun dimension one =>
      recordSVecDispatch (fun outcome => AxesCall.le dimension one outcome)
        (ops.le dimension one)
  let getindex' : List OneTo64 → D →
      SVecDispatchM (World × List (DispatchStep World (AxesCall D Other Custom)))
        (AxisResult Custom) :=
    fun axesTuple dimension =>
      recordSVecDispatch (fun outcome => AxesCall.getindex axesTuple dimension outcome)
        (ops.getindex axesTuple dimension)
  JuliaLean.base.essentials.Models2Group19.SimpleVector.axes
    { le := le', getindex := getindex' } v d

/-- Only an actually reachable selected comparison or indexing call may cause
this finite wrapper to diverge. The indexing tuple is characterized by its
independent cardinality/endpoint invariant, not a supplied helper law. -/
def AxesSelectedDiverges {World D Other Custom : Type}
    (ops : AxesOps (SVecDispatchM World) D Other Custom)
    (v : SizedSVec) (d : D) (world : World) : Prop :=
  (ops.le d (JInt.wrap .i64 1)).run world = none ∨
  (∃ afterCompare, ∃ axis : OneTo64,
    (ops.le d (JInt.wrap .i64 1)).run world = some (.ok (.bool true), afterCompare) ∧
    axis.stop.val = (v.obj.slots.length : Int) ∧
    (ops.getindex [axis] d).run afterCompare = none)

/-- For every constructible SimpleVector and every Integer representation,
axes(v,d) preserves the original dimension through its comparison and any
selected indexing. The true branch supplies one native axis counting v's
positions and returns the actual selected outcome. The false branch returns
a native 1:1 range without indexing; a non-Bool condition raises TypeError.
Selected errors, state changes (including those before a throw), and divergence
are retained. No comparison/indexing correctness or termination law is assumed.

SizedSVec already includes the native-length representation invariant; no
slot-initialization premise is added. D may contain unsigned, arbitrarily large,
or custom Integer values, and the result carrier includes non-range custom
indexing results. The sole tuple built here has fixed arity one.

Julia source: base/essentials.jl:1107
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/range.jl:478-491,505;
doc/src/manual/interfaces.md:215-231;
doc/src/manual/control-flow.md:377-386.
Independent invariant: axis endpoint and selected-call/state provenance. -/
def AxesDispatchAccounting : Prop :=
  ∀ (World D Other Custom : Type)
    (ops : AxesOps (SVecDispatchM World) D Other Custom)
    (v : SizedSVec) (d : D) (world : World),
    let observed := (observeAxes ops v d).run (world, [])
    (observed = none ↔ AxesSelectedDiverges ops v d world) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      AxesTraceOutcome v d outcome (calls.map (fun step => step.event)))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean JuliaLean.BootCov JuliaLean.base.essentials
open JuliaLean.base.essentials.Models2Group19

inductive SVecEqualCall (Other : Type) where
  | compare (left right : JVal) (outcome : Except Err (Condition Other))

/-- A log prefix contains exactly the stored pairs in increasing slot order,
and every observed comparison in it returned Boolean true. This inspects
input storage and observations; it calls neither the model nor a handler. -/
def SVecEqualTruePrefix {Other : Type}
    (left right : List (Option JVal)) (calls : List (SVecEqualCall Other)) : Prop :=
  ∀ (k : Nat) (event : SVecEqualCall Other), calls[k]? = some event →
    ∃ a b, left[k]? = some (some a) ∧ right[k]? = some (some b) ∧
      event = .compare a b (.ok (.bool true))

/-- Each completed run is either rejected by length, exhausts all stored
pairs, or ends at one terminal comparison/null slot after a true prefix.
The first false, non-Bool, exception, or null slot suppresses later calls.
Terminal comparison inputs come directly from the next stored pair, rather
than from a duplicate implementation of native indexing. -/
def SVecEqualTraceOutcome {Other : Type}
    (left right : Models1Group18.SizedSVec) (outcome : Except Err Bool)
    (calls : List (SVecEqualCall Other)) : Prop :=
  (left.obj.slots.length ≠ right.obj.slots.length ∧
    calls = [] ∧ outcome = .ok false) ∨
  (left.obj.slots.length = right.obj.slots.length ∧
    ((calls.length = left.obj.slots.length ∧
        SVecEqualTruePrefix left.obj.slots right.obj.slots calls ∧ outcome = .ok true) ∨
     (∃ priorCalls a b,
        SVecEqualTruePrefix left.obj.slots right.obj.slots priorCalls ∧
        left.obj.slots[priorCalls.length]? = some (some a) ∧
        right.obj.slots[priorCalls.length]? = some (some b) ∧
        calls = priorCalls ++ [.compare a b (.ok (.bool false))] ∧ outcome = .ok false) ∨
     (∃ priorCalls a b error,
        SVecEqualTruePrefix left.obj.slots right.obj.slots priorCalls ∧
        left.obj.slots[priorCalls.length]? = some (some a) ∧
        right.obj.slots[priorCalls.length]? = some (some b) ∧
        calls = priorCalls ++ [.compare a b (.error error)] ∧ outcome = .error error) ∨
     (∃ priorCalls a b other context,
        SVecEqualTruePrefix left.obj.slots right.obj.slots priorCalls ∧
        left.obj.slots[priorCalls.length]? = some (some a) ∧
        right.obj.slots[priorCalls.length]? = some (some b) ∧
        calls = priorCalls ++ [.compare a b (.ok (.other other))] ∧
        outcome = .error (.core (.typeError context))) ∨
     (calls.length < left.obj.slots.length ∧
        SVecEqualTruePrefix left.obj.slots right.obj.slots calls ∧
        (left.obj.slots[calls.length]? = some none ∨
          right.obj.slots[calls.length]? = some none) ∧
        outcome = .error (.undefinedBehaviour "null SimpleVector slot"))))

/-- A reachable world after exactly k successful selected comparisons. The
relation ranges over the actual arbitrary handler outcomes and states. It
does not require a correctness, termination, purity, or equality law. -/
def SVecEqualReachable {World Other : Type}
    (ops : SimpleVector.EqualityOps (SVecDispatchM World) Other)
    (left right : List (Option JVal)) (initial : World) : Nat → World → Prop
  | 0, final => final = initial
  | k + 1, final =>
      ∃ prior a b,
        SVecEqualReachable ops left right initial k prior ∧
        left[k]? = some (some a) ∧ right[k]? = some (some b) ∧
        (ops.equal a b).run prior = some (.ok (.bool true), final)

/-- Divergence occurs in a reachable selected comparison after an initial
true prefix, never in length comparison, native indexing, or loop control. -/
def SVecEqualSelectedDiverges {World Other : Type}
    (ops : SimpleVector.EqualityOps (SVecDispatchM World) Other)
    (left right : Models1Group18.SizedSVec) (initial : World) : Prop :=
  left.obj.slots.length = right.obj.slots.length ∧
    ∃ k world a b,
      k < left.obj.slots.length ∧
      SVecEqualReachable ops left.obj.slots right.obj.slots initial k world ∧
      left.obj.slots[k]? = some (some a) ∧ right.obj.slots[k]? = some (some b) ∧
      (ops.equal a b).run world = none

/-- Protected calls observe arbitrary element methods. Stored vectors are
unchanged inputs; mutable element identities remain in the handler world. -/
def observeSVecEqual {World Other : Type}
    (ops : SimpleVector.EqualityOps (SVecDispatchM World) Other)
    (left right : Models1Group18.SizedSVec) :
    SVecDispatchM (World × List (DispatchStep World (SVecEqualCall Other))) Bool :=
  SimpleVector.equal
    { equal := fun a b =>
        recordSVecDispatch (fun result => SVecEqualCall.compare a b result)
          (ops.equal a b) } left right

/-- SimpleVector equality compares the matching stored pairs in increasing
order, after rejecting unequal lengths. It returns true precisely on an
exhausted true prefix. Its first false, non-Bool result, selected exception,
or null slot stops the run. All selected state changes survive, including
those preceding an exception or a later native null-slot observation.

Every native-sized SimpleVector, arbitrary element-comparison implementation,
non-Bool result carrier, and initial world is quantified. Empty vectors and
internal null slots are included. No mathematical equality/reflexivity law
is assumed for arbitrary Julia == methods. Selected divergence is preserved
and is the only divergence in the finite loop. The property depends on the
real equalityLoop and native length/index/arithmetic helpers through equal.

Julia source: base/essentials.jl:1109-1115
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: doc/src/manual/control-flow.md:378-386,516-541.
Independent invariant: stored-pair provenance, terminal-prefix accounting,
and state conservation, including errors and divergence. -/
def SVecEqualityDispatchAccounting : Prop :=
  ∀ (World Other : Type)
    (ops : SimpleVector.EqualityOps (SVecDispatchM World) Other)
    (left right : Models1Group18.SizedSVec) (world : World),
    let observed := (observeSVecEqual ops left right).run (world, [])
    (observed = none ↔ SVecEqualSelectedDiverges ops left right world) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      SVecEqualTraceOutcome left right outcome (calls.map (fun step => step.event)))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19

open JuliaLean.BootCov
open JuliaLean.base.essentials.Models2Group19

/-- Observations at the two selected IO boundaries. The fixed name token
and the actual print argument remain visible in the protected call log. -/
inductive ShowColonCall (IO First R : Type) where
  | typeName (io : IO) (name : ColonTypeName) (outcome : Except Exc First)
  | print (io : IO) (text : String) (outcome : Except Exc R)

/-- A first-call failure is the terminal outcome. Otherwise exactly one
type-name success precedes the parentheses call, whose entire outcome is
returned unchanged. The discarded first payload may be any value. This
finite observation relation checks argument, order, and result provenance;
it executes no selected operation and assumes no IO behavior law. -/
def ShowColonTraceOutcome {IO First R : Type} (io : IO)
    (outcome : Except Exc R) (calls : List (ShowColonCall IO First R)) : Prop :=
  (∃ error,
    calls = [.typeName io .colon (.error error)] ∧ outcome = .error error) ∨
  (∃ discarded,
    calls = [.typeName io .colon (.ok discarded), .print io "()" outcome])

/-- Instrument only the selected operations. Each operation receives the
original World, so it cannot fabricate, erase, or reorder the protected log.
The real model supplies the fixed Colon metadata and the literal parentheses.
Julia source: base/essentials.jl:1174-1177. -/
def observeShowColon {World IO First R : Type}
    (ops : ShowColonOps (DispatchM World) IO First R) (io : IO)
    (colon : JuliaLean.base.essentials.ColonModel) :
    DispatchM (World × List (DispatchStep World (ShowColonCall IO First R))) R :=
  let name' : IO → ColonTypeName →
      DispatchM (World × List (DispatchStep World (ShowColonCall IO First R))) First :=
    fun actualIO actualName =>
      recordDispatch (fun outcome => ShowColonCall.typeName actualIO actualName outcome)
        (ops.showTypeName actualIO actualName)
  let print' : IO → String →
      DispatchM (World × List (DispatchStep World (ShowColonCall IO First R))) R :=
    fun actualIO text =>
      recordDispatch (fun outcome => ShowColonCall.print actualIO text outcome)
        (ops.print actualIO text)
  JuliaLean.base.essentials.Models2Group19.showColon
    { showTypeName := name', print := print' } io colon

/-- Only a reachable selected call can diverge: the first IO operation, or
the parentheses operation in the world left by a successful first call.
No operation is assumed to terminate or to obey a printing contract. -/
def ShowColonSelectedDiverges {World IO First R : Type}
    (ops : ShowColonOps (DispatchM World) IO First R) (io : IO) (world : World) : Prop :=
  (ops.showTypeName io .colon).run world = none ∨
  (∃ discarded afterName,
    (ops.showTypeName io .colon).run world = some (.ok discarded, afterName) ∧
    (ops.print io "()").run afterName = none)

/-- Colon display makes exactly one type-name call with the original IO and
the actual Colon.name token. Only after its success does one print call
receive that same IO and the literal "()". The first result is discarded,
and the print call supplies the actual final result or exception. Every
completed selected effect is retained, including writes before an error;
there is no rollback or invented state transition between the two calls.
Selected divergence is preserved and is the only source of divergence in
this finite wrapper. A divergent run exposes no final world/completed log
in the existing observation carrier.

Every IO carrier, mutable world, selected implementation, first-result type,
and final-result type is quantified without correctness or termination laws.
IOContext qualification and arbitrary custom IO behavior remain selected
dispatch; no literal type-name spelling or Unit return type is presumed.

Julia source: base/essentials.jl:1174-1177
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027.
Julia documentation: base/show.jl:1211-1246;
doc/src/manual/networking-and-streams.md:114-120;
doc/src/manual/functions.md:132-137.
Independent invariant: ordered IO-call, fixed-argument, selected-result,
exception, and state provenance.
-/
def ShowColonDispatchAccounting : Prop :=
  ∀ (World IO First R : Type) (ops : ShowColonOps (DispatchM World) IO First R)
    (io : IO) (colon : JuliaLean.base.essentials.ColonModel) (world : World),
    let observed := (observeShowColon ops io colon).run (world, [])
    (observed = none ↔ ShowColonSelectedDiverges ops io world) ∧
    (∀ outcome finalWorld calls,
      observed = some (outcome, (finalWorld, calls)) →
      DispatchStateContinuity world finalWorld calls ∧
      ShowColonTraceOutcome io outcome (calls.map (fun step => step.event)))

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19
open JuliaLean.BootCov
open JuliaLean.base.essentials.Models2Group19

set_option maxHeartbeats 1600000

theorem coreOpsDispatchBindRun {W A B : Type} (action : DispatchM W A)
    (next : A → DispatchM W B) (world : W) :
    (action >>= next).run world =
      match action.run world with
      | none => none
      | some (.error e, after) => some (.error e, after)
      | some (.ok value, after) => (next value).run after := by
  simp only [ExceptT.run, bind, ExceptT.bind, ExceptT.mk, StateT.bind]
  cases h : action world with
  | none => rfl
  | some result =>
    rcases result with ⟨answer, after⟩
    cases answer <;> rfl

@[simp] theorem coreOpsDispatchPureRun {W A : Type} (value : A) (world : W) :
    (pure value : DispatchM W A).run world = some (.ok value, world) := rfl

@[simp] theorem coreOpsDispatchThrowRun {W A : Type} (e : Exc) (world : W) :
    (throw e : DispatchM W A).run world = some (.error e, world) := rfl

theorem lengthDispatchAccounting_proven : LengthDispatchAccounting := by
  intro World A D R ops argument world
  dsimp only
  unfold observeLength JuliaLean.base.essentials.Models2Group19.lengthAbstract
  rw [coreOpsDispatchBindRun]
  cases hs : ops.size argument world with
  | none => simp [ExceptT.run, recordDispatch, hs, LengthSelectedDiverges]
  | some result =>
    rcases result with ⟨answer, after⟩
    cases answer with
    | error e =>
      constructor
      · simp [ExceptT.run, recordDispatch, hs, LengthSelectedDiverges]
      · intro outcome finalWorld calls h
        simp only [ExceptT.run, recordDispatch, hs, List.nil_append,
          Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact ⟨⟨rfl, rfl⟩, Or.inl ⟨e, rfl, rfl⟩⟩
    | ok dimensions =>
      cases hp : ops.prod dimensions after with
      | none =>
        simp [ExceptT.run, recordDispatch, hs, hp, LengthSelectedDiverges]
        exact ⟨dimensions, after, ⟨rfl, rfl⟩, hp⟩
      | some result =>
        rcases result with ⟨answer, final⟩
        constructor
        · simp [ExceptT.run, recordDispatch, hs, hp, LengthSelectedDiverges]
        · intro outcome finalWorld calls h
          simp only [ExceptT.run, recordDispatch, hs, hp, List.nil_append,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨⟨rfl, rfl, rfl⟩, Or.inr ⟨dimensions, rfl⟩⟩

theorem showColonDispatchAccounting_proven : ShowColonDispatchAccounting := by
  intro World IO First R ops io colon world
  dsimp only
  unfold observeShowColon JuliaLean.base.essentials.Models2Group19.showColon
  rw [coreOpsDispatchBindRun]
  cases hs : ops.showTypeName io .colon world with
  | none => simp [ExceptT.run, recordDispatch, hs, ShowColonSelectedDiverges]
  | some result =>
    rcases result with ⟨answer, after⟩
    cases answer with
    | error e =>
      constructor
      · simp [ExceptT.run, recordDispatch, hs, ShowColonSelectedDiverges]
      · intro outcome finalWorld calls h
        simp only [ExceptT.run, recordDispatch, hs, List.nil_append,
          Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl, rfl⟩
        exact ⟨⟨rfl, rfl⟩, Or.inl ⟨e, rfl, rfl⟩⟩
    | ok discarded =>
      cases hp : ops.print io "()" after with
      | none =>
        simp [ExceptT.run, recordDispatch, hs, hp, ShowColonSelectedDiverges]
        exact ⟨discarded, after, ⟨rfl, rfl⟩, hp⟩
      | some result =>
        rcases result with ⟨answer, final⟩
        constructor
        · simp [ExceptT.run, recordDispatch, hs, hp, ShowColonSelectedDiverges]
        · intro outcome finalWorld calls h
          simp only [ExceptT.run, recordDispatch, hs, hp, List.nil_append,
            Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact ⟨⟨rfl, rfl, rfl⟩, Or.inr ⟨discarded, rfl⟩⟩

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials.Models2Group19
open JuliaLean JuliaLean.base.essentials.Models2Group19

theorem coreOpsStringAddress (s : StringStorage) :
    (unsafeConvertStringUInt8 s).raw.addr.val = s.objectAddress.val + 8 := by
  change wrapInt .u64 (s.objectAddress.val + (JInt.wrap .u64 8).val) = _
  have h8 : (JInt.wrap .u64 8).val = 8 := by decide
  rw [h8]
  apply wrapInt_of_inRange
  have hb := s.objectAddress.property
  have hs := s.spanFits
  change 0 ≤ s.objectAddress.val ∧ s.objectAddress.val ≤ 2 ^ 64 - 1 at hb
  change 0 ≤ s.objectAddress.val + 8 ∧ s.objectAddress.val + 8 ≤ 2 ^ 64 - 1
  omega

theorem stringPointerAliasing_proven : StringPointerAliasing := by
  constructor
  · intro storage
    have haddr := coreOpsStringAddress storage
    refine ⟨haddr, haddr, rfl, ?_⟩
    intro heap backed offset byte stored
    have hread : readStringPointerByte heap (unsafeConvertStringUInt8 storage) offset = some byte := by
      unfold readStringPointerByte
      have he : (unsafeConvertStringUInt8 storage).raw.addr + JInt.wrap .u64 (offset : Int) =
          JInt.wrap .u64 (storage.objectAddress.val + 8 + (offset : Int)) := by
        apply Subtype.ext
        change wrapInt .u64 ((unsafeConvertStringUInt8 storage).raw.addr.val +
          wrapInt .u64 (offset : Int)) = _
        have hoff : wrapInt .u64 (offset : Int) = offset := by
          apply wrapInt_of_inRange
          have hbound := (List.getElem?_eq_some_iff.mp stored).choose
          have hlength := storage.lengthFits
          change 0 ≤ (offset : Int) ∧ (offset : Int) ≤ 2 ^ 64 - 1
          omega
        rw [haddr, hoff]
        rfl
      rw [he]
      exact backed offset byte stored
    exact ⟨hread, hread⟩
  · intro left right different
    have hleft := coreOpsStringAddress left
    have hright := coreOpsStringAddress right
    have distinct : (unsafeConvertStringUInt8 left).raw.addr ≠
        (unsafeConvertStringUInt8 right).raw.addr := by
      intro same
      have heq := congrArg Subtype.val same
      rw [hleft, hright] at heq
      apply different
      apply Subtype.ext
      omega
    exact ⟨distinct, distinct⟩

end JuliaLean.Proofs.base.essentials.Models2Group19

namespace JuliaLean.Proofs.base.essentials

open JuliaLean.Registry

namespace Models2Group19

theorem cconvertDispatchAccounting_proven : CconvertDispatchAccounting := by
  intro World Target Other ops argument world
  cases argument with
  | member value =>
    constructor
    · simp [observeCconvert, JuliaLean.base.essentials.Models2Group19.cconvert,
        pure, ExceptT.pure, StateT.pure]
    · intro outcome finalWorld calls h
      change some (.ok (.member value), (world, [])) =
        some (outcome, (finalWorld, calls)) at h
      cases h
      exact ⟨rfl, Or.inl ⟨value, rfl, rfl, rfl⟩⟩
  | other value =>
    dsimp only [observeCconvert, JuliaLean.base.essentials.Models2Group19.cconvert]
    cases h : ops.convert (.other value) world with
    | none => simp [ExceptT.run, recordDispatch, h]
    | some result =>
      rcases result with ⟨outcome, after⟩
      constructor
      · simp [ExceptT.run, recordDispatch, h]
      · intro observed finalWorld calls hr
        simp only [ExceptT.run, recordDispatch, h, List.nil_append, Option.some.injEq,
          Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨⟨rfl, rfl⟩, Or.inr ⟨value, rfl, rfl⟩⟩

theorem pointerConvertDispatchAccounting_proven : PointerConvertDispatchAccounting := by
  constructor
  · intro World Target Pointer Result ops target pointer world
    dsimp only [observePointerConversion, JuliaLean.base.essentials.unsafeConvertPointer]
    cases h : ops.convert target pointer world with
    | none =>
      simp [ExceptT.run, recordDispatch, h]
    | some result =>
      rcases result with ⟨outcome, after⟩
      constructor
      · simp [ExceptT.run, recordDispatch, h]
      · intro observed finalWorld calls hr
        simp only [ExceptT.run, recordDispatch, h, List.nil_append, Option.some.injEq,
          Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, rfl, rfl⟩
        exact ⟨⟨rfl, rfl⟩, rfl⟩
  · intro Pointer Result pointer
    exact ⟨_, rfl⟩

end Models2Group19

def entriesModels2Group19 : List Entry := [
  { id := "essentials-length-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["length(t::AbstractArray)"],
    statement := "The AbstractArray length fallback calls size once on the original array, passes its actual result to one product call only after size succeeds, and preserves each selected result, first exception, state effect, and divergence, for arbitrary custom dispatch without size or product correctness laws.",
    source := "base/essentials.jl:13; base/abstractarray.jl:305-318; doc/src/manual/interfaces.md:215-225; selected-call provenance invariant",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.LengthDispatchAccounting,
    thm := some ``JuliaLean.Proofs.base.essentials.Models2Group19.lengthDispatchAccounting_proven,
    notes := "Effectful size and prod boundaries are selected on types the method does not fix. Their result carriers are independent and retain object identities. The protected observation carrier retains state on exceptions and represents divergence by none; no final state/log is asserted during divergence. No native-dimension specialization or callee correctness law is assumed." },
  { id := "essentials-checkbounds-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["checkbounds(A::AbstractArray, I...)"],
    statement := "For every native-sized index tuple and arbitrary selected checkbounds(Bool,A,I...) implementation, the wrapper calls that implementation exactly once on the original arguments, retains its effects, permits success only for Boolean true, raises BoundsError for false and TypeError for a non-Boolean, and preserves selected exceptions and divergence.",
    source := "base/essentials.jl:389-393; base/abstractarray.jl:656-663,696-700; doc/src/manual/control-flow.md:378-386; check/exception accounting invariant",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.CheckboundsDispatchAccounting,
    thm := none,
    notes := "The only input premise is representable vararg arity below 2^63. Index carriers may be heterogeneous tagged Julia values and array identities are unchanged. Reuses installed Models1Group18.throwBoundserrorIndicesEmpty and throwBoundserrorIndicesMany for the false branch. The existing Exc boundary preserves BoundsError class but does not expose object/index payload fields." },
  { id := "essentials-oftype-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["oftype(x, y)"],
    statement := "oftype preserves compatible y by identity without calling convert; otherwise it converts the original y exactly once, returns the actual target-member result, rejects a wrong-type result with TypeError after retaining conversion effects, and preserves selected exceptions and divergence for every custom converter.",
    source := "base/essentials.jl:700-718; doc/src/manual/conversion-and-promotion.md:51-53; doc/src/manual/types.md:60-83; identity and selected-call provenance invariant",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.OftypeDispatchAccounting,
    thm := none,
    notes := "The model's Membership tags represent actual isa membership in the concrete runtime typeof(x), without an assumed sameType or conversion law. The result carrier admits erroneous outside conversion results, so the explicit type assertion is observable. The protected trace retains mutation on exceptions; divergence exposes no completed world/log. No field allocation or extra conversion is supplied as a callback." },
  { id := "essentials-cconvert-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["cconvert(::Type{T}, x) where {T}"],
    statement := "The cconvert fallback returns an existing member of T unchanged without conversion; otherwise one convert call receives the original argument and supplies the complete final result, including a value outside T, while preserving every selected exception, state effect, and divergence.",
    source := "base/essentials.jl:724-739; doc/src/manual/calling-c-and-fortran-code.md:248-273; identity and unrestricted selected-result provenance invariant",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.CconvertDispatchAccounting,
    thm := some ``JuliaLean.Proofs.base.essentials.Models2Group19.cconvertDispatchAccounting_proven,
    notes := "Target represents all values inhabiting the actual T, including abstract, union, and UnionAll targets, and Other its complement. No target-membership law is imposed on convert's result: cconvert has no postconversion type assertion. Reuses the protected conversion-event observer from the oftype property; no assumption about callee correctness or termination is introduced." },
  { id := "essentials-pointer-convert-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["unsafe_convert(::Type{P}, x::Ptr) where {P<:Ptr}"],
    statement := "The installed pointer-target unsafe_convert wrapper forwards the original target and pointer to exactly one selected convert call and preserves its complete result, error, state effects, and divergence. Instantiating the selected callee with the installed Union{} conversion raises ArgumentError for every pointer.",
    source := "base/essentials.jl:744,474; doc/src/manual/calling-c-and-fortran-code.md:248-275; selected-call provenance and bottom-target rejection invariants",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.PointerConvertDispatchAccounting,
    thm := some ``JuliaLean.Proofs.base.essentials.Models2Group19.pointerConvertDispatchAccounting_proven,
    notes := "Reuses JuliaLean.base.essentials.unsafeConvertPointer unchanged, instantiating its generic result with an effect monad. PointerConversionOps is property-side organization of the permitted selected conversion boundary. The concrete bottom conjunct calls JuliaLean.base.essentials.convertUnionBottom, with no callee correctness law. No universal success, result-type, or pointer-address preservation claim is made for abstract, union, UnionAll, bottom, or custom conversion targets." },
  { id := "essentials-string-pointer-aliasing", juliaFile := "base/essentials.jl",
    juliaFns := ["unsafe_convert(::Type{Ptr{UInt8}}, s::String)", "unsafe_convert(::Type{Ptr{Int8}}, s::String)"],
    statement := "Both String conversions return addresses aliasing the original live storage: every existing byte is readable unchanged through either pointer, their address bits agree immediately after the size word even for empty strings, and distinct object addresses yield distinct data addresses regardless of equal byte contents.",
    source := "base/essentials.jl:745-746; doc/src/manual/strings.md:405-411; doc/src/manual/calling-c-and-fortran-code.md:273-275; installed String storage layout and aliasing invariant",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.StringPointerAliasing,
    thm := some ``JuliaLean.Proofs.base.essentials.Models2Group19.stringPointerAliasing_proven,
    notes := "Covers both public methods and their concrete helper stringDataPointer. The live native-64-bit StringStorage representation carries nonnull, native-length, and nonwrapping-allocation invariants. The byte-heap premise relates only the input snapshot to existing storage; it never mentions conversion results. Arbitrary bytes, embedded NUL, invalid UTF-8, empty strings, and distinct equal-content objects are included. Signed/unsigned observations compare raw byte bits. Pointer conversion does not allocate, copy, or establish a GC root." },
  { id := "essentials-reinterpret-dispatch-bits", juliaFile := "base/essentials.jl",
    juliaFns := ["reinterpret(::Type{Out}, x) where {Out}"],
    statement := "reinterpret preserves arbitrary-width primitive value bits and nominal target identity with the pinned bitcast error order; same-type identity precedes distinct-type Bool low-bit canonicalization. When both primitive predicates select bitcast, raw UnionAll targets fail the DataType assertion. Other paths make exactly one original-argument _reinterpret call and preserve its result, error, state, and divergence. Metadata helpers obey independent bit, stored-layout, wrapper, and type-projection invariants.",
    source := "base/essentials.jl:544-550,754-794; base/runtime_internals.jl:885-891,1161; src/runtime_intrinsics.c:439-453; doc/src/manual/types.md:299-316",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.ReinterpretDispatchBits,
    thm := none,
    notes := "Registered dependencies: Reinterpret.flagSet, datatypePrimitive, datatypeConcrete, primitiveLayout, unwrapUnionAll, isPrimitiveType, typeofValue, and bitcast. Mask correctness uses mathematical bit positions 7/1; expected payloads use natural-number bit patterns and stored logical widths, independently of installed cast operations. The fallback has no correctness or result-type law. All nominal types, valid layout widths, and bit patterns are included. Physical padding and boxing allocation remain outside the installed jlBitcast value abstraction." },
  { id := "essentials-svec-iterate-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["iterate(v::SimpleVector, i=1)"],
    statement := "SimpleVector iteration compares its actual native length with the original arbitrary state, stops only on Boolean true, rejects non-Bool conditions, and otherwise reads before adding native one, preserving selected values, errors, state, and divergence. Closed native/default cases independently obey stored-slot order, exhaustion, BoundsError for nonpositive indices, the null-slot undefined-behavior marker, and signed wrapping successor arithmetic.",
    source := "base/essentials.jl:1096-1102,1267; base/int.jl:84; doc/src/manual/interfaces.md:8-33; doc/src/manual/control-flow.md:378-386; doc/src/manual/integers-and-floating-point-numbers.md:231-249",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.SVecIterationCorrect,
    thm := none,
    notes := "Generic state, value, and next-state carriers are independent; no custom comparison/indexing/addition correctness law is assumed. Native/default properties use the installed concrete methods through SimpleVector.liftResult, nativeIterationOps, iterateNative, and iterateDefault, covering those helper dependencies. SizedSVec supplies the native-length invariant. Null internal slots remain represented as undefined behavior rather than a fabricated Julia exception." },
  { id := "essentials-svec-axes-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["axes(v::SimpleVector, d::Integer)"],
    statement := "For every native-sized SimpleVector and arbitrary Integer dispatch, axes(v,d) compares the original d with native one once; a true result indexes the actual singleton axis tuple whose endpoint is v's position count and preserves the selected result, a false result returns native 1:1 without indexing, and non-Bool results raise TypeError. Selected arguments, exceptions, state effects, and divergence are preserved without callee correctness laws.",
    source := "base/essentials.jl:1107; base/range.jl:478-491,505; doc/src/manual/interfaces.md:215-231; doc/src/manual/control-flow.md:377-386; endpoint/provenance invariant",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.AxesDispatchAccounting,
    thm := none,
    notes := "D covers signed, unsigned, big, and custom Integers; generic tuple indexing may return any value. Fixed concrete dependencies are installed Models1Group18.svecAxes64, svecLength64, and oneTo64, not callbacks. SizedSVec carries native-representable length; null slots are retained, and the axes tuple has fixed arity one. Protected observations preserve state on exceptions; divergence has no completed final log/world." },
  { id := "essentials-svec-equality-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["==(v1::SimpleVector, v2::SimpleVector)"],
    statement := "For every constructible SimpleVector pair and arbitrary effectful element equality, unequal lengths return false without comparisons; equal lengths compare exactly a stored-pair prefix in order, stop at the first false, non-Bool, error or null slot, and return true only after exhausting Boolean-true results. Selected states, exceptions and divergence are preserved without an equality or purity law.",
    source := "base/essentials.jl:1109-1115; doc/src/manual/control-flow.md:378-386,516-541; stored-pair and terminal-prefix invariants",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.SVecEqualityDispatchAccounting,
    thm := none,
    notes := "Covers the actual equalityLoop helper and fixed installed native length, Int comparison/arithmetic and SimpleVector index operations. SizedSVec enforces native-representable slot counts but allows internal null slots. Mutable element identities are retained in JVal and the arbitrary world; exception observations keep all completed state changes. No final world is asserted for divergence." },
  { id := "essentials-show-colon-dispatch", juliaFile := "base/essentials.jl",
    juliaFns := ["show(io::IO, ::Colon)"],
    statement := "Colon display calls show_type_name once on the original IO and the fixed Colon.name metadata, then calls print on that same IO with the literal parentheses only after the first call succeeds. It discards the arbitrary first result, returns the actual print result without a Unit restriction, and preserves call order, first failure, state effects, and selected divergence for every custom IO implementation.",
    source := "base/essentials.jl:1174-1177; base/show.jl:1211-1246; doc/src/manual/networking-and-streams.md:114-120; doc/src/manual/functions.md:132-137; ordered IO-call and result-provenance invariant",
    status := .proven,
    prop := ``JuliaLean.Proofs.base.essentials.Models2Group19.ShowColonDispatchAccounting,
    thm := some ``JuliaLean.Proofs.base.essentials.Models2Group19.showColonDispatchAccounting_proven,
    notes := "The ColonTypeName token is the distinguished real Colon.name object, not a supplied arbitrary name. Both calls are selected on an IO subtype that this source method does not fix; no qualification, printing, success, or termination law is assumed. First and final return carriers are independent. The property reuses DispatchM, recordDispatch, DispatchStep, and DispatchStateContinuity; exceptions retain their resulting state, while divergence has no final observation. The existing ColonModel covers the source singleton argument." }
]

end JuliaLean.Proofs.base.essentials
