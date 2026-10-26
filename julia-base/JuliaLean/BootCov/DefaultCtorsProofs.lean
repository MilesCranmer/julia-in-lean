import JuliaLean.BootCov.DefaultCtors

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
