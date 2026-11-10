import JuliaLean.Proofs.Compiler.src.typelattice.Common
import JuliaLean.Compiler.src.typeutils.lattice

/-!
Properties of the small helpers of `Compiler/src/typeutils.jl`: `isTypeDataType`,
`has_extended_info`, `isknownlength`, `unionall_depth`, `unwraptv_ub`, `unwraptv_lb`,
`_typename`, `compatible_vatuple` and `unioncomplexity`.
-/

namespace JuliaLean.Proofs.Compiler.src.typeutils

open JuliaLean.Compiler JuliaLean.C JuliaLean.Proofs.Compiler.Lattice

/-! ## `isTypeDataType` -/

/-- `isTypeDataType(t)` holds exactly for the `DataType`s that are invariant in their parameters:
not `Type{T}`/`TypeEgal{T}`, not `typeof(Union{})` (which is `Union{}` at runtime) and not a
`Tuple` (which is covariant), per the comments at `Compiler/src/typeutils.jl:23-30`. -/
def IsTypeDataTypeSpec : Prop :=
  ∀ t : Val, isTypeDataType t = true ↔
    ∃ name ps, t = .datatype name ps ∧ name ≠ tupleName ∧ (t == typeofbottomType) = false

theorem isTypeDataTypeSpec_proven : IsTypeDataTypeSpec := by
  intro t
  cases t with
  | datatype name ps =>
    simp only [isTypeDataType, isType, isTypeEq, isTypeEgal, Val.isTypeeq, Val.isTypeegal,
      Bool.or_false, Bool.false_eq_true, if_false]
    constructor
    · intro h
      refine ⟨name, ps, rfl, ?_, ?_⟩
      · intro hn; subst hn; split at h <;> simp_all
      · split at h
        · simp at h
        · rename_i hb; simpa using hb
    · rintro ⟨n', ps', he, hn, hb⟩
      cases he
      rw [if_neg (by simpa using hb)]
      simpa using hn
  | _ => simp [isTypeDataType, isType, isTypeEq, isTypeEgal, Val.isTypeeq, Val.isTypeegal]

/-! ## `has_extended_info` -/

/-- `has_extended_info(x)` is false exactly for a native type other than `Type{T}`/`TypeEgal{T}`
and for a `Vararg`: every other lattice element (a `Const`, `PartialStruct`, `Conditional`, ...)
and every `Type{T}` carries information beyond its widened type. -/
def HasExtendedInfoSpec : Prop :=
  (∀ t : Val, hasExtendedInfo (.ty t) = false ↔ ((t.isType ∨ t.isVararg) ∧ isType t = false)) ∧
  (∀ x : LElt, (∀ t, x ≠ .ty t) → hasExtendedInfo x = true)

theorem hasExtendedInfoSpec_proven : HasExtendedInfoSpec := by
  refine ⟨fun t => ?_, fun x hx => ?_⟩
  · simp only [hasExtendedInfo, isvarargtype]
    cases h1 : t.isType <;> cases h2 : t.isVararg <;> cases h3 : isType t <;> simp
  · cases x with
    | ty t => exact absurd rfl (hx t)
    | _ => rfl

/-! ## `isknownlength` -/

/-- The length a tuple's parameters fix: known unless the last parameter is a `Vararg` without
an `Int` length. -/
def knownLengthOf (ps : List Val) : Bool :=
  match ps.getLast? with
  | some (.vararg _ (some (.long _))) => true
  | some (.vararg _ _) => false
  | _ => true

/-- `isknownlength(t)` holds exactly when every tuple of type `t` has the same length: `t` does
not end in a `Vararg`, or its `Vararg` has an `Int` length (`Compiler/src/typeutils.jl:47-51`).
Any other argument than a `DataType` is a `MethodError`. -/
def IsknownlengthSpec : Prop :=
  (∀ name ps s, (isknownlength (.datatype name ps)).run s = .ok (knownLengthOf ps, s)) ∧
  (∀ t, t.isDatatype = false → ThrowsJulia "MethodError" (isknownlength t))

theorem isknownlengthSpec_proven : IsknownlengthSpec := by
  refine ⟨fun name ps s => ?_, fun t ht s => ?_⟩
  · simp only [isknownlength, knownLengthOf]
    cases hl : ps.getLast? with
    | none => rfl
    | some va =>
      cases va with
      | vararg T N =>
        cases N with
        | none => rfl
        | some N => cases N <;> rfl
      | _ => rfl
  · cases t with
    | datatype => simp [Val.isDatatype] at ht
    | _ => exact ⟨_, rfl⟩

/-! ## `unionall_depth` -/

/-- The body of a `UnionAll`; any other object is left as it is. -/
def peelUnionall : Val → Val
  | .unionall _ _ _ _ body => body
  | t => t

/-- `k` times `peelUnionall`. -/
def peelN : Nat → Val → Val
  | 0, t => t
  | k + 1, t => peelN k (peelUnionall t)

/-- `unionall_depth(ua)` is the number of `UnionAll`s around `ua`'s body: peeling that many
leaves no `UnionAll`, and peeling fewer always leaves one (`Compiler/src/typeutils.jl:416-423`). -/
def UnionallDepthSpec : Prop :=
  ∀ t : Val, (peelN (unionallDepth t) t).isUnionall = false ∧
    ∀ k < unionallDepth t, (peelN k t).isUnionall = true

theorem unionallDepthSpec_aux : ∀ t : Val,
    (peelN (unionallDepth t) t).isUnionall = false ∧
    ∀ k < unionallDepth t, (peelN k t).isUnionall = true
  | .unionall id nm lb ub body => by
    obtain ⟨h1, h2⟩ := unionallDepthSpec_aux body
    refine ⟨?_, fun k hk => ?_⟩
    · simp only [unionallDepth, peelN, peelUnionall]
      exact h1
    · cases k with
      | zero => rfl
      | succ k =>
        simp only [peelN, peelUnionall]
        exact h2 k (by simp only [unionallDepth] at hk; omega)
  | .datatype .. | .union .. | .intersect .. | .typeeq .. | .typeegal .. | .typevar ..
  | .vararg .. | .bottom | .typeapp .. | .long .. | .symbol .. | .bits .. | .imm ..
  | .mutableRef .. | .module .. => ⟨rfl, fun k hk => by simp [unionallDepth] at hk⟩

theorem unionallDepthSpec_proven : UnionallDepthSpec := unionallDepthSpec_aux

/-! ## `unwraptv_ub` and `unwraptv_lb` -/

/-- `unwraptv_lb(t)` follows lower bounds through `TypeVar`s to a non-`TypeVar`, and leaves any
other object unchanged (`Compiler/src/typeutils.jl:431-436`). -/
def UnwraptvLbSpec : Prop :=
  (∀ t : Val, (unwraptvLb t).isTypevar = false) ∧
  (∀ t : Val, t.isTypevar = false → unwraptvLb t = t) ∧
  (∀ id nm lb ub, unwraptvLb (.typevar id nm lb ub) = unwraptvLb lb)

theorem unwraptvLb_not_typevar : ∀ t : Val, (unwraptvLb t).isTypevar = false
  | .typevar _ _ lb _ => by simpa [unwraptvLb] using unwraptvLb_not_typevar lb
  | .datatype .. | .union .. | .intersect .. | .typeeq .. | .typeegal .. | .unionall ..
  | .vararg .. | .bottom | .typeapp .. | .long .. | .symbol .. | .bits .. | .imm ..
  | .mutableRef .. | .module .. => rfl

theorem unwraptvLbSpec_proven : UnwraptvLbSpec := by
  refine ⟨unwraptvLb_not_typevar, fun t ht => ?_, fun _ _ _ _ => rfl⟩
  cases t with
  | typevar => simp [Val.isTypevar] at ht
  | _ => rfl

/-- `unwraptv_ub(t)` follows upper bounds through `TypeVar`s to a non-`TypeVar`, and leaves any
other object unchanged (`Compiler/src/typeutils.jl:425-430`). -/
def UnwraptvUbSpec : Prop :=
  (∀ n t, Returns (unwraptv n t) (fun r => r.isTypevar = false)) ∧
  (∀ n t s, t.isTypevar = false → (unwraptv (n + 1) t).run s = .ok (t, s)) ∧
  (∀ n id nm lb ub, unwraptv (n + 1) (.typevar id nm lb ub) = unwraptv n ub)

theorem unwraptvUbSpec_proven : UnwraptvUbSpec := by
  refine ⟨fun n => ?_, fun n t s ht => ?_, fun _ _ _ _ _ => rfl⟩
  · induction n with
    | zero => intro t s r s' h; cases h
    | succ n ih =>
      intro t s r s' h
      cases t with
      | typevar _ _ _ ub => exact ih ub s r s' h
      | _ =>
        simp only [unwraptv] at h
        cases h; rfl
  · cases t with
    | typevar => simp [Val.isTypevar] at ht
    | _ => rfl

/-! ## `_typename` -/

/-- `_typename` on a `Union` does not depend on the order of the members, and gives `Const(name)`
for a `DataType`, `TypeName` for a `TypeVar` and `TypeEq{T}`, and looks through `UnionAll`
(`Compiler/src/typeutils.jl:164-176`). -/
def TypenameSpec : Prop :=
  (∀ a b : Val, typenameT (.union a b) = typenameT (.union b a)) ∧
  (∀ name ps, typenameT (.datatype name ps) = .const name) ∧
  (∀ id nm lb ub, typenameT (.typevar id nm lb ub) = .typeName) ∧
  (∀ T, typenameT (.typeeq T) = .typeName) ∧
  (∀ id nm lb ub body, typenameT (.unionall id nm lb ub body) = typenameT body) ∧
  (∀ a b : Val, typenameT a = typenameT b → typenameT (.union a b) = typenameT a)

@[simp] theorem tnb_bb : (TypenameT.bottom == .bottom) = true := rfl
@[simp] theorem tnb_bt : (TypenameT.bottom == .typeName) = false := rfl
@[simp] theorem tnb_bc (a : String) : (TypenameT.bottom == .const a) = false := rfl
@[simp] theorem tnb_tb : (TypenameT.typeName == .bottom) = false := rfl
@[simp] theorem tnb_tt : (TypenameT.typeName == .typeName) = true := rfl
@[simp] theorem tnb_tc (a : String) : (TypenameT.typeName == .const a) = false := rfl
@[simp] theorem tnb_cb (a : String) : (TypenameT.const a == .bottom) = false := rfl
@[simp] theorem tnb_ct (a : String) : (TypenameT.const a == .typeName) = false := rfl
@[simp] theorem tnb_cc (a b : String) : (TypenameT.const a == .const b) = (a == b) := rfl

theorem typenameT_beq_comm (x y : TypenameT) : (x == y) = (y == x) := by
  cases x <;> cases y <;> simp only [tnb_bb, tnb_bt, tnb_bc, tnb_tb, tnb_tt, tnb_tc, tnb_cb,
    tnb_ct, tnb_cc]
  rename_i a b
  by_cases h : a = b
  · subst h; rfl
  · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]

theorem typenameT_beq_self (x : TypenameT) : (x == x) = true := by
  cases x <;> simp

theorem typenameT_eq_of_beq {x y : TypenameT} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> simp at h ⊢
  exact h

theorem typenameSpec_proven : TypenameSpec := by
  refine ⟨fun a b => ?_, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ => rfl, fun _ _ _ _ _ => rfl,
    fun a b h => ?_⟩
  · simp only [typenameT]
    rw [typenameT_beq_comm (typenameT b) (typenameT a)]
    by_cases hab : (typenameT a == typenameT b) = true
    · rw [if_pos hab, if_pos hab]; exact typenameT_eq_of_beq hab
    · rw [if_neg hab, if_neg hab]
      cases ha : typenameT a <;> cases hb : typenameT b <;> simp <;> omega
  · simp only [typenameT, h, typenameT_beq_self, if_true]

/-! ## `compatible_vatuple` -/

/-- `compatible_vatuple(a, b)` is symmetric when `===` is, and is `true` exactly when both tuples
end in a `Vararg` with the same length or both end in something else
(`Compiler/src/typeutils.jl:103-112`). -/
def CompatibleVatupleSpec : Prop :=
  ∀ n E na nb (pa pb : List Val) (va vb : Val) s,
    let a := Val.datatype na (pa ++ [va])
    let b := Val.datatype nb (pb ++ [vb])
    (isvarargtype va = false → isvarargtype vb = false →
      (compatibleVatuple n E a b).run s = .ok (true, s)) ∧
    (isvarargtype va ≠ isvarargtype vb → (compatibleVatuple n E a b).run s = .ok (false, s)) ∧
    (∀ T U N M, va = .vararg T N → vb = .vararg U M →
      (N = none → M = none → (compatibleVatuple n E a b).run s = .ok (true, s)) ∧
      ((N = none) ≠ (M = none) → (compatibleVatuple n E a b).run s = .ok (false, s)) ∧
      (∀ x y, N = some x → M = some y → compatibleVatuple n E a b = egal n E x y))

theorem compatibleVatupleSpec_proven : CompatibleVatupleSpec := by
  intro n E na nb pa pb va vb s
  simp only [compatibleVatuple, Val.isDatatype, Bool.not_true, Bool.or_false, Bool.false_eq_true,
    if_false, Val.params, List.getLast?_concat]
  refine ⟨fun ha hb => ?_, fun hne => ?_, fun T U N M hva hvb => ?_⟩
  · simp [ha, hb]; rfl
  · have h1 : (!(isvarargtype va && isvarargtype vb)) = true := by
      cases h : isvarargtype va <;> cases h' : isvarargtype vb <;> simp_all
    have h2 : (isvarargtype va == isvarargtype vb) = false := by
      cases h : isvarargtype va <;> cases h' : isvarargtype vb <;> simp_all
    rw [if_pos h1, h2]; rfl
  · subst hva; subst hvb
    simp only [isvarargtype, Val.isVararg, Bool.and_self, Bool.not_true, Bool.false_eq_true,
      if_false]
    refine ⟨fun h1 h2 => ?_, fun hne => ?_, fun x y h1 h2 => ?_⟩
    · subst h1; subst h2; rfl
    · cases N <;> cases M <;> simp_all <;> rfl
    · subst h1; subst h2; rfl

/-! ## `unioncomplexity` -/

/-- `unioncomplexity` "estimates the number of calls to `tmerge` to obtain the given type by
counting the Union instances" (`Compiler/src/typeutils.jl:394-395`): on a union it is one more
than the sum over both members, so it counts at least the `unionlen(x) - 1` `Union` nodes; it is
`0` on a non-`Tuple` `DataType`. -/
def UnioncomplexitySpec : Prop :=
  (∀ n x, Returns (unioncomplexity n x) (fun k => unionlen x ≤ k + 1)) ∧
  (∀ n a b, unioncomplexity (n + 1) (.union a b) =
    (do return (← unioncomplexity n a) + (← unioncomplexity n b) + 1)) ∧
  (∀ n name ps s, name ≠ tupleName →
    (unioncomplexity (n + 1) (.datatype name ps)).run s = .ok (0, s))

theorem unioncomplexitySpec_proven : UnioncomplexitySpec := by
  refine ⟨fun n => ?_, fun _ _ _ => rfl, fun n name ps s hn => ?_⟩
  · induction n with
    | zero => intro x s r s' h; cases h
    | succ n ih =>
      intro x s r s' h
      cases x with
      | union a b =>
        simp only [unioncomplexity] at h
        obtain ⟨ka, s₁, ha, h⟩ := run_bind_inv h
        obtain ⟨kb, s₂, hb, h⟩ := run_bind_inv h
        have h1 := ih a s ka s₁ ha
        have h2 := ih b s₁ kb s₂ hb
        cases h
        simp only [unionlen]; omega
      | _ => simp only [unionlen]; omega
  · simp only [unioncomplexity]
    rw [if_pos (by simpa using hn)]
    rfl

end JuliaLean.Proofs.Compiler.src.typeutils
