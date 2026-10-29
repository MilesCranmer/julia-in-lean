import JuliaLean.base.promotion
import JuliaLean.base.bool
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.Proofs.base.int
import JuliaLean.Registry.Types

/-!
# Properties of `base/promotion.jl`

`typejoin` and `promote_type` are least fixed points of their methods (`none`: the recursion
never returns). On finite, well-formed types (declared parameterless types and their unions,
each type name declared once) both are shown to return, `typejoin` with the documented closest
common ancestor. `typesplit` is checked against its source comment, and `promote_type` against
arbitrary promotion-rule tables (the methods later files add) as well as the primitive numeric
table of `base/bool.jl`, `base/int.jl` and `base/float.jl`. Value conversion (`convert`),
runtime `typeof` and inference (`_return_type`) are other files' functions and stay typed
parameters; value computations run in `JlPartial`, where a type computation that never returns
gives `none`.
-/

namespace JuliaLean.Proofs.base.promotion

open JuliaLean
open JuliaLean.base.promotion
open JuliaLean.Registry

/-! Nothing to promise: _has_ancestor_typename@25: private name lookup used by the binary typejoin method. -/
/-! Nothing to promise: typejoin@22: n-ary fold adapter over the binary typejoin method. -/
/-! Nothing to promise: typejoin@23: vararg fold adapter over the binary typejoin method. -/
/-! Nothing to promise: _promote_typesubtract@202: private Nothing/Missing cleanup used by promote_typejoin. -/
/-! Nothing to promise: promote_typejoin_union@209: private recursive union normalization helper. -/
/-! Nothing to promise: typejoin_union_tuple@226: private tuple-union normalization helper. -/
/-! Nothing to promise: full_va_len@256: private tuple-length helper. -/
/-! Nothing to promise: tailjoin@270: private tuple-tail helper used by typejoin. -/
/-! Nothing to promise: promote_typeof@402: one-argument form returning `typeof(x)`; the two-, three- and n-argument forms are covered with `_promote`. -/
/-! Nothing to promise: promote@435: n-ary wrapper; conversion and same-type checks belong to `_promote` and `not_sametype`. -/
/-! Nothing to promise: +@454: generic forwarding method; addition semantics belong to the selected numeric method. -/
/-! Nothing to promise: *@455: generic forwarding method; multiplication semantics belong to the selected numeric method. -/
/-! Nothing to promise: -@456: generic forwarding method; subtraction semantics belong to the selected numeric method. -/
/-! Nothing to promise: /@457: generic forwarding method; division semantics belong to the selected numeric method. -/
/-! Nothing to promise: +%@459: generic forwarding method; wrapping addition semantics belong to the selected numeric method. -/
/-! Nothing to promise: *%@460: generic forwarding method; wrapping multiplication semantics belong to the selected numeric method. -/
/-! Nothing to promise: -%@461: generic forwarding method; wrapping subtraction semantics belong to the selected numeric method. -/
/-! Nothing to promise: ^@507: generic forwarding method; power semantics belong to the selected numeric method. -/
/-! Nothing to promise: fma@509: generic forwarding method; fused multiply-add semantics belong to the selected numeric method. -/
/-! Nothing to promise: ==@516: generic forwarding method; equality semantics belong to the selected numeric method. -/
/-! Nothing to promise: <@517: generic forwarding method; ordering semantics belong to the selected numeric method. -/
/-! Nothing to promise: <=@518: generic forwarding method; ordering semantics belong to the selected numeric method. -/
/-! Nothing to promise: rem@520: generic forwarding method; remainder semantics belong to the selected numeric method. -/
/-! Nothing to promise: mod@521: generic forwarding method; modulus semantics belong to the selected numeric method. -/
/-! Nothing to promise: mod1@522: generic forwarding method; mod1 semantics belong to the selected numeric method. -/
/-! Nothing to promise: fld1@523: generic forwarding method; fld1 semantics belong to the selected numeric method. -/
/-! Nothing to promise: max@525: generic forwarding method; maximum semantics belong to the selected numeric method. -/
/-! Nothing to promise: min@526: generic forwarding method; minimum semantics belong to the selected numeric method. -/
/-! Nothing to promise: minmax@527: generic forwarding method; extrema semantics belong to the selected numeric method. -/

/-! ## Type identity -/

mutual
theorem pEqual_refl : (t : PType) → pEqual t t = true
  | .bottom => by simp [pEqual]
  | .any => by simp [pEqual]
  | .typeVar _ u => by simp [pEqual, pEqual_refl u]
  | .unionAll v b => by simp [pEqual, pEqual_refl v, pEqual_refl b]
  | .union a b => by simp [pEqual, pEqual_refl a, pEqual_refl b]
  | .data _ _ ps s => by simp [pEqual, pListEqual_refl ps, pOptionEqual_refl s]
  | .typeEq p => by simp [pEqual, pEqual_refl p]
  | .typeEgal p => by simp [pEqual, pEqual_refl p]
  | .vararg e n => by
      simp [pEqual, pEqual_refl e]
  | .parameter _ => by simp [pEqual]

theorem pListEqual_refl : (ps : List PType) → pListEqual ps ps = true
  | [] => by simp [pListEqual]
  | p :: ps => by simp [pListEqual, pEqual_refl p, pListEqual_refl ps]

theorem pOptionEqual_refl : (o : Option PType) → pOptionEqual o o = true
  | none => by simp [pOptionEqual]
  | some p => by simp [pOptionEqual, pEqual_refl p]
end

/-! ## Nominal type hierarchies

A type environment gives each declared type name (`Core.TypeName`) its one declaration: the
wrapper name and the supertype. A nominal type is a parameterless datatype declared in the
environment whose supertype chain ends at `Any` (every concrete and abstract number type is one).
`pAncestors t` lists `t` and its supertypes, `pName` is the type name. -/

/-- The declaration of each type name: wrapper name and supertype. -/
abbrev TypeEnv := TypeName → Option (String × PType)

inductive Nominal (env : TypeEnv) : PType → Prop
  | any : Nominal env .any
  | data {n : TypeName} {w : String} {s : PType} :
      n ≠ anyTypeName → n ≠ tupleTypeName → env n = some (w, s) → Nominal env s →
      Nominal env (.data n w [] (some s))

/-- Finite well-formed types of `env`: `Union{}`, nominal types and their unions. -/
inductive SimpleUnion (env : TypeEnv) : PType → Prop
  | bottom : SimpleUnion env .bottom
  | leaf {t : PType} : Nominal env t → SimpleUnion env t
  | union {x y : PType} : SimpleUnion env x → SimpleUnion env y → SimpleUnion env (.union x y)

def pName : PType → TypeName
  | .any => anyTypeName
  | .data n _ _ _ => n
  | _ => ⟨"", ""⟩

def pAncestors : PType → List PType
  | .data n w ps (some s) => .data n w ps (some s) :: pAncestors s
  | t => [t]

/-- The nominal members of a union. -/
def pLeaves : PType → List PType
  | .union x y => pLeaves x ++ pLeaves y
  | .bottom => []
  | t => [t]

/-- The number of `Union` nodes of a type. -/
def pUnions : PType → Nat
  | .union x y => pUnions x + pUnions y + 1
  | _ => 0

theorem pAncestors_any : pAncestors .any = [.any] := by simp [pAncestors]

theorem pAncestors_data (n : TypeName) (w : String) (s : PType) :
    pAncestors (.data n w [] (some s)) = .data n w [] (some s) :: pAncestors s := by
  simp [pAncestors]

theorem pSubtype_any_right (t : PType) : pSubtype t .any = true := by
  cases t <;> simp [pSubtype]

theorem pSubtype_bottom_left (z : PType) : pSubtype .bottom z = true := by
  cases z <;> simp [pSubtype]

theorem pSubtype_union_left (x y z : PType) :
    pSubtype (.union x y) z = (pSubtype x z && pSubtype y z) := by
  cases z <;> simp [pSubtype]

theorem typejoin_unfold (a b : PType) :
    typejoin a b = typejoinPair sourcePTypeOps typejoin a b := by
  rw [typejoin]

section Hierarchy
variable {env : TypeEnv}

theorem mem_ancestors_self {t : PType} (ht : Nominal env t) : t ∈ pAncestors t := by
  cases ht <;> simp [pAncestors_any, pAncestors_data]

theorem any_mem_ancestors {t : PType} (ht : Nominal env t) : PType.any ∈ pAncestors t := by
  induction ht with
  | any => simp [pAncestors_any]
  | data _ _ _ _ ih => simp [pAncestors_data, ih]

theorem nominal_of_mem {t x : PType} (ht : Nominal env t) :
    x ∈ pAncestors t → Nominal env x := by
  induction ht with
  | any =>
      intro hx
      simp [pAncestors_any] at hx
      subst hx
      exact .any
  | @data n w s hn hnt he hs ih =>
      intro hx
      simp only [pAncestors_data, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact .data hn hnt he hs
      · exact ih hx

theorem ancestors_trans {t x y : PType} (ht : Nominal env t) :
    x ∈ pAncestors t → y ∈ pAncestors x → y ∈ pAncestors t := by
  induction ht with
  | any =>
      intro hx hy
      simp [pAncestors_any] at hx
      subst hx
      exact hy
  | @data n w s hn hnt he hs ih =>
      intro hx hy
      simp only [pAncestors_data, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · simpa [pAncestors_data] using hy
      · exact Or.inr (ih hx hy)

theorem pHasAncestorName_iff {t : PType} (ht : Nominal env t) (n : TypeName) :
    pHasAncestorName t n = true ↔ ∃ x ∈ pAncestors t, pName x = n := by
  induction ht with
  | any =>
      simp [pHasAncestorName, pAncestors_any, pName]
  | @data m w s hm hmt he hs ih =>
      by_cases hmn : m = n
      · subst hmn
        simp [pHasAncestorName, pAncestors_data, pName]
      · simp [pHasAncestorName, hmn, pAncestors_data, pName, ih]

theorem nominal_isDataType {t : PType} (ht : Nominal env t) : pIsDataType t = true := by
  cases ht <;> rfl

theorem hasAncestorTypename_nominal {t : PType} (ht : Nominal env t) (n : TypeName) :
    hasAncestorTypename t n = .ok (pHasAncestorName t n) := by
  induction ht with
  | any =>
      by_cases h : anyTypeName = n <;> simp [hasAncestorTypename, pHasAncestorName, h]
  | @data m w s hm hmt he hs ih =>
      by_cases hmn : m = n
      · simp [hasAncestorTypename, pHasAncestorName, hmn]
      · simp [hasAncestorTypename, pHasAncestorName, hmn, nominal_isDataType hs, ih]

theorem nominal_subtype {a b : PType} (ha : Nominal env a) (hb : Nominal env b) :
    pSubtype a b = true ↔ ∃ x ∈ pAncestors a, pName x = pName b := by
  cases hb with
  | any =>
      simp only [pSubtype_any_right, true_iff]
      exact ⟨.any, any_mem_ancestors ha, rfl⟩
  | @data bn bw bs hbn hbt hbe hbs =>
      cases ha with
      | any =>
          simp [pSubtype, pEqual, pAncestors_any, pName]
          exact fun h => hbn h.symm
      | @data an aw as han hat hae has =>
          by_cases h : an = bn
          · subst h
            simp only [pSubtype, pListEqual, if_true, true_iff]
            exact ⟨_, mem_ancestors_self (.data han hat hae has), rfl⟩
          · simp only [pSubtype, h, if_false]
            simpa [pName] using pHasAncestorName_iff (.data han hat hae has) bn

/-- `Core.TypeName` identifies one declaration: nominal types of one environment with the same
name are the same type. -/
theorem nominal_name_unique {x y : PType} (hx : Nominal env x) (hy : Nominal env y)
    (h : pName x = pName y) : x = y := by
  cases hx with
  | any =>
      cases hy with
      | any => rfl
      | @data n w s hn _ _ _ =>
          simp only [pName] at h
          exact absurd h.symm hn
  | @data n w s hn hnt he hs =>
      cases hy with
      | any =>
          simp only [pName] at h
          exact absurd h hn
      | @data n' w' s' hn' hnt' he' hs' =>
          simp only [pName] at h
          subst h
          rw [he] at he'
          cases he'
          rfl

theorem nominal_pEqual_eq {a b : PType} (ha : Nominal env a) (hb : Nominal env b)
    (h : pEqual a b = true) : a = b := by
  induction ha generalizing b with
  | any =>
      cases hb with
      | any => rfl
      | data => simp [pEqual] at h
  | @data n w s hn hnt he hs ih =>
      cases hb with
      | any => simp [pEqual] at h
      | @data n' w' s' _ _ _ hs' =>
          simp [pEqual, pListEqual, pOptionEqual] at h
          obtain ⟨⟨rfl, rfl⟩, h3⟩ := h
          rw [ih hs' h3]

theorem nominal_subtype_trans {a b c : PType} (ha : Nominal env a) (hb : Nominal env b)
    (hc : Nominal env c) (hab : pSubtype a b = true) (hbc : pSubtype b c = true) :
    pSubtype a c = true := by
  obtain ⟨x, hx, hxn⟩ := (nominal_subtype ha hb).1 hab
  have hxb : x = b := nominal_name_unique (nominal_of_mem ha hx) hb hxn
  rw [hxb] at hx
  obtain ⟨y, hy, hyn⟩ := (nominal_subtype hb hc).1 hbc
  exact (nominal_subtype ha hc).2 ⟨y, ancestors_trans ha hx hy, hyn⟩

theorem ascend_of_mem {a : PType} {n : TypeName} (ha : Nominal env a) :
    (∃ x ∈ pAncestors a, pName x = n) →
      ∃ A, pAscendToName a n = some A ∧ A ∈ pAncestors a ∧ pName A = n := by
  induction ha with
  | any =>
      rintro ⟨x, hx, hn⟩
      simp [pAncestors_any] at hx
      subst hx
      simp only [pName] at hn
      subst hn
      exact ⟨.any, by simp [pAscendToName], by simp [pAncestors_any], rfl⟩
  | @data m w s hm hmt he hs ih =>
      rintro ⟨x, hx, hn⟩
      by_cases hmn : m = n
      · subst hmn
        exact ⟨.data m w [] (some s), by simp [pAscendToName], by simp [pAncestors_data],
          by simp [pName]⟩
      · simp only [pAncestors_data, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [pName] at hn
          exact absurd hn hmn
        · obtain ⟨A, h1, h2, h3⟩ := ih ⟨x, hx, hn⟩
          exact ⟨A, by simp [pAscendToName, hmn, h1, nominal_isDataType hs],
            by simp [pAncestors_data, h2], h3⟩

theorem joinData_nominal {a b : PType} (ops : PTypeOps) (ha : Nominal env a)
    (hb : Nominal env b) :
    ∃ A R, pJoinData ops a b = some A ∧ A ∈ pAncestors a ∧ R ∈ pAncestors b ∧
      pName A = pName R ∧
      ∀ C ∈ pAncestors b, (∃ x ∈ pAncestors a, pName x = pName C) → C ∈ pAncestors R := by
  induction hb with
  | any =>
      refine ⟨.any, .any, by simp [pJoinData], any_mem_ancestors ha,
        by simp [pAncestors_any], rfl, ?_⟩
      intro C hC _
      exact hC
  | @data bn bw bs hbn hbt hbe hbs ih =>
      by_cases hh : pHasAncestorName a bn = true
      · obtain ⟨A, hA1, hA2, hA3⟩ := ascend_of_mem ha ((pHasAncestorName_iff ha bn).1 hh)
        have hAn := nominal_of_mem ha hA2
        cases hAn with
        | any =>
            simp [pName] at hA3
            exact absurd hA3.symm hbn
        | @data an aw as han hat hae has =>
            refine ⟨_, .data bn bw [] (some bs), ?_, hA2,
              mem_ancestors_self (.data hbn hbt hbe hbs), by simpa [pName] using hA3, ?_⟩
            · simp [pJoinData, hasAncestorTypename_nominal ha, hh, hA1]
            · intro C hC _
              exact hC
      · obtain ⟨A, R, h1, h2, h3, h4, h5⟩ := ih
        refine ⟨A, R, ?_, h2, by simp [pAncestors_data, h3], h4, ?_⟩
        · simp only [Bool.not_eq_true] at hh
          simp [pJoinData, hasAncestorTypename_nominal ha, hh, nominal_isDataType hbs, h1]
        · intro C hC hx
          simp only [pAncestors_data, List.mem_cons] at hC
          rcases hC with rfl | hC
          · exact absurd ((pHasAncestorName_iff ha bn).2 (by simpa [pName] using hx)) hh
          · exact h5 C hC hx

/-! ### Subtyping on unions of nominal types -/

theorem pSubtype_nominal_union {t : PType} (ht : Nominal env t) (x y : PType) :
    pSubtype t (.union x y) = (pSubtype t x || pSubtype t y) := by
  cases ht <;> simp [pSubtype]

theorem pSubtype_nominal_bottom {t : PType} (ht : Nominal env t) : pSubtype t .bottom = false := by
  cases ht <;> simp [pSubtype, pEqual]

theorem simple_subtype_mono {t z1 z2 : PType} (ht : SimpleUnion env t)
    (hl : ∀ l, Nominal env l → pSubtype l z1 = true → pSubtype l z2 = true) :
    pSubtype t z1 = true → pSubtype t z2 = true := by
  induction ht with
  | bottom => intro _; exact pSubtype_bottom_left _
  | leaf hn => exact hl _ hn
  | union _ _ ih1 ih2 =>
      intro h
      rw [pSubtype_union_left] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ih1 h.1, ih2 h.2⟩

theorem simple_subtype_union_left {t x : PType} (ht : SimpleUnion env t) (y : PType) :
    pSubtype t x = true → pSubtype t (.union x y) = true :=
  simple_subtype_mono ht fun l hl h => by rw [pSubtype_nominal_union hl]; simp [h]

theorem simple_subtype_union_right {t y : PType} (ht : SimpleUnion env t) (x : PType) :
    pSubtype t y = true → pSubtype t (.union x y) = true :=
  simple_subtype_mono ht fun l hl h => by rw [pSubtype_nominal_union hl]; simp [h]

theorem simple_subtype_refl {t : PType} (ht : SimpleUnion env t) : pSubtype t t = true := by
  induction ht with
  | bottom => exact pSubtype_bottom_left _
  | leaf hn => exact (nominal_subtype hn hn).2 ⟨_, mem_ancestors_self hn, rfl⟩
  | @union x y hx hy ih1 ih2 =>
      rw [pSubtype_union_left]
      simp only [Bool.and_eq_true]
      exact ⟨simple_subtype_union_left hx y ih1, simple_subtype_union_right hy x ih2⟩

theorem pLeaves_nominal {t : PType} (ht : Nominal env t) : pLeaves t = [t] := by
  cases ht <;> rfl

theorem pUnions_nominal {t : PType} (ht : Nominal env t) : pUnions t = 0 := by
  cases ht <;> rfl

theorem leaves_nominal {t : PType} (ht : SimpleUnion env t) :
    ∀ l ∈ pLeaves t, Nominal env l := by
  induction ht with
  | bottom => simp [pLeaves]
  | leaf hn =>
      rw [pLeaves_nominal hn]
      intro l hl
      simp only [List.mem_singleton] at hl
      subst hl
      exact hn
  | union _ _ ih1 ih2 =>
      intro l hl
      simp only [pLeaves, List.mem_append] at hl
      rcases hl with hl | hl
      · exact ih1 l hl
      · exact ih2 l hl

theorem subtype_simple_left {t : PType} (ht : SimpleUnion env t) (z : PType) :
    pSubtype t z = true ↔ ∀ l ∈ pLeaves t, pSubtype l z = true := by
  induction ht with
  | bottom => simp [pLeaves, pSubtype_bottom_left]
  | leaf hn => rw [pLeaves_nominal hn]; simp
  | union _ _ ih1 ih2 =>
      rw [pSubtype_union_left]
      simp only [Bool.and_eq_true, ih1, ih2, pLeaves, List.mem_append]
      constructor
      · rintro ⟨h1, h2⟩ l (hl | hl)
        · exact h1 l hl
        · exact h2 l hl
      · intro h
        exact ⟨fun l hl => h l (Or.inl hl), fun l hl => h l (Or.inr hl)⟩

theorem subtype_nominal_right {l z : PType} (hl : Nominal env l) (hz : SimpleUnion env z) :
    pSubtype l z = true ↔ ∃ l' ∈ pLeaves z, pSubtype l l' = true := by
  induction hz with
  | bottom => simp [pLeaves, pSubtype_nominal_bottom hl]
  | leaf hn => rw [pLeaves_nominal hn]; simp
  | union _ _ ih1 ih2 =>
      rw [pSubtype_nominal_union hl]
      simp only [Bool.or_eq_true, ih1, ih2, pLeaves, List.mem_append]
      constructor
      · rintro (⟨l', h1, h2⟩ | ⟨l', h1, h2⟩)
        · exact ⟨l', Or.inl h1, h2⟩
        · exact ⟨l', Or.inr h1, h2⟩
      · rintro ⟨l', h1 | h1, h2⟩
        · exact Or.inl ⟨l', h1, h2⟩
        · exact Or.inr ⟨l', h1, h2⟩

theorem simple_subtype_trans {a b c : PType} (ha : SimpleUnion env a) (hb : SimpleUnion env b)
    (hc : SimpleUnion env c) (hab : pSubtype a b = true) (hbc : pSubtype b c = true) :
    pSubtype a c = true := by
  rw [subtype_simple_left ha]
  intro l hl
  have hln := leaves_nominal ha l hl
  obtain ⟨l', hl', hll'⟩ := (subtype_nominal_right hln hb).1 ((subtype_simple_left ha b).1 hab l hl)
  have hl'n := leaves_nominal hb l' hl'
  obtain ⟨l'', hl'', hl'l''⟩ :=
    (subtype_nominal_right hl'n hc).1 ((subtype_simple_left hb c).1 hbc l' hl')
  exact (subtype_nominal_right hln hc).2
    ⟨l'', hl'', nominal_subtype_trans hln hl'n (leaves_nominal hc l'' hl'') hll' hl'l''⟩

theorem simple_pEqual_eq {a b : PType} (ha : SimpleUnion env a) (hb : SimpleUnion env b)
    (h : pEqual a b = true) : a = b := by
  induction ha generalizing b with
  | bottom =>
      cases hb with
      | bottom => rfl
      | leaf hn => cases hn <;> simp [pEqual] at h
      | union => simp [pEqual] at h
  | leaf hn =>
      cases hb with
      | bottom => cases hn <;> simp [pEqual] at h
      | leaf hn' => exact nominal_pEqual_eq hn hn' h
      | union => cases hn <;> simp [pEqual] at h
  | union hx hy ih1 ih2 =>
      cases hb with
      | bottom => simp [pEqual] at h
      | leaf hn => cases hn <;> simp [pEqual] at h
      | union hx' hy' =>
          simp [pEqual] at h
          rw [ih1 hx' h.1, ih2 hy' h.2]

theorem simple_isType {t : PType} (ht : SimpleUnion env t) : pIsType t = true := by
  cases ht with
  | bottom => rfl
  | leaf hn => cases hn <;> rfl
  | union => rfl

/-! ### `typejoin` on unions of nominal types -/

theorem typejoinPair_top (join : PType → PType → Option PType) {a b : PType}
    (ha : SimpleUnion env a) (hb : SimpleUnion env b)
    (h : pEqual a b = true ∨ pSubtype a b = true ∨ pSubtype b a = true) :
    typejoinPair sourcePTypeOps join a b =
      some (if pEqual a b = true then a else if pSubtype a b = true then b else a) := by
  rcases ha with _ | ha | ⟨_, _⟩ <;> (try rcases ha with _ | ⟨_, _, _, _⟩) <;>
    rcases hb with _ | hb | ⟨_, _⟩ <;> (try rcases hb with _ | ⟨_, _, _, _⟩) <;>
    simp only [typejoinPair, sourcePTypeOps, pIsType, Bool.not_true, Bool.or_false,
      Bool.false_eq_true, ite_false] <;>
    (repeat' split) <;> simp_all

theorem typejoinPair_union_left (join : PType → PType → Option PType) {x y b : PType}
    (hb : SimpleUnion env b) (h1 : pEqual (.union x y) b = false)
    (h2 : pSubtype (.union x y) b = false) (h3 : pSubtype b (.union x y) = false) :
    typejoinPair sourcePTypeOps join (.union x y) b = join x y >>= fun c => join c b := by
  rcases hb with _ | hb | ⟨_, _⟩
  · simp [pSubtype_bottom_left] at h3
  · rcases hb with _ | ⟨_, _, _, _⟩
    · simp [pSubtype_any_right] at h2
    · simp [typejoinPair, sourcePTypeOps, pIsType, h1, h2, h3]
  · simp [typejoinPair, sourcePTypeOps, pIsType, h1, h2, h3]

theorem typejoinPair_union_right (join : PType → PType → Option PType) {a x y : PType}
    (ha : Nominal env a) (h1 : pEqual a (.union x y) = false)
    (h2 : pSubtype a (.union x y) = false) (h3 : pSubtype (.union x y) a = false) :
    typejoinPair sourcePTypeOps join a (.union x y) = join x y >>= fun c => join a c := by
  rcases ha with _ | ⟨_, _, _, _⟩
  · simp [pSubtype_any_right] at h3
  · simp [typejoinPair, sourcePTypeOps, pIsType, h1, h2, h3]

theorem typejoinPair_nominal (join : PType → PType → Option PType) {a b : PType}
    (ha : Nominal env a) (hb : Nominal env b) (h1 : pEqual a b = false)
    (h2 : pSubtype a b = false) (h3 : pSubtype b a = false) :
    typejoinPair sourcePTypeOps join a b = pJoinData sourcePTypeOps a b := by
  rcases ha with _ | ⟨_, hat, _, _⟩
  · simp [pSubtype_any_right] at h3
  · rcases hb with _ | ⟨_, hbt, _, _⟩
    · simp [pSubtype_any_right] at h2
    · simp [typejoinPair, sourcePTypeOps, pIsType, h1, h2, h3, hat, hbt]

theorem typejoin_simple_aux :
    ∀ (n : Nat) (a b : PType), pUnions a + pUnions b < n →
      SimpleUnion env a → SimpleUnion env b →
      ∃ r, typejoin a b = some r ∧ SimpleUnion env r ∧ pUnions r ≤ pUnions a + pUnions b ∧
        pSubtype a r = true ∧ pSubtype b r = true ∧
        ∀ c, Nominal env c → pSubtype a c = true → pSubtype b c = true →
          pSubtype r c = true := by
  intro n
  induction n with
  | zero => intro a b h; omega
  | succ n ih =>
      intro a b hlt ha hb
      rw [typejoin_unfold]
      by_cases h1 : pEqual a b = true
      · have hab := simple_pEqual_eq ha hb h1
        subst hab
        rw [typejoinPair_top typejoin ha ha (Or.inl h1), if_pos h1]
        exact ⟨a, rfl, ha, by omega, simple_subtype_refl ha, simple_subtype_refl ha,
          fun _ _ hac _ => hac⟩
      have h1' : pEqual a b = false := by simpa using h1
      by_cases h2 : pSubtype a b = true
      · rw [typejoinPair_top typejoin ha hb (Or.inr (Or.inl h2)), if_neg h1, if_pos h2]
        exact ⟨b, rfl, hb, by omega, h2, simple_subtype_refl hb, fun _ _ _ hbc => hbc⟩
      have h2' : pSubtype a b = false := by simpa using h2
      by_cases h3 : pSubtype b a = true
      · rw [typejoinPair_top typejoin ha hb (Or.inr (Or.inr h3)), if_neg h1, if_neg h2]
        exact ⟨a, rfl, ha, by omega, simple_subtype_refl ha, h3, fun _ _ hac _ => hac⟩
      have h3' : pSubtype b a = false := by simpa using h3
      cases ha with
      | bottom => exact absurd (pSubtype_bottom_left b) h2
      | @union x y hx hy =>
          rw [typejoinPair_union_left typejoin hb h1' h2' h3']
          have hxy : pUnions x + pUnions y < n := by simp only [pUnions] at hlt; omega
          obtain ⟨m, hm, hmS, hmu, hxm, hym, hmleast⟩ := ih x y hxy hx hy
          have hmb : pUnions m + pUnions b < n := by simp only [pUnions] at hlt; omega
          obtain ⟨r, hr, hrS, hru, hmr, hbr, hrleast⟩ := ih m b hmb hmS hb
          refine ⟨r, by simp [hm, hr], hrS, by simp only [pUnions]; omega, ?_, hbr, ?_⟩
          · rw [pSubtype_union_left]
            simp only [Bool.and_eq_true]
            exact ⟨simple_subtype_trans hx hmS hrS hxm hmr,
              simple_subtype_trans hy hmS hrS hym hmr⟩
          · intro c hc hac hbc
            rw [pSubtype_union_left] at hac
            simp only [Bool.and_eq_true] at hac
            exact hrleast c hc (hmleast c hc hac.1 hac.2) hbc
      | leaf hna =>
          cases hb with
          | bottom => exact absurd (pSubtype_bottom_left a) h3
          | @union x y hx hy =>
              rw [typejoinPair_union_right typejoin hna h1' h2' h3']
              have hxy : pUnions x + pUnions y < n := by
                simp only [pUnions, pUnions_nominal hna] at hlt; omega
              obtain ⟨m, hm, hmS, hmu, hxm, hym, hmleast⟩ := ih x y hxy hx hy
              have ham : pUnions a + pUnions m < n := by
                simp only [pUnions, pUnions_nominal hna] at hlt ⊢; omega
              obtain ⟨r, hr, hrS, hru, har, hmr, hrleast⟩ := ih a m ham (.leaf hna) hmS
              refine ⟨r, by simp [hm, hr], hrS, by simp only [pUnions]; omega, har,
                ?_, ?_⟩
              · rw [pSubtype_union_left]
                simp only [Bool.and_eq_true]
                exact ⟨simple_subtype_trans hx hmS hrS hxm hmr,
                  simple_subtype_trans hy hmS hrS hym hmr⟩
              · intro c hc hac hbc
                rw [pSubtype_union_left] at hbc
                simp only [Bool.and_eq_true] at hbc
                exact hrleast c hc hac (hmleast c hc hbc.1 hbc.2)
          | leaf hnb =>
              rw [typejoinPair_nominal typejoin hna hnb h1' h2' h3']
              obtain ⟨A, R, hJ, hA, hR, hAR, hleast⟩ :=
                joinData_nominal sourcePTypeOps hna hnb
              have hAn := nominal_of_mem hna hA
              have hEq : A = R := nominal_name_unique hAn (nominal_of_mem hnb hR) hAR
              refine ⟨A, hJ, .leaf hAn, by rw [pUnions_nominal hAn]; omega,
                (nominal_subtype hna hAn).2 ⟨A, hA, rfl⟩,
                (nominal_subtype hnb hAn).2 ⟨R, hR, hAR.symm⟩, ?_⟩
              intro c hc hac hbc
              obtain ⟨xa, hxa, hxan⟩ := (nominal_subtype hna hc).1 hac
              obtain ⟨xb, hxb, hxbn⟩ := (nominal_subtype hnb hc).1 hbc
              have hxR : xb ∈ pAncestors R := hleast xb hxb ⟨xa, hxa, hxan.trans hxbn.symm⟩
              exact (nominal_subtype hAn hc).2 ⟨xb, hEq ▸ hxR, hxbn⟩

/-- On unions of nominal types `typejoin` returns a union of nominal types that is a common
supertype of its arguments and a subtype of every nominal common supertype. -/
theorem typejoin_simple {a b : PType} (ha : SimpleUnion env a) (hb : SimpleUnion env b) :
    ∃ r, typejoin a b = some r ∧ SimpleUnion env r ∧ pUnions r ≤ pUnions a + pUnions b ∧
      pSubtype a r = true ∧ pSubtype b r = true ∧
      ∀ c, Nominal env c → pSubtype a c = true → pSubtype b c = true →
        pSubtype r c = true :=
  typejoin_simple_aux _ a b (Nat.lt_succ_self _) ha hb

end Hierarchy

/-- typejoin docstring: `typejoin(T, S)` is the closest common ancestor of `T` and `S`, the
narrowest type from which both inherit. On finite, well-formed types (declared parameterless
types and their unions, each type name declared once in `env`) it returns (the recursion
terminates), and its result is a supertype of both and a subtype of every declared common
supertype. -/
def TypejoinClosestCommonAncestor : Prop :=
  ∀ (env : TypeEnv) (a b : PType), SimpleUnion env a → SimpleUnion env b →
    ∃ r, typejoin a b = some r ∧ pSubtype a r = true ∧ pSubtype b r = true ∧
      ∀ c : PType, Nominal env c → pSubtype a c = true → pSubtype b c = true →
        pSubtype r c = true

theorem typejoinClosestCommonAncestor_proven : TypejoinClosestCommonAncestor := by
  intro env a b ha hb
  obtain ⟨r, hr, _, _, h1, h2, h3⟩ := typejoin_simple ha hb
  exact ⟨r, hr, h1, h2, h3⟩

/-- `typejoin()` is `Union{}`, `typejoin(t)` is `t`, and every type other than a type variable
joins with itself to itself: the recursion returns at once. -/
def TypejoinIdempotent : Prop :=
  typejoinZero = .bottom ∧
  (∀ t : PType, typejoinOne t = t) ∧
  (∀ t : PType, (∀ i u, t ≠ .typeVar i u) → typejoin t t = some t)

theorem typejoinIdempotent_proven : TypejoinIdempotent := by
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro t ht
  rw [typejoin_unfold]
  cases t with
  | typeVar i u => exact absurd rfl (ht i u)
  | _ => simp [typejoinPair, sourcePTypeOps, pEqual_refl]

/-! ## `typesplit` -/

section Typesplit
variable {env : TypeEnv}

theorem typesplit_unfold (a b : PType) :
    typesplit sourcePTypeOps a b =
      if pSubtype a b = true then .bottom
      else match a with
        | .union x y => .union (typesplit sourcePTypeOps x b) (typesplit sourcePTypeOps y b)
        | _ => a := by
  conv => lhs; rw [typesplit.eq_def]
  rfl

theorem typesplit_simple {a : PType} (b : PType) (ha : SimpleUnion env a) :
    SimpleUnion env (typesplit sourcePTypeOps a b) := by
  induction ha with
  | bottom =>
      rw [typesplit_unfold, if_pos (pSubtype_bottom_left b)]
      exact .bottom
  | leaf hn =>
      rw [typesplit_unfold]
      split
      · exact .bottom
      · cases hn with
        | any => exact .leaf .any
        | data h1 h2 h3 h4 => exact .leaf (.data h1 h2 h3 h4)
  | union _ _ ih1 ih2 =>
      rw [typesplit_unfold]
      split
      · exact .bottom
      · exact .union ih1 ih2

theorem typesplit_upper {a : PType} (b : PType) (ha : SimpleUnion env a) :
    pSubtype (typesplit sourcePTypeOps a b) a = true := by
  induction ha with
  | bottom =>
      rw [typesplit_unfold, if_pos (pSubtype_bottom_left b)]
      exact pSubtype_bottom_left _
  | leaf hn =>
      rw [typesplit_unfold]
      split
      · exact pSubtype_bottom_left _
      · cases hn with
        | any => exact simple_subtype_refl (.leaf (env := env) .any)
        | data h1 h2 h3 h4 => exact simple_subtype_refl (.leaf (.data h1 h2 h3 h4))
  | @union x y hx hy ih1 ih2 =>
      rw [typesplit_unfold]
      split
      · exact pSubtype_bottom_left _
      · rw [pSubtype_union_left]
        simp only [Bool.and_eq_true]
        exact ⟨simple_subtype_union_left (typesplit_simple b hx) y ih1,
          simple_subtype_union_right (typesplit_simple b hy) x ih2⟩

theorem typesplit_cover {a : PType} (b : PType) (ha : SimpleUnion env a) :
    pSubtype a (.union (typesplit sourcePTypeOps a b) b) = true := by
  induction ha with
  | bottom => exact pSubtype_bottom_left _
  | leaf hn =>
      rw [typesplit_unfold]
      split
      · next h => rw [pSubtype_nominal_union hn]; simp [h]
      · cases hn with
        | any =>
            exact simple_subtype_union_left (.leaf (env := env) .any) b
              (simple_subtype_refl (.leaf (env := env) .any))
        | data h1 h2 h3 h4 =>
            exact simple_subtype_union_left (.leaf (.data h1 h2 h3 h4)) b
              (simple_subtype_refl (.leaf (.data h1 h2 h3 h4)))
  | @union x y hx hy ih1 ih2 =>
      rw [typesplit_unfold]
      split
      · next h => exact simple_subtype_union_right (.union hx hy) _ h
      · rw [pSubtype_union_left]
        simp only [Bool.and_eq_true]
        constructor
        · refine simple_subtype_mono hx (fun l hl h => ?_) ih1
          rw [pSubtype_nominal_union hl] at h ⊢
          rw [pSubtype_nominal_union hl]
          simp only [Bool.or_eq_true] at h ⊢
          rcases h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        · refine simple_subtype_mono hy (fun l hl h => ?_) ih2
          rw [pSubtype_nominal_union hl] at h ⊢
          rw [pSubtype_nominal_union hl]
          simp only [Bool.or_eq_true] at h ⊢
          rcases h with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h

end Typesplit

/-- Source comment of `typesplit(a, b)`: it returns an upper bound on `a` with `b` removed, such
that `return <: a` and `Union{return, b} == Union{a, b}`, for simple types `b`. -/
def TypesplitRemovesSubtype : Prop :=
  ∀ (env : TypeEnv) (a b : PType), SimpleUnion env a → SimpleUnion env b →
    pSubtype (typesplit sourcePTypeOps a b) a = true ∧
    pSubtype (.union (typesplit sourcePTypeOps a b) b) (.union a b) = true ∧
    pSubtype (.union a b) (.union (typesplit sourcePTypeOps a b) b) = true

theorem typesplitRemovesSubtype_proven : TypesplitRemovesSubtype := by
  intro env a b ha hb
  have hr := typesplit_simple b ha
  have hbu : ∀ {z : PType}, pSubtype b (.union z b) = true :=
    simple_subtype_union_right hb _ (simple_subtype_refl hb)
  refine ⟨typesplit_upper b ha, ?_, ?_⟩
  · rw [pSubtype_union_left]
    simp only [Bool.and_eq_true]
    exact ⟨simple_subtype_union_left hr b (typesplit_upper b ha), hbu⟩
  · rw [pSubtype_union_left]
    simp only [Bool.and_eq_true]
    exact ⟨typesplit_cover b ha, hbu⟩

/-! ## `promote_typejoin` -/

section PromoteTypejoin
variable {env : TypeEnv}

theorem subtract_simple {a : PType} (ha : SimpleUnion env a) :
    SimpleUnion env (primitivePromoteTypesubtractDispatch a) := by
  unfold primitivePromoteTypesubtractDispatch promoteTypesubtract
  repeat' split
  all_goals first | exact ha | exact typesplit_simple _ ha

theorem subtract_id {a : PType} (h1 : pSubtype primitiveNothingType a = false)
    (h2 : pSubtype primitiveMissingType a = false) :
    primitivePromoteTypesubtractDispatch a = a := by
  simp [primitivePromoteTypesubtractDispatch, promoteTypesubtract, sourcePTypeOps,
    pSubtype_union_left, h1, h2]

end PromoteTypejoin

/-- promote_typejoin docstring: `promote_typejoin(T, S)` computes a type that contains both `T`
and `S` (a parent of both or a `Union`) and falls back to `typejoin`. On declared types and
their unions it returns such a supertype of both, and when neither contains `Nothing` or
`Missing` the result is equivalent to `typejoin(T, S)`. -/
def PromoteTypejoinContainsInputs : Prop :=
  ∀ (env : TypeEnv) (a b : PType), SimpleUnion env a → SimpleUnion env b →
    ∃ r, primitivePromoteTypejoinDispatch a b = some r ∧
      pSubtype a r = true ∧ pSubtype b r = true ∧
      (pSubtype primitiveNothingType a = false → pSubtype primitiveMissingType a = false →
        pSubtype primitiveNothingType b = false → pSubtype primitiveMissingType b = false →
        ∃ j, typejoin a b = some j ∧ pSubtype r j = true ∧ pSubtype j r = true)

theorem promoteTypejoinContainsInputs_proven : PromoteTypejoinContainsInputs := by
  intro env a b ha hb
  obtain ⟨c, hc, -, -, -, -, -⟩ := typejoin_simple (subtract_simple ha) (subtract_simple hb)
  refine ⟨.union a (.union b c), ?_, ?_, ?_, ?_⟩
  · simp [primitivePromoteTypejoinDispatch, promoteTypejoin, hc]
  · exact simple_subtype_union_left ha _ (simple_subtype_refl ha)
  · exact simple_subtype_union_right hb _ (simple_subtype_union_left hb _ (simple_subtype_refl hb))
  · intro h1 h2 h3 h4
    rw [subtract_id h1 h2, subtract_id h3 h4] at hc
    obtain ⟨j, hj, hjS, -, haj, hbj, -⟩ := typejoin_simple ha hb
    have hcj : c = j := by
      rw [hj] at hc
      exact (Option.some.inj hc).symm
    subst hcj
    refine ⟨c, hj, ?_, ?_⟩
    · rw [pSubtype_union_left, pSubtype_union_left]
      simp [haj, hbj, simple_subtype_refl hjS]
    · exact simple_subtype_union_right hjS _
        (simple_subtype_union_right hjS _ (simple_subtype_refl hjS))

/-! ## `promote_type` for an arbitrary promotion-rule table -/

theorem promoteTypeDispatch_right_bottom (u : PType → PType → Option PType) (T : PType) :
    promoteTypeDispatch u T .bottom = some T := by
  unfold promoteTypeDispatch
  cases T <;> simp [promoteTypeBottomBottom, promoteTypeRightBottom]

theorem promoteTypeDispatch_left_bottom (u : PType → PType → Option PType) (S : PType) :
    promoteTypeDispatch u .bottom S = some S := by
  unfold promoteTypeDispatch
  cases S <;> simp [promoteTypeBottomBottom, promoteTypeLeftBottom]

theorem promoteTypeDispatch_self (u : PType → PType → Option PType) (T : PType) :
    promoteTypeDispatch u T T = some T := by
  unfold promoteTypeDispatch
  cases T <;> simp [promoteTypeBottomBottom, promoteTypeSame, pEqual_refl]

theorem promoteTypeDispatch_ne (u : PType → PType → Option PType)
    {T S : PType} (hT : T ≠ .bottom) (hS : S ≠ .bottom) :
    promoteTypeDispatch u T S =
      if pEqual T S = true then some T
      else if (!pIsType T || !pIsType S) = true then some .any
      else promoteResultDispatch u T S (promoteRuleDispatch u T S)
        (promoteRuleDispatch u S T) := by
  unfold promoteTypeDispatch
  cases T <;> cases S <;> simp_all [promoteTypeSame, promoteTypePair]

theorem promoteRuleDispatch_some (u : PType → PType → Option PType) {T S R : PType}
    (hT : T ≠ .bottom) (hS : S ≠ .bottom) (h : u T S = some R) :
    promoteRuleDispatch u T S = R := by
  cases T <;> cases S <;> simp_all [promoteRuleDispatch]

theorem promoteRuleDispatch_none (u : PType → PType → Option PType) {T S : PType}
    (hT : T ≠ .bottom) (hS : S ≠ .bottom) (h : u T S = none) :
    promoteRuleDispatch u T S = .bottom := by
  cases T <;> cases S <;> simp_all [promoteRuleDispatch, promoteRuleDefault]

theorem promoteRuleDispatch_bottom (u : PType → PType → Option PType) {T S : PType}
    (hT : T ≠ .bottom) (hS : S ≠ .bottom) (h : u T S = none ∨ u T S = some .bottom) :
    promoteRuleDispatch u T S = .bottom := by
  rcases h with h | h
  · exact promoteRuleDispatch_none u hT hS h
  · exact promoteRuleDispatch_some u hT hS h

theorem promoteResultDispatch_bottom (u : PType → PType → Option PType) (T S : PType) :
    promoteResultDispatch u T S .bottom .bottom = typejoin T S := by
  unfold promoteResultDispatch
  simp [promoteResultNoRules]

theorem promoteResultDispatch_left (u : PType → PType → Option PType)
    (T S : PType) {R1 : PType} (R2 : PType) (h : R1 ≠ .bottom) :
    promoteResultDispatch u T S R1 R2 = promoteTypeDispatch u R1 R2 := by
  unfold promoteResultDispatch
  cases R1 <;> simp_all [promoteResultDefault]

theorem promoteResultDispatch_right (u : PType → PType → Option PType)
    (T S R1 : PType) {R2 : PType} (h : R2 ≠ .bottom) :
    promoteResultDispatch u T S R1 R2 = promoteTypeDispatch u R1 R2 := by
  unfold promoteResultDispatch
  cases R1 <;> cases R2 <;> simp_all [promoteResultDefault]

theorem promoteType_self (u : PType → PType → Option PType) (T : PType) :
    promoteType u T T = some T := promoteTypeDispatch_self u T

theorem promoteType_right_bottom (u : PType → PType → Option PType) (T : PType) :
    promoteType u T .bottom = some T := promoteTypeDispatch_right_bottom u T

theorem promoteType_left_bottom (u : PType → PType → Option PType) (S : PType) :
    promoteType u .bottom S = some S := promoteTypeDispatch_left_bottom u S

/-- `Union{}` is the identity of `promote_type`, and every type promotes with itself to itself,
whatever promotion rules are defined: `promote_type` returns these types. -/
def PromoteTypeIdentities : Prop :=
  ∀ (u : PType → PType → Option PType) (T : PType),
    promoteType u .bottom .bottom = some .bottom ∧
    promoteType u T .bottom = some T ∧
    promoteType u .bottom T = some T ∧
    promoteType u T T = some T

theorem promoteTypeIdentities_proven : PromoteTypeIdentities := fun u T =>
  ⟨promoteType_self u .bottom, promoteType_right_bottom u T, promoteType_left_bottom u T,
    promoteType_self u T⟩

theorem promoteType_rule_forward (u : PType → PType → Option PType) {T S R : PType}
    (hT : T ≠ .bottom) (hS : S ≠ .bottom) (hR : R ≠ .bottom) (hTS : pEqual T S = false)
    (hTt : pIsType T = true) (hSt : pIsType S = true)
    (hrule : (u T S = some R ∧ (u S T = none ∨ u S T = some R)) ∨
      (u T S = none ∧ u S T = some R)) :
    promoteType u T S = some R := by
  show promoteTypeDispatch u T S = some R
  rw [promoteTypeDispatch_ne u hT hS]
  simp only [hTS, hTt, hSt, Bool.not_true, Bool.or_false, Bool.false_eq_true, if_false]
  rcases hrule with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩
  · rw [promoteRuleDispatch_some u hT hS h1, promoteRuleDispatch_none u hS hT h2,
      promoteResultDispatch_left u T S .bottom hR]
    exact promoteTypeDispatch_right_bottom u R
  · rw [promoteRuleDispatch_some u hT hS h1, promoteRuleDispatch_some u hS hT h2,
      promoteResultDispatch_left u T S R hR]
    exact promoteTypeDispatch_self u R
  · rw [promoteRuleDispatch_none u hT hS h1, promoteRuleDispatch_some u hS hT h2,
      promoteResultDispatch_right u T S .bottom hR]
    exact promoteTypeDispatch_left_bottom u R

/-- Manual, Conversion and Promotion: a promotion rule needs to be defined in one direction
only; `promote_type` then returns the rule's type in either argument order. -/
def PromoteTypeUserRules : Prop :=
  ∀ (u : PType → PType → Option PType) (T S R : PType),
    T ≠ .bottom → S ≠ .bottom → R ≠ .bottom →
    pEqual T S = false → pEqual S T = false →
    pIsType T = true → pIsType S = true →
    ((u T S = some R ∧ (u S T = none ∨ u S T = some R)) ∨
      (u T S = none ∧ u S T = some R)) →
    promoteType u T S = some R ∧ promoteType u S T = some R

theorem promoteTypeUserRules_proven : PromoteTypeUserRules := by
  intro u T S R hT hS hR hTS hST hTt hSt hrule
  refine ⟨promoteType_rule_forward u hT hS hR hTS hTt hSt hrule,
    promoteType_rule_forward u hS hT hR hST hSt hTt ?_⟩
  rcases hrule with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, Or.inr h1⟩
  · exact Or.inl ⟨h2, Or.inl h1⟩

/-- When no promotion rule names a type in either direction (none is defined, or it returns
`Union{}`), `promote_type` falls back to `typejoin` of the two types; on declared types and
their unions both return. -/
def PromoteTypeFallback : Prop :=
  ∀ (env : TypeEnv) (u : PType → PType → Option PType) (a b : PType),
    SimpleUnion env a → SimpleUnion env b → a ≠ PType.bottom → b ≠ PType.bottom →
    (u a b = none ∨ u a b = some .bottom) → (u b a = none ∨ u b a = some .bottom) →
    ∃ r, promoteType u a b = some r ∧ typejoin a b = some r

theorem promoteTypeFallback_proven : PromoteTypeFallback := by
  intro env u a b ha hb hna hnb hu1 hu2
  obtain ⟨r, hr, -⟩ := typejoin_simple ha hb
  refine ⟨r, ?_, hr⟩
  show promoteTypeDispatch u a b = some r
  rw [promoteTypeDispatch_ne u hna hnb]
  by_cases h1 : pEqual a b = true
  · have hab := simple_pEqual_eq ha hb h1
    subst hab
    rw [if_pos h1]
    have hself : typejoin a a = some a := by
      rw [typejoin_unfold, typejoinPair_top typejoin ha ha (Or.inl h1), if_pos h1]
    rw [hself] at hr
    exact hr
  · rw [if_neg h1, if_neg (by simp [simple_isType ha, simple_isType hb]),
      promoteRuleDispatch_bottom u hna hnb hu1, promoteRuleDispatch_bottom u hnb hna hu2,
      promoteResultDispatch_bottom]
    exact hr

/-- The `promote_rule` methods for `Union{}` return the other type (or `Union{}`) whatever
further arguments are slurped, and the fallback returns `Union{}` when no rule is defined. -/
def PromoteRuleBottomIdentities : Prop :=
  ∀ (u : PType → PType → Option PType),
    promoteRuleDispatch u .bottom .bottom = .bottom ∧
    (∀ t : PType, promoteRuleDispatch u .bottom t = t) ∧
    (∀ t : PType, promoteRuleDispatch u t .bottom = t) ∧
    (∀ t s : PType, t ≠ .bottom → s ≠ .bottom → u t s = none →
      promoteRuleDispatch u t s = .bottom) ∧
    (∀ (t : PType) (slurp : List PType),
      promoteRuleBottomFirst PType.bottom slurp = .bottom ∧
      promoteRuleBottomBoth PType.bottom slurp = .bottom ∧
      promoteRuleBottomThenType .bottom t slurp = t ∧
      promoteRuleTypeThenBottom .bottom t slurp = t)

theorem promoteRuleBottomIdentities_proven : PromoteRuleBottomIdentities := by
  intro u
  refine ⟨by simp [promoteRuleDispatch, promoteRuleBottomBoth], ?_, ?_,
    fun t s ht hs h => promoteRuleDispatch_none u ht hs h, fun t slurp => ⟨rfl, rfl, rfl, rfl⟩⟩
  · intro t
    cases t <;> simp [promoteRuleDispatch, promoteRuleBottomBoth, promoteRuleBottomThenType]
  · intro t
    cases t <;> simp [promoteRuleDispatch, promoteRuleBottomBoth, promoteRuleTypeThenBottom]


theorem promoteType_absorb (u : PType → PType → Option PType) {T y : PType}
    (h : y = T ∨ y = .bottom) : promoteType u T y = some T := by
  rcases h with rfl | rfl
  · exact promoteType_self u y
  · exact promoteType_right_bottom u T

/-! ## Primitive promotion table -/

def primitiveFloatBits : JuliaLean.base.float.FTy → Nat
  | .f16 => 16
  | .f32 => 32
  | .f64 => 64

def primitiveExpected : PrimitiveType → PrimitiveType → PrimitiveType
  | .bool, s => s
  | t, .bool => t
  | .int t, .int s =>
      .int (if t.bits > s.bits then t else if s.bits > t.bits then s
        else if t.signed then s else t)
  | .float t, .int _ => .float t
  | .int _, .float s => .float s
  | .float t, .float s =>
      if primitiveFloatBits t >= primitiveFloatBits s then .float t else .float s

section PrimitiveTable

attribute [local simp]
  JuliaLean.base.promotion.primitivePromoteType
  JuliaLean.base.promotion.promoteType
  JuliaLean.base.promotion.promoteTypeDispatch
  JuliaLean.base.promotion.promoteRuleDispatch
  JuliaLean.base.promotion.promoteResultDispatch
  JuliaLean.base.promotion.primitivePromoteRule
  JuliaLean.base.promotion.primitiveTypeOfPType
  JuliaLean.base.promotion.primitivePType
  JuliaLean.base.promotion.primitiveBoolRuleWitness
  JuliaLean.base.promotion.primitiveIntName
  JuliaLean.base.promotion.primitiveFloatName
  JuliaLean.base.int.promote_rule
  JuliaLean.base.int.promote_rule_Int16
  JuliaLean.base.int.promote_rule_Int32
  JuliaLean.base.int.promote_rule_Int64
  JuliaLean.base.int.promote_rule_Int128
  JuliaLean.base.int.promote_rule_UInt16
  JuliaLean.base.int.promote_rule_UInt32
  JuliaLean.base.int.promote_rule_UInt64
  JuliaLean.base.int.promote_rule_UInt128
  JuliaLean.base.int.promote_rule_UInt8_Int8
  JuliaLean.base.int.promote_rule_UInt16_Int16
  JuliaLean.base.int.promote_rule_UInt32_Int32
  JuliaLean.base.int.promote_rule_UInt64_Int64
  JuliaLean.base.int.promote_rule_UInt128_Int128
  JuliaLean.base.float.promote_rule_float_int
  JuliaLean.base.float.promote_rule_float
  JuliaLean.base.float.promote_rule_float_Bool
  JuliaLean.base.float.promote_rule_Float64_UInt128
  JuliaLean.base.float.promote_rule_Float64_Int128
  JuliaLean.base.float.promote_rule_Float32_UInt128
  JuliaLean.base.float.promote_rule_Float32_Int128
  JuliaLean.base.float.promote_rule_Float16_UInt128
  JuliaLean.base.float.promote_rule_Float16_Int128
  JuliaLean.base.float.promote_rule_Float32_Float16
  JuliaLean.base.float.promote_rule_Float64_Float16
  JuliaLean.base.float.promote_rule_Float64_Float32
  JuliaLean.base.promotion.pEqual
  JuliaLean.base.promotion.pIsType
  JuliaLean.base.promotion.pListEqual
  JuliaLean.base.promotion.pOptionEqual
  JuliaLean.base.promotion.promoteTypePair
  JuliaLean.base.promotion.promoteTypeSame
  JuliaLean.base.promotion.promoteTypeBottomBottom
  JuliaLean.base.promotion.promoteTypeRightBottom
  JuliaLean.base.promotion.promoteTypeLeftBottom
  JuliaLean.base.promotion.promoteRuleDefault
  JuliaLean.base.promotion.promoteResultDefault
  JuliaLean.base.promotion.promoteResultNoRules
  JuliaLean.base.promotion.promoteRuleBottomBoth
  JuliaLean.base.promotion.promoteRuleBottomThenType
  JuliaLean.base.promotion.promoteRuleTypeThenBottom
  JuliaLean.base.float.promote_rule_float_BitSigned64
  JuliaLean.base.float.promote_rule_float_BitUnsigned64
  JuliaLean.base.promotion.pPromotionNumber
  JuliaLean.base.promotion.pPromotionReal
  JuliaLean.base.promotion.pPromotionInteger
  JuliaLean.base.promotion.pPromotionSigned
  JuliaLean.base.promotion.pPromotionUnsigned
  JuliaLean.base.promotion.pPromotionAbstractFloat
  IntTy.bits IntTy.signed


def PromoteTypeTable : Prop :=
  ∀ a b : PrimitiveType,
    primitivePromoteType (primitivePType a) (primitivePType b) =
      some (primitivePType (primitiveExpected a b))

theorem promoteTypeTable_proven : PromoteTypeTable := by
  intro a b
  cases a with
  | bool =>
      cases b with
      | bool => simp [primitiveExpected, primitiveFloatBits]
      | int t => cases t <;> simp [primitiveExpected, primitiveFloatBits]
      | float t => cases t <;> simp [primitiveExpected, primitiveFloatBits]
  | int t =>
      cases t <;>
        cases b with
        | bool => simp [primitiveExpected, primitiveFloatBits]
        | int s => cases s <;> simp [primitiveExpected, primitiveFloatBits]
        | float s => cases s <;> simp [primitiveExpected, primitiveFloatBits]
  | float t =>
      cases t <;>
        cases b with
        | bool => simp [primitiveExpected, primitiveFloatBits]
        | int s => cases s <;> simp [primitiveExpected, primitiveFloatBits]
        | float s => cases s <;> simp [primitiveExpected, primitiveFloatBits]

theorem primitiveExpectedSymmetric (a b : PrimitiveType) :
    primitiveExpected a b = primitiveExpected b a := by
  cases a with
  | bool =>
      cases b <;> simp [primitiveExpected]
  | int t =>
      cases t <;>
        cases b with
        | bool => simp [primitiveExpected]
        | int s => cases s <;> simp [primitiveExpected, IntTy.bits, IntTy.signed]
        | float s => cases s <;> simp [primitiveExpected, primitiveFloatBits]
  | float t =>
      cases t <;>
        cases b with
        | bool => simp [primitiveExpected]
        | int s => cases s <;> simp [primitiveExpected, primitiveFloatBits]
        | float s => cases s <;> simp [primitiveExpected, primitiveFloatBits]

def PromoteTypeSymmetric : Prop :=
  ∀ a b : PrimitiveType,
    primitivePromoteType (primitivePType a) (primitivePType b) =
      primitivePromoteType (primitivePType b) (primitivePType a)

theorem promoteTypeSymmetric_proven : PromoteTypeSymmetric := by
  intro a b
  rw [promoteTypeTable_proven a b, promoteTypeTable_proven b a, primitiveExpectedSymmetric a b]

theorem primitivePromotionFoldTable (initial : PrimitiveType)
    (rest : List PrimitiveType) :
    (rest.map primitivePType).foldlM primitivePromoteType (primitivePType initial) =
      some (primitivePType (rest.foldl primitiveExpected initial)) := by
  induction rest generalizing initial with
  | nil => rfl
  | cons t rest ih =>
      simp only [List.map_cons, List.foldlM_cons, List.foldl_cons]
      rw [promoteTypeTable_proven initial t]
      exact ih (primitiveExpected initial t)

end PrimitiveTable

/-- `promote_type()` is `Union{}`, `promote_type(T)` is `T`, and more types are promoted from
left to right: the primitive table applies pairwise, and for any promotion rules, arguments
equal to the first type or `Union{}` leave it unchanged; `promote_type` returns all these. -/
def PromoteTypeNaryTable : Prop :=
  promoteTypeZero PType.bottom = .bottom ∧
  (∀ t : PType, promoteTypeOneGeneric t = t) ∧
  (∀ a b c : PrimitiveType,
    promoteTypeThree primitivePromoteType (primitivePType a) (primitivePType b)
      (primitivePType c) =
      some (primitivePType (primitiveExpected (primitiveExpected a b) c))) ∧
  (∀ a b c : PrimitiveType, ∀ rest : List PrimitiveType,
    promoteTypeMany primitivePromoteType (primitivePType a) (primitivePType b)
      (primitivePType c) (rest.map primitivePType) =
      some (primitivePType (rest.foldl (fun acc t => primitiveExpected acc t)
        (primitiveExpected (primitiveExpected a b) c)))) ∧
  (∀ (u : PType → PType → Option PType) (T y z : PType) (Vs : List PType),
    (y = T ∨ y = .bottom) → (z = T ∨ z = .bottom) → (∀ v ∈ Vs, v = T ∨ v = .bottom) →
    promoteTypeThree (promoteType u) T y z = some T ∧
    promoteTypeMany (promoteType u) T y z Vs = some T)

theorem promoteTypeNaryTable_proven : PromoteTypeNaryTable := by
  have h3 : ∀ a b c : PrimitiveType,
      promoteTypeThree primitivePromoteType (primitivePType a) (primitivePType b)
        (primitivePType c) =
        some (primitivePType (primitiveExpected (primitiveExpected a b) c)) := by
    intro a b c
    rw [promoteTypeThree, promoteTypeTable_proven a b]
    exact promoteTypeTable_proven (primitiveExpected a b) c
  refine ⟨rfl, fun _ => rfl, h3, ?_, ?_⟩
  · intro a b c rest
    rw [promoteTypeMany, h3 a b c]
    exact primitivePromotionFoldTable (primitiveExpected (primitiveExpected a b) c) rest
  · intro u T y z Vs hy hz hVs
    have hT3 : promoteTypeThree (promoteType u) T y z = some T := by
      rw [promoteTypeThree, promoteType_absorb u hy]
      exact promoteType_absorb u hz
    refine ⟨hT3, ?_⟩
    rw [promoteTypeMany, hT3]
    show Vs.foldlM (promoteType u) T = some T
    induction Vs with
    | nil => rfl
    | cons v Vs ih =>
        rw [List.foldlM_cons, promoteType_absorb u (hVs v (List.mem_cons_self ..))]
        exact ih (fun w hw => hVs w (List.mem_cons_of_mem _ hw))

/-! ## `typejoin` on the primitive numeric types -/

/-- The declarations of the primitive number types and their abstract supertypes (`Core`). -/
def primitiveEnv (n : TypeName) : Option (String × PType) :=
  if n.module = "Core" then
    match n.name with
    | "Number" => some ("Number", .any)
    | "Real" => some ("Real", pPromotionNumber)
    | "Integer" => some ("Integer", pPromotionReal)
    | "Signed" => some ("Signed", pPromotionInteger)
    | "Unsigned" => some ("Unsigned", pPromotionInteger)
    | "AbstractFloat" => some ("AbstractFloat", pPromotionReal)
    | "Bool" => some ("Bool", pPromotionInteger)
    | "Int8" | "Int16" | "Int32" | "Int64" | "Int128" => some (n.name, pPromotionSigned)
    | "UInt8" | "UInt16" | "UInt32" | "UInt64" | "UInt128" => some (n.name, pPromotionUnsigned)
    | "Float16" | "Float32" | "Float64" => some (n.name, pPromotionAbstractFloat)
    | _ => none
  else none

theorem nominal_primitive (a : PrimitiveType) : Nominal primitiveEnv (primitivePType a) := by
  have hNumber : Nominal primitiveEnv pPromotionNumber :=
    .data (by decide) (by decide) rfl .any
  have hReal : Nominal primitiveEnv pPromotionReal := .data (by decide) (by decide) rfl hNumber
  have hInteger : Nominal primitiveEnv pPromotionInteger :=
    .data (by decide) (by decide) rfl hReal
  cases a with
  | bool => exact .data (by decide) (by decide) rfl hInteger
  | int t =>
      cases t <;> exact .data (by decide) (by decide) rfl
        (.data (by decide) (by decide) rfl hInteger)
  | float t =>
      cases t <;> exact .data (by decide) (by decide) rfl
        (.data (by decide) (by decide) rfl hReal)

/-- For every pair of primitive numeric types, `typejoin` returns their closest common ancestor
in the numeric hierarchy (`Bool`, `Signed`, `Unsigned` below `Integer`; `Integer` and
`AbstractFloat` below `Real`; `Real` below `Number`). -/
def TypejoinPrimitiveUpperBound : Prop :=
  ∀ a b : PrimitiveType, ∃ r, typejoin (primitivePType a) (primitivePType b) = some r ∧
    pSubtype (primitivePType a) r = true ∧ pSubtype (primitivePType b) r = true ∧
    ∀ c, Nominal primitiveEnv c → pSubtype (primitivePType a) c = true →
      pSubtype (primitivePType b) c = true → pSubtype r c = true

theorem typejoinPrimitiveUpperBound_proven : TypejoinPrimitiveUpperBound := fun a b =>
  typejoinClosestCommonAncestor_proven primitiveEnv _ _ (.leaf (nominal_primitive a))
    (.leaf (nominal_primitive b))

/-! ## Value promotion -/

theorem jlPartial_throw_bind {α β : Type} (e : JlError) (f : α → JlPartial β) :
    ((throw e : JlPartial α) >>= f) = throw e := rfl

theorem jlPartial_bind_eq_pure {α β : Type} {ma : JlPartial α} {f : α → JlPartial β} {b : β}
    (h : ma >>= f = pure b) : ∃ a, ma = pure a ∧ f a = pure b := by
  have key : ∀ r : Option (Except JlError α), (ExceptT.mk r >>= f) = pure b →
      ∃ a, ExceptT.mk r = pure a ∧ f a = pure b := by
    intro r hr
    match r, hr with
    | some (.ok a), hr => exact ⟨a, rfl, hr⟩
    | some (.error _), hr => cases hr
    | none, hr => cases hr
  exact key ma.run h

theorem jlPartial_pure_inj {α : Type} {a b : α} (h : (pure a : JlPartial α) = pure b) :
    a = b := by
  cases h
  rfl

theorem promoteTypeValue_eq (u : PType → PType → Option PType) {T S R : PType}
    (h : promoteType u T S = some R) : promoteTypeValue u T S = pure R := by
  show ExceptT.lift (promoteType u T S) = _
  rw [h]
  rfl

theorem promoteTypeValue_three (u : PType → PType → Option PType) {T S U R : PType}
    (h : promoteTypeThree (promoteType u) T S U = some R) :
    promoteTypeThree (promoteTypeValue u) T S U = pure R := by
  rw [promoteTypeThree] at h ⊢
  cases hTS : promoteType u T S with
  | none =>
      rw [hTS] at h
      cases h
  | some V =>
      rw [hTS] at h
      have hV : promoteType u V U = some R := h
      rw [promoteTypeValue_eq u hTS, pure_bind]
      exact promoteTypeValue_eq u hV

theorem promoteTypeofRest_fold {m : Type → Type} [Monad m] [LawfulMonad m] {ι : Type}
    {V : ι → Type} (typeOf : Sigma V → PType) (P : PType → PType → m PType) (x y : Sigma V)
    (zs : List (Sigma V)) :
    promoteTypeofRest typeOf P x y zs =
      P (typeOf x) (typeOf y) >>= fun R => zs.foldlM (fun acc v => P acc (typeOf v)) R := by
  match zs with
  | [] => simp [promoteTypeofRest, promoteTypeofTwo]
  | [z] => simp [promoteTypeofRest, promoteTypeofThree, promoteTypeThree]
  | z :: w :: rest =>
      simp [promoteTypeofRest, promoteTypeofMany, promoteTypeofThree, promoteTypeThree]

/-- `promote` raises the documented error when conversion changes no argument's type: for
same-typed values whose conversion to their own type is the identity, and, on runtime values,
exactly when every converted value keeps its runtime type. -/
def PromoteNoChangeErrors : Prop :=
  (∀ {α : Type} (u : PType → PType → Option PType) (typeOf : α → PType)
      (convert : PType → α → JlPartial α)
      (map : (α → String) → (α × α) → List String) (typeName : α → String)
      (join : List String → String → String → String) (error : String → JlError) (x y : α),
    typeOf x = typeOf y →
    convert (typeOf x) x = pure x → convert (typeOf y) y = pure y →
    promoteTwoValues
      (promotePairValues (promoteTypeofTwo typeOf typeOf (promoteTypeValue u)) convert convert)
      (notSameTypeEqual (sametypeError map typeName join error)) x y =
      throw (error ("promotion of types " ++ join (map typeName (x, y)) ", " " and " ++
        " failed to change any arguments"))) ∧
  (∀ {ι : Type} {V : ι → Type} (u : PType → PType → Option PType)
      (typeOf : Sigma V → PType) (convert : PType → Sigma V → JlPartial (Sigma V))
      (map : (Sigma V → String) → (Sigma V × Sigma V) → List String)
      (typeName : Sigma V → String) (join : List String → String → String → String)
      (error : String → JlError) (x y px py : Sigma V) (R : PType),
    promoteType u (typeOf x) (typeOf y) = some R →
    convert R x = pure px → convert R y = pure py →
    promoteTwoValues
      (promotePairValues (promoteTypeofTwo typeOf typeOf (promoteTypeValue u)) convert convert)
      (notSameTypePairDispatch typeOf (sametypeError map typeName join error)) x y =
      if pEqual (typeOf x) (typeOf px) && pEqual (typeOf y) (typeOf py) then
        throw (error ("promotion of types " ++ join (map typeName (x, y)) ", " " and " ++
          " failed to change any arguments"))
      else pure (px, py))

theorem promoteNoChangeErrors_proven : PromoteNoChangeErrors := by
  refine ⟨?_, ?_⟩
  · intro α u typeOf convert map typeName join error x y hT hx hy
    have hR : promoteTypeofTwo typeOf typeOf (promoteTypeValue u) x y = pure (typeOf x) := by
      rw [promoteTypeofTwo, ← hT]
      exact promoteTypeValue_eq u (promoteType_self u (typeOf x))
    rw [← hT] at hy
    simp only [promoteTwoValues, promotePairValues, hR, pure_bind, hx, hy, notSameTypeEqual,
      sametypeError]
    rfl
  · intro ι V u typeOf convert map typeName join error x y px py R hR hx hy
    have hRv : promoteTypeofTwo typeOf typeOf (promoteTypeValue u) x y = pure R :=
      promoteTypeValue_eq u hR
    simp only [promoteTwoValues, promotePairValues, hRv, pure_bind, hx, hy]
    by_cases h : (pEqual (typeOf x) (typeOf px) && pEqual (typeOf y) (typeOf py)) = true
    · simp only [notSameTypePairDispatch, h, if_true, notSameTypeEqual, sametypeError]
      rfl
    · simp only [Bool.not_eq_true] at h
      simp only [notSameTypePairDispatch, h, Bool.false_eq_true, if_false, notSameTypeDifferent,
        pure_bind]

/-- `promote(x, y)` returns both values converted to `promote_type(typeof(x), typeof(y))`
whenever conversion changes some argument's type; that type is the one a promotion rule names,
even a rule defined in one direction only. -/
def PromotePairCommonType : Prop :=
  ∀ {ι : Type} {V : ι → Type} (u : PType → PType → Option PType)
      (typeOf : Sigma V → PType) (convert : PType → Sigma V → JlPartial (Sigma V))
      (map : (Sigma V → String) → (Sigma V × Sigma V) → List String)
      (typeName : Sigma V → String) (join : List String → String → String → String)
      (error : String → JlError) (x y px py : Sigma V),
    (pEqual (typeOf x) (typeOf px) && pEqual (typeOf y) (typeOf py)) = false →
    (∀ R : PType, promoteType u (typeOf x) (typeOf y) = some R →
      convert R x = pure px → convert R y = pure py →
      promoteTwoValues
        (promotePairValues (promoteTypeofTwo typeOf typeOf (promoteTypeValue u)) convert convert)
        (notSameTypePairDispatch typeOf (sametypeError map typeName join error)) x y =
        pure (px, py)) ∧
    (∀ R : PType, typeOf x ≠ .bottom → typeOf y ≠ .bottom → R ≠ .bottom →
      pEqual (typeOf x) (typeOf y) = false →
      pIsType (typeOf x) = true → pIsType (typeOf y) = true →
      u (typeOf x) (typeOf y) = some R → u (typeOf y) (typeOf x) = none →
      convert R x = pure px → convert R y = pure py →
      promoteTwoValues
        (promotePairValues (promoteTypeofTwo typeOf typeOf (promoteTypeValue u)) convert convert)
        (notSameTypePairDispatch typeOf (sametypeError map typeName join error)) x y =
        pure (px, py))

theorem promotePairCommonType_proven : PromotePairCommonType := by
  intro ι V u typeOf convert map typeName join error x y px py hdiff
  have hbase : ∀ R : PType, promoteType u (typeOf x) (typeOf y) = some R →
      convert R x = pure px → convert R y = pure py →
      promoteTwoValues
        (promotePairValues (promoteTypeofTwo typeOf typeOf (promoteTypeValue u)) convert convert)
        (notSameTypePairDispatch typeOf (sametypeError map typeName join error)) x y =
        pure (px, py) := by
    intro R hR hx hy
    rw [promoteNoChangeErrors_proven.2 u typeOf convert map typeName join error x y px py R
      hR hx hy, hdiff]
    rfl
  refine ⟨hbase, ?_⟩
  intro R hT hS hR hTS hTt hSt h1 h2 hx hy
  exact hbase R (promoteType_rule_forward u hT hS hR hTS hTt hSt (Or.inl ⟨h1, Or.inl h2⟩)) hx hy

/-- `promote(x, y, z)` converts the three values to `promote_typeof(x, y, z)` and returns them,
unless no value's type changed, in which case it raises the same-type promotion error. -/
def PromoteTripleCommonType : Prop :=
  ∀ {ι : Type} {V : ι → Type} (u : PType → PType → Option PType)
      (typeOf : Sigma V → PType) (convert : PType → Sigma V → JlPartial (Sigma V))
      (map : (Sigma V → String) → (Sigma V × Sigma V × Sigma V) → List String)
      (typeName : Sigma V → String) (join : List String → String → String → String)
      (error : String → JlError) (x y z px py pz : Sigma V) (R : PType),
    promoteTypeThree (promoteType u) (typeOf x) (typeOf y) (typeOf z) = some R →
    convert R x = pure px → convert R y = pure py → convert R z = pure pz →
    promoteThreeValues
      (promoteTripleValues (promoteTypeofThree typeOf typeOf typeOf (promoteTypeValue u))
        convert convert convert)
      (notSameTypeTripleDispatch typeOf (sametypeError map typeName join error)) x y z =
      if pEqual (typeOf x) (typeOf px) && pEqual (typeOf y) (typeOf py) &&
          pEqual (typeOf z) (typeOf pz) then
        throw (error ("promotion of types " ++ join (map typeName (x, y, z)) ", " " and " ++
          " failed to change any arguments"))
      else pure (px, py, pz)

theorem promoteTripleCommonType_proven : PromoteTripleCommonType := by
  intro ι V u typeOf convert map typeName join error x y z px py pz R hR hx hy hz
  have hRv : promoteTypeofThree typeOf typeOf typeOf (promoteTypeValue u) x y z = pure R :=
    promoteTypeValue_three u hR
  simp only [promoteThreeValues, promoteTripleValues, hRv, pure_bind, hx, hy, hz]
  by_cases h : (pEqual (typeOf x) (typeOf px) && pEqual (typeOf y) (typeOf py) &&
      pEqual (typeOf z) (typeOf pz)) = true
  · simp only [notSameTypeTripleDispatch, h, if_true, notSameTypeEqual, sametypeError]
    rfl
  · simp only [Bool.not_eq_true] at h
    simp only [notSameTypeTripleDispatch, h, Bool.false_eq_true, if_false, notSameTypeDifferent,
      pure_bind]

theorem primitivePromoteTypeValue_table (a b : PrimitiveType) :
    primitivePromoteTypeValue (primitivePType a) (primitivePType b) =
      pure (primitivePType (primitiveExpected a b)) :=
  promoteTypeValue_eq primitivePromoteRule (promoteTypeTable_proven a b)

theorem primitivePromoteTypeValue_fold (init : PrimitiveType) (rest : List PrimitiveInput) :
    rest.foldlM (fun acc v => primitivePromoteTypeValue acc (primitiveInputType v))
        (primitivePType init) =
      pure (primitivePType (rest.foldl (fun acc v => primitiveExpected acc v.1) init)) := by
  induction rest generalizing init with
  | nil => rfl
  | cons v rest ih =>
      simp only [List.foldlM_cons, List.foldl_cons, primitiveInputType,
        primitivePromoteTypeValue_table, pure_bind]
      exact ih _

/-- `_promote(x, y, zs...)` converts every value, of whatever type, to the one type
`R = promote_typeof(x, y, zs...)` (given the documented `convert`: a converted value has the
target type, and a tuple converted to `Tuple{Vararg{R}}` keeps its length), and for numbers
`promote_typeof` returns the promotion table folded over the values' types from left to
right. -/
def PromoteRestConversions : Prop :=
  (∀ {ι : Type} {V : ι → Type} (u : PType → PType → Option PType)
      (typeOf : Sigma V → PType) (convert : PType → Sigma V → JlPartial (Sigma V))
      (convertTuple : PType → List (Sigma V) → JlPartial (List (Sigma V))),
    (∀ T v w, convert T v = pure w → pSubtype (typeOf w) T = true) →
    (∀ T vs ws,
      convertTuple (.data tupleTypeName "Tuple" [.vararg T .open] (some .any)) vs = pure ws →
        ws.length = vs.length ∧ ∀ w ∈ ws, pSubtype (typeOf w) T = true) →
    ∀ (x y : Sigma V) (zs : List (Sigma V)) (R : PType) (px py : Sigma V)
      (pzs : List (Sigma V)),
      promoteTypeofRest typeOf (promoteTypeValue u) x y zs = pure R →
      promoteRestValues (promoteTypeofRest typeOf (promoteTypeValue u)) convert convert
        convertTuple x y zs = pure ((px, py), pzs) →
      pSubtype (typeOf px) R = true ∧ pSubtype (typeOf py) R = true ∧
        pzs.length = zs.length ∧ ∀ w ∈ pzs, pSubtype (typeOf w) R = true) ∧
  (∀ (x y : PrimitiveInput) (zs : List PrimitiveInput),
    promoteTypeofRest primitiveInputType primitivePromoteTypeValue x y zs =
      pure (primitivePType (zs.foldl (fun acc v => primitiveExpected acc v.1)
        (primitiveExpected x.1 y.1))))

theorem promoteRestConversions_proven : PromoteRestConversions := by
  refine ⟨?_, ?_⟩
  · intro ι V u typeOf convert convertTuple hconv htuple x y zs R px py pzs hR hres
    simp only [promoteRestValues, hR, pure_bind] at hres
    obtain ⟨a, ha, hres⟩ := jlPartial_bind_eq_pure hres
    obtain ⟨b, hb, hres⟩ := jlPartial_bind_eq_pure hres
    obtain ⟨cs, hcs, hres⟩ := jlPartial_bind_eq_pure hres
    have heq := jlPartial_pure_inj hres
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
    obtain ⟨hlen, hall⟩ := htuple R zs cs hcs
    exact ⟨hconv R x a ha, hconv R y b hb, hlen, hall⟩
  · intro x y zs
    rw [promoteTypeofRest_fold]
    simp only [primitiveInputType, primitivePromoteTypeValue_table, pure_bind]
    exact primitivePromoteTypeValue_fold _ zs

/-- Values that all have one type `T` are returned unchanged by `promote`: the generic
conversion path converts them to `promote_typeof(...) == T`, which the identity conversion
leaves alone, and the specialised `promote(x::T, y::T, zs::T...)` returns them as given;
`promote()` and `promote(x)` return their (zero or one) arguments. -/
def PromoteSameTypeIdentity : Prop :=
  ∀ {ι : Type} {V : ι → Type} (u : PType → PType → Option PType)
      (typeOf : Sigma V → PType) (convert : PType → Sigma V → JlPartial (Sigma V))
      (convertTuple : PType → List (Sigma V) → JlPartial (List (Sigma V)))
      (T : PType) (x y : Sigma V) (zs : List (Sigma V)),
    typeOf x = T → typeOf y = T → (∀ z ∈ zs, typeOf z = T) →
    (∀ v, typeOf v = T → convert T v = pure v) →
    convertTuple (.data tupleTypeName "Tuple" [.vararg T .open] (some .any)) zs = pure zs →
    promoteRestValues (promoteTypeofRest typeOf (promoteTypeValue u)) convert convert
      convertTuple x y zs = pure ((x, y), zs) ∧
    promoteSameType x y zs = x :: y :: zs ∧
    (promoteEmpty : List (Sigma V)) = [] ∧
    promoteSingle x = [x]

theorem promoteSameTypeIdentity_proven : PromoteSameTypeIdentity := by
  intro ι V u typeOf convert convertTuple T x y zs hx hy hzs hconv htuple
  have hself : ∀ S, promoteTypeValue u S S = pure S := fun S =>
    promoteTypeValue_eq u (promoteType_self u S)
  have hfold : ∀ ws : List (Sigma V), (∀ w ∈ ws, typeOf w = T) →
      ws.foldlM (fun acc v => promoteTypeValue u acc (typeOf v)) T = pure T := by
    intro ws hws
    induction ws with
    | nil => rfl
    | cons w ws ih =>
        simp only [List.foldlM_cons, hws w (List.mem_cons_self ..), hself, pure_bind]
        exact ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
  have hR : promoteTypeofRest typeOf (promoteTypeValue u) x y zs = pure T := by
    rw [promoteTypeofRest_fold, hx, hy, hself, pure_bind]
    exact hfold zs hzs
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [promoteRestValues, hR, pure_bind, hconv x hx, hconv y hy, htuple]

/-! ## Arithmetic methods -/

/-- `muladd(a, b, c)` returns the promoted `c` when `a` or `b` is `false` (a strong zero), and
otherwise calls `muladd` on the promoted values. -/
def MuladdFalseStrongZero : Prop :=
  ∀ {r : PrimitiveType}
      (convert : PType → PrimitiveInput → JlPartial (primitiveValueType r))
      (muladd : primitiveValueType r → primitiveValueType r → primitiveValueType r →
        JlPartial (primitiveValueType r))
      (a b c : PrimitiveInput) (pa pb pc : primitiveValueType r),
    promoteTripleValues
      (promoteTypeofThree primitiveInputType primitiveInputType primitiveInputType
        primitivePromoteTypeValue)
      convert convert convert a b c = pure (pa, pb, pc) →
    ((a = ⟨.bool, false⟩ ∨ b = ⟨.bool, false⟩) →
      muladdNumber
        (promoteTripleValues
          (promoteTypeofThree primitiveInputType primitiveInputType primitiveInputType
            primitivePromoteTypeValue)
          convert convert convert)
        muladd primitiveEgalFalse primitiveEgalFalse a b c = pure pc) ∧
    (a ≠ ⟨.bool, false⟩ → b ≠ ⟨.bool, false⟩ →
      muladdNumber
        (promoteTripleValues
          (promoteTypeofThree primitiveInputType primitiveInputType primitiveInputType
            primitivePromoteTypeValue)
          convert convert convert)
        muladd primitiveEgalFalse primitiveEgalFalse a b c = muladd pa pb pc)

theorem primitiveEgalFalse_eq (v : PrimitiveInput) :
    primitiveEgalFalse v = true ↔ v = ⟨.bool, false⟩ := by
  rcases v with ⟨t, w⟩
  cases t with
  | bool => cases w <;> simp [primitiveEgalFalse] <;> (intro h; cases h)
  | int t => simp [primitiveEgalFalse]; intro h; cases h
  | float t => simp [primitiveEgalFalse]; intro h; cases h

theorem muladdFalseStrongZero_proven : MuladdFalseStrongZero := by
  intro r convert muladd a b c pa pb pc hp
  constructor
  · intro hFalse
    have hor : (primitiveEgalFalse a || primitiveEgalFalse b) = true := by
      rcases hFalse with h | h
      · simp [(primitiveEgalFalse_eq a).2 h]
      · simp [(primitiveEgalFalse_eq b).2 h]
    simp only [muladdNumber, hp, pure_bind, hor, if_true]
  · intro ha hb
    have hna : primitiveEgalFalse a = false := by
      cases h : primitiveEgalFalse a
      · rfl
      · exact absurd ((primitiveEgalFalse_eq a).1 h) ha
    have hnb : primitiveEgalFalse b = false := by
      cases h : primitiveEgalFalse b
      · rfl
      · exact absurd ((primitiveEgalFalse_eq b).1 h) hb
    simp only [muladdNumber, hp, pure_bind, hna, hnb, Bool.or_false, Bool.false_eq_true,
      if_false]


/-- `ArgsIsa typeOf args S`: the arguments `args` have runtime types below `S`, elementwise. -/
inductive ArgsIsa {Val : Type} (typeOf : Val → PType) : List Val → List PType → Prop
  | nil : ArgsIsa typeOf [] []
  | cons {a : Val} {as : List Val} {s : PType} {ss : List PType} :
      pSubtype (typeOf a) s = true → ArgsIsa typeOf as ss → ArgsIsa typeOf (a :: as) (s :: ss)

theorem argsIsa_mem_right {Val : Type} {typeOf : Val → PType} :
    ∀ {l1 : List Val} {l2 : List PType}, ArgsIsa typeOf l1 l2 → ∀ {b : PType}, b ∈ l2 →
      ∃ a ∈ l1, pSubtype (typeOf a) b = true
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hr hrest, _, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, List.mem_cons_self .., hr⟩
      · obtain ⟨a, ha, hab⟩ := argsIsa_mem_right hrest h
        exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- promote_op docstring: the type `R` that `promote_op(f, S...)` returns satisfies
`f(args...) isa R` for all `args isa S`, given that inference (`_return_type`) bounds the
result type of `f` on every argument tuple of the given types, and that runtime types are
`DataType`s (so no value has type `Union{}`). -/
def PromoteOpBehavior : Prop :=
  ∀ {α Val : Type} (returnType : α → PType → PType) (call : α → List Val → Val)
      (typeOf : Val → PType) (f : α) (S : List PType),
    (∀ v, ∃ n w ps sup, typeOf v = .data n w ps sup) →
    (∀ (args : List Val) (Ts : List PType), ArgsIsa typeOf args Ts →
      pSubtype (typeOf (call f args))
        (returnType f (.data tupleTypeName "Tuple" Ts (some .any))) = true) →
    ∀ args : List Val, ArgsIsa typeOf args S →
      pSubtype (typeOf (call f args)) (promoteOp tupleOrBottom returnType f S) = true

theorem promoteOpBehavior_proven : PromoteOpBehavior := by
  intro α Val returnType call typeOf f S hdata hlaw args hargs
  by_cases hb : S.any pIsBottom = true
  · exfalso
    obtain ⟨s, hs, hsb⟩ := List.any_eq_true.1 hb
    cases s with
    | bottom =>
        obtain ⟨a, _, hab⟩ := argsIsa_mem_right hargs hs
        obtain ⟨n, w, ps, sup, he⟩ := hdata a
        rw [he] at hab
        simp [pSubtype, pEqual] at hab
    | _ => simp [pIsBottom] at hsb
  · have hf : S.any pIsBottom = false := by simpa using hb
    simp only [promoteOp, tupleOrBottom, hf, Bool.false_eq_true, if_false]
    exact hlaw args S hargs

/-- For integers, the `fma` and `muladd` fallbacks compute `x*y + z` with the integer
operations, which wrap modulo the width. -/
def IntegerFmaMuladd : Prop :=
  ∀ (t : IntTy) (x y z : JInt t),
    (fmaIntegerFallback JuliaLean.base.int.mul JuliaLean.base.int.add x y z).val =
      wrapInt t (x.val * y.val + z.val) ∧
    (muladdFallback JuliaLean.base.int.mul JuliaLean.base.int.add x y z).val =
      wrapInt t (x.val * y.val + z.val)

theorem integerFmaMuladd_proven : IntegerFmaMuladd := by
  intro t x y z
  have h : (JuliaLean.base.int.add (JuliaLean.base.int.mul x y) z).val =
      wrapInt t (x.val * y.val + z.val) := by
    simp only [JuliaLean.base.int.add, JuliaLean.base.int.mul]
    rw [JuliaLean.Proofs.base.int.add_int_val, JuliaLean.Proofs.base.int.mul_int_val,
      JuliaLean.Proofs.base.int.wrapInt_add_left]
  exact ⟨h, h⟩

theorem ltSame_eq {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.ltSame x y = decide (x.val < y.val) := by
  unfold JuliaLean.base.int.ltSame
  cases h : t.signed
  · simp [JuliaLean.base.int.lt_BitUnsigned, JuliaLean.Proofs.base.int.ult_int_eq h]
  · simp [JuliaLean.base.int.lt_BitSigned, JuliaLean.Proofs.base.int.slt_int_eq h]

/-- On a `Real` type without its own methods (the integers), `==` is identity, `<=` is
`==` or `<`, `max`/`min`/`minmax` select the greater, the lesser and the ordered pair, and the
one-argument forms agree with the two-argument forms on `(x, x)`. -/
def RealOrderFallbacks : Prop :=
  ∀ (t : IntTy) (identical : JInt t → JInt t → Bool),
    (∀ a b, identical a b = true ↔ a = b) →
    ∀ x y : JInt t,
      equalFallback identical x y = .ok (decide (x.val = y.val)) ∧
      lessEqualFallback (equalFallback identical)
        (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y = .ok (decide (x.val ≤ y.val)) ∧
      (maxSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y).map Subtype.val =
        .ok (max x.val y.val) ∧
      (minSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y).map Subtype.val =
        .ok (min x.val y.val) ∧
      (minmaxSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y).map
        (fun p => (p.1.val, p.2.val)) = .ok (min x.val y.val, max x.val y.val) ∧
      maxSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x x = .ok (maxUnary x) ∧
      minSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x x = .ok (minUnary x) ∧
      minmaxSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x x =
        .ok (minmaxUnary x)

theorem realOrderFallbacks_proven : RealOrderFallbacks := by
  intro t identical hid x y
  have hxy : identical x y = decide (x.val = y.val) := by
    by_cases h : x.val = y.val
    · have : x = y := Subtype.ext h
      simp [h, (hid x y).2 this]
    · have : identical x y = false := by
        cases hb : identical x y
        · rfl
        · exact absurd (congrArg Subtype.val ((hid x y).1 hb)) h
      simp [h, this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [equalFallback, hxy]; rfl
  · simp only [lessEqualFallback, equalFallback, hxy, ltSame_eq]
    by_cases h1 : x.val = y.val
    · have h2 : x.val ≤ y.val := by omega
      simp [h1, h2]; rfl
    · by_cases h3 : x.val < y.val
      · have h2 : x.val ≤ y.val := by omega
        simp [h1, h3, h2]; rfl
      · have h2 : ¬ x.val ≤ y.val := by omega
        simp [h1, h3, h2]; rfl
  · have hm : maxSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y =
        .ok (if decide (y.val < x.val) then x else y) := by
      simp only [maxSameType, ltSame_eq]; rfl
    rw [hm]
    by_cases h : y.val < x.val
    · simp only [h, decide_true, if_true]
      show Except.ok x.val = Except.ok (max x.val y.val)
      rw [Int.max_def, if_neg (by omega)]
    · simp only [h, decide_false, Bool.false_eq_true, if_false]
      show Except.ok y.val = Except.ok (max x.val y.val)
      rw [Int.max_def, if_pos (by omega)]
  · have hm : minSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y =
        .ok (if decide (y.val < x.val) then y else x) := by
      simp only [minSameType, ltSame_eq]; rfl
    rw [hm]
    by_cases h : y.val < x.val
    · simp only [h, decide_true, if_true]
      show Except.ok y.val = Except.ok (min x.val y.val)
      rw [Int.min_def, if_neg (by omega)]
    · simp only [h, decide_false, Bool.false_eq_true, if_false]
      show Except.ok x.val = Except.ok (min x.val y.val)
      rw [Int.min_def, if_pos (by omega)]
  · have hm : minmaxSameType (fun a b => pure (JuliaLean.base.int.ltSame a b)) x y =
        .ok (if decide (y.val < x.val) then (y, x) else (x, y)) := by
      simp only [minmaxSameType, ltSame_eq]; rfl
    rw [hm]
    by_cases h : y.val < x.val
    · simp only [h, decide_true, if_true]
      show Except.ok (y.val, x.val) = Except.ok (min x.val y.val, max x.val y.val)
      rw [Int.min_def, Int.max_def, if_neg (by omega), if_neg (by omega)]
    · simp only [h, decide_false, Bool.false_eq_true, if_false]
      show Except.ok (x.val, y.val) = Except.ok (min x.val y.val, max x.val y.val)
      rw [Int.min_def, Int.max_def, if_pos (by omega), if_pos (by omega)]
  · simp [maxSameType, maxUnary, ltSame_eq]; rfl
  · simp [minSameType, minUnary, ltSame_eq]; rfl
  · simp [minmaxSameType, minmaxUnary, ltSame_eq]; rfl

def NumericFallbackErrors : Prop :=
  ∀ (α β : Type) (typeName : α → String) (error : String → β) (T : α),
    plusFallback (noOpErr typeName error) T = error ("+ not defined for " ++ typeName T) ∧
    timesFallback (noOpErr typeName error) T = error ("* not defined for " ++ typeName T) ∧
    minusFallback (noOpErr typeName error) T = error ("- not defined for " ++ typeName T) ∧
    divideFallback (noOpErr typeName error) T = error ("/ not defined for " ++ typeName T) ∧
    powerFallback (noOpErr typeName error) T = error ("^ not defined for " ++ typeName T) ∧
    fmaFallback (noOpErr typeName error) T = error ("fma not defined for " ++ typeName T) ∧
    andFallback (noOpErr typeName error) T = error ("& not defined for " ++ typeName T) ∧
    orFallback (noOpErr typeName error) T = error ("| not defined for " ++ typeName T) ∧
    xorFallback (noOpErr typeName error) T = error ("xor not defined for " ++ typeName T) ∧
    lessFallback (noOpErr typeName error) T = error ("< not defined for " ++ typeName T) ∧
    remFallback (noOpErr typeName error) T = error ("rem not defined for " ++ typeName T) ∧
    modFallback (noOpErr typeName error) T = error ("mod not defined for " ++ typeName T) ∧
    flipsignFallback (noOpErr typeName error) T = error ("flipsign not defined for " ++ typeName T)

theorem numericFallbackErrors_proven : NumericFallbackErrors := by
  intro α β typeName error T
  simp [plusFallback, timesFallback, minusFallback, divideFallback,
    powerFallback, fmaFallback, andFallback, orFallback, xorFallback,
    lessFallback, remFallback, modFallback, flipsignFallback, noOpErr]

/-! ## Registry -/

def entries : List Entry := [
  { id := "promotion-promote-type-table", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{S})", "promote_result(::Type,::Type,::Type{T},::Type{S})"]
    statement := "For primitive numeric types, promote_type returns the documented Boolean, integer-width, and Float16/32/64 promotion table type in either argument order."
    source := "manual: Conversion and Promotion; base/bool.jl:6; base/int.jl:809-822; base/float.jl:243-263,477-479; base/promotion.jl:331-366"
    status := .proven, prop := ``PromoteTypeTable, thm := some ``promoteTypeTable_proven },
  { id := "promotion-promote-type-symmetric", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{S})"]
    statement := "For every pair of primitive numeric types, promote_type returns the same type when the arguments are reversed."
    source := "manual: Conversion and Promotion; base/promotion.jl:336-366"
    status := .proven, prop := ``PromoteTypeSymmetric, thm := some ``promoteTypeSymmetric_proven },
  { id := "promotion-promote-type-identities", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{Bottom}, ::Type{Bottom})", "promote_type(::Type{T}, ::Type{T})", "promote_type(::Type{T}, ::Type{Bottom})", "promote_type(::Type{Bottom}, ::Type{T})"]
    statement := "For any promotion rules, promote_type returns: Union{} is an identity and every type promotes with itself to itself."
    source := "manual: Conversion and Promotion; base/promotion.jl:331-334"
    status := .proven, prop := ``PromoteTypeIdentities, thm := some ``promoteTypeIdentities_proven },
  { id := "promotion-promote-rule-bottom-identities", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_rule(::Type, ::Type)", "promote_rule(::Type{Bottom}, slurp...)", "promote_rule(::Type{Bottom}, ::Type{Bottom}, slurp...)", "promote_rule(::Type{Bottom}, ::Type{T}, slurp...)", "promote_rule(::Type{T}, ::Type{Bottom}, slurp...)"]
    statement := "The promote_rule methods for Union{} return the other type (Union{} when both are Union{}) whatever arguments are slurped, and without a defined rule promote_rule returns Union{}."
    source := "base/promotion.jl:355-361"
    status := .proven, prop := ``PromoteRuleBottomIdentities, thm := some ``promoteRuleBottomIdentities_proven },
  { id := "promotion-promote-type-nary-table", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type()", "promote_type(T)", "promote_type(T, S, U)", "promote_type(T, S, U, V...)"]
    statement := "Zero promotion types give Union{}, one type is unchanged, n-ary primitive promotion returns the pairwise table applied from left to right, and for any rules, further arguments equal to the first type or Union{} leave it unchanged."
    source := "manual: Conversion and Promotion; base/promotion.jl:326-329"
    status := .proven, prop := ``PromoteTypeNaryTable, thm := some ``promoteTypeNaryTable_proven },
  { id := "promotion-promote-common-type-values", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote(x::T, y::S)", "promote(x, y)", "not_sametype(x, y)", "promote_typeof(x, y)"]
    statement := "When conversion changes some argument's type, promote(x, y) returns both values converted to promote_type(typeof(x), typeof(y)), which is the type named by a promotion rule defined in either direction."
    source := "manual: Conversion and Promotion; promote docstring; base/promotion.jl:397-403,423-428,445"
    status := .proven, prop := ``PromotePairCommonType, thm := some ``promotePairCommonType_proven },
  { id := "promotion-promote-nochange-error", juliaFile := "base/promotion.jl"
    juliaFns := ["promote(x, y)", "not_sametype(x::T, y::T)", "not_sametype(x, y)", "sametype_error(input)"]
    statement := "promote raises the 'promotion of types ... failed to change any arguments' error exactly when conversion leaves every argument's type unchanged."
    source := "promote docstring; base/promotion.jl:423-428,443-452"
    status := .proven, prop := ``PromoteNoChangeErrors, thm := some ``promoteNoChangeErrors_proven },
  { id := "promotion-promote-triple-common-type", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote(x, y, z)", "promote(x, y, z)", "not_sametype(x::T, y::T)", "not_sametype(x, y)", "promote_typeof(x, y, z)"]
    statement := "promote(x, y, z) returns the three values converted to promote_type of their three types, or raises the same-type promotion error when no value's type changed."
    source := "manual: Conversion and Promotion; base/promotion.jl:404-410,429-434,445"
    status := .proven, prop := ``PromoteTripleCommonType, thm := some ``promoteTripleCommonType_proven },
  { id := "promotion-promote-rest-conversions", juliaFile := "base/promotion.jl"
    juliaFns := ["_promote(x, y, zs...)", "promote_typeof(x, y, z, a...)", "promote_typeof(x, y, z)", "promote_typeof(x, y)"]
    statement := "_promote(x, y, zs...) converts every value, of any type, to the one type R = promote_typeof(x, y, zs...), given that convert returns values of its target type; for numbers, promote_typeof returns the promotion table folded over the values' types from left to right."
    source := "manual: Conversion and Promotion; promote and convert docstrings; base/promotion.jl:403-405,411-415"
    status := .proven, prop := ``PromoteRestConversions, thm := some ``promoteRestConversions_proven },
  { id := "promotion-promote-same-type-identity", juliaFile := "base/promotion.jl"
    juliaFns := ["promote()", "promote(x)", "promote(x::T, y::T, zs::T...)", "_promote(x, y, zs...)"]
    statement := "Values that already share one type are returned unchanged by promote, by the generic conversion path and by the same-type method alike."
    source := "promote docstring; base/promotion.jl:411-415,420-421,441"
    status := .proven, prop := ``PromoteSameTypeIdentity, thm := some ``promoteSameTypeIdentity_proven },
  { id := "promotion-promote-type-user-rules", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{S})", "promote_result(::Type,::Type,::Type{T},::Type{S})", "promote_rule(::Type{T}, ::Type{Bottom}, slurp...)"]
    statement := "A promotion rule defined in one direction (or in both, agreeing) determines promote_type in either argument order."
    source := "manual: Conversion and Promotion (promotion rules); promote_type docstring; base/promotion.jl:336-363"
    status := .proven, prop := ``PromoteTypeUserRules, thm := some ``promoteTypeUserRules_proven },
  { id := "promotion-promote-typejoin-fallback", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_type(::Type{T}, ::Type{S})", "promote_rule(::Type, ::Type)", "promote_result(::Type{T},::Type{S},::Type{Bottom},::Type{Bottom})", "typejoin(a, b)"]
    statement := "When no promotion rule names a type in either direction, promote_type falls back to typejoin of the two types, and on declared types and their unions it returns."
    source := "base/promotion.jl:355-366 (source comment)"
    status := .proven, prop := ``PromoteTypeFallback, thm := some ``promoteTypeFallback_proven },
  { id := "promotion-typejoin-closest-common-ancestor", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin(a, b)", "_has_ancestor_typename(a, name)"]
    statement := "On declared parameterless types and their unions (each type name declared once), typejoin(T, S) returns a supertype of both that is a subtype of every declared common supertype: their closest common ancestor."
    source := "typejoin docstring; base/promotion.jl:25-35,37-160"
    status := .proven, prop := ``TypejoinClosestCommonAncestor, thm := some ``typejoinClosestCommonAncestor_proven },
  { id := "promotion-typejoin-idempotent", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin()", "typejoin(t)", "typejoin(a, b)"]
    statement := "typejoin of zero inputs is Union{}, one input is unchanged, and typejoin returns every type other than a type variable when joined with itself."
    source := "typejoin docstring; base/promotion.jl:20-21,37-57"
    status := .proven, prop := ``TypejoinIdempotent, thm := some ``typejoinIdempotent_proven },
  { id := "promotion-typejoin-primitive-upper-bound", juliaFile := "base/promotion.jl"
    juliaFns := ["typejoin(a, b)"]
    statement := "For every pair of primitive numeric types, typejoin returns their closest common ancestor in the numeric type hierarchy."
    source := "typejoin docstring; base/promotion.jl:37-160"
    status := .proven, prop := ``TypejoinPrimitiveUpperBound, thm := some ``typejoinPrimitiveUpperBound_proven },
  { id := "promotion-typesplit-removes-subtype", juliaFile := "base/promotion.jl"
    juliaFns := ["typesplit(a, b)"]
    statement := "For unions of simple types, typesplit(a, b) is a subtype of a, and Union{typesplit(a, b), b} == Union{a, b}."
    source := "base/promotion.jl:162-177 (source comment)"
    status := .proven, prop := ``TypesplitRemovesSubtype, thm := some ``typesplitRemovesSubtype_proven },
  { id := "promotion-promote-typejoin-union-membership", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_typejoin(@nospecialize(a), @nospecialize(b))", "_promote_typesubtract(@nospecialize(a))"]
    statement := "On declared types and their unions, promote_typejoin(T, S) returns a supertype of both T and S, which is equivalent to typejoin(T, S) when neither contains Nothing or Missing."
    source := "promote_typejoin docstring; base/promotion.jl:198-201"
    status := .proven, prop := ``PromoteTypejoinContainsInputs, thm := some ``promoteTypejoinContainsInputs_proven },
  { id := "promotion-promote-op-bottom", juliaFile := "base/promotion.jl"
    juliaFns := ["promote_op(f, S::Type...)", "TupleOrBottom(tt...)"]
    statement := "The type R returned by promote_op(f, S...) satisfies f(args...) isa R for all args isa S, given that inference bounds f's result type; for a Union{} argument type it is Union{}, which no call can reach."
    source := "promote_op docstring; base/promotion.jl:529-532,641-645"
    status := .proven, prop := ``PromoteOpBehavior, thm := some ``promoteOpBehavior_proven },
  { id := "promotion-muladd-false-strong-zero", juliaFile := "base/promotion.jl"
    juliaFns := ["muladd(a::Number, b::Number, c::Number)"]
    statement := "muladd returns the promoted third value when its first or second argument is false, and otherwise muladd of the promoted values."
    source := "base/promotion.jl:510-514"
    status := .proven, prop := ``MuladdFalseStrongZero, thm := some ``muladdFalseStrongZero_proven },
  { id := "promotion-integer-fma-muladd-fallback", juliaFile := "base/promotion.jl"
    juliaFns := ["fma(x::Integer, y::Integer, z::Integer)", "muladd(x::T, y::T, z::T)"]
    statement := "For every BitInteger width, the integer fma and the same-type muladd fallback compute x*y + z wrapped to the width."
    source := "fma and muladd docstrings; base/promotion.jl:658-659"
    status := .proven, prop := ``IntegerFmaMuladd, thm := some ``integerFmaMuladd_proven },
  { id := "promotion-real-order-fallbacks", juliaFile := "base/promotion.jl"
    juliaFns := ["==(x::T, y::T)", "<=(x::T, y::T)", "min(x::Real)", "max(x::Real)", "minmax(x::Real)", "max(x::T, y::T)", "min(x::T, y::T)", "minmax(x::T, y::T)"]
    statement := "On integers, the same-type == fallback is identity, <= is == or <, max/min/minmax return the greater, lesser and ordered pair, and the one-argument forms agree with the two-argument forms on (x, x)."
    source := "max, min, minmax docstrings; base/promotion.jl:665-678"
    status := .proven, prop := ``RealOrderFallbacks, thm := some ``realOrderFallbacks_proven },
  { id := "promotion-numeric-fallback-errors", juliaFile := "base/promotion.jl"
    juliaFns := ["no_op_err(name, T)", "+(x::T,y::T)", "*(x::T,y::T)", "-(x::T,y::T)", "/(x::T,y::T)", "^(x::T,y::T)", "fma(x::T,y::T,z::T)", "&(x::T,y::T)", "|(x::T,y::T)", "xor(x::T,y::T)", "<(x::T,y::T)", "rem(x::T,y::T)", "mod(x::T,y::T)", "flipsign(x::T,y::T)"]
    statement := "Unsupported generic numeric operations call the error handler with a message naming the operation and numeric type."
    source := "base/promotion.jl:650-680"
    status := .proven, prop := ``NumericFallbackErrors, thm := some ``numericFallbackErrors_proven }
]

end JuliaLean.Proofs.base.promotion
