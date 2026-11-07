import JuliaLean.base.stat
import JuliaLean.base.operators
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.stat

open JuliaLean.Registry

namespace Round1

open JuliaLean JuliaLean.base.stat

/-- Concrete dispatch for the four field types reached by installed statStructEqual.
Type tests only recover the statically known field type at the polymorphic interface.
Every reachable branch calls installed equality on its scalar carrier, and casts
preserve and reflect equality. No nominal Type disequality is required here; the
fallback is unreachable for the four pinned field types. This argument is specific
to equality and does not justify numeric hash dispatch. No comparison law is assumed. -/
noncomputable def scalarSame {A : Type} (left right : A) : Bool :=
  @dite Bool (A = U64) (Classical.propDecidable _) (fun h =>
    JuliaLean.base.int.eq_int (cast h left) (cast h right)) (fun _ =>
  @dite Bool (A = I64) (Classical.propDecidable _) (fun h =>
    JuliaLean.base.int.eq_int (cast h left) (cast h right)) (fun _ =>
  @dite Bool (A = I32) (Classical.propDecidable _) (fun h =>
    JuliaLean.base.int.eq_int (cast h left) (cast h right)) (fun _ =>
  @dite Bool (A = F64) (Classical.propDecidable _) (fun h =>
    JuliaLean.base.float.egal_float (T := .f64) (cast h left) (cast h right))
    (fun _ => false))))

/-- StatStruct equality is an equivalence relation over all Float64 bit patterns,
including signed zeros and NaN payloads.
Julia source: base/stat.jl:76-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:110-166; doc/src/base/base.md:143-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
noncomputable def StatEqualityRelationCorrect : Prop :=
  ∀ (Handle : Type),
    let equal := JuliaLean.base.operators.isequalDefault
      (statStructEqual scalarSame (Handle := Handle))
    (∀ st, equal st st = true) ∧
    (∀ left right, equal left right = equal right left) ∧
    (∀ first middle last, equal first middle = true → equal middle last = true →
      equal first last = true)

end Round1

end JuliaLean.Proofs.base.stat

namespace JuliaLean.ChatGPT.Batch4.Group16

def statCoreG16_RelationLaws {A : Type} (equal : A → A → Bool) : Prop :=
  (∀ x, equal x x = true) ∧
  (∀ x y, equal x y = equal y x) ∧
  (∀ x y z, equal x y = true → equal y z = true → equal x z = true)

theorem statCoreG16_beq_laws {A : Type} [BEq A] [LawfulBEq A] :
    statCoreG16_RelationLaws (fun x y : A => x == y) := by
  refine ⟨fun _ => BEq.rfl, fun _ _ => Bool.beq_comm, ?_⟩
  intro x y z hxy hyz
  exact beq_iff_eq.mpr ((beq_iff_eq.mp hxy).trans (beq_iff_eq.mp hyz))

theorem statCoreG16_field_laws {A B : Type} (field : A → B)
    (equal : B → B → Bool) (h : statCoreG16_RelationLaws equal) :
    statCoreG16_RelationLaws (fun x y => equal (field x) (field y)) := by
  exact ⟨fun x => h.1 (field x), fun x y => h.2.1 (field x) (field y),
    fun x y z hxy hyz => h.2.2 (field x) (field y) (field z) hxy hyz⟩

theorem statCoreG16_representation_laws {A B : Type} [BEq B] [LawfulBEq B]
    (representation : A → B) :
    statCoreG16_RelationLaws (fun x y => representation x == representation y) :=
  statCoreG16_field_laws representation (fun x y => x == y) statCoreG16_beq_laws

theorem statCoreG16_and_laws {A : Type} (first second : A → A → Bool)
    (hf : statCoreG16_RelationLaws first) (hs : statCoreG16_RelationLaws second) :
    statCoreG16_RelationLaws (fun x y => first x y && second x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change (first x x && second x x) = true
    rw [hf.1 x, hs.1 x] <;> rfl
  · intro x y
    change (first x y && second x y) = (first y x && second y x)
    rw [hf.2.1 x y, hs.2.1 x y]
  · intro x y z hxy hyz
    rw [Bool.and_eq_true] at hxy hyz ⊢
    exact ⟨hf.2.2 x y z hxy.1 hyz.1, hs.2.2 x y z hxy.2 hyz.2⟩

theorem statCoreG16_cast_laws {A B : Type} (same : A = B)
    (equal : B → B → Bool) (h : statCoreG16_RelationLaws equal) :
    statCoreG16_RelationLaws
      (fun x y : A => equal (cast same x) (cast same y)) :=
  statCoreG16_field_laws (fun x : A => cast same x) equal h

theorem statCoreG16_type_dispatch_laws {A B : Type}
    (selected : B → B → Bool) (fallback : A → A → Bool)
    (selectedLaws : statCoreG16_RelationLaws selected)
    (fallbackLaws : A ≠ B → statCoreG16_RelationLaws fallback) :
    statCoreG16_RelationLaws (fun x y : A =>
      @dite Bool (A = B) (Classical.propDecidable _)
        (fun h => selected (cast h x) (cast h y)) (fun _ => fallback x y)) := by
  classical
  by_cases same : A = B
  · simpa only [dif_pos same] using statCoreG16_cast_laws same selected selectedLaws
  · simpa only [dif_neg same] using fallbackLaws same

theorem statCoreG16_congr_laws {A : Type} (first second : A → A → Bool)
    (same : ∀ x y, first x y = second x y)
    (h : statCoreG16_RelationLaws first) : statCoreG16_RelationLaws second := by
  have functionsEqual : first = second := funext (fun x => funext (same x))
  rw [← functionsEqual]
  exact h

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.ChatGPT.Batch4.Group16
open JuliaLean JuliaLean.base.stat JuliaLean.Proofs.base.stat.Round1

theorem statG16_int_refl {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.eq_int x x = true := by
  simp only [JuliaLean.base.int.eq_int, JuliaLean.C.jlEqInt, BEq.rfl]

theorem statG16_int_symm {t : IntTy} (x y : JInt t) :
    JuliaLean.base.int.eq_int x y = JuliaLean.base.int.eq_int y x := by
  simp only [JuliaLean.base.int.eq_int, JuliaLean.C.jlEqInt]
  exact Bool.beq_comm

theorem statG16_int_trans {t : IntTy} (x y z : JInt t)
    (hxy : JuliaLean.base.int.eq_int x y = true)
    (hyz : JuliaLean.base.int.eq_int y z = true) :
    JuliaLean.base.int.eq_int x z = true := by
  simp only [JuliaLean.base.int.eq_int, JuliaLean.C.jlEqInt,
    beq_iff_eq] at hxy hyz ⊢
  exact hxy.trans hyz

theorem statG16_scalar_refl {A : Type}
    (hA : A = U64 ∨ A = I64 ∨ A = I32 ∨ A = F64) (x : A) :
    scalarSame x x = true := by
  unfold scalarSame
  split
  · exact statG16_int_refl _
  · rename_i hu
    split
    · exact statG16_int_refl _
    · rename_i hi
      split
      · exact statG16_int_refl _
      · rename_i hi32
        split
        · simp only [JuliaLean.base.float.egal_float, BEq.rfl]
        · rename_i hf
          rcases hA with h | h | h | h
          · exact False.elim (hu h)
          · exact False.elim (hi h)
          · exact False.elim (hi32 h)
          · exact False.elim (hf h)

theorem statG16_scalar_symm {A : Type} (x y : A) :
    scalarSame x y = scalarSame y x := by
  unfold scalarSame
  split
  · exact statG16_int_symm _ _
  · split
    · exact statG16_int_symm _ _
    · split
      · exact statG16_int_symm _ _
      · split
        · unfold JuliaLean.base.float.egal_float
          exact Bool.beq_comm
        · rfl

theorem statG16_scalar_trans {A : Type} (x y z : A)
    (hxy : scalarSame x y = true) (hyz : scalarSame y z = true) :
    scalarSame x z = true := by
  by_cases hu : A = U64
  · simp only [scalarSame, dif_pos hu] at hxy hyz ⊢
    exact statG16_int_trans _ _ _ hxy hyz
  · by_cases hi : A = I64
    · simp only [scalarSame, dif_neg hu, dif_pos hi] at hxy hyz ⊢
      exact statG16_int_trans _ _ _ hxy hyz
    · by_cases hi32 : A = I32
      · simp only [scalarSame, dif_neg hu, dif_neg hi, dif_pos hi32] at hxy hyz ⊢
        exact statG16_int_trans _ _ _ hxy hyz
      · by_cases hf : A = F64
        · simp only [scalarSame, dif_neg hu, dif_neg hi, dif_neg hi32, dif_pos hf,
            JuliaLean.base.float.egal_float, beq_iff_eq] at hxy hyz ⊢
          exact hxy.trans hyz
        · simp only [scalarSame, dif_neg hu, dif_neg hi, dif_neg hi32, dif_neg hf,
            Bool.false_eq_true] at hxy

def statG16_RelationLaws {A : Type} (equal : A → A → Bool) : Prop :=
  (∀ x, equal x x = true) ∧
  (∀ x y, equal x y = equal y x) ∧
  (∀ x y z, equal x y = true → equal y z = true → equal x z = true)

theorem statG16_scalar_laws {A : Type}
    (hA : A = U64 ∨ A = I64 ∨ A = I32 ∨ A = F64) :
    statG16_RelationLaws (@scalarSame A) :=
  ⟨statG16_scalar_refl hA, statG16_scalar_symm, statG16_scalar_trans⟩

theorem statG16_field_laws {A B : Type} (field : A → B)
    (equal : B → B → Bool) (h : statG16_RelationLaws equal) :
    statG16_RelationLaws (fun x y => equal (field x) (field y)) := by
  exact ⟨fun x => h.1 (field x), fun x y => h.2.1 (field x) (field y),
    fun x y z hxy hyz => h.2.2 (field x) (field y) (field z) hxy hyz⟩

theorem statG16_scalar_field_laws {A B : Type} (field : A → B)
    (hB : B = U64 ∨ B = I64 ∨ B = I32 ∨ B = F64) :
    statG16_RelationLaws (fun x y => scalarSame (field x) (field y)) :=
  statG16_field_laws field scalarSame (statG16_scalar_laws hB)

theorem statG16_and_laws {A : Type} (first second : A → A → Bool)
    (hf : statG16_RelationLaws first) (hs : statG16_RelationLaws second) :
    statG16_RelationLaws (fun x y => first x y && second x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change (first x x && second x x) = true
    rw [hf.1 x, hs.1 x] <;> rfl
  · intro x y
    change (first x y && second x y) = (first y x && second y x)
    rw [hf.2.1 x y, hs.2.1 x y]
  · intro x y z hxy hyz
    rw [Bool.and_eq_true] at hxy hyz ⊢
    exact ⟨hf.2.2 x y z hxy.1 hyz.1, hs.2.2 x y z hxy.2 hyz.2⟩

theorem StatEqualityEquivalence_proven : JuliaLean.Proofs.base.stat.Round1.StatEqualityRelationCorrect := by
  intro Handle
  change statG16_RelationLaws (statStructEqual scalarSame (Handle := Handle))
  unfold statStructEqual
  repeat' apply statG16_and_laws
  all_goals apply statG16_scalar_field_laws
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl rfl))
    | exact Or.inr (Or.inr (Or.inr rfl))

end JuliaLean.ChatGPT.Batch4.Group16

namespace JuliaLean.Proofs.base.stat
open JuliaLean.Registry

def entries : List Entry := [
  { id := "stat-equality-equivalence", juliaFile := "base/stat.jl",
    juliaFns := ["==(::StatStruct, ::StatStruct)"],
    statement := "StatStruct equality, with Float64 fields compared by bit pattern, is reflexive, symmetric and transitive over every snapshot.",
    source := "base/stat.jl:76-83; base/operators.jl:110-166 (isequal and == contracts)", status := .proven,
    prop := ``JuliaLean.Proofs.base.stat.Round1.StatEqualityRelationCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group16.StatEqualityEquivalence_proven }
]

end JuliaLean.Proofs.base.stat

namespace JuliaLean.Files

/-- For every 16-bit POSIX mode, the file type and permission accessors decode
the documented fields. `ispath` uses `ioerrno`, and `filesize` returns size. -/
def StatModeLayout : Prop :=
  ∀ mode : Fin 65536, ∀ size errno,
    let st : StatStruct := { mode, size, ioerrno := errno }
    filemode st = mode ∧
    isdir st = (mode.val / 4096 % 16 == 4) ∧
    islink st = (mode.val / 4096 % 16 == 10) ∧
    ispath st = (errno == 0) ∧
    uperm st = mode.val / 64 % 8 ∧
    gperm st = mode.val / 8 % 8 ∧
    operm st = mode.val % 8 ∧
    filesize st = size

theorem statModeLayout_proven : StatModeLayout := by
  intro mode size errno
  simp [filemode, isdir, islink, ispath, modeType, uperm, gperm, operm, filesize]

end JuliaLean.Files
