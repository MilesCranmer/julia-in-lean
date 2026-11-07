import JuliaLean.base.runtime_internals
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.runtime_internals

open JuliaLean JuliaLean.base.runtime_internals JuliaLean.Registry
open JuliaLean.base.io (M Error)

/-- Each successful global-constant query tests the actual Cint answer;
errors and mutations are retained by the source state monad. -/
def IsconstGlobalBodies : Prop :=
  (∀ (World Module Sym : Type) (query : Module → Sym → M World Cint)
    (m : Module) (s : Sym) (before after : World) (answer : Cint),
    query m s before = some (.ok (answer, after)) →
    isconstGlobal query m s before = some (.ok (answer.val != 0, after))) ∧
  (∀ (World GlobalRef : Type) (query : GlobalRef → M World Cint)
    (g : GlobalRef) (before after : World) (answer : Cint),
    query g before = some (.ok (answer, after)) →
    isconstGlobalRef query g before = some (.ok (answer.val != 0, after)))

theorem isconstGlobalBodies_proven : IsconstGlobalBodies := by
  constructor
  · intro World Module Sym query m s before after answer run
    simp [isconstGlobal, bind, pure, run]
  · intro World GlobalRef query g before after answer run
    simp [isconstGlobalRef, bind, pure, run]

/-- The padding docstring promises packed fields, the complement of padding. -/
def HaspaddingDoc : Prop :=
  ∀ layout : DataTypeLayout,
    datatypeHaspaddingLayout layout = !(layout.flags.val % 2 == 1)

private def packedLayout : DataTypeLayout :=
  ⟨JInt.lit .u32 16, JInt.lit .u32 2, JInt.lit .u32 0,
    JInt.lit .i32 (-1), JInt.lit .u16 8, JInt.lit .u16 1⟩

theorem haspaddingDoc_refuted : ¬ HaspaddingDoc := by
  intro promised
  have bad := promised packedLayout
  revert bad
  decide

/-- The documented byte count is twice the storage-word width. -/
def FielddescTypeDoc : Prop :=
  ∀ layout : DataTypeLayout,
    let code := (datatypeFielddescTypeLayout layout).val
    code < 3 → code = 2 * 2 ^ code.toNat

theorem fielddescTypeDoc_refuted : ¬ FielddescTypeDoc := by
  intro promised
  have bad := promised { packedLayout with flags := JInt.lit .u16 0 } (by decide)
  revert bad
  decide

private def returnedIntegerType {t : IntTy} (_ : JInt t) : IntTy := t

/-- The docstring advertises the native signed Int return type. -/
def NpointersReturnType : Prop :=
  ∀ layout : DataTypeLayout,
    returnedIntegerType (t := .u32) (datatypeNpointersLayout layout) = .i64

theorem npointersReturnType_refuted : ¬ NpointersReturnType := by
  intro promised
  have bad := promised packedLayout
  cases bad

open JuliaLean.Registry in
def entries : List Entry := [
  { id := "runtimecov-isconst-globals", juliaFile := "base/runtime_internals.jl",
    juliaFns := ["isconst(::Module, ::Symbol)", "isconst(::GlobalRef)"],
    statement := "Both global-constant queries return true exactly when their corresponding libjulia runtime query returns a nonzero C integer.",
    source := "base/runtime_internals.jl:522-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .proven, prop := ``IsconstGlobalBodies, thm := some ``isconstGlobalBodies_proven },
  { id := "runtimecov-datatype-haspadding-doc", juliaFile := "base/runtime_internals.jl",
    juliaFns := ["datatype_haspadding"],
    statement := "datatype_haspadding returns what its docstring says.",
    source := "base/runtime_internals.jl:693-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .refuted, prop := ``HaspaddingDoc, thm := some ``haspaddingDoc_refuted,
    issue := "#49318 (related; queries: datatype_haspadding)" },
  { id := "runtimecov-datatype-fielddesc-type-doc", juliaFile := "base/runtime_internals.jl",
    juliaFns := ["datatype_fielddesc_type"],
    statement := "datatype_fielddesc_type returns the field-descriptor entry size its docstring describes.",
    source := "base/runtime_internals.jl:744-754 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .refuted, prop := ``FielddescTypeDoc, thm := some ``fielddescTypeDoc_refuted,
    issue := "none found (queries: datatype_fielddesc_type)" },
  { id := "runtimecov-datatype-npointers-return-type", juliaFile := "base/runtime_internals.jl",
    juliaFns := ["datatype_npointers"],
    statement := "datatype_npointers returns an Int, as its docstring signature declares.",
    source := "base/runtime_internals.jl:725-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027",
    status := .refuted, prop := ``NpointersReturnType, thm := some ``npointersReturnType_refuted,
    issue := "none found (queries: datatype_npointers)" }
]

end JuliaLean.Proofs.base.runtime_internals
