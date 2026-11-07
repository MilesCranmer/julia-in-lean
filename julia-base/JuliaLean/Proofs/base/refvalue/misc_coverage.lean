import JuliaLean.base.refvalue

namespace JuliaLean.MiscCov.RefValue

variable {V : Type}

/-- The `isassigned` docstring (`base/refvalue.jl:12-35`) and the obvious contract of
the other methods: a `Ref` of an inline (bits) type is always assigned, a fresh
`Ref` of another type is not; assigning makes it assigned and `ref[]` returns the
converted value; `setindex!` returns the same object; `RefValue(x)` stores `x`;
`unsafe_convert` throws `UndefRefError` exactly for an unassigned non-inline
field and otherwise returns the address of the box, of the object, or the stored
pointer; `unsafe_convert(Ptr{Any}, ::RefValue{Any})` is the box address. -/
def Contract : Prop :=
  ∀ (T : Ty V) (P : Ptrs V) (a : Nat) (v : V),
    (isassigned (newEmpty T a) = true ↔ T.layout = .inline) ∧
    ((T.layout = .inline) → getindex (newEmpty T a) = .ok T.zero) ∧
    ((T.layout ≠ .inline) → getindex (newEmpty T a) = .error .undefRefError) ∧
    (∀ r : Obj V, setindex T r v = (T.conv v).map (fun w => { r with x := some w })) ∧
    (∀ r : Obj V, ∀ w, T.conv v = .ok w →
      ∃ r', setindex T r v = .ok r' ∧ r'.addr = r.addr ∧ isassigned r' = true ∧ getindex r' = .ok w) ∧
    (newWith T a v = (T.conv v).map (fun w => { addr := a, x := some w })) ∧
    (T.conv v = .ok v → newInfer T a v = .ok { addr := a, x := some v }) ∧
    (∀ r : Obj V, (unsafeConvert T P r = .error .undefRefError ↔ T.layout ≠ .inline ∧ r.x = none)) ∧
    (∀ r : Obj V, T.layout = .inline → unsafeConvert T P r = .ok r.addr) ∧
    (∀ r : Obj V, ∀ w, r.x = some w → T.layout = .mutableConcrete → unsafeConvert T P r = .ok (P.objref w)) ∧
    (∀ r : Obj V, ∀ w, r.x = some w → T.layout = .boxed → unsafeConvert T P r = .ok (P.boxed w)) ∧
    (∀ r : Obj V, unsafeConvertAny r = r.addr)

theorem contract_proven : @Contract V := by
  intro T P a v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [isassigned, newEmpty]; split <;> simp_all
  · intro h; simp [getindex, newEmpty, h]
  · intro h; simp [getindex, newEmpty, h]
  · intro r; simp only [setindex]; cases T.conv v <;> rfl
  · intro r w h; exact ⟨{ r with x := some w }, by simp [setindex, h]; rfl, rfl, rfl, rfl⟩
  · simp only [newWith]; cases T.conv v <;> rfl
  · intro h; simp [newInfer, newWith, h]; rfl
  · intro r
    cases hl : T.layout <;> cases hx : r.x <;> simp [unsafeConvert, hl, hx, getindex]
  · intro r h; simp [unsafeConvert, h]
  · intro r w hx h; simp [unsafeConvert, h, hx]
  · intro r w hx h; simp [unsafeConvert, h, hx]
  · intro r; rfl

end JuliaLean.MiscCov.RefValue

namespace JuliaLean.MiscCov

def RefValueContractClosed : Prop := @RefValue.Contract Unit
theorem refValueContractClosed_proven : RefValueContractClosed := RefValue.contract_proven

end JuliaLean.MiscCov
