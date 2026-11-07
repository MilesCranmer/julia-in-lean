import JuliaLean.base.special.trig

namespace JuliaLean.MissingChar

/-! ## `sincos`, `sincosd`, `sincospi` of `missing` -/

/-- Results of the tuple-valued trigonometric functions: a 2-tuple of values that
may be missing, or a bare `missing`. -/
inductive Trig (F : Type) where
  | missing
  | tuple (s c : Option F)

/-- `sincos(x)`: `sincos(x) = _sincos(float(x))` (`base/special/trig.jl:205`),
`float(::Missing) = missing` (`base/missing.jl:96-103`),
`_sincos(x) = (sin(x), cos(x))` (`:203`) and `sin(::Missing) = cos(::Missing) =
missing` (`base/math.jl:1322-1332`). `k` is the Float64 kernel. -/
def sincos (k : F → F × F) : Option F → Trig F
  | none => .tuple none none
  | some x => .tuple (some (k x).1) (some (k x).2)

/-- `sincosd(::Missing) = (missing, missing)`, `base/special/trig.jl:1547`. -/
def sincosd (k : F → F × F) : Option F → Trig F
  | none => .tuple none none
  | some x => .tuple (some (k x).1) (some (k x).2)

/-- `sincospi(::Missing) = missing` from the loop at `base/math.jl:1322-1332`. -/
def sincospi (k : F → F × F) : Option F → Trig F
  | none => .missing
  | some x => .tuple (some (k x).1) (some (k x).2)

/-- `sincos`, `sincosd` and `sincospi` return a tuple `(sine, cosine)`
(`base/special/trig.jl:993-996`), and missing propagates into both components
(doc/src/manual/missing.md:14-18). -/
def SincosFamilyMissing : Prop :=
  ∀ (F : Type) (k : F → F × F) (x : Option F),
    ∀ f ∈ [sincos k, sincosd k, sincospi k], ∃ s c, f x = .tuple s c ∧ (x = none → s = none ∧ c = none)

theorem sincosFamilyMissing_refuted : ¬ SincosFamilyMissing := by
  intro h
  obtain ⟨s, c, hf, -⟩ := h Unit (fun _ => ((), ())) none (sincospi fun _ => ((), ()))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))
  simp [sincospi] at hf

end JuliaLean.MissingChar
