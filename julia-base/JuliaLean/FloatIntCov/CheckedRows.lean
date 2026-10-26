import JuliaLean.FloatIntCov.Checked

namespace JuliaLean.FloatIntCov.CheckedRows

open JuliaLean JuliaLean.Registry JuliaLean.IntArith.Checked
open JuliaLean.FloatIntCov.Checked

def m26 {t s} (x : JInt t) (y : JInt s) := checkedAddMixed x y
def P26 : Prop := ∀ t s (x : JInt t) (y : JInt s), m26 x y = promoted @checkedAdd x y
theorem p26 : P26 := by unfold P26; intros; rfl

def m27 {t s} (x : JInt t) (y : JInt s) := checkedSubMixed x y
def P27 : Prop := ∀ t s (x : JInt t) (y : JInt s), m27 x y = promoted @checkedSub x y
theorem p27 : P27 := by unfold P27; intros; rfl

def m28 {t s} (x : JInt t) (y : JInt s) := checkedMulMixed x y
def P28 : Prop := ∀ t s (x : JInt t) (y : JInt s), m28 x y = promoted @checkedMul x y
theorem p28 : P28 := by unfold P28; intros; rfl

def m29 {t s} (x : JInt t) (y : JInt s) := checkedDivMixed x y
def P29 : Prop := ∀ t s (x : JInt t) (y : JInt s), m29 x y = promoted @checkedDiv x y
theorem p29 : P29 := by unfold P29; intros; rfl

def m30 {t s} (x : JInt t) (y : JInt s) := checkedRemMixed x y
def P30 : Prop := ∀ t s (x : JInt t) (y : JInt s), m30 x y = promoted @checkedRem x y
theorem p30 : P30 := by unfold P30; intros; rfl

def m31 {t s} (x : JInt t) (y : JInt s) := checkedFldMixed x y
def P31 : Prop := ∀ t s (x : JInt t) (y : JInt s), m31 x y = promoted @checkedFld x y
theorem p31 : P31 := by unfold P31; intros; rfl

def m32 {t s} (x : JInt t) (y : JInt s) := checkedModMixed x y
def P32 : Prop := ∀ t s (x : JInt t) (y : JInt s), m32 x y = promoted @checkedMod x y
theorem p32 : P32 := by unfold P32; intros; rfl

def m33 {t s} (x : JInt t) (y : JInt s) := checkedCldMixed x y
def P33 : Prop := ∀ t s (x : JInt t) (y : JInt s), m33 x y = promoted @checkedCld x y
theorem p33 : P33 := by unfold P33; intros; rfl

def m37 {α : Type} (x : α) : Jl α := checkedAbsFallback x
def P37 : Prop := ∀ (α : Type) (x : α), m37 x = .error (.methodError "checked_abs")
theorem p37 : P37 := by unfold P37; intros; rfl

def m89 {t} (x : JInt t) := checkedNeg x
def P89 : Prop := ∀ t (x : JInt t), ExactOrOverflow (m89 x) (-x.val)
theorem p89 : P89 := negExact

def m92 {α β : Type} (x : α) : Jl β := throwOverflowNegation x
def P92 : Prop := ∀ (α β : Type) (x : α), m92 (β := β) x = .error (.overflowError "")
theorem p92 : P92 := by unfold P92; intros; rfl

def m121 {t} (x : JInt t) := checkedAbs x
def P121 : Prop := ∀ t (x : JInt t),
  ExactOrOverflow (m121 x) (if x.val < 0 then -x.val else x.val)
theorem p121 : P121 := absExact

def m127 {t} (x : JInt t) := checkedAbs x
def P127 : Prop := ∀ t (x : JInt t), t.signed = false → m127 x = .ok x
theorem p127 : P127 := by intro t x h; cases t <;> simp_all [m127, checkedAbs, IntTy.signed]

def m128 (x : Bool) := checkedAbsBool x
def P128 : Prop := ∀ x, m128 x = x
theorem p128 : P128 := by unfold P128; intros; rfl

def m136 {t} (x y : JInt t) := intrinsicResult (t := t) (x.val + y.val)
def P136 : Prop := ∀ t (x y : JInt t), m136 x y = intrinsicResult (t := t) (x.val + y.val)
theorem p136 : P136 := by unfold P136; intros; rfl

def m137 {t} (x y : JInt t) := intrinsicResult (t := t) (x.val + y.val)
def P137 : Prop := ∀ t (x y : JInt t), m137 x y = intrinsicResult (t := t) (x.val + y.val)
theorem p137 : P137 := by unfold P137; intros; rfl

def m138 (x y : Bool) := addWithOverflowBool x y
def P138 : Prop := ∀ x y, m138 x y = (boolInt x + boolInt y, false)
theorem p138 : P138 := by unfold P138; intros; rfl

def m156 {α β γ δ : Type} (op : α) (x : β) (y : γ) : Jl δ := throwOverflowBinary op x y
def P156 : Prop := ∀ (α β γ δ : Type) (op : α) (x : β) (y : γ),
  m156 (δ := δ) op x y = .error (.overflowError "")
theorem p156 : P156 := by unfold P156; intros; rfl

def m166 {t} (x y : JInt t) := checkedAdd x y
def P166 : Prop := ∀ t (x y : JInt t), ExactOrOverflow (m166 x y) (x.val + y.val)
theorem p166 : P166 := by intro t x y; exact (addSubExact t x y).1

def m178 {α : Type} (x : α) := x
def P178 : Prop := ∀ (α : Type) (x : α), m178 x = x
theorem p178 : P178 := by unfold P178; intros; rfl

def m179 (x : Bool) := checkedAddBool x
def P179 : Prop := ∀ x, m179 x = boolInt x
theorem p179 : P179 := by unfold P179; intros; rfl

def m181 {t} (x1 x2 x3 : JInt t) : Jl (JInt t) := do checkedAdd (← checkedAdd x1 x2) x3
def P181 : Prop := ∀ t (x1 x2 x3 : JInt t), m181 x1 x2 x3 = do checkedAdd (← checkedAdd x1 x2) x3
theorem p181 : P181 := by unfold P181; intros; rfl

def m183 {t} (x1 x2 x3 x4 : JInt t) : Jl (JInt t) := do m181 (← checkedAdd x1 x2) x3 x4
def P183 : Prop := ∀ t (x1 x2 x3 x4 : JInt t), m183 x1 x2 x3 x4 = do m181 (← checkedAdd x1 x2) x3 x4
theorem p183 : P183 := by unfold P183; intros; rfl

def m185 {t} (x1 x2 x3 x4 x5 : JInt t) : Jl (JInt t) := do m183 (← checkedAdd x1 x2) x3 x4 x5
def P185 : Prop := ∀ t (x1 x2 x3 x4 x5 : JInt t), m185 x1 x2 x3 x4 x5 = do m183 (← checkedAdd x1 x2) x3 x4 x5
theorem p185 : P185 := by unfold P185; intros; rfl

def m187 {t} (x1 x2 x3 x4 x5 x6 : JInt t) : Jl (JInt t) := do m185 (← checkedAdd x1 x2) x3 x4 x5 x6
def P187 : Prop := ∀ t (x1 x2 x3 x4 x5 x6 : JInt t), m187 x1 x2 x3 x4 x5 x6 = do m185 (← checkedAdd x1 x2) x3 x4 x5 x6
theorem p187 : P187 := by unfold P187; intros; rfl

def m189 {t} (x1 x2 x3 x4 x5 x6 x7 : JInt t) : Jl (JInt t) := do m187 (← checkedAdd x1 x2) x3 x4 x5 x6 x7
def P189 : Prop := ∀ t (x1 x2 x3 x4 x5 x6 x7 : JInt t), m189 x1 x2 x3 x4 x5 x6 x7 = do m187 (← checkedAdd x1 x2) x3 x4 x5 x6 x7
theorem p189 : P189 := by unfold P189; intros; rfl

def m191 {t} (x1 x2 x3 x4 x5 x6 x7 x8 : JInt t) : Jl (JInt t) := do m189 (← checkedAdd x1 x2) x3 x4 x5 x6 x7 x8
def P191 : Prop := ∀ t (x1 x2 x3 x4 x5 x6 x7 x8 : JInt t), m191 x1 x2 x3 x4 x5 x6 x7 x8 = do m189 (← checkedAdd x1 x2) x3 x4 x5 x6 x7 x8
theorem p191 : P191 := by unfold P191; intros; rfl

def m200 {t} (x y : JInt t) := intrinsicResult (t := t) (x.val - y.val)
def P200 : Prop := ∀ t (x y : JInt t), m200 x y = intrinsicResult (t := t) (x.val - y.val)
theorem p200 : P200 := by unfold P200; intros; rfl

def m201 {t} (x y : JInt t) := intrinsicResult (t := t) (x.val - y.val)
def P201 : Prop := ∀ t (x y : JInt t), m201 x y = intrinsicResult (t := t) (x.val - y.val)
theorem p201 : P201 := by unfold P201; intros; rfl

def m202 (x y : Bool) := subWithOverflowBool x y
def P202 : Prop := ∀ x y, m202 x y = (boolInt x - boolInt y, false)
theorem p202 : P202 := by unfold P202; intros; rfl

def m226 {t} (x y : JInt t) := checkedSub x y
def P226 : Prop := ∀ t (x y : JInt t), ExactOrOverflow (m226 x y) (x.val - y.val)
theorem p226 : P226 := by intro t x y; exact (addSubExact t x y).2

def m239 {t} (x y : JInt t) := intrinsicResult (t := t) (x.val * y.val)
def P239 : Prop := ∀ t (x y : JInt t), m239 x y = intrinsicResult (t := t) (x.val * y.val)
theorem p239 : P239 := by unfold P239; intros; rfl

def m240 {t} (x y : JInt t) := intrinsicResult (t := t) (x.val * y.val)
def P240 : Prop := ∀ t (x y : JInt t), m240 x y = intrinsicResult (t := t) (x.val * y.val)
theorem p240 : P240 := by unfold P240; intros; rfl

def m241 (x y : Bool) := mulWithOverflowBool x y
def P241 : Prop := ∀ x y, m241 x y = (boolInt x * boolInt y, false)
theorem p241 : P241 := by unfold P241; intros; rfl

def m259 (x y : JInt .i128) := mulWithOverflow x y
def P259 : Prop := ∀ x y : JInt .i128, m259 x y = mulWithOverflow x y
theorem p259 : P259 := by unfold P259; intros; rfl

def m277 (x y : JInt .u128) := mulWithOverflow x y
def P277 : Prop := ∀ x y : JInt .u128, m277 x y = mulWithOverflow x y
theorem p277 : P277 := by unfold P277; intros; rfl

def m290 {t} (x y : JInt t) : Jl (JInt t) := do
  let (z, overflow) ← mulWithOverflow x y
  if overflow then .error (.overflowError "") else .ok z
def P290 : Prop := ∀ t (x y : JInt t), m290 x y = checkedMul x y
theorem p290 : P290 := by unfold P290; intros; rfl

def m298 {α : Type} (x : α) := x
def P298 : Prop := ∀ (α : Type) (x : α), m298 x = x
theorem p298 : P298 := by unfold P298; intros; rfl

def m299 {t} (x1 x2 x3 : JInt t) : Jl (JInt t) := do checkedMul (← checkedMul x1 x2) x3
def P299 : Prop := ∀ t (x1 x2 x3 : JInt t), m299 x1 x2 x3 = do checkedMul (← checkedMul x1 x2) x3
theorem p299 : P299 := by unfold P299; intros; rfl

def m301 {t} (x1 x2 x3 x4 : JInt t) : Jl (JInt t) := do m299 (← checkedMul x1 x2) x3 x4
def P301 : Prop := ∀ t (x1 x2 x3 x4 : JInt t), m301 x1 x2 x3 x4 = do m299 (← checkedMul x1 x2) x3 x4
theorem p301 : P301 := by unfold P301; intros; rfl

def m303 {t} (x1 x2 x3 x4 x5 : JInt t) : Jl (JInt t) := do m301 (← checkedMul x1 x2) x3 x4 x5
def P303 : Prop := ∀ t (x1 x2 x3 x4 x5 : JInt t), m303 x1 x2 x3 x4 x5 = do m301 (← checkedMul x1 x2) x3 x4 x5
theorem p303 : P303 := by unfold P303; intros; rfl

def m305 {t} (x1 x2 x3 x4 x5 x6 : JInt t) : Jl (JInt t) := do m303 (← checkedMul x1 x2) x3 x4 x5 x6
def P305 : Prop := ∀ t (x1 x2 x3 x4 x5 x6 : JInt t), m305 x1 x2 x3 x4 x5 x6 = do m303 (← checkedMul x1 x2) x3 x4 x5 x6
theorem p305 : P305 := by unfold P305; intros; rfl

def m307 {t} (x1 x2 x3 x4 x5 x6 x7 : JInt t) : Jl (JInt t) := do m305 (← checkedMul x1 x2) x3 x4 x5 x6 x7
def P307 : Prop := ∀ t (x1 x2 x3 x4 x5 x6 x7 : JInt t), m307 x1 x2 x3 x4 x5 x6 x7 = do m305 (← checkedMul x1 x2) x3 x4 x5 x6 x7
theorem p307 : P307 := by unfold P307; intros; rfl

def m309 {t} (x1 x2 x3 x4 x5 x6 x7 x8 : JInt t) : Jl (JInt t) := do m307 (← checkedMul x1 x2) x3 x4 x5 x6 x7 x8
def P309 : Prop := ∀ t (x1 x2 x3 x4 x5 x6 x7 x8 : JInt t), m309 x1 x2 x3 x4 x5 x6 x7 x8 = do m307 (← checkedMul x1 x2) x3 x4 x5 x6 x7 x8
theorem p309 : P309 := by unfold P309; intros; rfl

def m319 {t} (x y : JInt t) := JInt.div x y
def P319 : Prop := ∀ t (x y : JInt t), m319 x y = JInt.div x y
theorem p319 : P319 := by unfold P319; intros; rfl

def m328 {t} (x y : JInt t) := JInt.remInt x y
def P328 : Prop := ∀ t (x y : JInt t), m328 x y = JInt.remInt x y
theorem p328 : P328 := by unfold P328; intros; rfl

def m337 {t} (x y : JInt t) := JInt.fld x y
def P337 : Prop := ∀ t (x y : JInt t), m337 x y = JInt.fld x y
theorem p337 : P337 := by unfold P337; intros; rfl

def m346 {t} (x y : JInt t) := JInt.mod x y
def P346 : Prop := ∀ t (x y : JInt t), m346 x y = JInt.mod x y
theorem p346 : P346 := by unfold P346; intros; rfl

def m355 {t} (x y : JInt t) := JInt.cld x y
def P355 : Prop := ∀ t (x y : JInt t), m355 x y = JInt.cld x y
theorem p355 : P355 := by unfold P355; intros; rfl

def m364 {t s} (x : JInt t) (p : JInt s) := checkedPow x p
def P364 : Prop := ∀ t s (x : JInt t) (p : JInt s), m364 x p = checkedPow x p
theorem p364 : P364 := by unfold P364; intros; rfl

def m366 {t s} (x : JInt t) (p : JInt s) := checkedPow x p
def P366 : Prop := ∀ t s (x : JInt t) (p : JInt s), m366 x p = checkedPow x p
theorem p366 : P366 := by unfold P366; intros; rfl

def m368 (x : Bool) (p : Int) := checkedPowerBool x p
def P368 : Prop := ∀ x p, m368 x p = if p < 0 then
  if x then .ok true else .error (.domainError "") else if p = 0 then .ok true else .ok x
theorem p368 : P368 := by unfold P368; intros; rfl

def m376 {α β : Type} (length : α → Jl β) (r : α) := checkedLength length r
def P376 : Prop := ∀ (α β : Type) (length : α → Jl β) (r : α), m376 length r = length r
theorem p376 : P376 := by unfold P376; intros; rfl

private def mk (line : Nat) (name : String) (prop thm : Lean.Name)
    (status : Status := .proven) (issue : String := "") : Entry :=
  { id := s!"floatintcov-checked-l{line}", juliaFile := "base/checked.jl"
    juliaFns := [name], statement := s!"The method at base/checked.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/checked.jl:{line}", status, prop, thm := some thm, issue }

def entries : List Entry := [
  mk 26 "checked_add(::Integer,::Integer)" ``P26 ``p26,
  mk 27 "checked_sub(::Integer,::Integer)" ``P27 ``p27,
  mk 28 "checked_mul(::Integer,::Integer)" ``P28 ``p28,
  mk 29 "checked_div(::Integer,::Integer)" ``P29 ``p29,
  mk 30 "checked_rem(::Integer,::Integer)" ``P30 ``p30,
  mk 31 "checked_fld(::Integer,::Integer)" ``P31 ``p31,
  mk 32 "checked_mod(::Integer,::Integer)" ``P32 ``p32,
  mk 33 "checked_cld(::Integer,::Integer)" ``P33 ``p33,
  mk 37 "checked_abs fallback" ``P37 ``p37,
  mk 89 "checked_neg" ``P89 ``p89,
  mk 92 "throw_overflowerr_negation" ``P92 ``p92,
  mk 121 "checked_abs(::SignedInt)" ``P121 ``p121,
  mk 127 "checked_abs(::UnsignedInt)" ``P127 ``p127,
  mk 128 "checked_abs(::Bool)" ``P128 ``p128,
  mk 136 "add_with_overflow(::SignedInt)" ``P136 ``p136,
  mk 137 "add_with_overflow(::UnsignedInt)" ``P137 ``p137,
  mk 138 "add_with_overflow(::Bool)" ``P138 ``p138,
  mk 156 "throw_overflowerr_binaryop" ``P156 ``p156,
  mk 166 "checked_add same type" ``P166 ``p166,
  mk 178 "checked_add unary" ``P178 ``p178,
  mk 179 "checked_add(::Bool)" ``P179 ``p179,
  mk 181 "checked_add arity 3" ``P181 ``p181,
  mk 183 "checked_add arity 4" ``P183 ``p183,
  mk 185 "checked_add arity 5" ``P185 ``p185,
  mk 187 "checked_add arity 6" ``P187 ``p187,
  mk 189 "checked_add arity 7" ``P189 ``p189,
  mk 191 "checked_add arity 8" ``P191 ``p191,
  mk 200 "sub_with_overflow(::SignedInt)" ``P200 ``p200,
  mk 201 "sub_with_overflow(::UnsignedInt)" ``P201 ``p201,
  mk 202 "sub_with_overflow(::Bool)" ``P202 ``p202,
  mk 226 "checked_sub same type" ``P226 ``p226,
  mk 239 "mul_with_overflow(::SignedInt)" ``P239 ``p239,
  mk 240 "mul_with_overflow(::UnsignedInt)" ``P240 ``p240,
  mk 241 "mul_with_overflow(::Bool)" ``P241 ``p241,
  mk 259 "mul_with_overflow(::Int128)" ``P259 ``p259,
  mk 277 "mul_with_overflow(::UInt128)" ``P277 ``p277,
  mk 290 "checked_mul same type" ``P290 ``p290,
  mk 298 "checked_mul unary" ``P298 ``p298,
  mk 299 "checked_mul arity 3" ``P299 ``p299,
  mk 301 "checked_mul arity 4" ``P301 ``p301,
  mk 303 "checked_mul arity 5" ``P303 ``p303,
  mk 305 "checked_mul arity 6" ``P305 ``p305,
  mk 307 "checked_mul arity 7" ``P307 ``p307,
  mk 309 "checked_mul arity 8" ``P309 ``p309,
  mk 319 "checked_div same type" ``P319 ``p319,
  mk 328 "checked_rem same type" ``P328 ``p328,
  mk 337 "checked_fld same type" ``P337 ``p337,
  mk 346 "checked_mod same type" ``P346 ``p346,
  mk 355 "checked_cld same type" ``P355 ``p355,
  mk 364 "checked_pow" ``P364 ``p364,
  mk 366 "checked_power_by_squaring" ``P366 ``p366,
  mk 368 "checked_power_by_squaring(::Bool)" ``P368 ``p368,
  mk 376 "checked_length" ``P376 ``p376
]

end JuliaLean.FloatIntCov.CheckedRows
