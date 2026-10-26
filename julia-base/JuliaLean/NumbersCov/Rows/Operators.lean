import JuliaLean.NumbersCov.Rows.Common

namespace JuliaLean.NumbersCov.Rows.Operators

open JuliaLean JuliaLean.NumbersCov JuliaLean.NumbersCov.Rows

def m86 (compute : α → Unit) (super : α → β) (t : α) : β :=
  let _ := compute t; super t
def P86 : Prop := ∀ (α β : Type) (compute : α → Unit) (super : α → β) t,
  m86 compute super t = super t
theorem p86 : P86 := by simp [P86, m86]

def m95 (isSuper : σ → Bool) (super : α → β) (field : α → σ → β) (t : α) (s : σ) : β :=
  if isSuper s then super t else field t s
def P95 : Prop := ∀ (α β σ : Type) (isSuper : σ → Bool) (super : α → β)
  (field : α → σ → β) t s, m95 isSuper super field t s =
    if isSuper s then super t else field t s
theorem p95 : P95 := by simp [P95, m95]

def m102 (wrap : α → β → γ) (super : β → β) (v : α) (body : β) : γ := wrap v (super body)
def P102 : Prop := ∀ (α β γ : Type) (wrap : α → β → γ) (super : β → β) v body,
  m102 wrap super v body = wrap v (super body)
theorem p102 : P102 := by simp [P102, m102]
def m104 (anyType : α) : α := anyType
def P104 : Prop := ∀ (α : Type) (x : α), m104 x = x
theorem p104 : P104 := by simp [P104, m104]
def m105 (typeOf : α → β) (p : α) : β := typeOf p
def P105 : Prop := ∀ (α β : Type) (f : α → β) x, m105 f x = f x
theorem p105 : P105 := by simp [P105, m105]

def m196 (eq : α → β → Bool) (x : α) (y : β) : Bool := eq x y
def P196 : Prop := ∀ (α β : Type) (eq : α → β → Bool) x y, m196 eq x y = eq x y
theorem p196 : P196 := by simp [P196, m196]
def m198 (signbit : α → Bool) (x y : α) : Bool := signbit x == signbit y
def P198 : Prop := ∀ (α : Type) (f : α → Bool) x y, m198 f x y = (f x == f y)
theorem p198 : P198 := by simp [P198, m198]
def m199 (signbit : α → Bool) (x y : α) : Bool := signbit x && !signbit y
def P199 : Prop := ∀ (α : Type) (f : α → Bool) x y, m199 f x y = (f x && !f y)
theorem p199 : P199 := by simp [P199, m199]
def m201 (isnan : α → Bool) (signbit : α → Bool) (eq : α → α → Bool) (x y : α) : Bool :=
  (isnan x && isnan y) || ((signbit x == signbit y) && eq x y)
def P201 : Prop := ∀ (α : Type) (nan sign : α → Bool) (eq : α → α → Bool) x y,
  m201 nan sign eq x y = ((nan x && nan y) || ((sign x == sign y) && eq x y))
theorem p201 : P201 := by simp [P201, m201]
def m202 (isnanA : α → Bool) (isnanB : β → Bool) (signA : α → Bool)
    (signB : β → Bool) (eq : α → β → Bool) (x : α) (y : β) : Bool :=
  (isnanA x && isnanB y) || ((signA x == signB y) && eq x y)
def P202 : Prop := ∀ (α β : Type) (na : α → Bool) (nb : β → Bool)
  (sa : α → Bool) (sb : β → Bool) (eq : α → β → Bool) x y,
  m202 na nb sa sb eq x y = ((na x && nb y) || ((sa x == sb y) && eq x y))
theorem p202 : P202 := by simp [P202, m202]
def m240 (isnan : α → Bool) (signbit : α → Bool) (lt : α → α → Bool) (x y : α) : Bool :=
  (!isnan x && (isnan y || (signbit x && !signbit y))) || lt x y
def P240 : Prop := ∀ (α : Type) (nan sign : α → Bool) (lt : α → α → Bool) x y,
  m240 nan sign lt x y = ((!nan x && (nan y || (sign x && !sign y))) || lt x y)
theorem p240 : P240 := by simp [P240, m240]
def m248 (lt eq : α → α → Bool) (a b : α × α) : Bool :=
  lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2)
def P248 : Prop := ∀ (α : Type) (lt eq : α → α → Bool) a b,
  m248 lt eq a b = (lt a.1 b.1 || (eq a.1 b.1 && lt a.2 b.2))
theorem p248 : P248 := by simp [P248, m248]
def m309 (_ : α) : Bool := false
def P309 : Prop := ∀ (α : Type) (x : α), m309 x = false
theorem p309 : P309 := by simp [P309, m309]
def m310 (isnan : α → Bool) (x : α) : Bool := isnan x
def P310 : Prop := ∀ (α : Type) (f : α → Bool) x, m310 f x = f x
theorem p310 : P310 := by simp [P310, m310]
def m313 (typesEqual : α → α → Bool) (t s : α) : Bool := typesEqual t s
def P313 : Prop := ∀ (α : Type) (f : α → α → Bool) x y, m313 f x y = f x y
theorem p313 : P313 := by simp [P313, m313]
def m314 (_ : α) (_ : β) : Bool := false
def P314 : Prop := ∀ (α β : Type) (x : α) (y : β), m314 x y = false
theorem p314 : P314 := by simp [P314, m314]
def m315 := @m314
def P315 : Prop := ∀ (α β : Type) (x : α) (y : β), @m315 α β x y = false
theorem p315 : P315 := by simp [P315, m315, m314]
def m338 (eq : α → β → γ) (not : γ → δ) (x : α) (y : β) : δ := not (eq x y)
def P338 : Prop := ∀ (α β γ δ : Type) (eq : α → β → γ) (n : γ → δ) x y,
  m338 eq n x y = n (eq x y)
theorem p338 : P338 := by simp [P338, m338]
def m417 (isless : α → β → Bool) (x : α) (y : β) := isless x y
def P417 : Prop := ∀ (α β : Type) (f : α → β → Bool) x y, m417 f x y = f x y
theorem p417 : P417 := by simp [P417, m417]
def m443 (lt : β → α → Bool) (x : α) (y : β) := lt y x
def P443 : Prop := ∀ (α β : Type) (f : β → α → Bool) x y, m443 f x y = f y x
theorem p443 : P443 := by simp [P443, m443]
def m467 (lt : α → β → γ) (eq : α → β → δ) (bitOr : γ → δ → ε) (x : α) (y : β) :=
  bitOr (lt x y) (eq x y)
def P467 : Prop := ∀ (α β γ δ ε : Type) (lt : α → β → γ) (eq : α → β → δ)
  (or : γ → δ → ε) x y, m467 lt eq or x y = or (lt x y) (eq x y)
theorem p467 : P467 := by simp [P467, m467]
def m499 (le : β → α → γ) (x : α) (y : β) := le y x
def P499 : Prop := ∀ (α β γ : Type) (le : β → α → γ) x y, m499 le x y = le y x
theorem p499 : P499 := by simp [P499, m499]
def m526 (isless : α → α → Bool) (x y : α) : Int :=
  if isless x y then -1 else if isless y x then 1 else 0
def P526 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y,
  m526 lt x y = if lt x y then -1 else if lt y x then 1 else 0
theorem p526 : P526 := by simp [P526, m526]
def m534 (lt : α → α → Bool) (x y : α) : Int :=
  if lt x y then -1 else if lt y x then 1 else 0
def P534 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y,
  m534 lt x y = if lt x y then -1 else if lt y x then 1 else 0
theorem p534 : P534 := by simp [P534, m534]
def m588 (isless : α → α → Bool) (x y : α) : α × α := if isless y x then (y, x) else (x, y)
def P588 : Prop := ∀ (α : Type) (lt : α → α → Bool) x y,
  m588 lt x y = if lt y x then (y, x) else (x, y)
theorem p588 : P588 := by simp [P588, m588]

def m605 (x : α) := x
def P605 : Prop := ∀ (α : Type) (x : α), m605 x = x
theorem p605 : P605 := by simp [P605, m605]
def m607 := @m605
def P607 : Prop := ∀ (α : Type) (x : α), @m607 α x = x
theorem p607 : P607 := by simp [P607, m607, m605]
def m608 := @m605
def P608 : Prop := ∀ (α : Type) (x : α), @m608 α x = x
theorem p608 : P608 := by simp [P608, m608, m605]
def m609 := @m605
def P609 : Prop := ∀ (α : Type) (x : α), @m609 α x = x
theorem p609 : P609 := by simp [P609, m609, m605]
def m610 := @m605
def P610 : Prop := ∀ (α : Type) (x : α), @m610 α x = x
theorem p610 : P610 := by simp [P610, m610, m605]
def m611 := @m605
def P611 : Prop := ∀ (α : Type) (x : α), @m611 α x = x
theorem p611 : P611 := by simp [P611, m611, m605]
def m622 (_op : α → α → α) (a : α) : α := a
def P622 : Prop := ∀ (α : Type) (op : α → α → α) a, m622 op a = a
theorem p622 : P622 := by simp [P622, m622]
def m623 (op : α → α → α) (a : α) (bs : List α) := bs.foldl op a
def P623 : Prop := ∀ (α : Type) (op : α → α → α) a bs, m623 op a bs = bs.foldl op a
theorem p623 : P623 := by simp [P623, m623]
def m671 (op : α → α → α) (a b c : α) (xs : List α) := xs.foldl op (op (op a b) c)
def P671 : Prop := ∀ (α : Type) (op : α → α → α) a b c xs,
  m671 op a b c xs = xs.foldl op (op (op a b) c)
theorem p671 : P671 := by simp [P671, m671]

def m709 (adj : α → α) (div : α → α → α) (x y : α) := adj (div (adj y) (adj x))
def P709 : Prop := ∀ (α : Type) (adj : α → α) (div : α → α → α) x y,
  m709 adj div x y = adj (div (adj y) (adj x))
theorem p709 : P709 := by simp [P709, m709]

def m735 (shift : α → Int → α) (zero negOne : α) (nonneg : α → Bool) x c :=
  OperatorModel.shiftLeftInteger shift zero negOne nonneg x c
def P735 : Prop := ∀ (α : Type) (sh : α → Int → α) (z n : α) (p : α → Bool) x c,
  HasResult (m735 sh z n p x c)
theorem p735 : P735 := by simp [P735, HasResult]
def m741 (shift : α → Nat → α) (zero x : α) (c : Nat) (isUInt : Bool) : Jl α :=
  if isUInt then .error (.methodError "<<")
  else if c ≤ 2^64 - 1 then .ok (shift x c) else .ok (shift zero 0)
def P741 : Prop := ∀ (α : Type) (sh : α → Nat → α) z x c u, HasResult (m741 sh z x c u)
theorem p741 : P741 := by simp [P741, HasResult]
def m748 (left right : α → Nat → α) x c := OperatorModel.shiftSignedCount left right x c
def P748 : Prop := ∀ (α : Type) (l r : α → Nat → α) x c, HasResult (m748 l r x c)
theorem p748 : P748 := by simp [P748, HasResult]
def m780 (shift : α → Int → α) (zero negOne : α) (nonneg : α → Bool) x c isUInt :=
  OperatorModel.shiftRightGenericCount shift zero negOne nonneg x c isUInt
def P780 : Prop := ∀ (α : Type) (sh : α → Int → α) z n (p : α → Bool) x c u,
  HasResult (m780 sh z n p x c u)
theorem p780 : P780 := by simp [P780, HasResult]
def m789 (right left : α → Nat → α) x c := OperatorModel.shiftSignedCount right left x c
def P789 : Prop := ∀ (α : Type) (r l : α → Nat → α) x c, HasResult (m789 r l x c)
theorem p789 : P789 := by simp [P789, HasResult]
def m818 (shift : α → Int → α) zero x c := OperatorModel.shiftUnsignedRightInteger shift zero x c
def P818 : Prop := ∀ (α : Type) (sh : α → Int → α) z x c, HasResult (m818 sh z x c)
theorem p818 : P818 := by simp [P818, HasResult]
def m822 (shift : α → Nat → α) (zero x : α) (c : Nat) (isUInt : Bool) : Jl α :=
  if isUInt then .error (.methodError ">>>")
  else if c ≤ 2^64 - 1 then .ok (shift x c) else .ok (shift zero 0)
def P822 : Prop := ∀ (α : Type) (sh : α → Nat → α) z x c u, HasResult (m822 sh z x c u)
theorem p822 : P822 := by simp [P822, HasResult]
def m829 (right left : α → Nat → α) x c := OperatorModel.shiftSignedCount right left x c
def P829 : Prop := ∀ (α : Type) (r l : α → Nat → α) x c, HasResult (m829 r l x c)
theorem p829 : P829 := by simp [P829, HasResult]

def m914 (mod : α → α → α) (zero : α → Bool) x y := OperatorModel.mod1 mod zero x y
def P914 : Prop := ∀ (α : Type) (mod : α → α → α) (z : α → Bool) x y,
  m914 mod z x y = let m := mod x y; if z m then y else m
theorem p914 : P914 := by simp [P914, m914, OperatorModel.mod1]
def m943 (cld : α → α → β) (mod1 : α → α → γ) x y := (cld x y, mod1 x y)
def P943 : Prop := ∀ (α β γ : Type) (c : α → α → β) (m : α → α → γ) x y,
  m943 c m x y = (c x y, m x y)
theorem p943 : P943 := by simp [P943, m943]
def m952 (fld1 : α → α → β) (mod1 : α → α → γ) x y := (fld1 x y, mod1 x y)
def P952 : Prop := ∀ (α β γ : Type) (f : α → α → β) (m : α → α → γ) x y,
  m952 f m x y = (f x y, m x y)
theorem p952 : P952 := by simp [P952, m952]
def m975 (typeOf : α → β) (widenType : β → γ) (convert : γ → α → δ) x :=
  convert (widenType (typeOf x)) x
def P975 : Prop := ∀ (α β γ δ : Type) (t : α → β) (w : β → γ) (c : γ → α → δ) x,
  m975 t w c x = c (w (t x)) x
theorem p975 : P975 := by simp [P975, m975]
def m976 (name : String) : Jl α := .error (.methodError name)
def P976 : Prop := ∀ (α : Type) n, @m976 α n = .error (.methodError n)
theorem p976 : P976 := by simp [P976, m976]
def m977 := @m976
def P977 : Prop := ∀ (α : Type) n, @m977 α n = .error (.methodError n)
theorem p977 : P977 := by simp [P977, m977, m976]

def m1001 (x : α) (f : α → β) := f x
def P1001 : Prop := ∀ (α β : Type) (x : α) (f : α → β), m1001 x f = f x
theorem p1001 : P1001 := by simp [P1001, m1001]
def m1003 (typeOf : α → β) x := typeOf x
def P1003 : Prop := ∀ (α β : Type) (f : α → β) x, m1003 f x = f x
theorem p1003 : P1003 := by simp [P1003, m1003]
def m1004 (hasFree : α → Bool) (typeTag dataType : β) t := if !hasFree t then typeTag else dataType
def P1004 : Prop := ∀ (α β : Type) (h : α → Bool) (t d : β) x,
  m1004 h t d x = if !h x then t else d
theorem p1004 : P1004 := by simp [P1004, m1004]

structure ReturnsF (α : Type) where value : α
def m1031 (value : α) : ReturnsF α := ⟨value⟩
def P1031 : Prop := ∀ (α : Type) (v : α), m1031 v = ReturnsF.mk v
theorem p1031 : P1031 := by simp [P1031, m1031]
def m1032 := @m1031
def P1032 : Prop := ∀ (α : Type) (v : α), @m1032 α v = ReturnsF.mk v
theorem p1032 : P1032 := by simp [P1032, m1032, m1031]
def m1035 (r : ReturnsF α) (_args : β) (_kw : γ) : α := r.value
def P1035 : Prop := ∀ (α β γ : Type) (r : ReturnsF α) (a : β) (k : γ), m1035 r a k = r.value
theorem p1035 : P1035 := by simp [P1035, m1035]

structure ComposedF (O I : Type) where
  outer : O
  inner : I
def m1121 (o : O) (i : I) : ComposedF O I := ⟨o, i⟩
def P1121 : Prop := ∀ (O I : Type) (o : O) (i : I), m1121 o i = ComposedF.mk o i
theorem p1121 : P1121 := by simp [P1121, m1121]
def m1122 := @m1121
def P1122 : Prop := ∀ (O I : Type) (o : O) (i : I), @m1122 O I o i = ComposedF.mk o i
theorem p1122 : P1122 := by simp [P1122, m1122, m1121]
def m1125 (unwrap : ComposedF O I → F) (call : F → X → K → Y)
    (c : ComposedF O I) (x : X) (kw : K) := call (unwrap c) x kw
def P1125 : Prop := ∀ (O I F X K Y : Type) (u : ComposedF O I → F)
  (call : F → X → K → Y) (c : ComposedF O I) (a : X) (k : K),
  m1125 u call c a k = call (u c) a k
theorem p1125 : P1125 := by simp [P1125, m1125]
def m1126 (unwrapO : O → List F) (unwrapI : I → List F) (c : ComposedF O I) :=
  unwrapO c.outer ++ unwrapI c.inner
def P1126 : Prop := ∀ (O I F : Type) (uo : O → List F) (ui : I → List F) (c : ComposedF O I),
  m1126 uo ui c = uo c.outer ++ ui c.inner
theorem p1126 : P1126 := by simp [P1126, m1126]
def m1127 (maybe : α → β) (x : α) : List β := [maybe x]
def P1127 : Prop := ∀ (α β : Type) (f : α → β) (x : α), m1127 f x = [f x]
theorem p1127 : P1127 := by simp [P1127, m1127]
def m1128 (head : F → A → B) (tailCall : Fs → X → K → A)
    (fsHead : F) (fsTail : Fs) (x : X) (kw : K) :=
  head fsHead (tailCall fsTail x kw)
def P1128 : Prop := ∀ (F A B Fs X K : Type) (h : F → A → B) (t : Fs → X → K → A)
  (fh : F) (ft : Fs) (x : X) (k : K), m1128 h t fh ft x k = h fh (t ft x k)
theorem p1128 : P1128 := by simp [P1128, m1128]
def m1129 (call : F → X → K → Y) (f : F) (x : X) (kw : K) := call f x kw
def P1129 : Prop := ∀ (F X K Y : Type) (c : F → X → K → Y)
  (f : F) (x : X) (k : K), m1129 c f x k = c f x k
theorem p1129 : P1129 := by simp [P1129, m1129]
def m1132 (call : F → A → K → Y) (f : F) (a : A) (kw : K) := call f a kw
def P1132 : Prop := ∀ (F A K Y : Type) (c : F → A → K → Y)
  (f : F) (a : A) (k : K), m1132 c f a k = c f a k
theorem p1132 : P1132 := by simp [P1132, m1132]
def m1133 (wrap : F → C) (f : F) := wrap f
def P1133 : Prop := ∀ (F C : Type) (w : F → C) (f : F), m1133 w f = w f
theorem p1133 : P1133 := by simp [P1133, m1133]
def m1134 (f : F) := f
def P1134 : Prop := ∀ (F : Type) (f : F), m1134 f = f
theorem p1134 : P1134 := by simp [P1134, m1134]
def m1136 (f : F) := f
def P1136 : Prop := ∀ (F : Type) (f : F), m1136 f = f
theorem p1136 : P1136 := by simp [P1136, m1136]
def m1137 (f : O) (g : I) := ComposedF.mk f g
def P1137 : Prop := ∀ (O I : Type) (f : O) (g : I), m1137 f g = ComposedF.mk f g
theorem p1137 : P1137 := by simp [P1137, m1137]
def m1138 (compose2 : A → B → C) (composeRest : C → H → R)
    (f : A) (g : B) (rest : H) : R := composeRest (compose2 f g) rest
def P1138 : Prop := ∀ (A B C H R : Type) (c2 : A → B → C) (cr : C → H → R)
  (f : A) (g : B) (rest : H),
  m1138 c2 cr f g rest = cr (c2 f g) rest
theorem p1138 : P1138 := by simp [P1138, m1138]
def m1140 (showOuter showPartOuter : α → String) (showPartInner : β → String)
    (nested : Bool) (outer : α) (inner : β) :=
  (if nested then showOuter outer else showPartOuter outer) ++ " ∘ " ++ showPartInner inner
def P1140 : Prop := ∀ (α β : Type) (s p : α → String) (q : β → String)
  (n : Bool) (o : α) (i : β),
  m1140 s p q n o i = (if n then s o else p o) ++ " ∘ " ++ q i
theorem p1140 : P1140 := by simp [P1140, m1140]
def m1147 (showPart : α → String) (inner : α) := "!" ++ showPart inner
def P1147 : Prop := ∀ (α : Type) (s : α → String) (x : α), m1147 s x = "!" ++ s x
theorem p1147 : P1147 := by simp [P1147, m1147]
def m1152 (render : α → String) (x : α) := render x
def P1152 : Prop := ∀ (α : Type) (s : α → String) (x : α), m1152 s x = s x
theorem p1152 : P1152 := by simp [P1152, m1152]
def m1154 (operator : α → Bool) (render : α → String) (x : α) :=
  if operator x then "(" ++ render x ++ ")" else render x
def P1154 : Prop := ∀ (α : Type) (op : α → Bool) (s : α → String) (x : α),
  m1154 op s x = if op x then "(" ++ s x ++ ")" else s x
theorem p1154 : P1154 := by simp [P1154, m1154]
def m1156 (render : α → String) (x : α) := "(" ++ render x ++ ")"
def P1156 : Prop := ∀ (α : Type) (s : α → String) (x : α), m1156 s x = "(" ++ s x ++ ")"
theorem p1156 : P1156 := by simp [P1156, m1156]
def m1158 := @m1152
def P1158 : Prop := ∀ (α : Type) (s : α → String) (x : α), @m1158 α s x = s x
theorem p1158 : P1158 := by simp [P1158, m1158, m1152]
def m1182 (f : α → Bool) : α → Bool := fun x => !f x
def P1182 : Prop := ∀ (α : Type) (f : α → Bool) x, m1182 f x = !f x
theorem p1182 : P1182 := by simp [P1182, m1182]
def m1183 (inner : F) := inner
def P1183 : Prop := ∀ (F : Type) (f : F), m1183 f = f
theorem p1183 : P1183 := by simp [P1183, m1183]

structure FixF (F X : Type) where
  f : F
  x : X
def m1206 (n : Option Int) (f : F) (x : X) : Jl (FixF F X) :=
  match n with
  | none => .error (.argumentError "Fix index must be Int")
  | some n => if n < 1 then .error (.argumentError "Fix index must be positive") else .ok ⟨f, x⟩
def P1206 : Prop := ∀ (F X : Type) (n : Option Int) (f : F) (x : X), HasResult (m1206 n f x)
theorem p1206 : P1206 := by simp [P1206, HasResult]
def m1216 (n m : Int) (split : Args → Int → L × R)
    (call : F → L → X → R → K → Y) (f : FixF F X) (args : Args) (kw : K) : Jl Y :=
  if m < n - 1 then .error (.argumentError "Fix arguments")
  else let p := split args (n - 1); .ok (call f.f p.1 f.x p.2 kw)
def P1216 : Prop := ∀ (F X Args L R K Y : Type) (n m : Int) (s : Args → Int → L × R)
  (c : F → L → X → R → K → Y) (f : FixF F X) (a : Args) (k : K),
  HasResult (m1216 n m s c f a k)
theorem p1216 : P1216 := by simp [P1216, HasResult]
def m1223 (call : F → X → A → K → Y) (f : FixF F X) (arg : A) (kw : K) := call f.f f.x arg kw
def P1223 : Prop := ∀ (F X A K Y : Type) (c : F → X → A → K → Y)
  (f : FixF F X) (a : A) (k : K),
  m1223 c f a k = c f.f f.x a k
theorem p1223 : P1223 := by simp [P1223, m1223]
def m1224 (call : F → A → X → K → Y) (f : FixF F X) (arg : A) (kw : K) := call f.f arg f.x kw
def P1224 : Prop := ∀ (F X A K Y : Type) (c : F → A → X → K → Y)
  (f : FixF F X) (a : A) (k : K),
  m1224 c f a k = c f.f a f.x k
theorem p1224 : P1224 := by simp [P1224, m1224]
def m1226 (showF : F → String) (showX : X → String) (n : Int) (f : FixF F X) :=
  "Fix{" ++ toString n ++ "}(" ++ showF f.f ++ ", " ++ showX f.x ++ ")"
def P1226 : Prop := ∀ (F X : Type) (sf : F → String) (sx : X → String)
  (n : Int) (f : FixF F X),
  HasResult (m1226 sf sx n f)
theorem p1226 : P1226 := by simp [P1226, HasResult]

def fixSecond (f : α → β → γ) (x : β) : α → γ := fun y => f y x
def m1259 := @fixSecond
def P1259 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1259 α β γ f x y = f y x
theorem p1259 : P1259 := by simp [P1259, m1259, fixSecond]
def m1270 := @fixSecond
def P1270 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1270 α β γ f x y = f y x
theorem p1270 : P1270 := by simp [P1270, m1270, fixSecond]
def m1283 := @fixSecond
def P1283 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1283 α β γ f x y = f y x
theorem p1283 : P1283 := by simp [P1283, m1283, fixSecond]
def m1296 := @fixSecond
def P1296 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1296 α β γ f x y = f y x
theorem p1296 : P1296 := by simp [P1296, m1296, fixSecond]
def m1309 := @fixSecond
def P1309 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1309 α β γ f x y = f y x
theorem p1309 : P1309 := by simp [P1309, m1309, fixSecond]
def m1322 := @fixSecond
def P1322 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1322 α β γ f x y = f y x
theorem p1322 : P1322 := by simp [P1322, m1322, fixSecond]
def m1335 := @fixSecond
def P1335 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1335 α β γ f x y = f y x
theorem p1335 : P1335 := by simp [P1335, m1335, fixSecond]

structure SplatF (F : Type) where f : F
def m1366 (f : F) := SplatF.mk f
def P1366 : Prop := ∀ (F : Type) (f : F), m1366 f = SplatF.mk f
theorem p1366 : P1366 := by simp [P1366, m1366]
def m1384 := @m1366
def P1384 : Prop := ∀ (F : Type) (f : F), @m1384 F f = SplatF.mk f
theorem p1384 : P1384 := by simp [P1384, m1384, m1366]
def m1386 (apply : F → Args → Y) (s : SplatF F) (args : Args) := apply s.f args
def P1386 : Prop := ∀ (F Args Y : Type) (a : F → Args → Y)
  (s : SplatF F) (x : Args), m1386 a s x = a s.f x
theorem p1386 : P1386 := by simp [P1386, m1386]
def m1387 (render : F → String) (s : SplatF F) := "splat(" ++ render s.f ++ ")"
def P1387 : Prop := ∀ (F : Type) (render : F → String) (x : SplatF F),
  m1387 render x = "splat(" ++ render x.f ++ ")"
theorem p1387 : P1387 := by simp [P1387, m1387]
def m1415 (compose : F → TupleF → C) f tupleF := compose f tupleF
def P1415 : Prop := ∀ (F T C : Type) (c : F → T → C) f t, m1415 c f t = c f t
theorem p1415 : P1415 := by simp [P1415, m1415]
def m1416 (s : SplatF F) := s.f
def P1416 : Prop := ∀ (F : Type) (s : SplatF F), m1416 s = s.f
theorem p1416 : P1416 := by simp [P1416, m1416]
def m1417 (outer : F) := outer
def P1417 : Prop := ∀ (F : Type) (f : F), m1417 f = f
theorem p1417 : P1417 := by simp [P1417, m1417]
def m1438 (f : α → β) : α → α := fun x => let _ := f x; x
def P1438 : Prop := ∀ (α β : Type) (f : α → β) x, m1438 f x = x
theorem p1438 : P1438 := by simp [P1438, m1438]

def m1453 := @fixSecond
def P1453 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1453 α β γ f x y = f y x
theorem p1453 : P1453 := by simp [P1453, m1453, fixSecond]
def m1455 (any : (α → γ) → I → γ) (eq : X → α → γ) x itr := any (eq x) itr
def P1455 : Prop := ∀ (α γ I X : Type) (a : (α → γ) → I → γ) (e : X → α → γ) x i,
  m1455 a e x i = a (e x) i
theorem p1455 : P1455 := by simp [P1455, m1455]
def m1477 (mem : α → β → γ) (not : γ → δ) x y := not (mem x y)
def P1477 : Prop := ∀ (α β γ δ : Type) (m : α → β → γ) (n : γ → δ) x y,
  m1477 m n x y = n (m x y)
theorem p1477 : P1477 := by simp [P1477, m1477]
def m1478 := @fixSecond
def P1478 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1478 α β γ f x y = f y x
theorem p1478 : P1478 := by simp [P1478, m1478, fixSecond]
def m1486 (mem : α → β → γ) (itr : β) (x : α) := mem x itr
def P1486 : Prop := ∀ (α β γ : Type) (m : α → β → γ) x y, m1486 m y x = m x y
theorem p1486 : P1486 := by simp [P1486, m1486]
def m1497 := @fixSecond
def P1497 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1497 α β γ f x y = f y x
theorem p1497 : P1497 := by simp [P1497, m1497, fixSecond]
def m1499 (contains : β → α → γ) (not : γ → δ) itr x := not (contains itr x)
def P1499 : Prop := ∀ (α β γ δ : Type) (c : β → α → γ) (n : γ → δ) x y,
  m1499 c n y x = n (c y x)
theorem p1499 : P1499 := by simp [P1499, m1499]
def m1500 := @fixSecond
def P1500 : Prop := ∀ (α β γ : Type) (f : α → β → γ) x y, @m1500 α β γ f x y = f y x
theorem p1500 : P1500 := by simp [P1500, m1500, fixSecond]

end JuliaLean.NumbersCov.Rows.Operators
