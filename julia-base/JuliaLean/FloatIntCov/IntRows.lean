import JuliaLean.FloatIntCov.Int
import JuliaLean.Promotion.Ints

namespace JuliaLean.FloatIntCov.IntRows

open JuliaLean JuliaLean.Registry
open JuliaLean.FloatIntCov.Int
open JuliaLean.IntArith.Division
open JuliaLean.IntArith.PowersDigits

def m73 (_u : Unit) : IntTy := .i64
def P73 : Prop := ∀ u : Unit, m73 u = .i64
theorem p73 : P73 := by unfold P73; intros; rfl

def m74 (_u : Unit) : IntTy := .i8
def P74 : Prop := ∀ u : Unit, m74 u = .i8
theorem p74 : P74 := by unfold P74; intros; rfl

def m75 (_u : Unit) : IntTy := .i16
def P75 : Prop := ∀ u : Unit, m75 u = .i16
theorem p75 : P75 := by unfold P75; intros; rfl

def m76 (_u : Unit) : IntTy := .i32
def P76 : Prop := ∀ u : Unit, m76 u = .i32
theorem p76 : P76 := by unfold P76; intros; rfl

def m77 (_u : Unit) : IntTy := .i64
def P77 : Prop := ∀ u : Unit, m77 u = .i64
theorem p77 : P77 := by unfold P77; intros; rfl

def m78 (_u : Unit) : IntTy := .i128
def P78 : Prop := ∀ u : Unit, m78 u = .i128
theorem p78 : P78 := by unfold P78; intros; rfl

def m79 (t : IntTy) := t
def P79 : Prop := ∀ t : IntTy, m79 t = t
theorem p79 : P79 := by unfold P79; intros; rfl

def m80 {α : Type} (_u : Unit) : Jl α := unionTypeError (α := α) "signed"
def P80 : Prop := ∀ (α : Type) (u : Unit), m80 u = unionTypeError (α := α) "signed"
theorem p80 : P80 := by unfold P80; intros; rfl

def m84 {t : IntTy} (x y : JInt t) := decide (x.val < y.val)
def P84 : Prop := ∀ t (x y : JInt t), m84 x y = decide (x.val < y.val)
theorem p84 : P84 := by unfold P84; intros; rfl

def m86 {t : IntTy} (x : JInt t) := -x
def P86 : Prop := ∀ t (x : JInt t), m86 x = -x
theorem p86 : P86 := by unfold P86; intros; rfl

def m87 {t : IntTy} (x y : JInt t) := x - y
def P87 : Prop := ∀ t (x y : JInt t), m87 x y = x - y
theorem p87 : P87 := by unfold P87; intros; rfl

def m88 {t : IntTy} (x y : JInt t) := x + y
def P88 : Prop := ∀ t (x y : JInt t), m88 x y = x + y
theorem p88 : P88 := by unfold P88; intros; rfl

def m89 {t : IntTy} (x y : JInt t) := x * y
def P89 : Prop := ∀ t (x y : JInt t), m89 x y = x * y
theorem p89 : P89 := by unfold P89; intros; rfl

def m91 {t : IntTy} (x : JInt t) := -x
def P91 : Prop := ∀ t (x : JInt t), m91 x = -x
theorem p91 : P91 := by unfold P91; intros; rfl

def m92 {t : IntTy} (x y : JInt t) := x - y
def P92 : Prop := ∀ t (x y : JInt t), m92 x y = x - y
theorem p92 : P92 := by unfold P92; intros; rfl

def m93 {t : IntTy} (x y : JInt t) := x + y
def P93 : Prop := ∀ t (x y : JInt t), m93 x y = x + y
theorem p93 : P93 := by unfold P93; intros; rfl

def m94 {t : IntTy} (x y : JInt t) := x * y
def P94 : Prop := ∀ t (x y : JInt t), m94 x y = x * y
theorem p94 : P94 := by unfold P94; intros; rfl

def m96 {t : IntTy} (x : JInt t) := -x
def P96 : Prop := ∀ t (x : JInt t), m96 x = -x
theorem p96 : P96 := by unfold P96; intros; rfl

def m97 {t : IntTy} (x : JInt t) := negateUnsigned x
def P97 : Prop := ∀ t (x : JInt t), m97 x = negateUnsigned x
theorem p97 : P97 := by unfold P97; intros; rfl

def m100 (x : Value) := inv x
def P100 : Prop := ∀ x : Value, m100 x = inv x
theorem p100 : P100 := by unfold P100; intros; rfl

def m101 (x y : Value) := fdiv x y
def P101 : Prop := ∀ x y : Value, m101 x y = fdiv x y
theorem p101 : P101 := by unfold P101; intros; rfl

def m103 (x y : Value) := fdiv x y
def P103 : Prop := ∀ x y : Value, m103 x y = fdiv x y
theorem p103 : P103 := by unfold P103; intros; rfl

def m123 {t : IntTy} (x y : JInt t) := mulHi x y
def P123 : Prop := ∀ t (x y : JInt t), m123 x y = mulHi x y
theorem p123 : P123 := by unfold P123; intros; rfl

def m127 {t : IntTy} (x y : JInt t) := mulHi x y
def P127 : Prop := ∀ t (x y : JInt t), m127 x y = mulHi x y
theorem p127 : P127 := by unfold P127; intros; rfl

def m137 {t : IntTy} (x y : JInt t) := mulHi x y
def P137 : Prop := ∀ t (x y : JInt t), m137 x y = mulHi x y
theorem p137 : P137 := by unfold P137; intros; rfl

def m160 {α β : Type} (isreal : α → Bool) (real : α → β) (odd : β → Bool) (x : α) := isreal x && odd (real x)
def P160 : Prop := ∀ (α β : Type) (isreal : α → Bool) (real : α → β)
  (odd : β → Bool) (x : α), m160 isreal real odd x = (isreal x && odd (real x))
theorem p160 : P160 := by unfold P160; intros; rfl

def m161 {α : Type} (isinteger : α → Bool) (integer : α → Int) (x : α) := isinteger x && integer x % 2 != 0
def P161 : Prop := ∀ (α : Type) (isinteger : α → Bool) (integer : α → Int) (x : α),
  m161 isinteger integer x = (isinteger x && integer x % 2 != 0)
theorem p161 : P161 := by unfold P161; intros; rfl

def m180 {α β : Type} (isreal : α → Bool) (real : α → β) (even : β → Bool) (x : α) := isreal x && even (real x)
def P180 : Prop := ∀ (α β : Type) (isreal : α → Bool) (real : α → β)
  (even : β → Bool) (x : α), m180 isreal real even x = (isreal x && even (real x))
theorem p180 : P180 := by unfold P180; intros; rfl

def m181 {α : Type} (isinteger : α → Bool) (integer : α → Int) (x : α) := isinteger x && integer x % 2 == 0
def P181 : Prop := ∀ (α : Type) (isinteger : α → Bool) (integer : α → Int) (x : α),
  m181 isinteger integer x = (isinteger x && integer x % 2 == 0)
theorem p181 : P181 := by unfold P181; intros; rfl

def m183 {t : IntTy} (x : JInt t) := signbit x
def P183 : Prop := ∀ t (x : JInt t), m183 x = signbit x
theorem p183 : P183 := by unfold P183; intros; rfl

def m184 {t : IntTy} (x : JInt t) := signbit x
def P184 : Prop := ∀ t (x : JInt t), m184 x = signbit x
theorem p184 : P184 := by unfold P184; intros; rfl

def m186 {t : IntTy} (x : JInt t) := signbit x
def P186 : Prop := ∀ t (x : JInt t), m186 x = signbit x
theorem p186 : P186 := by unfold P186; intros; rfl

def m188 (x y : Value) := flipsign x y
def P188 : Prop := ∀ x y : Value, m188 x y = flipsign x y
theorem p188 : P188 := by unfold P188; intros; rfl

def m189 (x y : Value) := flipsign x y
def P189 : Prop := ∀ x y : Value, m189 x y = flipsign x y
theorem p189 : P189 := by unfold P189; intros; rfl

def m191 (x y : Value) := flipsign x y
def P191 : Prop := ∀ x y : Value, m191 x y = flipsign x y
theorem p191 : P191 := by unfold P191; intros; rfl

def m192 (x y : Value) := flipsign x y
def P192 : Prop := ∀ x y : Value, m192 x y = flipsign x y
theorem p192 : P192 := by unfold P192; intros; rfl

def m193 (x y : Value) := flipsign x y
def P193 : Prop := ∀ x y : Value, m193 x y = flipsign x y
theorem p193 : P193 := by unfold P193; intros; rfl

def m194 (x y : Value) := flipsign x y
def P194 : Prop := ∀ x y : Value, m194 x y = flipsign x y
theorem p194 : P194 := by unfold P194; intros; rfl

def m196 (x y : Value) := copysign x y
def P196 : Prop := ∀ x y : Value, m196 x y = copysign x y
theorem p196 : P196 := by unfold P196; intros; rfl

def m197 (x y : Value) := copysign x y
def P197 : Prop := ∀ x y : Value, m197 x y = copysign x y
theorem p197 : P197 := by unfold P197; intros; rfl

def m198 (x y : Value) := copysign x y
def P198 : Prop := ∀ x y : Value, m198 x y = copysign x y
theorem p198 : P198 := by unfold P198; intros; rfl

def m199 (x y : Value) := copysign x y
def P199 : Prop := ∀ x y : Value, m199 x y = copysign x y
theorem p199 : P199 := by unfold P199; intros; rfl

def m200 (x y : Value) := copysign x y
def P200 : Prop := ∀ x y : Value, m200 x y = copysign x y
theorem p200 : P200 := by unfold P200; intros; rfl

def m233 (x : Value) := abs x
def P233 : Prop := ∀ x : Value, m233 x = abs x
theorem p233 : P233 := by unfold P233; intros; rfl

def m234 (x : Value) := abs x
def P234 : Prop := ∀ x : Value, m234 x = abs x
theorem p234 : P234 := by unfold P234; intros; rfl

def m236 {t : IntTy} (x : JInt t) := bitNot x
def P236 : Prop := ∀ t (x : JInt t), m236 x = bitNot x
theorem p236 : P236 := by unfold P236; intros; rfl

def m261 (x : Value) := unsigned x
def P261 : Prop := ∀ x : Value, m261 x = unsigned x
theorem p261 : P261 := by unfold P261; intros; rfl

def m262 (x : Value) := unsigned x
def P262 : Prop := ∀ x : Value, m262 x = unsigned x
theorem p262 : P262 := by unfold P262; intros; rfl

def m272 (x : Value) := signed x
def P272 : Prop := ∀ x : Value, m272 x = signed x
theorem p272 : P272 := by unfold P272; intros; rfl

def m273 (x : Value) := signed x
def P273 : Prop := ∀ x : Value, m273 x = signed x
theorem p273 : P273 := by unfold P273; intros; rfl

def m275 (x y : Value) := div x y
def P275 : Prop := ∀ x y : Value, m275 x y = div x y
theorem p275 : P275 := by unfold P275; intros; rfl

def m276 (x y : Value) := div x y
def P276 : Prop := ∀ x y : Value, m276 x y = div x y
theorem p276 : P276 := by unfold P276; intros; rfl

def m278 (x y : Value) := rem x y
def P278 : Prop := ∀ x y : Value, m278 x y = rem x y
theorem p278 : P278 := by unfold P278; intros; rfl

def m279 (x y : Value) := rem x y
def P279 : Prop := ∀ x y : Value, m279 x y = rem x y
theorem p279 : P279 := by unfold P279; intros; rfl

def m281 (x y : Value) := divrem x y
def P281 : Prop := ∀ x y : Value, m281 x y = divrem x y
theorem p281 : P281 := by unfold P281; intros; rfl

def m286 (x y : Value) := divrem x y
def P286 : Prop := ∀ x y : Value, m286 x y = divrem x y
theorem p286 : P286 := by unfold P286; intros; rfl

def m331 (x y : Value) := mod x y
def P331 : Prop := ∀ x y : Value, m331 x y = mod x y
theorem p331 : P331 := by unfold P331; intros; rfl

def m338 (x y : Value) := mod x y
def P338 : Prop := ∀ x y : Value, m338 x y = mod x y
theorem p338 : P338 := by unfold P338; intros; rfl

def m342 (x y : Value) := mod x y
def P342 : Prop := ∀ x y : Value, m342 x y = mod x y
theorem p342 : P342 := by unfold P342; intros; rfl

def m347 (x y : Value) := mod x y
def P347 : Prop := ∀ x y : Value, m347 x y = mod x y
theorem p347 : P347 := by unfold P347; intros; rfl

def m351 (x y : Value) := mod x y
def P351 : Prop := ∀ x y : Value, m351 x y = mod x y
theorem p351 : P351 := by unfold P351; intros; rfl

def m355 {t : IntTy} (x y : JInt t) := JInt.div x y
def P355 : Prop := ∀ t (x y : JInt t), m355 x y = JInt.div x y
theorem p355 : P355 := by unfold P355; intros; rfl

def m356 {t : IntTy} (x y : JInt t) := JInt.remInt x y
def P356 : Prop := ∀ t (x y : JInt t), m356 x y = JInt.remInt x y
theorem p356 : P356 := by unfold P356; intros; rfl

def m357 {t : IntTy} (x y : JInt t) := JInt.div x y
def P357 : Prop := ∀ t (x y : JInt t), m357 x y = JInt.div x y
theorem p357 : P357 := by unfold P357; intros; rfl

def m358 {t : IntTy} (x y : JInt t) := JInt.remInt x y
def P358 : Prop := ∀ t (x y : JInt t), m358 x y = JInt.remInt x y
theorem p358 : P358 := by unfold P358; intros; rfl

def m381 {t : IntTy} (x : JInt t) := bitNot x
def P381 : Prop := ∀ t (x : JInt t), m381 x = bitNot x
theorem p381 : P381 := by unfold P381; intros; rfl

def m407 {t : IntTy} (x y : JInt t) := bitAnd x y
def P407 : Prop := ∀ t (x y : JInt t), m407 x y = bitAnd x y
theorem p407 : P407 := by unfold P407; intros; rfl

def m432 {t : IntTy} (x y : JInt t) := bitOr x y
def P432 : Prop := ∀ t (x y : JInt t), m432 x y = bitOr x y
theorem p432 : P432 := by unfold P432; intros; rfl

def m433 {t : IntTy} (x y : JInt t) := bitXor x y
def P433 : Prop := ∀ t (x y : JInt t), m433 x y = bitXor x y
theorem p433 : P433 := by unfold P433; intros; rfl

def m457 {t : IntTy} (x : JInt t) := bswap x
def P457 : Prop := ∀ t (x : JInt t), m457 x = bswap x
theorem p457 : P457 := by unfold P457; intros; rfl

def m458 {t : IntTy} (x : JInt t) := bswap x
def P458 : Prop := ∀ t (x : JInt t), m458 x = bswap x
theorem p458 : P458 := by unfold P458; intros; rfl

def m475 {t : IntTy} (x : JInt t) := countOnes x
def P475 : Prop := ∀ t (x : JInt t), m475 x = countOnes x
theorem p475 : P475 := by unfold P475; intros; rfl

def m488 {t : IntTy} (x : JInt t) := leadingZeros x
def P488 : Prop := ∀ t (x : JInt t), m488 x = leadingZeros x
theorem p488 : P488 := by unfold P488; intros; rfl

def m501 {t : IntTy} (x : JInt t) := trailingZeros x
def P501 : Prop := ∀ t (x : JInt t), m501 x = trailingZeros x
theorem p501 : P501 := by unfold P501; intros; rfl

def m517 {t : IntTy} (x : JInt t) := t.bits - countOnes x
def P517 : Prop := ∀ t (x : JInt t), m517 x = t.bits - countOnes x
theorem p517 : P517 := by unfold P517; intros; rfl

def m530 {t : IntTy} (x : JInt t) := leadingZeros (bitNot x)
def P530 : Prop := ∀ t (x : JInt t), m530 x = leadingZeros (bitNot x)
theorem p530 : P530 := by unfold P530; intros; rfl

def m543 {t : IntTy} (x : JInt t) := trailingZeros (bitNot x)
def P543 : Prop := ∀ t (x : JInt t), m543 x = trailingZeros (bitNot x)
theorem p543 : P543 := by unfold P543; intros; rfl

def m569 {t : IntTy} (x : JInt t) := topSetBit x
def P569 : Prop := ∀ t (x : JInt t), m569 x = topSetBit x
theorem p569 : P569 := by unfold P569; intros; rfl

def m573 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .lt x y
def P573 : Prop := ∀ t s (x : JInt t) (y : JInt s), m573 x y = JuliaLean.Promotion.intCmp .lt x y
theorem p573 : P573 := by unfold P573; intros; rfl

def m574 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .le x y
def P574 : Prop := ∀ t s (x : JInt t) (y : JInt s), m574 x y = JuliaLean.Promotion.intCmp .le x y
theorem p574 : P574 := by unfold P574; intros; rfl

def m575 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .le x y
def P575 : Prop := ∀ t s (x : JInt t) (y : JInt s), m575 x y = JuliaLean.Promotion.intCmp .le x y
theorem p575 : P575 := by unfold P575; intros; rfl

def m577 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .eq x y
def P577 : Prop := ∀ t s (x : JInt t) (y : JInt s), m577 x y = JuliaLean.Promotion.intCmp .eq x y
theorem p577 : P577 := by unfold P577; intros; rfl

def m578 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .lt x y
def P578 : Prop := ∀ t s (x : JInt t) (y : JInt s), m578 x y = JuliaLean.Promotion.intCmp .lt x y
theorem p578 : P578 := by unfold P578; intros; rfl

def m579 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .le x y
def P579 : Prop := ∀ t s (x : JInt t) (y : JInt s), m579 x y = JuliaLean.Promotion.intCmp .le x y
theorem p579 : P579 := by unfold P579; intros; rfl

def m582 {t s : IntTy} (x : JInt t) (y : JInt s) := JuliaLean.Promotion.intCmp .eq x y
def P582 : Prop := ∀ t s (x : JInt t) (y : JInt s), m582 x y = JuliaLean.Promotion.intCmp .eq x y
theorem p582 : P582 := by unfold P582; intros; rfl

def m591 (x y : Value) := intMax x y
def P591 : Prop := ∀ x y : Value, m591 x y = intMax x y
theorem p591 : P591 := by unfold P591; intros; rfl

def m596 (x y : Value) := intMin x y
def P596 : Prop := ∀ x y : Value, m596 x y = intMin x y
theorem p596 : P596 := by unfold P596; intros; rfl

def m597 (x y : Value) := intMin x y
def P597 : Prop := ∀ x y : Value, m597 x y = intMin x y
theorem p597 : P597 := by unfold P597; intros; rfl

def m599 (x y : Value) := intMinmax x y
def P599 : Prop := ∀ x y : Value, m599 x y = intMinmax x y
theorem p599 : P599 := by unfold P599; intros; rfl

def m604 {t : IntTy} (x : JInt t) (k : Nat) := ashr x k
def P604 : Prop := ∀ t (x : JInt t) k, m604 x k = ashr x k
theorem p604 : P604 := by unfold P604; intros; rfl

def m605 {t : IntTy} (x : JInt t) (k : Nat) := lshr x k
def P605 : Prop := ∀ t (x : JInt t) k, m605 x k = lshr x k
theorem p605 : P605 := by unfold P605; intros; rfl

def m606 {t : IntTy} (x : JInt t) (k : Nat) := JuliaLean.FloatIntCov.Int.shl x k
def P606 : Prop := ∀ t (x : JInt t) k, m606 x k = JuliaLean.FloatIntCov.Int.shl x k
theorem p606 : P606 := by unfold P606; intros; rfl

def m607 {t : IntTy} (x : JInt t) (k : Nat) := lshr x k
def P607 : Prop := ∀ t (x : JInt t) k, m607 x k = lshr x k
theorem p607 : P607 := by unfold P607; intros; rfl

def m611 {t : IntTy} (x : JInt t) (k : Int) := shrInt x k
def P611 : Prop := ∀ t (x : JInt t) k, m611 x k = shrInt x k
theorem p611 : P611 := by unfold P611; intros; rfl

def m613 {t : IntTy} (x : JInt t) (k : Int) := shlInt x k
def P613 : Prop := ∀ t (x : JInt t) k, m613 x k = shlInt x k
theorem p613 : P613 := by unfold P613; intros; rfl

def m615 {t : IntTy} (x : JInt t) (k : Int) := lshrInt x k
def P615 : Prop := ∀ t (x : JInt t) k, m615 x k = lshrInt x k
theorem p615 : P615 := by unfold P615; intros; rfl

def m621 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P621 : Prop := ∀ to src (x : JInt src), m621 to x = remType to x
theorem p621 : P621 := by unfold P621; intros; rfl

def m623 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P623 : Prop := ∀ to src (x : JInt src), m623 to x = remType to x
theorem p623 : P623 := by unfold P623; intros; rfl

def m626 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P626 : Prop := ∀ to src (x : JInt src), m626 to x = remType to x
theorem p626 : P626 := by unfold P626; intros; rfl

def m628 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P628 : Prop := ∀ to src (x : JInt src), m628 to x = remType to x
theorem p628 : P628 := by unfold P628; intros; rfl

def m631 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P631 : Prop := ∀ to src (x : JInt src), m631 to x = remType to x
theorem p631 : P631 := by unfold P631; intros; rfl

def m664 {t : IntTy} (x : JInt t) (k : Int) := bitrotate x k
def P664 : Prop := ∀ t (x : JInt t) k, m664 x k = bitrotate x k
theorem p664 : P664 := by unfold P664; intros; rfl

def m695 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P695 : Prop := ∀ to src (x : JInt src), m695 to x = remType to x
theorem p695 : P695 := by unfold P695; intros; rfl

def m696 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P696 : Prop := ∀ to src (x : JInt src), m696 to x = remType to x
theorem p696 : P696 := by unfold P696; intros; rfl

def m697 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P697 : Prop := ∀ to src (x : JInt src), m697 to x = remType to x
theorem p697 : P697 := by unfold P697; intros; rfl

def m698 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P698 : Prop := ∀ to src (x : JInt src), m698 to x = remType to x
theorem p698 : P698 := by unfold P698; intros; rfl

def m699 {t : IntTy} (x : JInt t) := remBool x
def P699 : Prop := ∀ t (x : JInt t), m699 x = remBool x
theorem p699 : P699 := by unfold P699; intros; rfl

def m700 {α : Type} (_u : Unit) : Jl α := unionTypeError (α := α) "rem"
def P700 : Prop := ∀ (α : Type) (u : Unit), m700 u = unionTypeError (α := α) "rem"
theorem p700 : P700 := by unfold P700; intros; rfl

def m701 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P701 : Prop := ∀ to src (x : JInt src), m701 to x = remType to x
theorem p701 : P701 := by unfold P701; intros; rfl

def m702 {α : Type} (_u : Unit) : Jl α := unionTypeError (α := α) "mod"
def P702 : Prop := ∀ (α : Type) (u : Unit), m702 u = unionTypeError (α := α) "mod"
theorem p702 : P702 := by unfold P702; intros; rfl

def m704 (to : IntTy) {src : IntTy} (x : JInt src) := remType to x
def P704 : Prop := ∀ to src (x : JInt src), m704 to x = remType to x
theorem p704 : P704 := by unfold P704; intros; rfl

def m705 {α : Type} (_u : Unit) : Jl α := unionTypeError (α := α) "unsafe_trunc"
def P705 : Prop := ∀ (α : Type) (u : Unit), m705 u = unionTypeError (α := α) "unsafe_trunc"
theorem p705 : P705 := by unfold P705; intros; rfl

def m725 {α : Type} (parse : List Char → Jl α) (s : List Char) := integerStringMacro parse s
def P725 : Prop := ∀ (α : Type) (parse : List Char → Jl α) s,
  m725 parse s = integerStringMacro parse s
theorem p725 : P725 := by unfold P725; intros; rfl

def m745 {α : Type} (parse : List Char → Jl α) (s : List Char) := integerStringMacro parse s
def P745 : Prop := ∀ (α : Type) (parse : List Char → Jl α) s,
  m745 parse s = integerStringMacro parse s
theorem p745 : P745 := by unfold P745; intros; rfl

def m778 {α : Type} (normalize : List Char → Jl (List Char)) (tryInt tryFloat : List Char → Option α) (s : List Char) := bigStringMacro normalize tryInt tryFloat s
def P778 : Prop := ∀ (α : Type) (normalize : List Char → Jl (List Char))
  (tryInt tryFloat : List Char → Option α) s,
  m778 normalize tryInt tryFloat s = bigStringMacro normalize tryInt tryFloat s
theorem p778 : P778 := by unfold P778; intros; rfl

def m809 (_u : Unit) : IntTy := .i16
def P809 : Prop := ∀ u : Unit, m809 u = .i16
theorem p809 : P809 := by unfold P809; intros; rfl

def m810 (_u : Unit) : IntTy := .i32
def P810 : Prop := ∀ u : Unit, m810 u = .i32
theorem p810 : P810 := by unfold P810; intros; rfl

def m811 (_u : Unit) : IntTy := .i64
def P811 : Prop := ∀ u : Unit, m811 u = .i64
theorem p811 : P811 := by unfold P811; intros; rfl

def m812 (_u : Unit) : IntTy := .i128
def P812 : Prop := ∀ u : Unit, m812 u = .i128
theorem p812 : P812 := by unfold P812; intros; rfl

def m813 (_u : Unit) : IntTy := .u16
def P813 : Prop := ∀ u : Unit, m813 u = .u16
theorem p813 : P813 := by unfold P813; intros; rfl

def m814 (_u : Unit) : IntTy := .u32
def P814 : Prop := ∀ u : Unit, m814 u = .u32
theorem p814 : P814 := by unfold P814; intros; rfl

def m815 (_u : Unit) : IntTy := .u64
def P815 : Prop := ∀ u : Unit, m815 u = .u64
theorem p815 : P815 := by unfold P815; intros; rfl

def m816 (_u : Unit) : IntTy := .u128
def P816 : Prop := ∀ u : Unit, m816 u = .u128
theorem p816 : P816 := by unfold P816; intros; rfl

def m818 (_u : Unit) : IntTy := .u8
def P818 : Prop := ∀ u : Unit, m818 u = .u8
theorem p818 : P818 := by unfold P818; intros; rfl

def m819 (_u : Unit) : IntTy := .u16
def P819 : Prop := ∀ u : Unit, m819 u = .u16
theorem p819 : P819 := by unfold P819; intros; rfl

def m820 (_u : Unit) : IntTy := .u32
def P820 : Prop := ∀ u : Unit, m820 u = .u32
theorem p820 : P820 := by unfold P820; intros; rfl

def m821 (_u : Unit) : IntTy := .u64
def P821 : Prop := ∀ u : Unit, m821 u = .u64
theorem p821 : P821 := by unfold P821; intros; rfl

def m822 (_u : Unit) : IntTy := .u128
def P822 : Prop := ∀ u : Unit, m822 u = .u128
theorem p822 : P822 := by unfold P822; intros; rfl

def m887 (_u : Unit) : JInt .i8 := JInt.typemin .i8
def P887 : Prop := ∀ u : Unit, m887 u = JInt.typemin .i8
theorem p887 : P887 := by unfold P887; intros; rfl

def m888 (_u : Unit) : JInt .i8 := JInt.typemax .i8
def P888 : Prop := ∀ u : Unit, m888 u = JInt.typemax .i8
theorem p888 : P888 := by unfold P888; intros; rfl

def m889 (_u : Unit) : JInt .u8 := JInt.typemin .u8
def P889 : Prop := ∀ u : Unit, m889 u = JInt.typemin .u8
theorem p889 : P889 := by unfold P889; intros; rfl

def m890 (_u : Unit) : JInt .u8 := JInt.typemax .u8
def P890 : Prop := ∀ u : Unit, m890 u = JInt.typemax .u8
theorem p890 : P890 := by unfold P890; intros; rfl

def m891 (_u : Unit) : JInt .i16 := JInt.typemin .i16
def P891 : Prop := ∀ u : Unit, m891 u = JInt.typemin .i16
theorem p891 : P891 := by unfold P891; intros; rfl

def m892 (_u : Unit) : JInt .i16 := JInt.typemax .i16
def P892 : Prop := ∀ u : Unit, m892 u = JInt.typemax .i16
theorem p892 : P892 := by unfold P892; intros; rfl

def m893 (_u : Unit) : JInt .u16 := JInt.typemin .u16
def P893 : Prop := ∀ u : Unit, m893 u = JInt.typemin .u16
theorem p893 : P893 := by unfold P893; intros; rfl

def m894 (_u : Unit) : JInt .u16 := JInt.typemax .u16
def P894 : Prop := ∀ u : Unit, m894 u = JInt.typemax .u16
theorem p894 : P894 := by unfold P894; intros; rfl

def m895 (_u : Unit) : JInt .i32 := JInt.typemin .i32
def P895 : Prop := ∀ u : Unit, m895 u = JInt.typemin .i32
theorem p895 : P895 := by unfold P895; intros; rfl

def m896 (_u : Unit) : JInt .i32 := JInt.typemax .i32
def P896 : Prop := ∀ u : Unit, m896 u = JInt.typemax .i32
theorem p896 : P896 := by unfold P896; intros; rfl

def m897 (_u : Unit) : JInt .u32 := JInt.typemin .u32
def P897 : Prop := ∀ u : Unit, m897 u = JInt.typemin .u32
theorem p897 : P897 := by unfold P897; intros; rfl

def m898 (_u : Unit) : JInt .u32 := JInt.typemax .u32
def P898 : Prop := ∀ u : Unit, m898 u = JInt.typemax .u32
theorem p898 : P898 := by unfold P898; intros; rfl

def m899 (_u : Unit) : JInt .i64 := JInt.typemin .i64
def P899 : Prop := ∀ u : Unit, m899 u = JInt.typemin .i64
theorem p899 : P899 := by unfold P899; intros; rfl

def m900 (_u : Unit) : JInt .i64 := JInt.typemax .i64
def P900 : Prop := ∀ u : Unit, m900 u = JInt.typemax .i64
theorem p900 : P900 := by unfold P900; intros; rfl

def m901 (_u : Unit) : JInt .u64 := JInt.typemin .u64
def P901 : Prop := ∀ u : Unit, m901 u = JInt.typemin .u64
theorem p901 : P901 := by unfold P901; intros; rfl

def m902 (_u : Unit) : JInt .u64 := JInt.typemax .u64
def P902 : Prop := ∀ u : Unit, m902 u = JInt.typemax .u64
theorem p902 : P902 := by unfold P902; intros; rfl

def m903 (_u : Unit) : JInt .u128 := JInt.typemin .u128
def P903 : Prop := ∀ u : Unit, m903 u = JInt.typemin .u128
theorem p903 : P903 := by unfold P903; intros; rfl

def m904 (_u : Unit) : JInt .u128 := JInt.typemax .u128
def P904 : Prop := ∀ u : Unit, m904 u = JInt.typemax .u128
theorem p904 : P904 := by unfold P904; intros; rfl

def m905 (_u : Unit) : JInt .i128 := JInt.typemin .i128
def P905 : Prop := ∀ u : Unit, m905 u = JInt.typemin .i128
theorem p905 : P905 := by unfold P905; intros; rfl

def m906 (_u : Unit) : JInt .i128 := JInt.typemax .i128
def P906 : Prop := ∀ u : Unit, m906 u = JInt.typemax .i128
theorem p906 : P906 := by unfold P906; intros; rfl

def m907 {α : Type} (_u : Unit) : Jl α := unionTypeError (α := α) "typemin"
def P907 : Prop := ∀ (α : Type) (u : Unit), m907 u = unionTypeError (α := α) "typemin"
theorem p907 : P907 := by unfold P907; intros; rfl

def m908 {α : Type} (_u : Unit) : Jl α := unionTypeError (α := α) "typemax"
def P908 : Prop := ∀ (α : Type) (u : Unit), m908 u = unionTypeError (α := α) "typemax"
theorem p908 : P908 := by unfold P908; intros; rfl

def m911 (_u : Unit) : IntTy := .i16
def P911 : Prop := ∀ u : Unit, m911 u = .i16
theorem p911 : P911 := by unfold P911; intros; rfl

def m912 (_u : Unit) : IntTy := .i32
def P912 : Prop := ∀ u : Unit, m912 u = .i32
theorem p912 : P912 := by unfold P912; intros; rfl

def m913 (_u : Unit) : IntTy := .i64
def P913 : Prop := ∀ u : Unit, m913 u = .i64
theorem p913 : P913 := by unfold P913; intros; rfl

def m914 (_u : Unit) : IntTy := .i128
def P914 : Prop := ∀ u : Unit, m914 u = .i128
theorem p914 : P914 := by unfold P914; intros; rfl

def m915 (_u : Unit) : IntTy := .u16
def P915 : Prop := ∀ u : Unit, m915 u = .u16
theorem p915 : P915 := by unfold P915; intros; rfl

def m916 (_u : Unit) : IntTy := .u32
def P916 : Prop := ∀ u : Unit, m916 u = .u32
theorem p916 : P916 := by unfold P916; intros; rfl

def m917 (_u : Unit) : IntTy := .u64
def P917 : Prop := ∀ u : Unit, m917 u = .u64
theorem p917 : P917 := by unfold P917; intros; rfl

def m918 (_u : Unit) : IntTy := .u128
def P918 : Prop := ∀ u : Unit, m918 u = .u128
theorem p918 : P918 := by unfold P918; intros; rfl

def m923 {t s : IntTy} (x : JInt t) (y : JInt s) := widemul x y
def P923 : Prop := ∀ t s (x : JInt t) (y : JInt s), m923 x y = widemul x y
theorem p923 : P923 := by unfold P923; intros; rfl

def m924 {t s : IntTy} (x : JInt t) (y : JInt s) := widemul x y
def P924 : Prop := ∀ t s (x : JInt t) (y : JInt s), m924 x y = widemul x y
theorem p924 : P924 := by unfold P924; intros; rfl

def m926 {t s : IntTy} (x : JInt t) (y : JInt s) := widemul x y
def P926 : Prop := ∀ t s (x : JInt t) (y : JInt s), m926 x y = widemul x y
theorem p926 : P926 := by unfold P926; intros; rfl

def m927 {t s : IntTy} (x : JInt t) (y : JInt s) := widemul x y
def P927 : Prop := ∀ t s (x : JInt t) (y : JInt s), m927 x y = widemul x y
theorem p927 : P927 := by unfold P927; intros; rfl

def m928 {t s : IntTy} (x : JInt t) (y : JInt s) := widemul x y
def P928 : Prop := ∀ t s (x : JInt t) (y : JInt s), m928 x y = widemul x y
theorem p928 : P928 := by unfold P928; intros; rfl

def m1083 {t : IntTy} (x y : JInt t) := x * y
def P1083 : Prop := ∀ t (x y : JInt t), m1083 x y = x * y
theorem p1083 : P1083 := by unfold P1083; intros; rfl

def m1085 (x y : JInt .i128) := JInt.div x y
def P1085 : Prop := ∀ x y : JInt .i128, m1085 x y = JInt.div x y
theorem p1085 : P1085 := by unfold P1085; intros; rfl

def m1086 (x y : JInt .u128) := JInt.div x y
def P1086 : Prop := ∀ x y : JInt .u128, m1086 x y = JInt.div x y
theorem p1086 : P1086 := by unfold P1086; intros; rfl

def m1088 (x y : JInt .i128) := JInt.remInt x y
def P1088 : Prop := ∀ x y : JInt .i128, m1088 x y = JInt.remInt x y
theorem p1088 : P1088 := by unfold P1088; intros; rfl

def m1089 (x y : JInt .u128) := JInt.remInt x y
def P1089 : Prop := ∀ x y : JInt .u128, m1089 x y = JInt.remInt x y
theorem p1089 : P1089 := by unfold P1089; intros; rfl

def m1094 (op : {t : IntTy} → JInt t → JInt t → JInt t) (x y : Value) := promotedBinary op x y
def P1094 : Prop := ∀ op (x y : Value), m1094 op x y = promotedBinary op x y
theorem p1094 : P1094 := by unfold P1094; intros; rfl

def m1124 {t : IntTy} (x : JInt t) := bitreverse x
def P1124 : Prop := ∀ t (x : JInt t), m1124 x = bitreverse x
theorem p1124 : P1124 := by unfold P1124; intros; rfl

private def mk (line : Nat) (name : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"floatintcov-int-l{line}", juliaFile := "base/int.jl", juliaFns := [name]
    statement := s!"The method at base/int.jl:{line} follows its method-specific source model for every allowed input."
    source := s!"base/int.jl:{line}", status := .proven, prop, thm := some thm }

def entries : List Entry := [
  mk 73 "signed(::Type{Bool})" ``P73 ``p73,
  mk 74 "signed(::Type{UInt8})" ``P74 ``p74,
  mk 75 "signed(::Type{UInt16})" ``P75 ``p75,
  mk 76 "signed(::Type{UInt32})" ``P76 ``p76,
  mk 77 "signed(::Type{UInt64})" ``P77 ``p77,
  mk 78 "signed(::Type{UInt128})" ``P78 ``p78,
  mk 79 "signed(::Type{T}) where {T<:Signed}" ``P79 ``p79,
  mk 80 "signed(::Type{Union{}}, slurp...)" ``P80 ``p80,
  mk 84 "(<)(x::T, y::T) where {T<:BitSigned}" ``P84 ``p84,
  mk 86 "(-)(x::BitInteger)" ``P86 ``p86,
  mk 87 "(-)(x::T, y::T) where {T<:BitInteger}" ``P87 ``p87,
  mk 88 "(+)(x::T, y::T) where {T<:BitInteger}" ``P88 ``p88,
  mk 89 "(*)(x::T, y::T) where {T<:BitInteger}" ``P89 ``p89,
  mk 91 "(-%)(x::BitInteger)" ``P91 ``p91,
  mk 92 "(-%)(x::T, y::T) where {T<:BitInteger}" ``P92 ``p92,
  mk 93 "(+%)(x::T, y::T) where {T<:BitInteger}" ``P93 ``p93,
  mk 94 "(*%)(x::T, y::T) where {T<:BitInteger}" ``P94 ``p94,
  mk 96 "negate(x)" ``P96 ``p96,
  mk 97 "negate(x::Unsigned)" ``P97 ``p97,
  mk 100 "inv(x::Integer)" ``P100 ``p100,
  mk 101 "(/)(x::T, y::T) where {T<:Integer}" ``P101 ``p101,
  mk 103 "(/)(x::BitInteger, y::BitInteger)" ``P103 ``p103,
  mk 123 "mul_hi(a::T, b::T) where {T<:Integer}" ``P123 ``p123,
  mk 127 "mul_hi(a::UInt128, b::UInt128)" ``P127 ``p127,
  mk 137 "mul_hi(a::Int128, b::Int128)" ``P137 ``p137,
  mk 160 "isodd(n::Number)" ``P160 ``p160,
  mk 161 "isodd(n::Real)" ``P161 ``p161,
  mk 180 "iseven(n::Number)" ``P180 ``p180,
  mk 181 "iseven(n::Real)" ``P181 ``p181,
  mk 183 "signbit(x::Integer)" ``P183 ``p183,
  mk 184 "signbit(x::Unsigned)" ``P184 ``p184,
  mk 186 "isnegative(x::Unsigned)" ``P186 ``p186,
  mk 188 "flipsign(x::T, y::T) where {T<:BitSigned}" ``P188 ``p188,
  mk 189 "flipsign(x::BitSigned, y::BitSigned)" ``P189 ``p189,
  mk 191 "flipsign(x::Signed, y::Float16)" ``P191 ``p191,
  mk 192 "flipsign(x::Signed, y::Float32)" ``P192 ``p192,
  mk 193 "flipsign(x::Signed, y::Float64)" ``P193 ``p193,
  mk 194 "flipsign(x::Signed, y::Real)" ``P194 ``p194,
  mk 196 "copysign(x::Signed, y::Signed)" ``P196 ``p196,
  mk 197 "copysign(x::Signed, y::Float16)" ``P197 ``p197,
  mk 198 "copysign(x::Signed, y::Float32)" ``P198 ``p198,
  mk 199 "copysign(x::Signed, y::Float64)" ``P199 ``p199,
  mk 200 "copysign(x::Signed, y::Real)" ``P200 ``p200,
  mk 233 "abs(x::Unsigned)" ``P233 ``p233,
  mk 234 "abs(x::Signed)" ``P234 ``p234,
  mk 236 "~(n::Integer)" ``P236 ``p236,
  mk 261 "unsigned(x)" ``P261 ``p261,
  mk 262 "unsigned(x::BitSigned)" ``P262 ``p262,
  mk 272 "signed(x)" ``P272 ``p272,
  mk 273 "signed(x::BitUnsigned)" ``P273 ``p273,
  mk 275 "div(x::BitSigned, y::Unsigned)" ``P275 ``p275,
  mk 276 "div(x::Unsigned, y::BitSigned)" ``P276 ``p276,
  mk 278 "rem(x::BitSigned, y::Unsigned)" ``P278 ``p278,
  mk 279 "rem(x::Unsigned, y::BitSigned)" ``P279 ``p279,
  mk 281 "divrem(x::BitSigned, y::Unsigned)" ``P281 ``p281,
  mk 286 "divrem(x::Unsigned, y::BitSigned)" ``P286 ``p286,
  mk 331 "mod(x::T, y::T) where T<:Integer" ``P331 ``p331,
  mk 338 "mod(x::T, y::T) where T<:BitSigned" ``P338 ``p338,
  mk 342 "mod(x::BitSigned, y::Unsigned)" ``P342 ``p342,
  mk 347 "mod(x::Unsigned, y::Signed)" ``P347 ``p347,
  mk 351 "mod(x::T, y::T) where {T<:Unsigned}" ``P351 ``p351,
  mk 355 "div(x::T, y::T) where {T<:BitSigned64}" ``P355 ``p355,
  mk 356 "rem(x::T, y::T) where {T<:BitSigned64}" ``P356 ``p356,
  mk 357 "div(x::T, y::T) where {T<:BitUnsigned64}" ``P357 ``p357,
  mk 358 "rem(x::T, y::T) where {T<:BitUnsigned64}" ``P358 ``p358,
  mk 381 "(~)(x::BitInteger)" ``P381 ``p381,
  mk 407 "(&)(x::T, y::T) where {T<:BitInteger}" ``P407 ``p407,
  mk 432 "(|)(x::T, y::T) where {T<:BitInteger}" ``P432 ``p432,
  mk 433 "xor(x::T, y::T) where {T<:BitInteger}" ``P433 ``p433,
  mk 457 "bswap(x::Union{Int8, UInt8, Bool})" ``P457 ``p457,
  mk 458 "bswap(x::Union{Int16, UInt16, Int32, UInt32, Int64, UInt64, Int128, UInt128})" ``P458 ``p458,
  mk 475 "count_ones(x::BitInteger)" ``P475 ``p475,
  mk 488 "leading_zeros(x::BitInteger)" ``P488 ``p488,
  mk 501 "trailing_zeros(x::BitInteger)" ``P501 ``p501,
  mk 517 "count_zeros(x::Integer)" ``P517 ``p517,
  mk 530 "leading_ones(x::Integer)" ``P530 ``p530,
  mk 543 "trailing_ones(x::Integer)" ``P543 ``p543,
  mk 569 "top_set_bit(x::BitInteger)" ``P569 ``p569,
  mk 573 "(< )(x::T, y::T) where {T<:BitUnsigned}" ``P573 ``p573,
  mk 574 "(<=)(x::T, y::T) where {T<:BitSigned}" ``P574 ``p574,
  mk 575 "(<=)(x::T, y::T) where {T<:BitUnsigned}" ``P575 ``p575,
  mk 577 "==(x::BitSigned, y::BitUnsigned)" ``P577 ``p577,
  mk 578 "<(x::BitSigned, y::BitUnsigned)" ``P578 ``p578,
  mk 579 "<=(x::BitSigned, y::BitUnsigned)" ``P579 ``p579,
  mk 582 "$op(x::BitUnsigned, y::BitSigned)" ``P582 ``p582,
  mk 591 "max(x::S, y::T) where {S <: BitInteger, T <: BitInteger}" ``P591 ``p591,
  mk 596 "min(x::S, y::BitUnsigned) where S <: BitSigned" ``P596 ``p596,
  mk 597 "min(x::BitUnsigned, y::T) where T <: BitSigned" ``P597 ``p597,
  mk 599 "minmax(x::BitInteger, y::BitInteger)" ``P599 ``p599,
  mk 604 ">>(x::BitSigned, y::BitUnsigned)" ``P604 ``p604,
  mk 605 ">>(x::BitUnsigned, y::BitUnsigned)" ``P605 ``p605,
  mk 606 "<<(x::BitInteger, y::BitUnsigned)" ``P606 ``p606,
  mk 607 ">>>(x::BitInteger, y::BitUnsigned)" ``P607 ``p607,
  mk 611 ">>(x::BitInteger, y::Int)" ``P611 ``p611,
  mk 613 "<<(x::BitInteger, y::Int)" ``P613 ``p613,
  mk 615 ">>>(x::BitInteger, y::Int)" ``P615 ``p615,
  mk 621 "rem(x::($from), ::Type{$to})" ``P621 ``p621,
  mk 623 "rem(x::($from), ::Type{$to})" ``P623 ``p623,
  mk 626 "rem(x::($from), ::Type{$to})" ``P626 ``p626,
  mk 628 "rem(x::($from), ::Type{$to})" ``P628 ``p628,
  mk 631 "rem(x::($from), ::Type{$to})" ``P631 ``p631,
  mk 664 "bitrotate(x::T, k::Integer) where {T <: BitInteger}" ``P664 ``p664,
  mk 695 "rem(x::T, ::Type{T}) where {T<:Integer}" ``P695 ``p695,
  mk 696 "rem(x::Signed, ::Type{Unsigned})" ``P696 ``p696,
  mk 697 "rem(x::Unsigned, ::Type{Signed})" ``P697 ``p697,
  mk 698 "rem(x::Integer, T::Type{<:Integer})" ``P698 ``p698,
  mk 699 "rem(x::Integer, ::Type{Bool})" ``P699 ``p699,
  mk 700 "rem(x, ::Type{Union{}}, slurp...)" ``P700 ``p700,
  mk 701 "mod(x::Integer, ::Type{T}) where {T<:Integer}" ``P701 ``p701,
  mk 702 "mod(x, ::Type{Union{}}, slurp...)" ``P702 ``p702,
  mk 704 "unsafe_trunc(::Type{T}, x::Integer) where {T<:Integer}" ``P704 ``p704,
  mk 705 "unsafe_trunc(::Type{Union{}}, slurp...)" ``P705 ``p705,
  mk 725 "int128_str(s::String)" ``P725 ``p725,
  mk 745 "uint128_str(s::String)" ``P745 ``p745,
  mk 778 "big_str(s::String)" ``P778 ``p778,
  mk 809 "promote_rule(::Type{Int16}, ::Union{Type{Int8}, Type{UInt8}})" ``P809 ``p809,
  mk 810 "promote_rule(::Type{Int32}, ::Union{Type{Int16}, Type{Int8}, Type{UInt16}, Type{UInt8}})" ``P810 ``p810,
  mk 811 "promote_rule(::Type{Int64}, ::Union{Type{Int16}, Type{Int32}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt8}})" ``P811 ``p811,
  mk 812 "promote_rule(::Type{Int128}, ::Union{Type{Int16}, Type{Int32}, Type{Int64}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt64}, Type{UInt8}})" ``P812 ``p812,
  mk 813 "promote_rule(::Type{UInt16}, ::Union{Type{Int8}, Type{UInt8}})" ``P813 ``p813,
  mk 814 "promote_rule(::Type{UInt32}, ::Union{Type{Int16}, Type{Int8}, Type{UInt16}, Type{UInt8}})" ``P814 ``p814,
  mk 815 "promote_rule(::Type{UInt64}, ::Union{Type{Int16}, Type{Int32}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt8}})" ``P815 ``p815,
  mk 816 "promote_rule(::Type{UInt128}, ::Union{Type{Int16}, Type{Int32}, Type{Int64}, Type{Int8}, Type{UInt16}, Type{UInt32}, Type{UInt64}, Type{UInt8}})" ``P816 ``p816,
  mk 818 "promote_rule(::Type{UInt8}, ::Type{Int8} )" ``P818 ``p818,
  mk 819 "promote_rule(::Type{UInt16}, ::Type{Int16} )" ``P819 ``p819,
  mk 820 "promote_rule(::Type{UInt32}, ::Type{Int32} )" ``P820 ``p820,
  mk 821 "promote_rule(::Type{UInt64}, ::Type{Int64} )" ``P821 ``p821,
  mk 822 "promote_rule(::Type{UInt128}, ::Type{Int128})" ``P822 ``p822,
  mk 887 "typemin(::Type{Int8 })" ``P887 ``p887,
  mk 888 "typemax(::Type{Int8 })" ``P888 ``p888,
  mk 889 "typemin(::Type{UInt8 })" ``P889 ``p889,
  mk 890 "typemax(::Type{UInt8 })" ``P890 ``p890,
  mk 891 "typemin(::Type{Int16 })" ``P891 ``p891,
  mk 892 "typemax(::Type{Int16 })" ``P892 ``p892,
  mk 893 "typemin(::Type{UInt16})" ``P893 ``p893,
  mk 894 "typemax(::Type{UInt16})" ``P894 ``p894,
  mk 895 "typemin(::Type{Int32 })" ``P895 ``p895,
  mk 896 "typemax(::Type{Int32 })" ``P896 ``p896,
  mk 897 "typemin(::Type{UInt32})" ``P897 ``p897,
  mk 898 "typemax(::Type{UInt32})" ``P898 ``p898,
  mk 899 "typemin(::Type{Int64 })" ``P899 ``p899,
  mk 900 "typemax(::Type{Int64 })" ``P900 ``p900,
  mk 901 "typemin(::Type{UInt64})" ``P901 ``p901,
  mk 902 "typemax(::Type{UInt64})" ``P902 ``p902,
  mk 903 "typemin(::Type{UInt128})" ``P903 ``p903,
  mk 904 "typemax(::Type{UInt128})" ``P904 ``p904,
  mk 905 "typemin(::Type{Int128} )" ``P905 ``p905,
  mk 906 "typemax(::Type{Int128} )" ``P906 ``p906,
  mk 907 "typemin(::Type{Union{}}, slurp...)" ``P907 ``p907,
  mk 908 "typemax(::Type{Union{}}, slurp...)" ``P908 ``p908,
  mk 911 "widen(::Type{Int8})" ``P911 ``p911,
  mk 912 "widen(::Type{Int16})" ``P912 ``p912,
  mk 913 "widen(::Type{Int32})" ``P913 ``p913,
  mk 914 "widen(::Type{Int64})" ``P914 ``p914,
  mk 915 "widen(::Type{UInt8})" ``P915 ``p915,
  mk 916 "widen(::Type{UInt16})" ``P916 ``p916,
  mk 917 "widen(::Type{UInt32})" ``P917 ``p917,
  mk 918 "widen(::Type{UInt64})" ``P918 ``p918,
  mk 923 "widemul(x::Signed,y::Unsigned)" ``P923 ``p923,
  mk 924 "widemul(x::Unsigned,y::Signed)" ``P924 ``p924,
  mk 926 "widemul(x::Bool,y::Bool)" ``P926 ``p926,
  mk 927 "widemul(x::Bool,y::Number)" ``P927 ``p927,
  mk 928 "widemul(x::Number,y::Bool)" ``P928 ``p928,
  mk 1083 "*(x::T, y::T) where {T<:Union{Int128,UInt128}}" ``P1083 ``p1083,
  mk 1085 "div(x::Int128, y::Int128)" ``P1085 ``p1085,
  mk 1086 "div(x::UInt128, y::UInt128)" ``P1086 ``p1086,
  mk 1088 "rem(x::Int128, y::Int128)" ``P1088 ``p1088,
  mk 1089 "rem(x::UInt128, y::UInt128)" ``P1089 ``p1089,
  mk 1094 "$op(a::Integer, b::Integer)" ``P1094 ``p1094,
  mk 1124 "bitreverse(x::BitInteger)" ``P1124 ``p1124
]

end JuliaLean.FloatIntCov.IntRows
