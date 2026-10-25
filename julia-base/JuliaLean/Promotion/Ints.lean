import JuliaLean.Promotion.Compare

/-!
Comparison between two `BitInteger` types at master `bbfa0ce4150`: same-type intrinsics
(`base/int.jl:569-575`, `base/promotion.jl:516-518` for equal-signedness promotion), and the
mixed-signedness methods `base/int.jl:577-589`.
-/

namespace JuliaLean.Promotion

/-- `op(x::Ti, y::Ts)` for two `BitInteger`s. Equal signedness promotes to the wider type
(`base/int.jl:809-822`) and compares there; a signed/unsigned pair uses
`base/int.jl:577-579`; an unsigned/signed pair uses `base/int.jl:581-589`. -/
def intCmp (op : Op) {t s : IntTy} (x : JInt t) (y : JInt s) : Bool :=
  if t.signed = s.signed then
    let p := t.promote s
    op.int (JInt.wrap p x.val).val (JInt.wrap p y.val).val
  else if t.signed then
    match op with
    | .eq => unsignedSigned .eq y x
    | .lt => !unsignedSigned .le y x
    | .le => !unsignedSigned .lt y x
  else unsignedSigned op x y
where
  /-- `base/int.jl:581-589`: `x` unsigned, `y` signed. -/
  unsignedSigned (op : Op) {u v : IntTy} (x : JInt u) (y : JInt v) : Bool :=
    if u.bits < v.bits then op.int (JInt.wrap v x.val).val y.val
    else decide (0 ≤ y.val) && op.int x.val (JInt.wrap u (JInt.wrap v.toUnsigned y.val).val).val

end JuliaLean.Promotion
