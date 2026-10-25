import JuliaLean.Serialization.State

/-!
`handle_deserialize` on each tag the serializer writes, and the decoding of
scalars, strings, symbols, backreferences and modules.
-/

namespace JuliaLean.Serialization

open JuliaLean

/-! ### Dispatch -/

theorem handle_zero (f : Nat) :
    handle (f + 1) 0 = (do let b' ← readU8; desertag b'.toNat) := rfl
theorem handle_value (f b : Nat) (h : 68 ≤ b) : handle (f + 1) b = desertag b := by
  simp only [handle]; rw [if_neg (by omega), if_pos h]
theorem handle_tuple (f : Nat) :
    handle (f + 1) 20 = (do let n ← readU8; deserTuple (deser f) n.toNat) := rfl
theorem handle_shortbackref (f : Nat) :
    handle (f + 1) 44 = (do let id ← readLE 2; getBackref id) := rfl
theorem handle_backref (f : Nat) :
    handle (f + 1) 42 = (do let id ← readInt .i32; getBackref id) := rfl
theorem handle_longbackref (f : Nat) :
    handle (f + 1) 43 = (do let id ← readInt .i64; getBackref id) := rfl
theorem handle_array (f : Nat) : handle (f + 1) 21 = deserArray (deser f) (handle f) := rfl
theorem handle_datatype (f : Nat) : handle (f + 1) 16 = deserDatatype (deser f) := rfl
theorem handle_object (f : Nat) :
    handle (f + 1) 52 = (do
      let t ← deser f
      match t with
      | .ty t => deserStruct (handle f) t
      | _ => fail .typeError) := rfl
theorem handle_refobject (f : Nat) :
    handle (f + 1) 53 = (do
      let slot ← newSlot
      let s ← getS
      setS { s with pending := slot :: s.pending }
      let t ← deser f
      match t with
      | .ty t => deserStruct (handle f) t
      | _ => fail .typeError) := rfl
theorem handle_shared (f : Nat) :
    handle (f + 1) 57 = (do let slot ← newSlot; let o ← deser f; setBackref slot .obj; pure o) :=
  rfl
theorem handle_symbol (f : Nat) :
    handle (f + 1) 1 = (do let n ← readU8; deserSymbol n.toNat) := rfl
theorem handle_shortint64 (f : Nat) :
    handle (f + 1) 49 = (do let x ← readInt .i32; pure (.v (.int .i64 x))) := rfl
theorem handle_expr (f : Nat) :
    handle (f + 1) 22 = (do let n ← readU8; deserExpr (deser f) n.toNat) := rfl
theorem handle_module (f : Nat) : handle (f + 1) 31 = deserModule (deser f) := rfl
theorem handle_string (f : Nat) :
    handle (f + 1) 33 = (do let n ← readU8; deserString n.toNat) := rfl
theorem handle_longstring (f : Nat) :
    handle (f + 1) 48 = (do let n ← readInt .i64; deserString n) := rfl
theorem handle_longtuple (f : Nat) :
    handle (f + 1) 45 = (do
      let n ← readInt .i32
      if n < 0 then fail (.unmodelled "negative tuple length") else deserTuple (deser f) n.toNat) :=
  rfl
theorem handle_longexpr (f : Nat) :
    handle (f + 1) 47 = (do let n ← readInt .i32; deserExpr (deser f) n) := rfl
theorem handle_longsymbol (f : Nat) :
    handle (f + 1) 46 = (do let n ← readInt .i32; deserSymbol n) := rfl
theorem handle_header (f : Nat) : handle (f + 1) 55 = (do readHeader; deser f) := rfl
theorem handle_int (f : Nat) (t : IntTy) :
    handle (f + 1) (intTag t) = (do let x ← readInt t; pure (.v (.int t x))) := by
  cases t <;> rfl
theorem handle_flt (f : Nat) (w : FTy) :
    handle (f + 1) w.tag = (do let x ← readLE w.nbytes; pure (.v (.flt w x))) := by
  cases w <;> rfl
theorem handle_char (f : Nat) :
    handle (f + 1) 15 = (do let c ← readChar; pure (.v (.char c))) := rfl

theorem deser_eq (f : Nat) : deser f = (readU8 >>= fun b => handle f b.toNat) := rfl

/-- Reading a tag byte and handling it. -/
theorem Dec.deser {f n : Nat} {b : UInt8} {tail : Bytes} {E E' : List Nat} {es es' : ES} {a : Obj}
    (hb : b.toNat = n) (h : Dec (handle f n) E es tail a E' es') :
    Dec (Serialization.deser f) E es (b :: tail) a E' es' := by
  rw [deser_eq]
  exact Dec.bind (Dec.readU8 b E es) (by rw [hb]; exact h) rfl

theorem tag_toNat {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := toNat_ofNat_lt h

/-! ### Value tags -/

/-- The value tags `≥ VALUE_TAGS` and the `0`-prefixed type tags. -/
theorem desertag_eq (b : Nat) : desertag b =
    if b = 0 then fail (.unmodelled "TAGS[0]")
    else if b < 68 then pure (.ty (.tagged b))
    else if b = 68 then pure (.v (.tup []))
    else if b = 74 then fail (.unmodelled "svec()")
    else if b < 76 then pure (.ty (.tagged b))
    else if b = 76 then pure (.v (.bool false))
    else if b = 77 then pure (.v (.bool true))
    else if b = 78 then pure (.v .nothing)
    else if b < 190 then pure (.v (.sym (symOfTag b)))
    else if b < 223 then pure (.v (.int .i32 ((b : Int) - 190)))
    else if b ≤ 255 then pure (.v (.int .i64 ((b : Int) - 223)))
    else fail (.unmodelled "tag") := by
  rfl

theorem Dec.desertag {b : Nat} {o : Obj} {E : List Nat} {es : ES}
    (h : Serialization.desertag b = Pure.pure o) : Dec (Serialization.desertag b) E es [] o E es := by
  rw [h]; exact Dec.pure o E es

theorem Dec.tagType {f : Nat} {t : Nat} (h1 : t ≠ 0) (h2 : t < 76) (h3 : t ≠ 68) (h4 : t ≠ 74)
    (E : List Nat) (es : ES) :
    Dec (Serialization.deser (f + 1)) E es (serTagType t) (.ty (.tagged t)) E es := by
  unfold serTagType writeAsTag
  by_cases ht : t < 68
  · simp only [VALUE_TAGS, ht, ↓reduceIte]
    refine Dec.deser (n := 0) (by decide) ?_
    rw [handle_zero]
    refine Dec.bind (b2 := []) (Dec.readU8 (UInt8.ofNat t) E es) ?_ rfl
    rw [tag_toNat (by omega)]
    refine Dec.desertag ?_
    rw [desertag_eq]
    simp [h1, ht]
  · simp only [VALUE_TAGS, ht, ↓reduceIte]
    refine Dec.deser (n := t) (tag_toNat (by omega)) ?_
    rw [handle_value f t (by omega)]
    refine Dec.desertag ?_
    rw [desertag_eq]
    have : t ≠ 0 := h1
    simp only [this, ht, h3, h4, h2, ↓reduceIte]

end JuliaLean.Serialization
