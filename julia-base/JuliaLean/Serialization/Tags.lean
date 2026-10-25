import JuliaLean.Core

/-!
# Serialization tags, `stdlib/Serialization/src/Serialization.jl:42-190`

The serialized form of a value starts with a tag byte, the 1-based index into
`TAGS` (`:46-87`). Tags below `VALUE_TAGS` (68) name a type or a special
format; tags from 68 on are values that represent themselves (`:148-149`).
-/

namespace JuliaLean.Serialization

/-- A byte stream. -/
abbrev Bytes := List UInt8

/-! ### Type tags (`TAGS[1:40]`, `:47-51`) -/

abbrev SYMBOL_TAG : Nat := 1
abbrev INT8_TAG : Nat := 2
abbrev CHAR_TAG : Nat := 15
abbrev DATATYPE_TAG : Nat := 16
abbrev TUPLE_TAG : Nat := 20
abbrev ARRAY_TAG : Nat := 21
abbrev EXPR_TAG : Nat := 22
abbrev MODULE_TAG : Nat := 31
abbrev STRING_TAG : Nat := 33
abbrev INT32_TAG : Nat := 6
abbrev INT64_TAG : Nat := 8

/-! ### Format tags, `o0 = sertag(SSAValue) = 40` (`:173-190`) -/

abbrev UNDEFREF_TAG : Nat := 41
abbrev BACKREF_TAG : Nat := 42
abbrev LONGBACKREF_TAG : Nat := 43
abbrev SHORTBACKREF_TAG : Nat := 44
abbrev LONGTUPLE_TAG : Nat := 45
abbrev LONGSYMBOL_TAG : Nat := 46
abbrev LONGEXPR_TAG : Nat := 47
abbrev LONGSTRING_TAG : Nat := 48
abbrev SHORTINT64_TAG : Nat := 49
abbrev FULL_DATATYPE_TAG : Nat := 50
abbrev WRAPPER_DATATYPE_TAG : Nat := 51
abbrev OBJECT_TAG : Nat := 52
abbrev REF_OBJECT_TAG : Nat := 53
abbrev FULL_GLOBALREF_TAG : Nat := 54
abbrev HEADER_TAG : Nat := 55
abbrev IDDICT_TAG : Nat := 56
abbrev SHARED_REF_TAG : Nat := 57

/-! ### Value tags (`:74-86`) -/

/-- `VALUE_TAGS = sertag(())`; also `EMPTYTUPLE_TAG`. -/
abbrev VALUE_TAGS : Nat := 68
abbrev EMPTYTUPLE_TAG : Nat := 68
/-- `sertag(Bool)`. -/
abbrev BOOL_TYPE_TAG : Nat := 69
/-- `sertag(Any)`. -/
abbrev ANY_TAG : Nat := 70
/-- `sertag(Tuple{})`. -/
abbrev EMPTYTUPLE_TYPE_TAG : Nat := 75
abbrev FALSE_TAG : Nat := 76
abbrev TRUE_TAG : Nat := 77
abbrev NOTHING_TAG : Nat := 78
/-- `ZERO32_TAG = NTAGS-(2*n_int_literals-1) = 190` (`:150`). -/
abbrev ZERO32_TAG : Nat := 190
/-- `ZERO64_TAG = NTAGS-(n_int_literals-1) = 223` (`:151`). -/
abbrev ZERO64_TAG : Nat := 223

/-- UTF-8 names of the symbols at tags 79 through 165 (`TAGS`, `:75-81`). These are
the only symbols `sertag` finds; the 24 `:_reserved_` slots (166-189) are left out
of the lookup table (`:99`). -/
def symTagNames : List Bytes := [
  [65, 110, 121],  -- 79 :Any
  [65, 114, 114, 97, 121],  -- 80 :Array
  [84, 121, 112, 101, 86, 97, 114],  -- 81 :TypeVar
  [66, 111, 120],  -- 82 :Box
  [84, 117, 112, 108, 101],  -- 83 :Tuple
  [80, 116, 114],  -- 84 :Ptr
  [114, 101, 116, 117, 114, 110],  -- 85 :return
  [99, 97, 108, 108],  -- 86 :call
  [58, 58],  -- 87 :(::)
  [70, 117, 110, 99, 116, 105, 111, 110],  -- 88 :Function
  [61],  -- 89 :(=)
  [61, 61],  -- 90 :(==)
  [61, 61, 61],  -- 91 :(===)
  [103, 111, 116, 111, 105, 102, 110, 111, 116],  -- 92 :gotoifnot
  [65], [66], [67], [77], [78], [84], [83], [88], [89],  -- 93-101 :A :B :C :M :N :T :S :X :Y
  [97], [98], [99], [100], [101], [102], [103], [104], [105], [106], [107], [108], [109],
  [110], [111], [112], [113], [114], [115], [116], [117], [118], [119], [120], [121], [122],
    -- 102-127 :a through :z
  [97, 100, 100, 95, 105, 110, 116],  -- 128 :add_int
  [115, 117, 98, 95, 105, 110, 116],  -- 129 :sub_int
  [109, 117, 108, 95, 105, 110, 116],  -- 130 :mul_int
  [97, 100, 100, 95, 102, 108, 111, 97, 116],  -- 131 :add_float
  [115, 117, 98, 95, 102, 108, 111, 97, 116],  -- 132 :sub_float
  [110, 101, 119],  -- 133 :new
  [109, 117, 108, 95, 102, 108, 111, 97, 116],  -- 134 :mul_float
  [98, 105, 116, 99, 97, 115, 116],  -- 135 :bitcast
  [115, 116, 97, 114, 116],  -- 136 :start
  [100, 111, 110, 101],  -- 137 :done
  [110, 101, 120, 116],  -- 138 :next
  [105, 110, 100, 101, 120, 101, 100, 95, 105, 116, 101, 114, 97, 116, 101],  -- 139 :indexed_iterate
  [103, 101, 116, 102, 105, 101, 108, 100],  -- 140 :getfield
  [109, 101, 116, 97],  -- 141 :meta
  [101, 113, 95, 105, 110, 116],  -- 142 :eq_int
  [115, 108, 116, 95, 105, 110, 116],  -- 143 :slt_int
  [115, 108, 101, 95, 105, 110, 116],  -- 144 :sle_int
  [110, 101, 95, 105, 110, 116],  -- 145 :ne_int
  [112, 117, 115, 104, 95, 108, 111, 99],  -- 146 :push_loc
  [112, 111, 112, 95, 108, 111, 99],  -- 147 :pop_loc
  [112, 111, 112],  -- 148 :pop
  [97, 114, 114, 97, 121, 115, 101, 116],  -- 149 :arrayset
  [97, 114, 114, 97, 121, 114, 101, 102],  -- 150 :arrayref
  [97, 112, 112, 108, 121, 95, 116, 121, 112, 101],  -- 151 :apply_type
  [105, 110, 98, 111, 117, 110, 100, 115],  -- 152 :inbounds
  [103, 101, 116, 105, 110, 100, 101, 120],  -- 153 :getindex
  [115, 101, 116, 105, 110, 100, 101, 120, 33],  -- 154 :setindex!
  [67, 111, 114, 101],  -- 155 :Core
  [33],  -- 156 :!
  [43],  -- 157 :+
  [66, 97, 115, 101],  -- 158 :Base
  [115, 116, 97, 116, 105, 99, 95, 112, 97, 114, 97, 109, 101, 116, 101, 114],  -- 159 :static_parameter
  [99, 111, 110, 118, 101, 114, 116],  -- 160 :convert
  [99, 111, 108, 111, 110],  -- 161 :colon
  [35, 115, 101, 108, 102, 35],  -- 162 Symbol("#self#")
  [35, 116, 101, 109, 112, 35],  -- 163 Symbol("#temp#")
  [116, 117, 112, 108, 101],  -- 164 :tuple
  []]  -- 165 Symbol("")

/-- `:_reserved_`, the symbol at tags 166-189 (`:83`). -/
def reservedName : Bytes := [95, 114, 101, 115, 101, 114, 118, 101, 100, 95]

/-- Names used in type and module references. -/
def nameBase : Bytes := [66, 97, 115, 101]
def nameCore : Bytes := [67, 111, 114, 101]
def nameTuple : Bytes := [84, 117, 112, 108, 101]
def nameRefValue : Bytes := [82, 101, 102, 86, 97, 108, 117, 101]
def nameUnitRange : Bytes := [85, 110, 105, 116, 82, 97, 110, 103, 101]
def nameNamedTuple : Bytes := [78, 97, 109, 101, 100, 84, 117, 112, 108, 101]

/-- `sertag(s::Symbol)` (`:132-145`): the tag of a symbol in the table, if any. -/
def sertagSym (name : Bytes) : Option Nat :=
  (symTagNames.findIdx? (· == name)).map (· + 79)

/-- `desertag(b)` for a symbol tag `79 ≤ b ≤ 189`. -/
def symOfTag (b : Nat) : Bytes :=
  if b ≤ 165 then symTagNames.getD (b - 79) [] else reservedName

end JuliaLean.Serialization
