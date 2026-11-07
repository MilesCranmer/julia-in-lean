import JuliaLean.src.identity_runtime

/-! Exact native 64-bit egal/objectid control flow from pinned builtins.c.
Object payloads share GenericMemory's byte heap. The records in identity_runtime
are C field views, not equality/hash callbacks. Recursive C calls use the same
partial, heap-preserving execution carrier as the iterator models. -/
namespace JuliaLean.src.builtins_identity_c
open JuliaLean.src.identity_runtime
namespace H
export JuliaLean.src.support.hashing_c (byteAt load64 load32 int32hash int64hash inthash
  memhash memhash_seed bitmix)
end H

-- Source: src/builtins.c:103-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline size_t used_bytes(jl_datatype_t *dt) JL_NOTSAFEPOINT
-- {
--     return (jl_datatype_nbits(dt) + 7) / 8;
-- }
-- 
-- static inline uint8_t last_byte_mask(jl_datatype_t *dt) JL_NOTSAFEPOINT
-- {
--     return (uint8_t)(0xff >> (used_bytes(dt) * 8 - jl_datatype_nbits(dt)));
-- }
-- /Source
def used_bytes (dt : Datatype) : Nat := (dt.bits + 7) / 8

def last_byte_mask (dt : Datatype) : UInt8 :=
  0xff >>> UInt8.ofNat (used_bytes dt * 8 - dt.bits)

-- Source: src/builtins.c:58-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int bits_equal(const void *a, const void *b, int sz) JL_NOTSAFEPOINT
-- {
--     switch (sz) {
--     case 1:  return *(uint8_t*)a == *(uint8_t*)b;
--         // Let compiler constant folds the following, though we may not know alignment of them
--     case 2:  return memcmp(a, b, 2) == 0;
--     case 4:  return memcmp(a, b, 4) == 0;
--     case 8:  return memcmp(a, b, 8) == 0;
--     default: return memcmp(a, b, sz) == 0;
--     }
-- }
-- /Source
def bits_equal (a b : Word) (size : Nat) : M Bool := do
  requireReadable a size
  requireReadable b size
  for i in [0:size] do
    if (← loadByte (a + UInt64.ofNat i)) != (← loadByte (b + UInt64.ofNat i)) then return false
  return true

-- Source: src/builtins.c:113-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline int primitive_bits_equal(const void *a, const void *b, jl_datatype_t *dt) JL_NOTSAFEPOINT
-- {
--     size_t nb = used_bytes(dt);
--     if (nb == 0)
--         return 1;
--     return (nb <= 1 || bits_equal(a, b, nb - 1)) &&
--            ((((const uint8_t*)a)[nb - 1] ^ ((const uint8_t*)b)[nb - 1]) & last_byte_mask(dt)) == 0;
-- }
-- /Source
def primitive_bits_equal (a b : Word) (dt : Datatype) : M Bool := do
  let nb := used_bytes dt
  if nb = 0 then return true
  if nb > 1 then
    if !(← bits_equal a b (nb-1)) then return false
  let x ← loadByte (a + UInt64.ofNat (nb-1))
  let y ← loadByte (b + UInt64.ofNat (nb-1))
  return ((x ^^^ y) &&& last_byte_mask dt) == 0

-- Source: src/builtins.c:389-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static uintptr_t bits_hash(const void *b, size_t sz) JL_NOTSAFEPOINT
-- {
--     switch (sz) {
--     case 1:  return int32hash(*(const int8_t*)b);
--     case 2:  return int32hash(jl_load_unaligned_i16(b));
--     case 4:  return int32hash(jl_load_unaligned_i32(b));
-- #ifdef _P64
--     case 8:  return int64hash(jl_load_unaligned_i64(b));
-- #else
--     case 8:  return int64to32hash(jl_load_unaligned_i64(b));
-- #endif
--     default:
-- #ifdef _P64
--         return memhash((const char*)b, sz);
-- #else
--         return memhash32((const char*)b, sz);
-- #endif
--     }
-- }
-- /Source
def bits_hash (address : Word) (size : Nat) : M Word := do
  requireReadable address size
  let heap := (← getWorld).raw.heap
  match size with
  | 1 =>
    let value := (H.byteAt heap address.toNat).toUInt32
    return (H.int32hash ((value ^^^ 0x80) - 0x80)).toUInt64
  | 2 =>
    let value := (H.byteAt heap address.toNat).toUInt32 |||
      ((H.byteAt heap (address.toNat+1)).toUInt32 <<< 8)
    return (H.int32hash ((value ^^^ 0x8000) - 0x8000)).toUInt64
  | 4 => return (H.int32hash (H.load32 heap address.toNat)).toUInt64
  | 8 => return H.int64hash (H.load64 heap address.toNat)
  | _ => return H.memhash heap address.toNat size

/-- A private stack-byte view for immut_id_'s alloca/memcpy/mask. It does not
write the original heap. Its address never escapes the bits_hash call. -/
def masked_bits_hash (address : Word) (dt : Datatype) : M Word := do
  let nb := used_bytes dt
  requireReadable address nb
  if nb = 0 then return (← bits_hash address 0)
  let world ← getWorld
  let last := address.toNat + nb - 1
  let byte := (H.byteAt world.raw.heap last) &&& last_byte_mask dt
  let shadow := world.raw.heap.writeByte last (JuliaLean.JInt.wrap .u8 byte.toNat)
  let privateWorld := { world with raw := { world.raw with heap := shadow } }
  match bits_hash address nb privateWorld with
  | none => fun _ => none
  | some (.error error, _) => fail error
  | some (.ok hash, _) => pure hash

/-- C's type-variable environment cells, newest first. -/
abbrev TypeEnv := List (Word × Word)
abbrev VarIndices := List Word

mutual
-- Source: src/builtins.c:89-99 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int NOINLINE compare_svec(jl_svec_t *a, jl_svec_t *b) JL_NOTSAFEPOINT
-- {
--     size_t i, l = jl_svec_len(a);
--     if (l != jl_svec_len(b))
--         return 0;
--     for (i = 0; i < l; i++) {
--         if (!jl_egal(jl_svecref(a, i), jl_svecref(b, i)))
--             return 0;
--     }
--     return 1;
-- }
-- /Source
  def compare_svec (a b : Word) : M Bool := do
    let va ← objectAt a
    let vb ← objectAt b
    if va.length != vb.length then return false
    compare_svec_loop a b va.length 0
  partial_fixpoint

  def compare_svec_loop (a b : Word) (length index : Nat) : M Bool := do
    if index ≥ length then return true
    let x ← loadWord (a + 8 + UInt64.ofNat (8*index))
    let y ← loadWord (b + 8 + UInt64.ofNat (8*index))
    if !(← jl_egal_ x y) then pure false
    else compare_svec_loop a b length (index+1)
  partial_fixpoint

-- Source: src/builtins.c:123-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int NOINLINE compare_fields(const jl_value_t *a, const jl_value_t *b, jl_datatype_t *dt) JL_NOTSAFEPOINT
-- {
--     size_t nf = jl_datatype_nfields(dt);
--     // npointers is used at end, but fetched here for locality with nfields.
--     int npointers = ((jl_datatype_t*)dt)->layout->npointers;
--     for (size_t f = 0; f < nf; f++) {
--         size_t offs = jl_field_offset(dt, f);
--         char *ao = (char*)a + offs;
--         char *bo = (char*)b + offs;
--         if (jl_field_isptr(dt, f)) {
--             // Save ptr recursion until the end -- only recurse if otherwise equal
--             // Note that we also skip comparing the pointers for null here, because
--             // null fields are rare so it can save CPU to delay this read too.
--             continue;
--         }
--         else {
--             jl_datatype_t *ft = (jl_datatype_t*)jl_field_type_concrete(dt, f);
--             if (jl_is_uniontype(ft)) {
--                 size_t idx = jl_field_size(dt, f) - 1;
--                 uint8_t asel = ((uint8_t*)ao)[idx];
--                 uint8_t bsel = ((uint8_t*)bo)[idx];
--                 if (asel != bsel)
--                     return 0;
--                 ft = (jl_datatype_t*)jl_nth_union_component((jl_value_t*)ft, asel);
--             }
--             else if (ft->layout->first_ptr >= 0) {
--                 // If the field is a inline immutable that can be undef
--                 // we need to check for undef first since undef struct
--                 // may have fields that are different but should still be treated as equal.
--                 int32_t idx = ft->layout->first_ptr;
--                 jl_value_t *ptra = ((jl_value_t**)ao)[idx];
--                 jl_value_t *ptrb = ((jl_value_t**)bo)[idx];
--                 if ((ptra == NULL) != (ptrb == NULL)) {
--                     return 0;
--                 }
--                 else if (ptra == NULL) { // implies ptrb == NULL
--                     continue; // skip this field (it is #undef)
--                 }
--             }
--             if (!ft->layout->flags.haspadding && ft->layout->flags.isbitsegal) {
--                 if (!bits_equal(ao, bo, ft->layout->size))
--                     return 0;
--             }
--             else {
--                 if (jl_datatype_nfields(ft) == 0) {
--                     // Odd-bit primitives have trailing unused bits, which are
--                     // represented as padding even though they have no fields.
--                     if (!primitive_bits_equal(ao, bo, ft))
--                         return 0;
--                 }
--                 else if (!compare_fields((jl_value_t*)ao, (jl_value_t*)bo, ft))
--                     return 0;
--             }
--         }
--     }
--     // If we've gotten here, the objects are bitwise equal, besides their pointer fields.
--     // Now, we will recurse into jl_egal for the pointed-to elements, which might be
--     // arbitrarily expensive.
--     for (size_t p = 0; p < npointers; p++) {
--         size_t offs = jl_ptr_offset(dt, p);
--         jl_value_t *af = ((jl_value_t**)a)[offs];
--         jl_value_t *bf = ((jl_value_t**)b)[offs];
--         if (af != bf) {
--             if (af == NULL || bf == NULL)
--                 return 0;
--             if (!jl_egal(af, bf))
--                 return 0;
--         }
--     }
--     return 1;
-- }
-- /Source
  def compare_fields (a b : Word) (dt : Datatype) : M Bool := do
    for field in dt.fields do
      if !field.isPointer then
        let ao := a + UInt64.ofNat field.offset
        let bo := b + UInt64.ofNat field.offset
        let mut ftAddress := field.fieldType
        let mut skip := false
        if tagKind (← typetag ftAddress) == .uniontype then
          if field.size = 0 then fail (.abort "union field selector size")
          let asel ← loadByte (ao + UInt64.ofNat (field.size-1))
          let bsel ← loadByte (bo + UInt64.ofNat (field.size-1))
          if asel != bsel then return false
          ftAddress ← jl_nth_union_component ftAddress (Int32.ofNat asel.toNat)
        else
          let ft ← datatypeAt ftAddress
          if 0 ≤ ft.firstPointer then
            let x ← loadWord (ao + UInt64.ofNat (8*ft.firstPointer.toNat))
            let y ← loadWord (bo + UInt64.ofNat (8*ft.firstPointer.toNat))
            if (x == 0) != (y == 0) then return false
            if x == 0 then skip := true
        if !skip then
          let ft ← datatypeAt ftAddress
          if !ft.hasPadding && ft.isBitsEgal then
            if !(← bits_equal ao bo ft.size) then return false
          else if ft.fields.isEmpty then
            if !(← primitive_bits_equal ao bo ft) then return false
          else if !(← compare_fields ao bo ft) then return false
    for offset in dt.pointerOffsets do
      let x ← loadWord (a + UInt64.ofNat (8*offset))
      let y ← loadWord (b + UInt64.ofNat (8*offset))
      if x != y then
        if x == 0 || y == 0 then return false
        if !(← jl_egal_ x y) then return false
    return true
  partial_fixpoint

-- Source: src/builtins.c:195-261 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static int egal_types(const jl_value_t *a, const jl_value_t *b, jl_typeenv_t *env, int tvar_names) JL_NOTSAFEPOINT
-- {
--     if (a == b)
--         return 1;
--     uintptr_t dtag = jl_typetagof(a);
--     if (dtag != jl_typetagof(b))
--         return 0;
--     if (dtag == jl_datatype_tag << 4) {
--         jl_datatype_t *dta = (jl_datatype_t*)a;
--         jl_datatype_t *dtb = (jl_datatype_t*)b;
--         if (dta->name != dtb->name)
--             return 0;
--         size_t i, l = jl_nparams(dta);
--         if (jl_nparams(dtb) != l)
--             return 0;
--         for (i = 0; i < l; i++) {
--             if (!egal_types(jl_tparam(dta, i), jl_tparam(dtb, i), env, tvar_names))
--                 return 0;
--         }
--         return 1;
--     }
--     if (dtag == jl_tvar_tag << 4) {
--         jl_typeenv_t *pe = env;
--         while (pe != NULL) {
--             if (pe->var == (jl_tvar_t*)a)
--                 return pe->val == b;
--             pe = pe->prev;
--         }
--         return 0;
--     }
--     if (dtag == jl_unionall_tag << 4) {
--         jl_unionall_t *ua = (jl_unionall_t*)a;
--         jl_unionall_t *ub = (jl_unionall_t*)b;
--         if (tvar_names && ua->var->name != ub->var->name)
--             return 0;
--         if (!(egal_types(ua->var->lb, ub->var->lb, env, tvar_names) && egal_types(ua->var->ub, ub->var->ub, env, tvar_names)))
--             return 0;
--         jl_typeenv_t e = { ua->var, (jl_value_t*)ub->var, env };
--         return egal_types(ua->body, ub->body, &e, tvar_names);
--     }
--     if (dtag == jl_uniontype_tag << 4) {
--         return egal_types(((jl_uniontype_t*)a)->a, ((jl_uniontype_t*)b)->a, env, tvar_names) &&
--             egal_types(((jl_uniontype_t*)a)->b, ((jl_uniontype_t*)b)->b, env, tvar_names);
--     }
--     if (dtag == jl_typeegal_tag << 4) {
--         // `TypeEgal` parameters are egality keys: alpha-renamed parameters are
--         // `==` but not `===`, so their `TypeEgal`s are distinct types. The
--         // name-insensitive mode (tvar_names==0) must therefore still compare
--         // the parameter by name.
--         return egal_types(((jl_typeeq_t*)a)->T, ((jl_typeeq_t*)b)->T, env, 1);
--     }
--     if (dtag == jl_typeeq_tag << 4)
--         return egal_types(((jl_typeeq_t*)a)->T, ((jl_typeeq_t*)b)->T, env, tvar_names);
--     if (dtag == jl_vararg_tag << 4) {
--         jl_vararg_t *vma = (jl_vararg_t*)a;
--         jl_vararg_t *vmb = (jl_vararg_t*)b;
--         jl_value_t *vmaT = vma->T ? vma->T : (jl_value_t*)jl_any_type;
--         jl_value_t *vmbT = vmb->T ? vmb->T : (jl_value_t*)jl_any_type;
--         if (!egal_types(vmaT, vmbT, env, tvar_names))
--             return 0;
--         if (vma->N && vmb->N)
--             return egal_types(vma->N, vmb->N, env, tvar_names);
--         return !vma->N && !vmb->N;
--     }
--     assert(dtag == jl_symbol_tag << 4 || dtag == jl_module_tag << 4 || !((jl_datatype_t*)jl_typeof(a))->name->mutabl);
--     return jl_egal__bitstag(a, b, dtag);
-- }
-- /Source
  def egal_types (a b : Word) (env : TypeEnv) (tvarNames : Bool) : M Bool := do
    if a == b then return true
    let tag ← typetag a
    if tag != (← typetag b) then return false
    let kind := tagKind tag
    if kind == .datatype then
      let da ← datatypeAt a
      let db ← datatypeAt b
      if da.name != db.name then return false
      let pa ← objectAt da.parameters
      let pb ← objectAt db.parameters
      if pa.length != pb.length then return false
      return ← egal_parameters da.parameters db.parameters pa.length 0 env tvarNames
    if kind == .tvar then
      for (typeVar, value) in env do
        if typeVar == a then return value == b
      return false
    if kind == .unionall then
      let ua ← objectAt a
      let ub ← objectAt b
      let va ← objectAt ua.variable
      let vb ← objectAt ub.variable
      if tvarNames && va.name != vb.name then return false
      if !(← egal_types va.lower vb.lower env tvarNames) then return false
      if !(← egal_types va.upper vb.upper env tvarNames) then return false
      return ← egal_types ua.body ub.body ((ua.variable,ub.variable)::env) tvarNames
    if kind == .uniontype then
      let ua ← objectAt a
      let ub ← objectAt b
      if !(← egal_types ua.left ub.left env tvarNames) then return false
      return ← egal_types ua.right ub.right env tvarNames
    if kind == .typeegal || kind == .typeeq then
      return ← egal_types (← objectAt a).typeArgument (← objectAt b).typeArgument env
        (if kind == .typeegal then true else tvarNames)
    if kind == .vararg then
      let va ← objectAt a
      let vb ← objectAt b
      let anyType := (← getWorld).globals.anyType
      let ta := if va.typeArgument == 0 then anyType else va.typeArgument
      let tb := if vb.typeArgument == 0 then anyType else vb.typeArgument
      if !(← egal_types ta tb env tvarNames) then return false
      if va.countArgument != 0 && vb.countArgument != 0 then
        return ← egal_types va.countArgument vb.countArgument env tvarNames
      return va.countArgument == 0 && vb.countArgument == 0
    if kind != .symbol && kind != .module_ then
      if (← datatypeAt (← toTypeof tag)).isMutable then
        fail (.abort "egal_types immutable fallback")
    jl_egal__bitstag a b tag
  partial_fixpoint

  def egal_parameters (a b : Word) (length index : Nat)
      (env : TypeEnv) (tvarNames : Bool) : M Bool := do
    if index ≥ length then return true
    let x ← loadWord (a + 8 + UInt64.ofNat (8*index))
    let y ← loadWord (b + 8 + UInt64.ofNat (8*index))
    if !(← egal_types x y env tvarNames) then pure false
    else egal_parameters a b length (index+1) env tvarNames
  partial_fixpoint

-- Source: src/julia.h:2083-2103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- STATIC_INLINE int jl_egal__unboxed_(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, uintptr_t dtag) JL_NOTSAFEPOINT
-- {
--     if (dtag < jl_max_tags << 4) {
--         if (dtag == jl_symbol_tag << 4 || dtag == jl_bool_tag << 4 || dtag == jl_nothing_tag << 4)
--             return 0;
--     }
--     else if (((jl_datatype_t*)dtag)->name->mutabl)
--         return 0;
--     return jl_egal__bitstag(a, b, dtag);
-- }
-- 
-- STATIC_INLINE int jl_egal_(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED) JL_NOTSAFEPOINT
-- {
--     if (a == b)
--         return 1;
--     uintptr_t dtag = jl_typetagof(a);
--     if (dtag != jl_typetagof(b))
--         return 0;
--     return jl_egal__unboxed_(a, b, dtag);
-- }
-- #define jl_egal(a, b) jl_egal_((a), (b))
-- /Source
  def jl_egal_ (a b : Word) : M Bool := do
    if a == b then return true
    let tag ← typetag a
    if tag != (← typetag b) then return false
    jl_egal__unboxed_ a b tag
  partial_fixpoint

  def jl_egal__unboxed_ (a b tag : Word) : M Bool := do
    if tag < 1024 then
      let kind := tagKind tag
      if kind == .symbol || kind == .bool_ || kind == .nothing then return false
    else if (← datatypeAt tag).isMutable then return false
    jl_egal__bitstag a b tag
  partial_fixpoint

-- Source: src/builtins.c:283-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- JL_DLLEXPORT int jl_egal__bitstag(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, uintptr_t dtag) JL_NOTSAFEPOINT
-- {
--     if (dtag < jl_max_tags << 4) {
--         switch ((enum jl_small_typeof_tags)(dtag >> 4)) {
--         case jl_int8_tag:
--         case jl_uint8_tag:
--         case jl_addrspacecore_tag:
--             return *(uint8_t*)a == *(uint8_t*)b;
--         case jl_int16_tag:
--         case jl_uint16_tag:
--             return *(uint16_t*)a == *(uint16_t*)b;
--         case jl_int32_tag:
--         case jl_uint32_tag:
--         case jl_char_tag:
--         case jl_intrinsic_tag:
--             return *(uint32_t*)a == *(uint32_t*)b;
--         case jl_int64_tag:
--         case jl_uint64_tag:
--             return *(uint64_t*)a == *(uint64_t*)b;
--         case jl_ssavalue_tag:
--         case jl_slotnumber_tag:
--         case jl_argument_tag:
--             return *(size_t*)a == *(size_t*)b;
--         case jl_gotoifnot_tag:
--             return compare_fields(a, b, jl_gotoifnot_type);
--         case jl_returnnode_tag:
--             return compare_fields(a, b, jl_returnnode_type);
--         case jl_enternode_tag:
--             return compare_fields(a, b, jl_enternode_type);
--         case jl_pinode_tag:
--             return compare_fields(a, b, jl_pinode_type);
--         case jl_phinode_tag:
--             return compare_fields(a, b, jl_phinode_type);
--         case jl_phicnode_tag:
--             return compare_fields(a, b, jl_phicnode_type);
--         case jl_upsilonnode_tag:
--             return compare_fields(a, b, jl_upsilonnode_type);
--         case jl_globalref_tag:
--             return compare_fields(a, b, jl_globalref_type);
--         case jl_gotonode_tag:
--             return *(size_t*)a == *(size_t*)b;
--         case jl_quotenode_tag:
--             return compare_fields(a, b, jl_quotenode_type);
--         case jl_unionall_tag:
--             return egal_types(a, b, NULL, 1);
--         case jl_uniontype_tag:
--             return compare_fields(a, b, jl_uniontype_type);
--         case jl_typeeq_tag:
--         case jl_typeegal_tag:
--             return egal_types(a, b, NULL, 1);
--         case jl_vararg_tag:
--             return compare_fields(a, b, jl_vararg_type);
--         case jl_task_tag:
--         case jl_tvar_tag:
--         case jl_symbol_tag:
--         case jl_module_tag:
--         case jl_bool_tag:
--         case jl_nothing_tag:
--         case jl_cancel_source_tag: // mutable: identity (a == b checked above)
--         case jl_wait_entry_tag:    // mutable: identity (a == b checked above)
--             return 0;
--         case jl_simplevector_tag:
--             return compare_svec((jl_svec_t*)a, (jl_svec_t*)b);
--         case jl_string_tag: {
--                 size_t l = jl_string_len(a);
--                 if (jl_string_len(b) != l)
--                     return 0;
--                 return !memcmp(jl_string_data(a), jl_string_data(b), l);
--             }
--         case jl_datatype_tag: {
--                 jl_datatype_t *dta = (jl_datatype_t*)a;
--                 jl_datatype_t *dtb = (jl_datatype_t*)b;
--                 if (dta->name != dtb->name)
--                     return 0;
--                 if (dta->name != jl_tuple_typename && (dta->isconcretetype || dtb->isconcretetype))
--                     return 0;
--                 return compare_svec(dta->parameters, dtb->parameters);
--             }
-- #ifndef NDEBUG
--         default:
-- #endif
--         case jl_max_tags:
--         case jl_null_tag:
--         case jl_typeofbottom_tag:
--         case jl_tags_count:
--             abort();
--         }
--     }
--     return jl_egal__bits(a, b, (jl_datatype_t*)dtag);
-- }
-- 
-- inline int jl_egal__bits(const jl_value_t *a JL_MAYBE_UNROOTED, const jl_value_t *b JL_MAYBE_UNROOTED, jl_datatype_t *dt) JL_NOTSAFEPOINT
-- {
--     size_t sz = jl_datatype_size(dt);
--     if (sz == 0)
--         return 1;
--     size_t nf = jl_datatype_nfields(dt);
--     if (nf == 0)
--         return dt->layout->flags.haspadding ? primitive_bits_equal(a, b, dt) : bits_equal(a, b, sz);
--     if (!dt->layout->flags.haspadding && dt->layout->flags.isbitsegal)
--         return bits_equal(a, b, sz);
--     return compare_fields(a, b, dt);
-- }
-- /Source
  def jl_egal__bitstag (a b tag : Word) : M Bool := do
    if tag < 1024 then
      match tagKind tag with
      | .int8 | .uint8 | .addrspacecore => bits_equal a b 1
      | .int16 | .uint16 => bits_equal a b 2
      | .int32 | .uint32 | .char | .intrinsic => bits_equal a b 4
      | .int64 | .uint64 | .ssavalue | .slotnumber | .argument | .gotonode => bits_equal a b 8
      | .gotoifnot | .returnnode | .enternode | .pinode | .phinode | .phicnode
        | .upsilonnode | .globalref | .quotenode | .uniontype | .vararg =>
        compare_fields a b (← datatypeAt (← toTypeof tag))
      | .unionall | .typeeq | .typeegal => egal_types a b [] true
      | .task | .tvar | .symbol | .module_ | .bool_ | .nothing | .cancelSource | .waitEntry => pure false
      | .simplevector => compare_svec a b
      | .string =>
        let x ← objectAt a
        let y ← objectAt b
        if x.length != y.length then return false
        bits_equal (a+8) (b+8) x.length
      | .datatype =>
        let x ← datatypeAt a
        let y ← datatypeAt b
        if x.name != y.name then return false
        if x.name != (← getWorld).globals.tupleTypename && (x.isConcrete || y.isConcrete) then return false
        compare_svec x.parameters y.parameters
      | _ => fail (.abort "jl_egal__bitstag invalid small tag")
    else jl_egal__bits a b (← datatypeAt tag)
  partial_fixpoint

  def jl_egal__bits (a b : Word) (dt : Datatype) : M Bool := do
    if dt.size = 0 then return true
    if dt.fields.isEmpty then
      if dt.hasPadding then primitive_bits_equal a b dt else bits_equal a b dt.size
    else if !dt.hasPadding && dt.isBitsEgal then bits_equal a b dt.size
    else compare_fields a b dt
  partial_fixpoint

-- Source: src/builtins.c:409-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static uintptr_t NOINLINE hash_svec(jl_svec_t *v) JL_NOTSAFEPOINT
-- {
--     uintptr_t h = 0;
--     size_t i, l = jl_svec_len(v);
--     for (i = 0; i < l; i++) {
--         jl_value_t *x = jl_svecref(v, i);
--         uintptr_t u = (x == NULL) ? 0 : jl_object_id(x);
--         h = bitmix(h, u);
--     }
--     return h;
-- }
-- /Source
  def hash_svec (value : Word) : M Word := do
    let vector ← objectAt value
    hash_svec_loop value vector.length 0 0
  partial_fixpoint

  def hash_svec_loop (value : Word) (length index : Nat) (hash : Word) : M Word := do
    if index ≥ length then return hash
    let x ← loadWord (value+8+UInt64.ofNat (8*index))
    let u ← if x == 0 then pure 0 else jl_object_id x
    hash_svec_loop value length (index+1) (H.bitmix hash u)
  partial_fixpoint

-- Source: src/builtins.c:428-488 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static uintptr_t type_object_id_(jl_value_t *v, jl_varidx_t *env) JL_NOTSAFEPOINT
-- {
--     if (v == NULL)
--         return 0;
--     jl_datatype_t *tv = (jl_datatype_t*)jl_typeof(v);
--     if (tv == jl_tvar_type) {
--         jl_varidx_t *pe = env;
--         int i = 0;
--         while (pe != NULL) {
--             if (pe->var == (jl_tvar_t*)v)
--                 return (i<<8) + 42;
--             i++;
--             pe = pe->prev;
--         }
--         uintptr_t bits = jl_astaggedvalue(v)->header;
--         if (bits & GC_IN_IMAGE)
--             return ((uintptr_t*)v)[-2];
--         return inthash((uintptr_t)v);
--     }
--     if (tv == jl_uniontype_type) {
--         return bitmix(bitmix(jl_object_id((jl_value_t*)tv),
--                              type_object_id_(((jl_uniontype_t*)v)->a, env)),
--                       type_object_id_(((jl_uniontype_t*)v)->b, env));
--     }
--     if (tv == jl_typeeq_type || tv == jl_typeegal_type) {
--         return bitmix(jl_object_id((jl_value_t*)tv),
--                       type_object_id_(((jl_typeeq_t*)v)->T, env));
--     }
--     if (tv == jl_unionall_type) {
--         jl_unionall_t *u = (jl_unionall_t*)v;
--         uintptr_t h = u->var->name->hash;
--         h = bitmix(h, type_object_id_(u->var->lb, env));
--         h = bitmix(h, type_object_id_(u->var->ub, env));
--         jl_varidx_t e = { u->var, env };
--         return bitmix(h, type_object_id_(u->body, &e));
--     }
--     if (tv == jl_datatype_type) {
--         jl_datatype_t *dtv = (jl_datatype_t*)v;
--         if (dtv->isconcretetype)
--             return dtv->hash;
--         uintptr_t h = ~dtv->name->hash;
--         size_t i, l = jl_nparams(v);
--         for (i = 0; i < l; i++) {
--             h = bitmix(h, type_object_id_(jl_tparam(v, i), env));
--         }
--         return h;
--     }
--     if (tv == jl_vararg_type) {
--         jl_vararg_t *vm = (jl_vararg_t*)v;
--         jl_value_t *t = vm->T ? vm->T : (jl_value_t*)jl_any_type;
--         jl_value_t *n = vm->N ? vm->N : jl_nothing;
--         return bitmix(type_object_id_(t, env),
--             type_object_id_(n, env));
--     }
--     if (tv == jl_symbol_type)
--         return ((jl_sym_t*)v)->hash;
--     if (tv == jl_module_type)
--         return ((jl_module_t*)v)->hash;
--     assert(!tv->name->mutabl);
--     return immut_id_(tv, v, tv->hash);
-- }
-- /Source
  def type_object_id_ (value : Word) (env : VarIndices) : M Word := do
    if value == 0 then return 0
    let tv ← typeof value
    let kind := tagKind (← typetag value)
    if kind == .tvar then
      let mut index := 0
      for typeVar in env do
        if typeVar == value then return UInt64.ofNat (index*256+42)
        index := index+1
      let header ← loadWord (value-8)
      if header &&& 4 != 0 then return ← loadWord (value-16)
      return H.inthash value
    if kind == .uniontype then
      let union ← objectAt value
      return H.bitmix (H.bitmix (← jl_object_id tv) (← type_object_id_ union.left env))
        (← type_object_id_ union.right env)
    if kind == .typeeq || kind == .typeegal then
      return H.bitmix (← jl_object_id tv) (← type_object_id_ (← objectAt value).typeArgument env)
    if kind == .unionall then
      let union ← objectAt value
      let typeVar ← objectAt union.variable
      let mut hash := (← objectAt typeVar.name).hash
      hash := H.bitmix hash (← type_object_id_ typeVar.lower env)
      hash := H.bitmix hash (← type_object_id_ typeVar.upper env)
      return H.bitmix hash (← type_object_id_ union.body (union.variable::env))
    if kind == .datatype then
      let datatype ← datatypeAt value
      if datatype.isConcrete then return datatype.hash
      let nameHash ← typename_hash datatype.name
      let parameters ← objectAt datatype.parameters
      return ← hash_parameters datatype.parameters parameters.length 0 (~~~nameHash) env
    if kind == .vararg then
      let vararg ← objectAt value
      let globals := (← getWorld).globals
      return H.bitmix (← type_object_id_ (if vararg.typeArgument == 0 then globals.anyType else vararg.typeArgument) env)
        (← type_object_id_ (if vararg.countArgument == 0 then globals.nothing else vararg.countArgument) env)
    if kind == .symbol || kind == .module_ then return (← objectAt value).hash
    let datatype ← datatypeAt tv
    if datatype.isMutable then fail (.abort "type_object_id_ immutable fallback")
    immut_id_ datatype value datatype.hash
  partial_fixpoint

  def hash_parameters (parameters : Word) (length index : Nat)
      (hash : Word) (env : VarIndices) : M Word := do
    if index ≥ length then return hash
    let parameter ← loadWord (parameters+8+UInt64.ofNat (8*index))
    let component ← type_object_id_ parameter env
    hash_parameters parameters length (index+1) (H.bitmix hash component) env
  partial_fixpoint

  def typename_hash (name : Word) : M Word := do
    match (← getWorld).typenameHashes name with
    | some hash => pure hash
    | none => fail (.undefinedBehavior "jl_typename_t.hash" name)

-- Source: src/builtins.c:490-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static uintptr_t immut_id_(jl_datatype_t *dt, jl_value_t *v, uintptr_t h) JL_NOTSAFEPOINT
-- {
--     size_t sz = jl_datatype_size(dt);
--     if (sz == 0)
--         return ~h;
--     size_t f, nf = jl_datatype_nfields(dt);
--     if (nf == 0 || (!dt->layout->flags.haspadding && dt->layout->flags.isbitsegal && dt->layout->npointers == 0)) {
--         // operate element-wise if there are unused bits inside,
--         // otherwise just take the whole data block at once
--         // a few select pointers (notably symbol) also have special hash values
--         // which may affect the stability of the objectid hash, even though
--         // they don't affect egal comparison
--         if (nf == 0 && dt->layout->flags.haspadding) {
--             // hash only the value bits, so padding cannot perturb the hash
--             size_t nb = used_bytes(dt);
--             void *buf = alloca(nb);
--             memcpy(buf, v, nb);
--             ((uint8_t*)buf)[nb - 1] &= last_byte_mask(dt);
--             return bits_hash(buf, nb) ^ h;
--         }
--         return bits_hash(v, sz) ^ h;
--     }
--     if (dt == jl_unionall_type)
--         return type_object_id_(v, NULL);
--     for (f = 0; f < nf; f++) {
--         size_t offs = jl_field_offset(dt, f);
--         char *vo = (char*)v + offs;
--         uintptr_t u;
--         if (jl_field_isptr(dt, f)) {
--             jl_value_t *f = *(jl_value_t**)vo;
--             u = (f == NULL) ? 0 : jl_object_id(f);
--         }
--         else {
--             jl_datatype_t *fieldtype = (jl_datatype_t*)jl_field_type_concrete(dt, f);
--             if (jl_is_uniontype(fieldtype)) {
--                 uint8_t sel = ((uint8_t*)vo)[jl_field_size(dt, f) - 1];
--                 fieldtype = (jl_datatype_t*)jl_nth_union_component((jl_value_t*)fieldtype, sel);
--             }
--             assert(jl_is_datatype(fieldtype) && !fieldtype->name->abstract && !fieldtype->name->mutabl);
--             int32_t first_ptr = fieldtype->layout->first_ptr;
--             if (first_ptr >= 0 && ((jl_value_t**)vo)[first_ptr] == NULL) {
--                 // If the field is a inline immutable that can be undef
--                 // we need to check for undef first since undef struct
--                 // may have fields that are different but should still be treated as equal.
--                 u = 0;
--             }
--             else {
--                 u = immut_id_(fieldtype, (jl_value_t*)vo, 0);
--             }
--         }
--         h = bitmix(h, u);
--     }
--     return h;
-- }
-- /Source
  def immut_id_ (dt : Datatype) (value hash : Word) : M Word := do
    if dt.size = 0 then return ~~~hash
    if dt.fields.isEmpty || (!dt.hasPadding && dt.isBitsEgal && dt.pointerOffsets.isEmpty) then
      if dt.fields.isEmpty && dt.hasPadding then return (← masked_bits_hash value dt) ^^^ hash
      return (← bits_hash value dt.size) ^^^ hash
    if tagKind (← typetag value) == .unionall then return ← type_object_id_ value []
    let mut hash := hash
    for field in dt.fields do
      let address := value + UInt64.ofNat field.offset
      let u ← if field.isPointer then do
          let pointer ← loadWord address
          if pointer == 0 then pure 0 else jl_object_id pointer
        else do
          let mut fieldType := field.fieldType
          if tagKind (← typetag fieldType) == .uniontype then
            if field.size = 0 then fail (.abort "union field selector size")
            fieldType ← jl_nth_union_component fieldType
              (Int32.ofNat (← loadByte (address+UInt64.ofNat (field.size-1))).toNat)
          let ft ← datatypeAt fieldType
          if ft.isAbstract || ft.isMutable then fail (.abort "immut_id_ concrete immutable field")
          if 0 ≤ ft.firstPointer then
            if (← loadWord (address+UInt64.ofNat (8*ft.firstPointer.toNat))) == 0 then pure 0
            else immut_id_ ft address 0
          else immut_id_ ft address 0
      hash := H.bitmix hash u
    return hash
  partial_fixpoint

-- Source: src/builtins.c:545-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static uintptr_t NOINLINE jl_object_id__cold(uintptr_t tv, jl_value_t *v) JL_NOTSAFEPOINT
-- {
--     jl_datatype_t *dt = (jl_datatype_t*)jl_to_typeof(tv);
--     if (dt->name->mutabl) {
--         if (dt == jl_string_type) {
-- #ifdef _P64
--             return memhash_seed(jl_string_data(v), jl_string_len(v), 0xedc3b677);
-- #else
--             return memhash32_seed(jl_string_data(v), jl_string_len(v), 0xedc3b677);
-- #endif
--         }
--         if (dt == jl_simplevector_type)
--             return hash_svec((jl_svec_t*)v);
--         if (dt == jl_datatype_type) {
--             jl_datatype_t *dtv = (jl_datatype_t*)v;
--             uintptr_t h = ~dtv->name->hash;
--             return bitmix(h, hash_svec(dtv->parameters));
--         }
--         if (dt == jl_module_type) {
--             jl_module_t *m = (jl_module_t*)v;
--             return m->hash;
--         }
--         uintptr_t bits = jl_astaggedvalue(v)->header;
--         if (bits & GC_IN_IMAGE)
--             return ((uintptr_t*)v)[-2];
--         return inthash((uintptr_t)v);
--     }
--     return immut_id_(dt, v, dt->hash);
-- }
-- 
-- JL_DLLEXPORT inline uintptr_t jl_object_id_(uintptr_t tv, jl_value_t *v) JL_NOTSAFEPOINT
-- {
--     if (tv == jl_symbol_tag << 4) {
--         return ((jl_sym_t*)v)->hash;
--     }
--     else if (tv == jl_datatype_tag << 4) {
--         jl_datatype_t *dtv = (jl_datatype_t*)v;
--         // dt->hash is an egal-consistent object id for any datatype (concrete ones already
--         // use it); reuse it for non-concrete ones too rather than rehashing on every call.
--         if (dtv->hash)
--             return dtv->hash;
--     }
--     else if (tv == (uintptr_t)jl_typename_type) {
--         return ((jl_typename_t*)v)->hash;
--     }
--     return jl_object_id__cold(tv, v);
-- }
-- 
-- 
-- JL_DLLEXPORT uintptr_t jl_object_id(jl_value_t *v) JL_NOTSAFEPOINT
-- {
--     return jl_object_id_(jl_typetagof(v), v);
-- }
-- /Source
  def jl_object_id__cold (tag value : Word) : M Word := do
    let dtAddress ← toTypeof tag
    let dt ← datatypeAt dtAddress
    if dt.isMutable then
      let kind := tagKind tag
      if kind == .string then
        let string ← objectAt value
        requireReadable (value+8) string.length
        return H.memhash_seed (← getWorld).raw.heap (value+8).toNat string.length 0xedc3b677
      if kind == .simplevector then return ← hash_svec value
      if kind == .datatype then
        let datatype ← datatypeAt value
        return H.bitmix (~~~(← typename_hash datatype.name)) (← hash_svec datatype.parameters)
      if kind == .module_ then return (← objectAt value).hash
      let header ← loadWord (value-8)
      if header &&& 4 != 0 then return ← loadWord (value-16)
      return H.inthash value
    immut_id_ dt value dt.hash
  partial_fixpoint

  def jl_object_id_ (tag value : Word) : M Word := do
    if tagKind tag == .symbol then return (← objectAt value).hash
    if tagKind tag == .datatype then
      let dt ← datatypeAt value
      if dt.hash != 0 then return dt.hash
    if tag == (← getWorld).globals.typenameType then return ← typename_hash value
    jl_object_id__cold tag value
  partial_fixpoint

  def jl_object_id (value : Word) : M Word := do
    jl_object_id_ (← typetag value) value
  partial_fixpoint

  /-- src/jltypes.c:442-459. The local C int is returned with the pointer. -/
  def nth_union_component (value : Word) (index : Int32) : M (Word × Int32) := do
    if tagKind (← typetag value) == .uniontype then
      let union ← objectAt value
      let (found, index) ← nth_union_component union.left index
      if found != 0 then pure (found, index)
      else nth_union_component union.right index
    else if index == 0 then pure (value, index)
    else if index.toInt == -(2^31) then
      fail (.undefinedBehavior "union-component int decrement overflow" value)
    else pure (0, index-1)
  partial_fixpoint

  def jl_nth_union_component (value : Word) (index : Int32) : M Word := do
    return (← nth_union_component value index).1
end

end JuliaLean.src.builtins_identity_c
