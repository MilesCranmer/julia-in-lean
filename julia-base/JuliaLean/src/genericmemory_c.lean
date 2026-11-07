import JuliaLean.base.genericmemory
import JuliaLean.base.pointer
import JuliaLean.base.runtime_internals
import JuliaLean.Runtime.Collections

-- UNTRANSLATED
-- Source: src/genericmemory.c:1-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- // This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- /*
--   GenericMemory{kind, T} constructors and primitives
-- */
-- #include <stdlib.h>
-- #include <string.h>
-- #ifdef _OS_WINDOWS_
-- #include <malloc.h>
-- #endif
-- #include "julia.h"
-- #include "julia_internal.h"
-- #include "julia_assert.h"
-- 
-- #ifdef __cplusplus
-- extern "C" {
-- #endif
-- 
-- // genericmemory constructors ---------------------------------------------------------
-- JL_DLLEXPORT char *jl_genericmemory_typetagdata(jl_genericmemory_t *m) JL_NOTSAFEPOINT
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m))->layout;
--     assert(layout->flags.arrayelem_isunion);
--     return (char*)m->ptr + m->length * layout->size;
-- }
-- 
-- #define MAXINTVAL (((size_t)-1)>>1)
-- 
-- // Leaves the length and the data uninitialized. Before the next safepoint, the caller must set
-- // the length, and zero the data if the element type requires it.
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory_unchecked(jl_ptls_t ptls, size_t nbytes, jl_datatype_t *mtype)
-- {
--     // LateLowerGCFrame inlines the pooled case for constant sizes; dynamic sizes still get here
--     int pooled = jl_genericmemory_data_inline(nbytes);
--     size_t tot = nbytes + JL_GENERICMEMORY_INLINE_DATA_OFFSET;
--     char *data;
--     jl_genericmemory_t *m;
--     if (!pooled) {
--         data = (char*)jl_gc_managed_malloc(nbytes);
--         tot = sizeof(jl_genericmemory_t) + sizeof(void*);
--     }
--     m = (jl_genericmemory_t*)jl_gc_alloc(ptls, tot, mtype);
--     if (pooled) {
--         data = (char*)m + JL_GENERICMEMORY_INLINE_DATA_OFFSET;
--     }
--     else {
--         int isaligned = 1; // jl_gc_managed_malloc is always aligned
--         jl_gc_track_malloced_genericmemory(ptls, m, isaligned);
--         jl_genericmemory_data_owner_field(m) = (jl_value_t*)m;
--     }
--     m->ptr = data;
--     return m;
-- }
-- 
-- /Source

-- UNTRANSLATED
-- Source: src/genericmemory.c:74-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_genericmemory(jl_value_t *mtype, size_t nel)
-- {
--     assert(jl_is_datatype(mtype));
--     jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     if (m == NULL) {
--         jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
--         if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
--             jl_error("GenericMemory kind must be :not_atomic or :atomic");
--         jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
--         if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
--             jl_error("GenericMemory addrspace must be Core.CPU");
--         if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
--             jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
--         abort(); // this is checked already by jl_get_genericmemory_layout
--     }
--     assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
--     if (nel == 0) // zero-sized allocation optimization fast path
--         return m;
-- 
--     size_t elsz = layout->size;
--     int isboxed = layout->flags.arrayelem_isboxed;
--     int isunion = layout->flags.arrayelem_isunion;
--     int zi = ((jl_datatype_t*)mtype)->zeroinit;
--     if (isboxed)
--         elsz = sizeof(void*);
--     return _new_genericmemory_(mtype, nel, isunion, zi, elsz);
-- }
-- 
-- JL_DLLEXPORT jl_genericmemory_t *jl_string_to_genericmemory(jl_value_t *str) JL_CANSAFEPOINT
-- {
--     if (jl_string_len(str) == 0)
--         return (jl_genericmemory_t*)((jl_datatype_t*)jl_memory_uint8_type)->instance;
--     jl_task_t *ct = jl_current_task;
--     int tsz = sizeof(jl_genericmemory_t) + sizeof(void*);
--     jl_genericmemory_t *m = (jl_genericmemory_t*)jl_gc_alloc(ct->ptls, tsz, jl_memory_uint8_type);
--     m->length = jl_string_len(str);
--     m->ptr = jl_string_data(str);
--     jl_genericmemory_data_owner_field(m) = str;
--     return m;
-- }
-- 
-- // own_buffer != 0 iff GC should call free() on this pointer eventually
-- JL_DLLEXPORT jl_genericmemory_t *jl_ptr_to_genericmemory(jl_value_t *mtype, void *data,
--                                                          size_t nel, int own_buffer)
-- {
--     jl_task_t *ct = jl_current_task;
--     assert(jl_is_datatype(mtype));
--     jl_genericmemory_t *m = (jl_genericmemory_t*)((jl_datatype_t*)mtype)->instance;
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     if (m == NULL) {
--         jl_value_t *kind = jl_tparam0((jl_datatype_t*)mtype);
--         if (kind != (jl_value_t*)jl_not_atomic_sym && kind != (jl_value_t*)jl_atomic_sym)
--             jl_error("GenericMemory kind must be :not_atomic or :atomic");
--         jl_value_t *addrspace = jl_tparam2((jl_datatype_t*)mtype);
--         if (!jl_is_addrspacecore(addrspace) || jl_unbox_uint8(addrspace) != 0)
--             jl_error("GenericMemory addrspace must be Core.CPU");
--         if (!((jl_datatype_t*)mtype)->has_concrete_subtype || layout == NULL)
--             jl_type_error_rt("GenericMemory", "element type", (jl_value_t*)jl_type_type, jl_tparam1(mtype));
--         abort();
--     }
--     assert(((jl_datatype_t*)mtype)->has_concrete_subtype && layout != NULL);
--     //if (nel == 0) {// zero-sized allocation optimization fast path
--     //    if (own_buffer)
--     //        free(data);
--     //    return m;
--     //}
-- 
--     size_t elsz = layout->size;
--     size_t align = layout->alignment;
--     int isboxed = layout->flags.arrayelem_isboxed;
--     int isunion = layout->flags.arrayelem_isunion;
--     if (isboxed)
--         elsz = sizeof(void*);
--     if (isunion)
--         jl_exceptionf(jl_argumenterror_type,
--                       "unsafe_wrap: unspecified layout for union element type");
--     if (((uintptr_t)data) & ((align > JL_HEAP_ALIGNMENT ? JL_HEAP_ALIGNMENT : align) - 1))
--         jl_exceptionf(jl_argumenterror_type,
--                       "unsafe_wrap: pointer %p is not properly aligned to %u bytes", data, align);
--     size_t nbytes = 0; // initialized to workaround clang sa bug on v20: https://github.com/llvm/llvm-project/issues/136292
--     int overflow = __builtin_mul_overflow(nel, elsz, &nbytes);
--     if (isunion) {
--         // an extra byte for each isbits union memory element, stored at m->ptr + m->length
--         overflow |= __builtin_add_overflow(nel, nbytes, &nbytes);
--     }
--     if ((nel >= MAXINTVAL) || (nbytes >= MAXINTVAL) || overflow)
--         jl_exceptionf(jl_argumenterror_type, "invalid GenericMemory size: the number of elements is either negative or too large for system address width");
--     int tsz = sizeof(jl_genericmemory_t) + sizeof(void*);
--     m = (jl_genericmemory_t*)jl_gc_alloc(ct->ptls, tsz, mtype);
--     m->ptr = data;
--     m->length = nel;
--     jl_genericmemory_data_owner_field(m) = own_buffer ? (jl_value_t*)m : NULL;
--     if (own_buffer) {
--         int isaligned = 0;  // TODO: allow passing memalign'd buffers
--         jl_gc_track_malloced_genericmemory(ct->ptls, m, isaligned);
--         size_t allocated_bytes = memory_block_usable_size(data, isaligned);
--         jl_gc_count_allocd(allocated_bytes);
--     }
--     return m;
-- }
-- 
-- JL_DLLEXPORT jl_genericmemory_t *jl_new_genericmemory(jl_value_t *mtype, jl_value_t *nel)
-- {
--     return jl_alloc_genericmemory(mtype, jl_unbox_long(nel));
-- }
-- 
-- JL_DLLEXPORT jl_genericmemory_t *jl_pchar_to_genericmemory(const char *str, size_t len) JL_CANSAFEPOINT
-- {
--     jl_genericmemory_t *m = jl_alloc_genericmemory(jl_memory_uint8_type, len);
--     memcpy(m->ptr, str, len);
--     return m;
-- }
-- 
-- JL_DLLEXPORT jl_value_t *jl_genericmemory_to_string(jl_genericmemory_t *m, size_t len)
-- {
--     assert(len <= m->length);
--     if (len == 0) {
--         // this may seem like purely an optimization (which it also is), but it
--         // also ensures that calling `String(m)` doesn't corrupt a previous
--         // string also created the same way, where `m = StringVector(_)`.
--         return jl_an_empty_string;
--     }
--     int how = jl_genericmemory_how(m);
--     size_t mlength = m->length;
--     if (how != JL_GENERICMEMORY_INLINED) {
--         jl_value_t *o = jl_genericmemory_data_owner_field(m);
--         if (how == JL_GENERICMEMORY_STRINGOWNED && // implies jl_is_string(o)
--              ((mlength + sizeof(void*) + 1 <= GC_MAX_SZCLASS) == (len + sizeof(void*) + 1 <= GC_MAX_SZCLASS))) {
--             jl_string_data(o)[len] = '\0';
--             *(size_t*)o = len;
--             return o;
--         }
--         JL_GC_PUSH1(&o);
--         jl_value_t *str = jl_pchar_to_string((const char*)m->ptr, len);
--         JL_GC_POP();
--         return str;
--     }
--     // n.b. how == JL_GENERICMEMORY_INLINED is always pool-allocated, so the freed bytes are computed from the pool not the object
--     return jl_pchar_to_string((const char*)m->ptr, len);
-- }
-- 
-- JL_DLLEXPORT jl_genericmemory_t *jl_alloc_memory_any(size_t n)
-- {
--     return jl_alloc_genericmemory(jl_memory_any_type, n);
-- }
-- 
-- JL_DLLEXPORT void jl_genericmemory_copyto(jl_genericmemory_t *dest, char* destdata,
--                                           jl_genericmemory_t *src, char* srcdata,
--                                           size_t n) JL_NOTSAFEPOINT
-- {
--     jl_datatype_t *dt = (jl_datatype_t*)jl_typetagof(dest);
--     if (dt != (jl_datatype_t*)jl_typetagof(src))
--         jl_exceptionf(jl_argumenterror_type, "jl_genericmemory_copyto requires source and dest to have same type");
--     const jl_datatype_layout_t *layout = dt->layout;
--     if (layout->flags.arrayelem_isboxed) {
--         jl_value_t *owner = jl_genericmemory_owner(dest);
--         return jl_gc_genericmemory_copy_boxed(owner, (_Atomic(void*)*)destdata, src,
--                                               (_Atomic(void*)*)srcdata, n);
--     }
--     size_t elsz = layout->size;
--     int isbitsunion = layout->flags.arrayelem_isunion;
--     if (isbitsunion) {
--         char *sourcetypetagdata = jl_genericmemory_typetagdata(src);
--         char *desttypetagdata = jl_genericmemory_typetagdata(dest);
--         memmove(desttypetagdata+(size_t)destdata, sourcetypetagdata+(size_t)srcdata, n);
--         srcdata = (char*)src->ptr + elsz*(size_t)srcdata;
--         destdata = (char*)dest->ptr + elsz*(size_t)destdata;
--     }
--     if (layout->first_ptr != -1) {
--         jl_value_t *owner = jl_genericmemory_owner(dest);
--         jl_gc_genericmemory_copy_ptr(owner, destdata, src, srcdata, n, dt);
--     }
--     else {
--         memmove(destdata, srcdata, n * elsz);
--     }
-- }
-- 
-- 
-- // genericmemory primitives -----------------------------------------------------------
-- 
-- jl_value_t *jl_genericmemoryref(jl_genericmemory_t *mem, size_t i)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(mem))->layout;
--     int isatomic = layout->flags.arrayelem_isatomic || layout->flags.arrayelem_islocked;
--     jl_genericmemoryref_t m;
--     m.mem = mem;
--     m.ptr_or_offset = (layout->flags.arrayelem_isunion || layout->size == 0) ? (void*)i : (void*)((char*)mem->ptr + layout->size * i);
--     return jl_memoryrefget(m, isatomic);
-- }
-- 
-- jl_genericmemory_t *jl_genericmemory_copy_slice(jl_genericmemory_t *mem, void *data, size_t len)
-- {
--     jl_value_t *mtype = (jl_value_t*)jl_typetagof(mem);
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     size_t elsz = layout->size;
--     int isunion = layout->flags.arrayelem_isunion;
--     jl_genericmemory_t *new_mem = _new_genericmemory_(mtype, len, isunion, 0, elsz);
--     if (isunion) {
--         memcpy(new_mem->ptr, (char*)mem->ptr + (size_t)data * elsz, len * elsz);
--         memcpy(jl_genericmemory_typetagdata(new_mem), jl_genericmemory_typetagdata(mem) + (size_t)data, len);
--     }
--     else if (layout->first_ptr != -1) {
--         if (data == NULL) {
--             assert(len * elsz / sizeof(void*) == 0); // make static analyzer happy
--         }
--         memmove_refs((_Atomic(void*)*)new_mem->ptr, (_Atomic(void*)*)data, len * elsz / sizeof(void*));
--     }
--     else if (data != NULL) {
--         memcpy(new_mem->ptr, data, len * elsz);
--     }
--     return new_mem;
-- }
-- 
-- jl_genericmemory_t *jl_genericmemory_copy(jl_genericmemory_t *mem)
-- {
--     jl_value_t *mtype = (jl_value_t*)jl_typetagof(mem);
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)mtype)->layout;
--     return jl_genericmemory_copy_slice(mem, layout->flags.arrayelem_isunion || layout->size == 0 ? (void*)0 : mem->ptr, mem->length);
-- }
-- 
-- JL_DLLEXPORT jl_value_t *(jl_genericmemory_data_owner)(jl_genericmemory_t *m) JL_NOTSAFEPOINT
-- {
--     return jl_genericmemory_data_owner_field(m);
-- }
-- 
-- jl_genericmemoryref_t *jl_new_memoryref(jl_value_t *typ, jl_genericmemory_t *mem, void *data)
-- {
--     jl_task_t *ct = jl_current_task;
--     jl_genericmemoryref_t *m = (jl_genericmemoryref_t*)jl_gc_alloc(ct->ptls, sizeof(jl_genericmemoryref_t), typ);
--     m->mem = mem;
--     m->ptr_or_offset = data;
--     return m;
-- }
-- 
-- // memoryref primitives
-- jl_genericmemoryref_t jl_memoryrefindex(jl_genericmemoryref_t m JL_PROPAGATES_ROOT, size_t idx)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     if ((layout->flags.arrayelem_isboxed || !layout->flags.arrayelem_isunion) && layout->size != 0) {
--         m.ptr_or_offset = (void*)((char*)m.ptr_or_offset + idx * layout->size);
--         assert((char*)m.ptr_or_offset - (char*)m.mem->ptr < layout->size * m.mem->length);
--     }
--     else {
--         m.ptr_or_offset = (void*)((size_t)m.ptr_or_offset + idx);
--         assert((size_t)m.ptr_or_offset < m.mem->length);
--     }
--     return m;
-- }
-- 
-- static jl_value_t *jl_ptrmemrefget(jl_genericmemoryref_t m JL_PROPAGATES_ROOT, int isatomic) JL_NOTSAFEPOINT
-- {
--     assert((char*)m.ptr_or_offset - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
--     assert(((jl_datatype_t*)jl_typetagof(m.mem))->layout->flags.arrayelem_isboxed);
--     _Atomic(jl_value_t*) *ptr = (_Atomic(jl_value_t*)*)m.ptr_or_offset;
--     jl_value_t *elt = isatomic ? jl_atomic_load(ptr) : jl_atomic_load_relaxed(ptr);
--     if (elt == NULL)
--         jl_throw(jl_undefref_exception);
--     return elt;
-- }
-- 
-- jl_value_t *jl_memoryrefget(jl_genericmemoryref_t m, int isatomic)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     assert(isatomic == (layout->flags.arrayelem_isatomic || layout->flags.arrayelem_islocked));
--     if (layout->flags.arrayelem_isboxed)
--         return jl_ptrmemrefget(m, isatomic);
--     jl_value_t *eltype = normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
--     char *data = (char*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isunion) {
--         assert(!isatomic);
--         assert(jl_is_uniontype(eltype));
--         size_t i = (size_t)data;
--         assert(i < m.mem->length);
--         // isbits union selector bytes are always stored directly after the last memory element
--         uint8_t sel = jl_genericmemory_typetagdata(m.mem)[i];
--         eltype = jl_nth_union_component(eltype, sel);
--         data = (char*)m.mem->ptr + i * layout->size;
--     }
--     if (layout->size == 0) {
--         assert(jl_is_datatype_singleton((jl_datatype_t*)eltype));
--         return ((jl_datatype_t*)eltype)->instance;
--     }
--     assert(data - (char*)m.mem->ptr < layout->size * m.mem->length);
--     jl_value_t *r;
--     size_t fsz = jl_datatype_size(eltype);
--     int needlock = layout->flags.arrayelem_islocked;
--     if (isatomic && !needlock) {
--         r = jl_atomic_new_bits(eltype, data);
--     }
--     else if (needlock) {
--         jl_task_t *ct = jl_current_task;
--         r = jl_gc_alloc(ct->ptls, fsz, eltype);
--         jl_lock_field((jl_mutex_t*)data);
--         memcpy((char*)r, data + LLT_ALIGN(sizeof(jl_mutex_t), JL_SMALL_BYTE_ALIGNMENT), fsz);
--         jl_unlock_field((jl_mutex_t*)data);
--     }
--     else {
--         // TODO: a finalizer here could make the isunion case not quite right
--         r = jl_new_bits(eltype, data);
--     }
--     r = undefref_check((jl_datatype_t*)eltype, r);
--     if (__unlikely(r == NULL))
--         jl_throw(jl_undefref_exception);
--     return r;
-- }
-- 
-- static int _jl_memoryref_isassigned(jl_genericmemoryref_t m, int isatomic)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     _Atomic(jl_value_t*) *elem = (_Atomic(jl_value_t*)*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isboxed) {
--     }
--     else if (layout->first_ptr >= 0) {
--         elem = &elem[layout->first_ptr];
--     }
--     else {
--         return 1;
--     }
--     return (isatomic ? jl_atomic_load(elem) : jl_atomic_load_relaxed(elem)) != NULL;
-- }
-- 
-- jl_value_t *jl_memoryref_isassigned(jl_genericmemoryref_t m, int isatomic)
-- {
--     return _jl_memoryref_isassigned(m, isatomic) ? jl_true : jl_false;
-- }
-- 
-- /Source

namespace JuliaLean.src.genericmemory_c

open JuliaLean
open JuliaLean.base.genericmemory
abbrev Layout := JuliaLean.base.runtime_internals.DataTypeLayout
abbrev ByteHeap := JuliaLean.base.pointer.ByteHeap
abbrev Byte := JInt .u8

/-- Native layout construction; conversions are exactly the declared C/Julia field widths. -/
def nativeLayout (size nfields npointers : Nat) (firstptr : Int) (alignment flags : Nat) : Layout :=
  ⟨JInt.wrap .u32 size, JInt.wrap .u32 nfields, JInt.wrap .u32 npointers,
    JInt.wrap .i32 firstptr, JInt.wrap .u16 alignment, JInt.wrap .u16 flags⟩

/-- Last entry of the nonempty pointer vector supplied to jl_get_layout. -/
def lastPointer (first : JInt .u32) : List (JInt .u32) → JInt .u32
  | [] => first
  | x :: rest => lastPointer x rest

/-- The nfields=0 GenericMemory specialization of src/datatype.c:191-253.
The post-layout-construction pointer vector is nonempty even for pointer-free
elements: its first value is UINT32_MAX, yielding descriptor type 2 and firstptr=-1.
`arrayelem` is the four-bit result of datatype.c:613-623, not the element's flags. -/
def genericMemoryHeader (size alignment arrayelem : Nat) (firstptr : Int)
    (rest : List Nat := []) : Layout :=
  let first := JInt.wrap .u32 firstptr
  let tail := rest.map (fun (n : Nat) => JInt.wrap .u32 (n : Int))
  let maximumOffset := (lastPointer first tail).val.toNat
  let descriptor := if maximumOffset < 256 then 0 else if maximumOffset < 65536 then 1 else 2
  nativeLayout size 0 (tail.length + 1) (JInt.wrap .i32 first.val).val alignment
    (1 + 2 * descriptor + 8 * (arrayelem % 16))

/-- Runtime type metadata, not a user-selected unset effect. `direct` is dt->layout;
`wrapper` is jl_unwrap_unionall(dt->name->wrapper)->layout, used only by jl_datatype_layout.
`pointerTable` is the unsigned table at jl_dt_layout_ptrs(direct), in pointer-word units.
Sources: src/julia.h:1679-1686,1783-1797. -/
structure Datatype where
  direct : Layout
  wrapper : Layout
  pointerTable : Nat → Nat

/-- The only alias normalized by src/julia_internal.h:1324-1328. A union/boxed
metadata record need not be a datatype, since unset returns before reading it. -/
inductive ElementType where
  | datatype (dt : Datatype)
  | typeEqBottom
  | other

def normalizeTypeofbottomLayoutAlias (typeofBottom : Option Datatype) : ElementType → ElementType
  | .typeEqBottom => match typeofBottom with
    | some dt => .datatype dt
    | none => .typeEqBottom
  | ty => ty

def datatypeLayout (dt : Datatype) : Layout :=
  if dt.direct.nfields.val == 0 && dt.direct.npointers.val != 0 then dt.wrapper else dt.direct

def datatypeSize (dt : Datatype) : Nat := (datatypeLayout dt).size.val.toNat

/-- A typed snapshot of the same runtime memory type: layout is
((jl_datatype_t*)jl_typetagof(m.mem))->layout, elementType is its tparam1,
and kind is its tparam0. These are runtime metadata reads, not separately
chosen layouts/element types; sources genericmemory.c:404,421 and builtins.c:2383.
elementTag is the existing abstractset reflection of that same tparam1. -/
structure RuntimeTypeSnapshot where
  identity : Nat
  layout : Layout
  elementType : ElementType
  elementTag : JuliaLean.base.abstractset.JuliaType
  kind : MemoryKind

/-- The runtime type snapshot, owner, and ABI inputs do not contain storage operations.
The mutex size is an ABI primitive at genericmemory.c:426; small alignment is 16
(julia_internal.h:672), pointer width 8 and atomic maximum 16 (julia.h:58-67). -/
structure Metadata where
  runtimeType : RuntimeTypeSnapshot
  typeofBottom : Option Datatype
  owner : Nat
  mutexBytes : Nat

def Metadata.memoryLayout (m : Metadata) : Layout := m.runtimeType.layout
def Metadata.elementType (m : Metadata) : ElementType := m.runtimeType.elementType
def Metadata.kind (m : Metadata) : MemoryKind := m.runtimeType.kind

/-- Native UInt16 bit test from the installed runtime-internals model. -/
def flag (l : Layout) (bit : Nat) : Bool :=
  JuliaLean.base.runtime_internals.has16 l.flags (2 ^ bit)

def isBoxed (m : Metadata) : Bool := flag m.memoryLayout 3
def isUnion (m : Metadata) : Bool := flag m.memoryLayout 4
def isAtomic (m : Metadata) : Bool := flag m.memoryLayout 5
def isLocked (m : Metadata) : Bool := flag m.memoryLayout 6

def lockPayloadOffset (m : Metadata) : Nat :=
  (JuliaLean.base.runtime_internals.lltAlign
    JuliaLean.base.int.add
    (fun x : JInt .u64 => JuliaLean.base.int.sub x (JInt.wrap .u64 1))
    JuliaLean.base.int.neg JuliaLean.base.int.band
    (JInt.wrap .u64 m.mutexBytes) (JInt.wrap .u64 16)).val.toNat

/-- `jl_ptr_offset(dt,i)`: the unsigned table read selected by fielddesc_type.
The C table is already typed uint8_t/uint16_t/uint32_t. Modulo is that unsigned read;
no byte-order convention is imposed on the host ABI. Foreign descriptors are excluded
by the C assertion at julia.h:1795. -/
def ptrOffset (dt : Datatype) (i : Nat) : Nat :=
  let fielddesc := (JuliaLean.base.runtime_internals.datatypeFielddescTypeLayout dt.direct).val
  let width := if fielddesc == 0 then 8 else if fielddesc == 1 then 16 else 32
  dt.pointerTable i % 2 ^ width

inductive StoreOrder where
  | seqCst
  | release
  deriving Repr, DecidableEq

/-- Calls in their C execution order. Barriers carry the exact address of the
reference being overwritten, rather than a value guessed from an Option slot. -/
inductive Effect where
  | deletionBarrier (owner address : Nat)
  | storePointerNull (address : Nat) (order : StoreOrder)
  | storeBitsZero (address size : Nat)
  | lock (address : Nat)
  | memsetZero (address size : Nat)
  | unlock (address : Nat)
  deriving Repr, DecidableEq

/-- C assertions are not Julia exceptions. `invalidDatatype` identifies an
unreachable metadata combination, never a silent preserve/clear fallback. -/
inductive Failure where
  | invalidDatatype
  | invalidAtomicOrdering
  | nonAtomicWrite
  | atomicWrite
  | bounds
  deriving Repr, DecidableEq

/--
Julia source: src/genericmemory.c:402-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
void jl_memoryrefunset(jl_genericmemoryref_t m, int isatomic)
{
    const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
    assert(isatomic == (layout->flags.arrayelem_isatomic || layout->flags.arrayelem_islocked));
    if (layout->flags.arrayelem_isboxed) {
        assert((char*)m.ptr_or_offset - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
        _Atomic(jl_value_t*) *p = (_Atomic(jl_value_t*)*)m.ptr_or_offset;
        // Deletion barrier: snapshot the overwritten reference for SATB collectors.
        jl_gc_wb(jl_genericmemory_owner(m.mem), (void*)p, NULL);
        if (isatomic)
            jl_atomic_store(p, (jl_value_t*)NULL);
        else
            jl_atomic_store_release(p, (jl_value_t*)NULL);
        return;
    }
    if (layout->flags.arrayelem_isunion)
        return;
    if (layout->first_ptr < 0)
        return;
    jl_datatype_t *dt = (jl_datatype_t*)normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
    assert(jl_is_datatype(dt)); // implied by !isboxed && !isunion
    size_t fsz = jl_datatype_size(dt);
    char *data = (char*)m.ptr_or_offset;
    int needlock = layout->flags.arrayelem_islocked;
    char *payload = needlock ? data + LLT_ALIGN(sizeof(jl_mutex_t), JL_SMALL_BYTE_ALIGNMENT) : data;
    // Deletion barriers: one per reference field being cleared.
    jl_value_t *owner = jl_genericmemory_owner(m.mem);
    for (size_t i = 0; i < dt->layout->npointers; i++)
        jl_gc_wb(owner, (jl_value_t**)payload + jl_ptr_offset(dt, i), NULL);
    if (isatomic && !needlock) {
        _Alignas(MAX_POINTERATOMIC_SIZE) char zero_buf[MAX_POINTERATOMIC_SIZE] = {0};
        assert(fsz <= MAX_POINTERATOMIC_SIZE);
        jl_atomic_store_bits(data, (jl_value_t*)zero_buf, fsz);
    }
    else if (needlock) {
        jl_lock_field((jl_mutex_t*)data);
        memset(payload, 0, fsz);
        jl_unlock_field((jl_mutex_t*)data);
    }
    else {
        memset(data, 0, fsz);
    }
}
```
`data` is already the reference's byte address, except in no-op union/zero-sized
branches. fsz comes from the normalized element datatype, not memoryLayout.size.
The barriers precede lock acquisition.
-/
def memoryrefUnsetProgram (m : Metadata) (data : Nat) (atomic : Bool) :
    Except Failure (List Effect) := do
  if isBoxed m then
    return [.deletionBarrier m.owner data,
      .storePointerNull data (if atomic then .seqCst else .release)]
  if isUnion m then return []
  if m.memoryLayout.firstptr.val < 0 then return []
  let dt ← match normalizeTypeofbottomLayoutAlias m.typeofBottom m.elementType with
    | .datatype dt => pure dt
    | _ => throw .invalidDatatype
  let fsz := datatypeSize dt
  let payload := if isLocked m then data + lockPayloadOffset m else data
  let barriers := (List.range dt.direct.npointers.val.toNat).map fun i =>
    Effect.deletionBarrier m.owner (payload + 8 * ptrOffset dt i)
  if atomic && !isLocked m then
    return barriers ++ [.storeBitsZero data fsz]
  else if isLocked m then
    return barriers ++ [.lock data, .memsetZero payload fsz, .unlock data]
  else
    return barriers ++ [.memsetZero data fsz]

/-- Domain of the assertions reached by jl_memoryrefunset, not additional
preconditions on the public Julia API. Other layout consistency is supplied by the
runtime type constructor, not asserted as a law of a user callback. -/
def RuntimeValid (m : Metadata) (data base length : Nat) (atomic : Bool) : Prop :=
  atomic = (isAtomic m || isLocked m) ∧
  (isBoxed m = true → base ≤ data ∧ data - base < 8 * length) ∧
  (isBoxed m = false → isUnion m = false → 0 ≤ m.memoryLayout.firstptr.val →
    ∃ dt, normalizeTypeofbottomLayoutAlias m.typeofBottom m.elementType = .datatype dt ∧
      (JuliaLean.base.runtime_internals.datatypeFielddescTypeLayout dt.direct).val < 3 ∧
      (atomic = true → isLocked m = false → datatypeSize dt ≤ 16))

/-- Symbols represented by the installed MemoryOrder, including arbitrary symbols. -/
def orderSymbol : MemoryOrder → String
  | .notAtomic => "not_atomic"
  | .monotonic => "monotonic"
  | .acquire => "acquire"
  | .release => "release"
  | .acqRel => "acquire_release"
  | .seqCst => "sequentially_consistent"
  | .other name => name

/-- Store-order validation at src/builtins.c:1146-1170,2375-2398. The boundscheck
Bool argument is type-checked but does not suppress the zero-length check. -/
def checkStoreOrder (order : MemoryOrder) : Except Failure Unit :=
  if ["not_atomic", "unordered", "monotonic", "release", "sequentially_consistent"].contains
      (orderSymbol order) then .ok () else .error .invalidAtomicOrdering

def memoryrefUnsetBuiltinProgram (m : Metadata) (data length : Nat)
    (order : MemoryOrder) (_boundsChecking : Bool) : Except Failure (List Effect) := do
  match m.kind with
  | .notAtomic =>
    if orderSymbol order != "not_atomic" then
      checkStoreOrder order
      throw .nonAtomicWrite
  | .atomic =>
    checkStoreOrder order
    if orderSymbol order == "not_atomic" then throw .atomicWrite
  if length == 0 then throw .bounds
  memoryrefUnsetProgram m data (m.kind == .atomic)

/-- Observable runtime-call trace. The barrier snapshots all eight old pointer
bytes before any clear; collector-internal state is outside the storage model.
Lock/unlock calls are preserved as events, not replaced by storage callbacks. -/
inductive Event where
  | barrier (owner address : Nat) (oldPointer : List Byte)
  | storePointer (address : Nat) (order : StoreOrder)
  | storeBits (address size : Nat)
  | lock (address : Nat)
  | memset (address size : Nat)
  | unlock (address : Nat)
  deriving Repr

/-- The installed raw GenericMemory storage representation, pointer.ByteHeap,
plus a trace of the C primitive calls that are not byte storage. -/
structure RawState where
  heap : ByteHeap
  events : List Event := []

def zeroBytes (h : ByteHeap) (address size : Nat) : ByteHeap :=
  h.writeBytes address (List.replicate size (JInt.wrap .u8 0))

/-- jl_atomic_store_bits writes the next supported scalar width, including zeroed
padding above fsz, src/datatype.c:1263-1287. RuntimeValid restricts fsz to ≤ 16. -/
def atomicStoreWidth (fsz : Nat) : Nat :=
  if fsz = 0 then 0 else if fsz = 1 then 1 else 2 ^ (Nat.log2 (fsz - 1) + 1)

def interpretRawEffect (s : RawState) : Effect → RawState
  | .deletionBarrier owner address =>
    { s with events := s.events ++ [.barrier owner address (s.heap.readBytes address 8)] }
  | .storePointerNull address order =>
    { heap := zeroBytes s.heap address 8, events := s.events ++ [.storePointer address order] }
  | .storeBitsZero address size =>
    { heap := zeroBytes s.heap address (atomicStoreWidth size),
      events := s.events ++ [.storeBits address size] }
  | .lock address => { s with events := s.events ++ [.lock address] }
  | .memsetZero address size =>
    { heap := zeroBytes s.heap address size, events := s.events ++ [.memset address size] }
  | .unlock address => { s with events := s.events ++ [.unlock address] }

def interpretRaw (effects : List Effect) (s : RawState) : RawState :=
  effects.foldl interpretRawEffect s

/-- Existing GenericMemoryRef is used unchanged. Length/ptr/metadata are runtime
object fields, not new free storage operations. -/
structure MemoryObject where
  ptr : Nat
  length : Nat
  metadata : Metadata

abbrev RawRef := GenericMemoryRef MemoryObject Nat

def rawMemoryrefUnset (ref : RawRef) (order : MemoryOrder) (boundsChecking : Bool) :
    ExceptT Failure (StateM RawState) Unit := do
  match memoryrefUnsetBuiltinProgram ref.mem.metadata ref.ptr_or_offset ref.mem.length
      order boundsChecking with
  | .error e => throw e
  | .ok effects => modify (interpretRaw effects)

/-- Reference construction uses the memory-layout stride, src/genericmemory.c:256-263,
especially line 262. Incrementing a reference is at :311-321. -/
def refAt (mem : MemoryObject) (index0 : Nat) : RawRef :=
  ⟨mem, if isUnion mem.metadata || mem.metadata.memoryLayout.size.val == 0 then index0
    else mem.ptr + mem.metadata.memoryLayout.size.val.toNat * index0⟩

/-- Option storage is the installed Dict contents model. Inline values with a
pointer become unassigned when the first pointer is zero; union and pointer-free
values retain their old Option. It is a projection of the *same* program, not a
second Bool/isbits dispatcher. The full byte clear and call trace remain in RawState. -/
def interpretSlotEffect {α : Type} (index : Nat) (slots : Nat → Option α) :
    Effect → Nat → Option α
  | .storePointerNull _ _ => fun j => if j = index then none else slots j
  | .storeBitsZero _ _ => fun j => if j = index then none else slots j
  | .memsetZero _ _ => fun j => if j = index then none else slots j
  | _ => slots

def interpretSlots {α : Type} (effects : List Effect) (index : Nat)
    (slots : Nat → Option α) : Nat → Option α :=
  effects.foldl (interpretSlotEffect index) slots

/-- Runtime metadata for a valid Memory{T}, with the C datatype assertion made
explicit at construction. This is runtime data, not a correctness-law callback.
Non-atomic Dict memories cannot have either atomic/locked flag. -/
structure DictLayout where
  metadata : Metadata
  nonAtomicKind : metadata.kind = .notAtomic
  nonAtomicFlag : isAtomic metadata = false
  unlocked : isLocked metadata = false
  inlineDatatype : isBoxed metadata = false → isUnion metadata = false →
    0 ≤ metadata.memoryLayout.firstptr.val →
    ∃ dt, normalizeTypeofbottomLayoutAlias metadata.typeofBottom metadata.elementType = .datatype dt

/-- The Option projection has no recoverable failure on valid runtime metadata.
The dependent match consumes the *C datatype assertion*, without a fallback. -/
def dictUnsetEffects (l : DictLayout) (index0 : Nat) : List Effect :=
  match he : memoryrefUnsetProgram l.metadata (l.metadata.memoryLayout.size.val.toNat * index0) false with
  | .ok effects => effects
  | .error _ => False.elim (by
      cases hb : isBoxed l.metadata with
      | true => simp [memoryrefUnsetProgram, hb, pure, Except.pure] at he
      | false =>
        cases hu : isUnion l.metadata with
        | true => simp [memoryrefUnsetProgram, hb, hu, pure, Except.pure] at he
        | false =>
          by_cases hp : l.metadata.memoryLayout.firstptr.val < 0
          · simp [memoryrefUnsetProgram, hb, hu, hp, pure, Except.pure] at he
          · obtain ⟨dt, hdt⟩ := l.inlineDatatype hb hu (by omega)
            simp [memoryrefUnsetProgram, hb, hu, hp, hdt, l.unlocked,
              pure, Except.pure, bind, Except.bind] at he)

/-- Replacement for dict.round2's rt parameter. On the source domain (1 ≤ index ≤
size), C memoryrefAt points to index-1; all Option indices remain one-based. -/
def dictMemoryrefUnset {α : Type} (layout : DictLayout) (index : Nat) :
    StateM (Nat → Option α) Unit :=
  fun slots => ((), interpretSlots (dictUnsetEffects layout (index - 1)) index slots)

/-- The Nothing element layout and the Memory{Nothing} header are distinct.
The header follows datatype.c:543-553,567-585,613-625: npointers=1,
firstptr=-1, descriptor=2, haspadding=1, isbitsegal=0, hence flags=5. -/
def nothingElementLayout : Layout := nativeLayout 0 0 0 (-1) 1 128
def nothingMemoryLayout : Layout := genericMemoryHeader 0 1 0 (-1)
def nothingMetadata : Metadata :=
  { runtimeType :=
      { identity := 0
        layout := nothingMemoryLayout
        elementType := .datatype ⟨nothingElementLayout, nothingElementLayout, fun _ => 0⟩
        elementTag := .nothing
        kind := .notAtomic }
    typeofBottom := none
    owner := 0
    mutexBytes := 0 }

def nothingDictLayout : DictLayout where
  metadata := nothingMetadata
  nonAtomicKind := rfl
  nonAtomicFlag := rfl
  unlocked := rfl
  inlineDatatype := by
    intro _ _ _
    exact ⟨⟨nothingElementLayout, nothingElementLayout, fun _ => 0⟩, rfl⟩

/-- Actual boxed-memory header: datatype.c:543-553,607-625 leaves npointers=1,
firstptr=-1; the UINT32_MAX pointer sentinel selects descriptor 2, so flags=13.
The element representation is boxed and need not be a datatype. -/
def boxedLayout : Layout := genericMemoryHeader 8 8 1 (-1)
def boxedDictLayout : DictLayout where
  metadata :=
    { nothingMetadata with runtimeType :=
        { identity := 1
          layout := boxedLayout
          elementType := .other
          elementTag := .other
          kind := .notAtomic } }
  nonAtomicKind := rfl
  nonAtomicFlag := rfl
  unlocked := rfl
  inlineDatatype := by
    intro hb
    change true = false at hb
    cases hb


/-- MemoryRef operations on raw Option slots, using the native unset program. -/
def runtimeAccessOps {α : Type} (layout : DictLayout) :
    JuliaLean.base.genericmemory.MemoryAccessOps (StateM (Nat → Option α))
      Unit Nat (Option α) (Option α) where
  memoryref _ := pure ⟨(), 1⟩
  memoryrefAt _ i := pure ⟨(), i.val.toNat⟩
  memoryrefNew ref i _ := pure ⟨ref.mem, i.val.toNat⟩
  memoryrefIsAssigned ref _ _ := fun s => ((s ref.ptr_or_offset).isSome, s)
  memoryrefUnset ref _ _ := dictMemoryrefUnset layout ref.ptr_or_offset
  memoryrefSet ref v _ _ := fun s => ((), fun j => if j = ref.ptr_or_offset then v else s j)
  defaultOrderMemory _ := .notAtomic
  defaultOrderRef _ := .notAtomic
  checkboundsBool _ _ := pure true
  checkbounds _ _ := pure ()
  castElement := some
  convertElement v := pure v
  getindex _ i := fun s => (s i.val.toNat, s)

/-- Project the selected raw slot after the MemoryRef wrapper at
`base/genericmemory.jl:119`; byte and GC effects remain in the native program. -/
def unsetCell {α : Type} (layout : DictLayout) (index : Nat) (old : Option α) : Option α :=
  let slots : Nat → Option α := fun _ => old
  let result := Id.run ((JuliaLean.base.genericmemory.unsetindexRef
    (runtimeAccessOps layout) false ⟨(), index⟩).run slots)
  result.2 index

end JuliaLean.src.genericmemory_c

-- UNTRANSLATED
-- Source: src/genericmemory.c:445-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- void jl_memoryrefset(jl_genericmemoryref_t m, jl_value_t *rhs JL_ROOTED_BY_ARG(0) JL_MAYBE_UNROOTED, int isatomic)
-- {
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     assert(isatomic == (layout->flags.arrayelem_isatomic || layout->flags.arrayelem_islocked));
--     jl_value_t *eltype = normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
--     if (eltype != (jl_value_t*)jl_any_type && !jl_typeis(rhs, eltype)) {
--         JL_GC_PUSH1(&rhs);
--         if (!jl_isa(rhs, eltype))
--             jl_type_error("memoryrefset!", eltype, rhs);
--         JL_GC_POP();
--     }
--     if (layout->flags.arrayelem_isboxed) {
--         assert((char*)m.ptr_or_offset - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
--         jl_gc_wb(jl_genericmemory_owner(m.mem), m.ptr_or_offset, rhs);
--         if (isatomic)
--             jl_atomic_store((_Atomic(jl_value_t*)*)m.ptr_or_offset, rhs);
--         else
--             jl_atomic_store_release((_Atomic(jl_value_t*)*)m.ptr_or_offset, rhs);
--         return;
--     }
--     int hasptr;
--     char *data = (char*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isunion) {
--         assert(!isatomic);
--         assert(jl_is_uniontype(eltype));
--         size_t i = (size_t)data;
--         assert(i < m.mem->length);
--         uint8_t *psel = (uint8_t*)jl_genericmemory_typetagdata(m.mem) + i;
--         unsigned nth = 0;
--         if (!jl_find_union_component(eltype, jl_typeof(rhs), &nth))
--             assert(0 && "invalid genericmemoryset to isbits union");
--         *psel = nth;
--         hasptr = 0;
--         data = (char*)m.mem->ptr + i * layout->size;
--     }
--     else {
--         hasptr = layout->first_ptr >= 0;
--     }
--     if (layout->size != 0) {
--         assert(data - (char*)m.mem->ptr < layout->size * m.mem->length);
--         int needlock = layout->flags.arrayelem_islocked;
--         size_t fsz = jl_datatype_size((jl_datatype_t*)jl_typeof(rhs)); // need to shrink-wrap the final copy
--         char *payload = needlock ? data + LLT_ALIGN(sizeof(jl_mutex_t), JL_SMALL_BYTE_ALIGNMENT) : data;
--         if (hasptr)
--             jl_gc_multi_wb(jl_genericmemory_owner(m.mem), payload, rhs); // rhs is immutable
--         if (isatomic && !needlock) {
--             jl_atomic_store_bits(data, rhs, fsz);
--         }
--         else if (needlock) {
--             jl_lock_field((jl_mutex_t*)data);
--             memassign_safe(hasptr, payload, rhs, fsz);
--             jl_unlock_field((jl_mutex_t*)data);
--         }
--         else {
--             memassign_safe(hasptr, data, rhs, fsz);
--         }
--     }
-- }
-- 
-- jl_value_t *jl_memoryrefswap(jl_genericmemoryref_t m, jl_value_t *rhs, int isatomic)
-- {
--     jl_value_t *eltype = normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
--     if (eltype != (jl_value_t*)jl_any_type && !jl_typeis(rhs, eltype)) {
--         if (!jl_isa(rhs, eltype))
--             jl_type_error("memoryrefswap!", eltype, rhs);
--     }
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     jl_value_t *owner = jl_genericmemory_owner(m.mem);
--     char *data = (char*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isboxed) {
--         assert(data - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
--         jl_value_t *r;
--         jl_gc_wb(owner, (void*)data, rhs);
--         if (isatomic)
--             r = jl_atomic_exchange((_Atomic(jl_value_t*)*)data, rhs);
--         else
--             r = jl_atomic_exchange_release((_Atomic(jl_value_t*)*)data, rhs);
--         if (__unlikely(r == NULL))
--             jl_throw(jl_undefref_exception);
--         return r;
--     }
--     uint8_t *psel = NULL;
--     if (layout->flags.arrayelem_isunion) {
--         assert(!isatomic);
--         assert(jl_is_uniontype(eltype));
--         size_t i = (size_t)data;
--         assert(i < m.mem->length);
--         psel = (uint8_t*)jl_genericmemory_typetagdata(m.mem) + i;
--         data = (char*)m.mem->ptr + i * layout->size;
--     }
--     return swap_bits(eltype, data, psel, owner, rhs, isatomic ? isatomic_field : isatomic_none);
-- }
-- 
-- jl_value_t *jl_memoryrefmodify(jl_genericmemoryref_t m, jl_value_t *op, jl_value_t *rhs, int isatomic, jl_value_t *op_target)
-- {
--     jl_value_t *eltype = normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     jl_value_t *owner = jl_genericmemory_owner(m.mem);
--     char *data = (char*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isboxed) {
--         assert(data - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
--         return modify_value(eltype, (_Atomic(jl_value_t*)*)data, owner, op, rhs, isatomic, op_target);
--     }
--     size_t fsz = layout->size;
--     uint8_t *psel = NULL;
--     if (layout->flags.arrayelem_isunion) {
--         assert(!isatomic);
--         assert(jl_is_uniontype(eltype));
--         size_t i = (size_t)data;
--         assert(i < m.mem->length);
--         psel = (uint8_t*)jl_genericmemory_typetagdata(m.mem) + i;
--         data = (char*)m.mem->ptr + i * fsz;
--     }
--     return modify_bits(eltype, data, psel, owner, op, rhs, isatomic ? isatomic_field : isatomic_none, op_target);
-- }
-- 
-- jl_value_t *jl_memoryrefreplace(jl_genericmemoryref_t m, jl_value_t *expected, jl_value_t *rhs, int isatomic)
-- {
--     jl_value_t *eltype = normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
--     if (eltype != (jl_value_t*)jl_any_type && !jl_typeis(rhs, eltype)) {
--         if (!jl_isa(rhs, eltype))
--             jl_type_error("memoryrefreplace!", eltype, rhs);
--     }
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     jl_value_t *owner = jl_genericmemory_owner(m.mem);
--     char *data = (char*)m.ptr_or_offset;
--     if (layout->flags.arrayelem_isboxed) {
--         assert(data - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
--         return replace_value(eltype, (_Atomic(jl_value_t*)*)data, owner, expected, rhs, isatomic);
--     }
--     uint8_t *psel = NULL;
--     if (layout->flags.arrayelem_isunion) {
--         assert(!isatomic);
--         assert(jl_is_uniontype(eltype));
--         size_t i = (size_t)data;
--         assert(i < m.mem->length);
--         psel = (uint8_t*)jl_genericmemory_typetagdata(m.mem) + i;
--         data = (char*)m.mem->ptr + i * layout->size;
--     }
--     return replace_bits(eltype, data, psel, owner, expected, rhs, isatomic ? isatomic_field : isatomic_none);
-- }
-- 
-- jl_value_t *jl_memoryrefsetonce(jl_genericmemoryref_t m, jl_value_t *rhs, int isatomic)
-- {
--     jl_value_t *eltype = normalize_typeofbottom_layout_alias(jl_tparam1(jl_typetagof(m.mem)));
--     if (eltype != (jl_value_t*)jl_any_type && !jl_typeis(rhs, eltype)) {
--         if (!jl_isa(rhs, eltype))
--             jl_type_error("memoryrefsetonce!", eltype, rhs);
--     }
--     const jl_datatype_layout_t *layout = ((jl_datatype_t*)jl_typetagof(m.mem))->layout;
--     jl_value_t *owner = jl_genericmemory_owner(m.mem);
--     char *data = (char*)m.ptr_or_offset;
--     int success;
--     if (layout->flags.arrayelem_isboxed) {
--         assert(data - (char*)m.mem->ptr < sizeof(jl_value_t*) * m.mem->length);
--         jl_value_t *r = NULL;
--         _Atomic(jl_value_t*) *px = (_Atomic(jl_value_t*)*)data;
--         jl_gc_wb(owner, (void*)px, rhs);
--         success = isatomic ? jl_atomic_cmpswap(px, &r, rhs) : jl_atomic_cmpswap_release(px, &r, rhs);
--     }
--     else {
--         if (layout->flags.arrayelem_isunion) {
--             assert(!isatomic);
--             assert(jl_is_uniontype(eltype));
--             size_t i = (size_t)data;
--             assert(i < m.mem->length);
--             (void)i;
--             success = 0;
--         }
--         else if (layout->first_ptr < 0) {
--             success = 0;
--         }
--         else {
--             success = setonce_bits((jl_datatype_t*)eltype, data, owner, rhs, isatomic ? isatomic_field : isatomic_none);
--         }
--     }
--     return success ? jl_true : jl_false;
-- }
-- 
-- JL_DLLEXPORT jl_value_t *ijl_genericmemory_owner(jl_genericmemory_t *m JL_PROPAGATES_ROOT) JL_NOTSAFEPOINT
-- {
--     return jl_genericmemory_owner(m);
-- }
-- #ifdef __cplusplus
-- }
-- #endif
-- /Source
