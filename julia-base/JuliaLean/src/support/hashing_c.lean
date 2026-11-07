import JuliaLean.base.pointer

/-! Pinned native 64-bit hashing used by objectid. All bytes come from the
installed pointer.ByteHeap; the C hash functions are executable mirrors. -/
namespace JuliaLean.src.support.hashing_c
open JuliaLean
abbrev Heap := JuliaLean.base.pointer.ByteHeap

def byteAt (heap : Heap) (address : Nat) : UInt8 :=
  UInt8.ofNat (heap.readByte address).val.toNat

def load64 (heap : Heap) (address : Nat) : UInt64 := Id.run do
  let mut value : UInt64 := 0
  for i in [0:8] do
    value := value ||| ((byteAt heap (address+i)).toUInt64 <<< UInt64.ofNat (8*i))
  return value

def load32 (heap : Heap) (address : Nat) : UInt32 := Id.run do
  let mut value : UInt32 := 0
  for i in [0:4] do
    value := value ||| ((byteAt heap (address+i)).toUInt32 <<< UInt32.ofNat (8*i))
  return value

-- Source: src/support/hashing.c:17-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- uint32_t int32hash(uint32_t a)
-- {
--     a = (a+0x7ed55d16) + (a<<12);
--     a = (a^0xc761c23c) ^ (a>>19);
--     a = (a+0x165667b1) + (a<<5);
--     a = (a+0xd3a2646c) ^ (a<<9);
--     a = (a+0xfd7046c5) + (a<<3);
--     a = (a^0xb55a4f09) ^ (a>>16);
--     return a;
-- }
-- /Source
def int32hash (a : UInt32) : UInt32 := Id.run do
  let mut a := a
  a := (a + (0x7ed55d16 : UInt32)) + (a <<< 12)
  a := (a ^^^ (0xc761c23c : UInt32)) ^^^ (a >>> 19)
  a := (a + (0x165667b1 : UInt32)) + (a <<< 5)
  a := (a + (0xd3a2646c : UInt32)) ^^^ (a <<< 9)
  a := (a + (0xfd7046c5 : UInt32)) + (a <<< 3)
  return (a ^^^ (0xb55a4f09 : UInt32)) ^^^ (a >>> 16)

-- Source: src/support/hashing.c:28-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- uint64_t int64hash(uint64_t key)
-- {
--     key = (~key) + (key << 21);            // key = (key << 21) - key - 1;
--     key =   key  ^ (key >> 24);
--     key = (key + (key << 3)) + (key << 8); // key * 265
--     key =  key ^ (key >> 14);
--     key = (key + (key << 2)) + (key << 4); // key * 21
--     key =  key ^ (key >> 28);
--     key =  key + (key << 31);
--     return key;
-- }
-- /Source
def int64hash (key : UInt64) : UInt64 := Id.run do
  let mut key := (~~~key) + (key <<< 21)
  key := key ^^^ (key >>> 24)
  key := (key + (key <<< 3)) + (key <<< 8)
  key := key ^^^ (key >>> 14)
  key := (key + (key <<< 2)) + (key <<< 4)
  key := key ^^^ (key >>> 28)
  return key + (key <<< 31)

-- Source: src/support/hashing.c:40-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- uint32_t int64to32hash(uint64_t key)
-- {
--     key = (~key) + (key << 18); // key = (key << 18) - key - 1;
--     key =   key  ^ (key >> 31);
--     key = key * 21;             // key = (key + (key << 2)) + (key << 4);
--     key = key ^ (key >> 11);
--     key = key + (key << 6);
--     key = key ^ (key >> 22);
--     return (uint32_t)key;
-- }
-- /Source
def int64to32hash (key : UInt64) : UInt32 := Id.run do
  let mut key := (~~~key) + (key <<< 18)
  key := key ^^^ (key >>> 31)
  key := key * 21
  key := key ^^^ (key >>> 11)
  key := key + (key <<< 6)
  key := key ^^^ (key >>> 22)
  return key.toUInt32

-- Source: src/support/hashing.h:17-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #ifdef _P64
-- #define inthash int64hash
-- #else
-- #define inthash int32hash
-- #endif
-- JL_DLLEXPORT uint64_t memhash(const char *buf, size_t n) JL_NOTSAFEPOINT;
-- JL_DLLEXPORT uint64_t memhash_seed(const char *buf, size_t n, uint32_t seed) JL_NOTSAFEPOINT;
-- JL_DLLEXPORT uint32_t memhash32(const char *buf, size_t n) JL_NOTSAFEPOINT;
-- JL_DLLEXPORT uint32_t memhash32_seed(const char *buf, size_t n, uint32_t seed) JL_NOTSAFEPOINT;
-- 
-- #ifdef _P64
-- STATIC_INLINE uint64_t bitmix(uint64_t a, uint64_t b) JL_NOTSAFEPOINT
-- {
--     return int64hash(a^bswap_64(b));
-- }
-- #else
-- STATIC_INLINE uint32_t bitmix(uint32_t a, uint32_t b) JL_NOTSAFEPOINT
-- {
--     return int64to32hash((((uint64_t)a) << 32) | (uint64_t)b);
-- }
-- #endif
-- #define bitmix(a, b) (bitmix)((uintptr_t)(a), (uintptr_t)(b))
-- /Source
def inthash (key : UInt64) : UInt64 := int64hash key

def bswap64 (value : UInt64) : UInt64 := Id.run do
  let mut out : UInt64 := 0
  for i in [0:8] do
    out := (out <<< 8) ||| ((value >>> UInt64.ofNat (8*i)) &&& 0xff)
  return out

def bitmix (a b : UInt64) : UInt64 := int64hash (a ^^^ bswap64 b)

-- Source: src/support/MurmurHash3.c:21-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- static inline uint64_t rotl64 ( uint64_t x, int8_t r )
-- {
--   return (x << r) | (x >> (64 - r));
-- }
-- /Source
def rotl64 (x : UInt64) (r : UInt64) : UInt64 := (x <<< r) ||| (x >>> (64-r))

-- Source: src/support/MurmurHash3.c:47-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- FORCE_INLINE uint64_t fmix64 ( uint64_t k )
-- {
--   k ^= k >> 33;
--   k *= BIG_CONSTANT(0xff51afd7ed558ccd);
--   k ^= k >> 33;
--   k *= BIG_CONSTANT(0xc4ceb9fe1a85ec53);
--   k ^= k >> 33;
-- 
--   return k;
-- }
-- /Source
def fmix64 (k : UInt64) : UInt64 := Id.run do
  let mut k := k ^^^ (k >>> 33)
  k := k * 0xff51afd7ed558ccd
  k := k ^^^ (k >>> 33)
  k := k * 0xc4ceb9fe1a85ec53
  return k ^^^ (k >>> 33)

-- Source: src/support/MurmurHash3.c:220-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- void MurmurHash3_x64_128 ( const void * key, const size_t len,
--                            const uint32_t seed, void * out )
-- {
--   const uint8_t * data = (const uint8_t*)key;
--   const size_t nblocks = len / 16;
-- 
--   uint64_t h1 = seed;
--   uint64_t h2 = seed;
-- 
--   uint64_t c1 = BIG_CONSTANT(0x87c37b91114253d5);
--   uint64_t c2 = BIG_CONSTANT(0x4cf5ad432745937f);
-- 
--   //----------
--   // body
-- 
--   for(size_t i = 0; i < nblocks; i++)
--   {
--     uint64_t k1 = jl_load_unaligned_i64(data + sizeof(uint64_t)*(i*2 + 0));
--     uint64_t k2 = jl_load_unaligned_i64(data + sizeof(uint64_t)*(i*2 + 1));
-- 
--     k1 *= c1; k1  = ROTL64(k1,31); k1 *= c2; h1 ^= k1;
-- 
--     h1 = ROTL64(h1,27); h1 += h2; h1 = h1*5+0x52dce729;
-- 
--     k2 *= c2; k2  = ROTL64(k2,33); k2 *= c1; h2 ^= k2;
-- 
--     h2 = ROTL64(h2,31); h2 += h1; h2 = h2*5+0x38495ab5;
--   }
-- 
--   //----------
--   // tail
-- 
--   const uint8_t * tail = (const uint8_t*)(data + nblocks*16);
-- 
--   uint64_t k1 = 0;
--   uint64_t k2 = 0;
-- 
--   switch(len & 15)
--   {
--   case 15: k2 ^= ((uint64_t)(tail[14])) << 48; JL_FALLTHROUGH;
--   case 14: k2 ^= ((uint64_t)(tail[13])) << 40; JL_FALLTHROUGH;
--   case 13: k2 ^= ((uint64_t)(tail[12])) << 32; JL_FALLTHROUGH;
--   case 12: k2 ^= ((uint64_t)(tail[11])) << 24; JL_FALLTHROUGH;
--   case 11: k2 ^= ((uint64_t)(tail[10])) << 16; JL_FALLTHROUGH;
--   case 10: k2 ^= ((uint64_t)(tail[ 9])) << 8; JL_FALLTHROUGH;
--   case  9: k2 ^= ((uint64_t)(tail[ 8])) << 0;
--            k2 *= c2; k2  = ROTL64(k2,33); k2 *= c1; h2 ^= k2;
--            JL_FALLTHROUGH;
-- 
--   case  8: k1 ^= ((uint64_t)(tail[ 7])) << 56; JL_FALLTHROUGH;
--   case  7: k1 ^= ((uint64_t)(tail[ 6])) << 48; JL_FALLTHROUGH;
--   case  6: k1 ^= ((uint64_t)(tail[ 5])) << 40; JL_FALLTHROUGH;
--   case  5: k1 ^= ((uint64_t)(tail[ 4])) << 32; JL_FALLTHROUGH;
--   case  4: k1 ^= ((uint64_t)(tail[ 3])) << 24; JL_FALLTHROUGH;
--   case  3: k1 ^= ((uint64_t)(tail[ 2])) << 16; JL_FALLTHROUGH;
--   case  2: k1 ^= ((uint64_t)(tail[ 1])) << 8; JL_FALLTHROUGH;
--   case  1: k1 ^= ((uint64_t)(tail[ 0])) << 0;
--            k1 *= c1; k1  = ROTL64(k1,31); k1 *= c2; h1 ^= k1;
--   };
-- 
--   //----------
--   // finalization
-- 
--   h1 ^= len; h2 ^= len;
-- 
--   h1 += h2;
--   h2 += h1;
-- 
--   h1 = fmix64(h1);
--   h2 = fmix64(h2);
-- 
--   h1 += h2;
--   h2 += h1;
-- 
--   ((uint64_t*)out)[0] = h1;
--   ((uint64_t*)out)[1] = h2;
-- }
-- /Source
def MurmurHash3_x64_128 (heap : Heap) (address length : Nat) (seed : UInt32) : UInt64 × UInt64 := Id.run do
  let nblocks := length / 16
  let mut h1 := seed.toUInt64
  let mut h2 := seed.toUInt64
  let c1 : UInt64 := 0x87c37b91114253d5
  let c2 : UInt64 := 0x4cf5ad432745937f
  for i in [0:nblocks] do
    let mut k1 := load64 heap (address + 16*i)
    let mut k2 := load64 heap (address + 16*i + 8)
    k1 := k1 * c1
    k1 := rotl64 k1 31
    k1 := k1 * c2
    h1 := h1 ^^^ k1
    h1 := rotl64 h1 27
    h1 := h1 + h2
    h1 := h1*5 + 0x52dce729
    k2 := k2 * c2
    k2 := rotl64 k2 33
    k2 := k2 * c1
    h2 := h2 ^^^ k2
    h2 := rotl64 h2 31
    h2 := h2 + h1
    h2 := h2*5 + 0x38495ab5
  let tail := address + nblocks*16
  let remaining := length % 16
  let mut k1 : UInt64 := 0
  let mut k2 : UInt64 := 0
  for i in [0:min remaining 8] do
    k1 := k1 ^^^ ((byteAt heap (tail+i)).toUInt64 <<< UInt64.ofNat (8*i))
  if 8 < remaining then
    for i in [8:remaining] do
      k2 := k2 ^^^ ((byteAt heap (tail+i)).toUInt64 <<< UInt64.ofNat (8*(i-8)))
    k2 := k2*c2
    k2 := rotl64 k2 33
    k2 := k2*c1
    h2 := h2 ^^^ k2
  if 0 < remaining then
    k1 := k1*c1
    k1 := rotl64 k1 31
    k1 := k1*c2
    h1 := h1 ^^^ k1
  h1 := h1 ^^^ UInt64.ofNat length
  h2 := h2 ^^^ UInt64.ofNat length
  h1 := h1+h2
  h2 := h2+h1
  h1 := fmix64 h1
  h2 := fmix64 h2
  h1 := h1+h2
  h2 := h2+h1
  return (h1,h2)

-- Source: src/support/hashing.c:53-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #define _MHASH_SEED_ 0xcafe8881
-- 
-- uint64_t memhash(const char *buf, size_t n)
-- {
--     uint64_t out[2];
-- 
--     // TODO: expose 128-bit hash
-- #ifdef _P64
--     MurmurHash3_x64_128(buf, n, _MHASH_SEED_, out);
-- #else
--     MurmurHash3_x86_128(buf, n, _MHASH_SEED_, out);
-- #endif
--     return out[1];
-- }
-- 
-- uint64_t memhash_seed(const char *buf, size_t n, uint32_t seed)
-- {
--     uint64_t out[2];
-- 
--     // TODO: expose 128-bit hash
-- #ifdef _P64
--     MurmurHash3_x64_128(buf, n, seed, out);
-- #else
--     MurmurHash3_x86_128(buf, n, seed, out);
-- #endif
--     return out[1];
-- }
-- /Source
def memhash (heap : Heap) (address length : Nat) : UInt64 :=
  (MurmurHash3_x64_128 heap address length 0xcafe8881).2

def memhash_seed (heap : Heap) (address length : Nat) (seed : UInt32) : UInt64 :=
  (MurmurHash3_x64_128 heap address length seed).2

end JuliaLean.src.support.hashing_c
