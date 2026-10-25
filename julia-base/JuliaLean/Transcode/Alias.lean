import JuliaLean.Core

/-!
# `String(v::Vector{UInt8})` and arrays that share memory

A small heap model of `Memory{UInt8}` objects, `Vector{UInt8}` arrays and
`String` objects, enough to follow `String(v::Vector{UInt8})`
(`base/strings/string.jl:114-127`) and `jl_genericmemory_to_string`
(`src/genericmemory.c:189-215`) on master `bbfa0ce4150`.

* A `Memory` whose `how` is `JL_GENERICMEMORY_STRINGOWNED` stores the bytes of a
  `String` object (`owner`); this is what `Base.StringMemory(n) =
  unsafe_wrap(Memory{UInt8}, _string_n(n))` creates (`base/iobuffer.jl:167`),
  and what `StringVector(n)` and `take!(::IOBuffer)` return vectors over.
* A `String` object either lives in such a memory (its first `len` bytes) or
  owns a copy of its bytes.
* An operation that would throw (an out-of-bounds index) leaves the heap
  unchanged; the property below is about operations that succeed.
-/

namespace JuliaLean.Transcode

/-- `GC_MAX_SZCLASS = 2032 - sizeof(void*)` on 64-bit platforms (`src/julia_internal.h:675`). -/
def gcMaxSzclass : Nat := 2032 - 8

structure Mem where
  data : List UInt8
  /-- The owning String object when `how == JL_GENERICMEMORY_STRINGOWNED`. -/
  owner : Option Nat
  deriving DecidableEq, Repr

/-- A String object: its length, and the memory holding its bytes or its own copy. -/
structure Str where
  len : Nat
  mem : Option Nat
  own : List UInt8
  deriving DecidableEq, Repr

/-- A `Vector{UInt8}`: its memory, the offset of its first element in that memory, its length. -/
structure Vec where
  mem : Nat
  off : Nat
  len : Nat
  deriving DecidableEq, Repr

structure Heap where
  mems : List Mem
  strs : List Str
  vecs : List Vec
  /-- The Strings returned to the program by `String(v)`. -/
  visible : List Nat
  deriving DecidableEq, Repr

def Heap.empty : Heap := ⟨[], [], [], []⟩

/-- The bytes of String object `i`. -/
def Heap.content (h : Heap) (i : Nat) : Option (List UInt8) := do
  let s ← h.strs[i]?
  match s.mem with
  | none => pure s.own
  | some m => do let mm ← h.mems[m]?; pure (mm.data.take s.len)

inductive Op where
  /-- `v = Base.StringVector(n)`: a vector over a fresh string-owned memory. -/
  | stringVector (n : Nat)
  /-- `w = vec(reshape(v, 1, :))`: a new vector over the same memory as `v`. -/
  | share (v : Nat)
  /-- `v[i] = x`. -/
  | setindex (v i : Nat) (x : UInt8)
  /-- `resize!(v, n)` with `n ≤ length(v)`. -/
  | shrink (v n : Nat)
  /-- `String(v)`. -/
  | string (v : Nat)
  deriving DecidableEq, Repr

/-- A new String object owning a copy of `bs`, made visible. -/
def Heap.copyStr (h : Heap) (bs : List UInt8) : Heap × Nat :=
  ({ h with strs := h.strs ++ [⟨bs.length, none, bs⟩] }, h.strs.length)

/-- `jl_genericmemory_to_string(m, len)` for `len > 0`, `src/genericmemory.c:189-215`. -/
def Heap.memToString (h : Heap) (m len : Nat) : Heap × Nat :=
  match h.mems[m]? with
  | none => h.copyStr []
  | some mm =>
    let mlength := mm.data.length
    match mm.owner with
    | some o =>
      if decide (mlength + 8 + 1 ≤ gcMaxSzclass) = decide (len + 8 + 1 ≤ gcMaxSzclass) then
        -- `jl_string_data(o)[len] = '\0'; *(size_t*)o = len; return o;`
        let data := if len < mlength then mm.data.set len 0 else mm.data
        ({ h with mems := h.mems.set m { mm with data := data },
                  strs := h.strs.modify o fun s => { s with len := len } }, o)
      else h.copyStr (mm.data.take len)
    | none => h.copyStr (mm.data.take len)

/-- One operation; one that would throw changes nothing. -/
def Heap.step (h : Heap) : Op → Heap
  | .stringVector n =>
    let s := h.strs.length
    let m := h.mems.length
    { h with strs := h.strs ++ [⟨n, some m, []⟩], mems := h.mems ++ [⟨List.replicate n 0, some s⟩],
             vecs := h.vecs ++ [⟨m, 0, n⟩] }
  | .share v =>
    match h.vecs[v]? with
    | none => h
    | some vv => { h with vecs := h.vecs ++ [vv] }
  | .setindex v i x =>
    match h.vecs[v]? with
    | none => h
    | some vv =>
      if 1 ≤ i ∧ i ≤ vv.len then
        match h.mems[vv.mem]? with
        | none => h
        | some mm => { h with mems := h.mems.set vv.mem { mm with data := mm.data.set (vv.off + i - 1) x } }
      else h
  | .shrink v n =>
    match h.vecs[v]? with
    | none => h
    | some vv => if n ≤ vv.len then { h with vecs := h.vecs.set v { vv with len := n } } else h
  | .string v =>
    match h.vecs[v]? with
    | none => h
    | some vv =>
      -- `base/strings/string.jl:115-122`
      let (h', i) :=
        if vv.len = 0 then h.copyStr []
        else if vv.off = 0 then h.memToString vv.mem vv.len
        else match h.mems[vv.mem]? with
          | none => h.copyStr []
          | some mm => h.copyStr ((mm.data.drop vv.off).take vv.len)
      -- `setfield!(v, :size, (0,)); setfield!(v, :ref, memoryref(Memory{UInt8}()))`
      { h' with mems := h'.mems ++ [⟨[], none⟩],
                vecs := h'.vecs.set v ⟨h'.mems.length, 0, 0⟩,
                visible := h'.visible ++ [i] }

def Heap.run (h : Heap) (ops : List Op) : Heap := ops.foldl Heap.step h

/-- Strings are immutable (`base/strings/string.jl:85`): once `String(v)` has
returned a String, no later operation changes its bytes. -/
def StringVectorImmutable : Prop :=
  ∀ (p q : List Op) (i : Nat) (c : List UInt8), i ∈ (Heap.empty.run p).visible →
    (Heap.empty.run p).content i = some c → (Heap.empty.run (p ++ q)).content i = some c

/-- `v = StringVector(3); v .= "abc"; b = reshape(v, 1, 3); s = String(v)`. -/
def aliasProg : List Op :=
  [.stringVector 3, .setindex 0 1 0x61, .setindex 0 2 0x62, .setindex 0 3 0x63, .share 0, .string 0]

theorem stringVectorImmutable_refuted : ¬ StringVectorImmutable := by
  intro h
  -- `b[1] = UInt8('A')` changes `s` from "abc" to "Abc".
  have := h aliasProg [.setindex 1 1 0x41] 0 [0x61, 0x62, 0x63] (by decide) (by decide)
  revert this; decide

/-- `w = vec(reshape(v, 1, 3)); s1 = String(v); resize!(w, 1); s2 = String(w)` truncates `s1`. -/
theorem stringVector_truncate :
    (Heap.empty.run (aliasProg ++ [.shrink 1 1, .string 1])).content 0 = some [0x61] := by decide

end JuliaLean.Transcode
