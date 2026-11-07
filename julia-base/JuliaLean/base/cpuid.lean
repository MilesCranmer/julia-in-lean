import JuliaLean.base.runtime_internals
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.io
import JuliaLean.base.lock

/-!
# Model of `base/cpuid.jl`

Typed CPU-feature and ISA models for Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
BitInteger values keep their Julia widths. C feature-table calls, byte buffers, set operations,
string operations, and the compiler's literal-argument representation are typed interfaces. The
macro result uses an explicit representation for its two source expansion forms.
-/

namespace JuliaLean.base.cpuid

open JuliaLean JuliaLean.base.int

abbrev M := JuliaLean.base.io.M
abbrev Error := JuliaLean.base.io.Error
abbrev I64 := JInt .i64
abbrev U8 := JInt .u8
abbrev I32 := JInt .i32
abbrev U32 := JInt .u32
abbrev U64 := JInt .u64

def int64 (value : Int) : I64 := JInt.lit .i64 value

def uint32 (value : Nat) : U32 := JInt.lit .u32 (Int.ofNat value)

structure SetOps (Set Element : Type) where
  empty : Set
  push : Set → Element → Set
  contains : Set → Element → Bool
  subset : Set → Set → Bool
  properSubset : Set → Set → Bool
  elements : Set → List Element

structure ByteBufferOps (World Buffer : Type) where
  allocate : I64 → M World Buffer
  length : Buffer → I64
  get : Buffer → I64 → M World U8

structure CFeatureOps (World Buffer Pointer : Type) where
  crossNbytes : String → M World U64
  crossLookup : String → String → Buffer → U64 → M World U64
  crossNumFeatures : String → M World U32
  crossFeatureName : String → U32 → M World (Option Pointer)
  crossFeatureBit : String → U32 → M World I32
  unsafeString : Pointer → M World String
  localNbytes : M World U64
  localLookup : String → Buffer → U64 → M World I32
  hostFeatures : Buffer → U64 → M World Unit
  testCpuFeature : U32 → M World Bool
  codegenFeatures : M World String
  targetFeatures : String → M World (Option String)

structure Ops (World Buffer Pointer FeatureSet SymbolSet : Type) where
  bytes : ByteBufferOps World Buffer
  c : CFeatureOps World Buffer Pointer
  featureSets : SetOps FeatureSet U32
  symbolSets : SetOps SymbolSet String
  hostArchitecture : String
  lowercase : String → M World String
  sortStrings : List String → M World (List String)
  uniqueSymbols : List String → M World (List String)
  sortSymbols : List String → M World (List String)
  splitComma : String → M World (List String)
  symbol : String → M World String
  joinStrings : String → List String → M World String
  showUInt32 : U32 → M World String

-- UNTRANSLATED
-- Source: base/cpuid.jl:1-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- module CPUID
-- 
-- export cpu_isa
-- /Source
-- Reason: Module imports and export registration are supplied by the Base load graph.

/--
Julia source: base/cpuid.jl:7-18 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ISA(features::Set{UInt32})

A structure which represents the Instruction Set Architecture (ISA) of a
computer.  It holds the `Set` of features of the CPU.

Feature bit indices come from the cpufeatures library's generated tables
(extracted from LLVM's TableGen data at build time).
"""
struct ISA
    features::Set{UInt32}
end
```
-/
structure ISA (Set Element : Type) where
  features : Set

abbrev ISA32 (Set : Type) := ISA Set U32

/--
Julia source: base/cpuid.jl:20-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:<=(a::ISA, b::ISA) = a.features <= b.features
```
-/
def leISA {Set : Type} (setOps : SetOps Set U32) (a b : ISA32 Set) : Bool :=
  setOps.subset a.features b.features

/--
Julia source: base/cpuid.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:<(a::ISA,  b::ISA) = a.features <  b.features
```
-/
def ltISA {Set : Type} (setOps : SetOps Set U32) (a b : ISA32 Set) : Bool :=
  setOps.properSubset a.features b.features

/--
Julia source: base/cpuid.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.isless(a::ISA,  b::ISA) = a < b
```
-/
def islessISA {Set : Type} (setOps : SetOps Set U32) (a b : ISA32 Set) : Bool :=
  ltISA setOps a b

-- UNTRANSLATED
-- Source: base/cpuid.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include(string(Base.BUILDROOT, "features_h.jl"))  # include($BUILDROOT/base/features_h.jl)
-- /Source
-- Reason: The included `features_h.jl` table is generated from LLVM TableGen during the Julia build.

abbrev BitNameMap := List (U32 × String)

def insertBitName : BitNameMap → U32 → String → BitNameMap
  | [], bit, name => [(bit, name)]
  | (key, oldName) :: rest, bit, name =>
      if key.val == bit.val then (key, name) :: rest
      else (key, oldName) :: insertBitName rest bit name

def lookupBitName : BitNameMap → U32 → Option String
  | [], _ => none
  | (key, name) :: rest, bit =>
      if key.val == bit.val then some name else lookupBitName rest bit

def allocateByteBuffer {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (nbytes : U64) : M World Buffer := do
  let length ← JuliaLean.base.io.liftJl (convert .i64 nbytes)
  ops.bytes.allocate length

/--
Julia source: base/cpuid.jl:26-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    _featurebytes_to_isa(buf::Vector{UInt8}) -> ISA

Convert a raw feature byte buffer (from cpufeatures) into an ISA.
"""
function _featurebytes_to_isa(buf::Vector{UInt8})
    features = Set{UInt32}()
    for byte_idx in 0:length(buf)-1
        b = buf[byte_idx + 1]
        b == 0 && continue
        for bit in 0:7
            if (b >> bit) & 1 != 0
                push!(features, UInt32(byte_idx * 8 + bit))
            end
        end
    end
    return ISA(features)
end
```
-/
def featureBytesToISA {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (buffer : Buffer) :
    M World (ISA32 FeatureSet) := do
  let length := ops.bytes.length buffer
  let features ← JuliaLean.base.io.whileLoop (fun (byteIndex, current) => do
    if byteIndex.val >= length.val then
      pure (.inl current)
    else
      let byte ← ops.bytes.get buffer (add_int byteIndex (int64 1))
      if byte.val == 0 then
        pure (.inr (add_int byteIndex (int64 1), current))
      else
        let updated ← JuliaLean.base.io.whileLoop (fun (remainingBits, set) => do
          match remainingBits with
          | [] => pure (.inl set)
          | bit :: rest => do
              let shift := JInt.lit .i64 (Int.ofNat bit)
              let shifted := lshr_int byte shift
              let masked := and_int shifted (JInt.lit .u8 1)
              if masked.val != 0 then
                let bitIndex := add_int (mul_int byteIndex (int64 8)) shift
                let feature ← JuliaLean.base.io.liftJl (convert .u32 bitIndex)
                pure (.inr (rest, ops.featureSets.push set feature))
              else
                pure (.inr (rest, set))) (List.range 8, current)
        pure (.inr (add_int byteIndex (int64 1), updated))) (int64 0, ops.featureSets.empty)
  pure ⟨features⟩

/--
Julia source: base/cpuid.jl:45-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    _cross_lookup_cpu(arch::String, name::String) -> ISA

Look up hardware features for a CPU on any architecture using the
cross-arch tables. Works regardless of host architecture.
Returns an empty ISA if the CPU or architecture is not found.
"""
function _cross_lookup_cpu(arch::String, name::String)
    nbytes = ccall(:jl_cpufeatures_cross_nbytes, Csize_t, (Cstring,), arch)
    nbytes == 0 && return ISA(Set{UInt32}())
    buf = Vector{UInt8}(undef, nbytes)
    written = ccall(:jl_cpufeatures_cross_lookup, Csize_t,
                    (Cstring, Cstring, Ptr{UInt8}, Csize_t),
                    arch, name, buf, nbytes)
    written == 0 && return ISA(Set{UInt32}())
    return _featurebytes_to_isa(buf)
end
```
-/
def crossLookupCPU {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (arch name : String) :
    M World (ISA32 FeatureSet) := do
  let nbytes ← ops.c.crossNbytes arch
  if nbytes.val == 0 then
    pure ⟨ops.featureSets.empty⟩
  else
    let buffer ← allocateByteBuffer ops nbytes
    let written ← ops.c.crossLookup arch name buffer nbytes
    if written.val == 0 then
      pure ⟨ops.featureSets.empty⟩
    else
      featureBytesToISA ops buffer

/--
Julia source: base/cpuid.jl:63-79 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    _build_bit_to_name(arch::String) -> Dict{UInt32, String}

Build a mapping from feature bit index to feature name for an architecture.
"""
function _build_bit_to_name(arch::String)
    nfeats = ccall(:jl_cpufeatures_cross_num_features, UInt32, (Cstring,), arch)
    result = Dict{UInt32, String}()
    for i in 0:nfeats-1
        name_ptr = ccall(:jl_cpufeatures_cross_feature_name, Cstring, (Cstring, UInt32), arch, i)
        name_ptr == C_NULL && continue
        bit = ccall(:jl_cpufeatures_cross_feature_bit, Cint, (Cstring, UInt32), arch, i)
        bit < 0 && continue
        result[UInt32(bit)] = unsafe_string(name_ptr)
    end
    return result
end
```
-/
def buildBitToName {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (arch : String) :
    M World BitNameMap := do
  let featureCount ← ops.c.crossNumFeatures arch
  JuliaLean.base.io.whileLoop (fun (index, result) => do
    if index >= featureCount.val.toNat then
      pure (.inl result)
    else
      let namePointer ← ops.c.crossFeatureName arch (uint32 index)
      match namePointer with
      | none => pure (.inr (index + 1, result))
      | some pointer => do
          let bit ← ops.c.crossFeatureBit arch (uint32 index)
          if bit.val < 0 then
            pure (.inr (index + 1, result))
          else
            let key ← JuliaLean.base.io.liftJl (convert .u32 bit)
            let name ← ops.c.unsafeString pointer
            pure (.inr (index + 1, insertBitName result key name))) (0, [])

/--
Julia source: base/cpuid.jl:81-97 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    feature_names(arch::String, cpu::String) -> Vector{String}
    feature_names(arch::String, isa::ISA) -> Vector{String}
    feature_names(isa::ISA) -> Vector{String}
    feature_names() -> Vector{String}

Return sorted hardware feature names. Can query by CPU name (on any
architecture) or by ISA. Defaults to the host architecture and CPU.

# Examples
```julia
feature_names()                           # host CPU features
feature_names("x86_64", "haswell")        # haswell's features
feature_names("aarch64", "cortex-x925")   # cross-arch query
```
"""
feature_names() = feature_names(string(Sys.ARCH), _host_isa())
````
-/
def featureNamesHost {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet)
    (hostIsa : Ops World Buffer Pointer FeatureSet SymbolSet → M World (ISA32 FeatureSet))
    (featureNames : Ops World Buffer Pointer FeatureSet SymbolSet → String → ISA32 FeatureSet → M World (List String)) :
    M World (List String) := do
  let arch := ops.hostArchitecture
  let isa ← hostIsa ops
  featureNames ops arch isa

/--
Julia source: base/cpuid.jl:98-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
feature_names(isa::ISA) = feature_names(string(Sys.ARCH), isa)
```
-/
def featureNamesISA {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet)
    (featureNames : Ops World Buffer Pointer FeatureSet SymbolSet → String → ISA32 FeatureSet → M World (List String))
    (isa : ISA32 FeatureSet) : M World (List String) :=
  featureNames ops ops.hostArchitecture isa

/--
Julia source: base/cpuid.jl:99-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function feature_names(arch::String, cpu::String)
    isa = _cross_lookup_cpu(arch, cpu)
    return feature_names(arch, isa)
end
```
-/
def featureNamesCPU {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet)
    (featureNames : Ops World Buffer Pointer FeatureSet SymbolSet → String → ISA32 FeatureSet → M World (List String))
    (arch cpu : String) : M World (List String) := do
  let isa ← crossLookupCPU ops arch cpu
  featureNames ops arch isa

/--
Julia source: base/cpuid.jl:103-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function feature_names(arch::String, isa::ISA)
    mapping = _build_bit_to_name(arch)
    return sort([get(mapping, bit, "unknown_$bit") for bit in isa.features])
end
```
-/
def featureNamesForISA {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (arch : String)
    (isa : ISA32 FeatureSet) : M World (List String) := do
  let mapping ← buildBitToName ops arch
  let names ← (ops.featureSets.elements isa.features).mapM (fun bit => do
    let shown ← ops.showUInt32 bit
    pure ((lookupBitName mapping bit).getD ("unknown_" ++ shown)))
  ops.sortStrings names

/--
Julia source: base/cpuid.jl:108-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    _lookup_cpu(name::String) -> ISA

Look up hardware features for the named CPU on the host architecture.
Returns an empty ISA if the CPU name is not found.
"""
function _lookup_cpu(name::String)
    nbytes = ccall(:jl_cpufeatures_nbytes, Csize_t, ())
    buf = Vector{UInt8}(undef, nbytes)
    ret = ccall(:jl_cpufeatures_lookup, Cint, (Cstring, Ptr{UInt8}, Csize_t), name, buf, nbytes)
    ret != 0 && return ISA(Set{UInt32}())
    return _featurebytes_to_isa(buf)
end
```
-/
def lookupCPU {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (name : String) :
    M World (ISA32 FeatureSet) := do
  let nbytes ← ops.c.localNbytes
  let buffer ← allocateByteBuffer ops nbytes
  let result ← ops.c.localLookup name buffer nbytes
  if result.val != 0 then pure ⟨ops.featureSets.empty⟩ else featureBytesToISA ops buffer

/--
Julia source: base/cpuid.jl:122-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    _host_isa() -> ISA

Get the hardware features of the host CPU from the cpufeatures library.
"""
function _host_isa()
    nbytes = ccall(:jl_cpufeatures_nbytes, Csize_t, ())
    buf = Vector{UInt8}(undef, nbytes)
    ccall(:jl_cpufeatures_host, Cvoid, (Ptr{UInt8}, Csize_t), buf, nbytes)
    return _featurebytes_to_isa(buf)
end
```
-/
def hostISA {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) : M World (ISA32 FeatureSet) := do
  let nbytes ← ops.c.localNbytes
  let buffer ← allocateByteBuffer ops nbytes
  let _ ← ops.c.hostFeatures buffer nbytes
  featureBytesToISA ops buffer

/--
Julia source: base/cpuid.jl:134-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Build an ISA list for a given architecture family.
# Uses cross-arch lookup so it works on any host.
# Entries with empty cpuname get an empty ISA (generic baseline).
function _make_isa_list(arch::String, entries::Vector{Pair{String,String}})
    result = Pair{String,ISA}[]
    for (label, cpuname) in entries
        if isempty(cpuname)
            push!(result, label => ISA(Set{UInt32}()))
        else
            push!(result, label => _cross_lookup_cpu(arch, cpuname))
        end
    end
    return result
end
```
-/
def makeISAList {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (arch : String)
    (entries : List (String × String)) : M World (List (String × ISA32 FeatureSet)) := do
  let result ← JuliaLean.base.io.whileLoop (fun (remaining, reverseResult) => do
    match remaining with
    | [] => pure (.inl reverseResult)
    | (label, cpuName) :: rest => do
        let isa ← if cpuName == "" then pure ⟨ops.featureSets.empty⟩
          else crossLookupCPU ops arch cpuName
        pure (.inr (rest, (label, isa) :: reverseResult))) (entries, [])
  pure result.reverse

/--
Julia source: base/cpuid.jl:149-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# ISA definitions per architecture family.
# CPU names are LLVM names in the cpufeatures database.
# Keep in sync with `arch_march_isa_mapping` in binaryplatforms.jl.
const ISAs_by_family = Dict(
    "i686" => _make_isa_list("x86_64", [
        "pentium4" => "",
        "prescott" => "prescott",
    ]),
    "x86_64" => _make_isa_list("x86_64", [
        "x86_64" => "",
        "core2" => "core2",
        "nehalem" => "nehalem",
        "sandybridge" => "sandybridge",
        "haswell" => "haswell",
        "skylake" => "skylake",
        "skylake_avx512" => "skylake-avx512",
    ]),
    "aarch64" => _make_isa_list("aarch64", [
        "armv8.0-a" => "",
        "armv8.1-a" => "cortex-a76",
        "armv8.2-a+crypto" => "cortex-a78",
        "a64fx" => "a64fx",
        "apple_m1" => "apple-a14",
    ]),
    "riscv64" => _make_isa_list("riscv64", [
        "riscv64" => "",
    ]),
)
```
-/
def isasByFamily {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) :
    M World (List (String × List (String × ISA32 FeatureSet))) := do
  let i686 ← makeISAList ops "x86_64" [("pentium4", ""), ("prescott", "prescott")]
  let x86_64 ← makeISAList ops "x86_64"
    [("x86_64", ""), ("core2", "core2"), ("nehalem", "nehalem"),
     ("sandybridge", "sandybridge"), ("haswell", "haswell"),
     ("skylake", "skylake"), ("skylake_avx512", "skylake-avx512")]
  let aarch64 ← makeISAList ops "aarch64"
    [("armv8.0-a", ""), ("armv8.1-a", "cortex-a76"),
     ("armv8.2-a+crypto", "cortex-a78"), ("a64fx", "a64fx"),
     ("apple_m1", "apple-a14")]
  let riscv64 ← makeISAList ops "riscv64" [("riscv64", "")]
  pure [("i686", i686), ("x86_64", x86_64), ("aarch64", aarch64), ("riscv64", riscv64)]

/--
Julia source: base/cpuid.jl:178-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Test a CPU feature exists on the currently-running host
test_cpu_feature(feature::UInt32) = ccall(:jl_test_cpu_feature, Bool, (UInt32,), feature)
```
-/
def testCPUFeature {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (feature : U32) : M World Bool :=
  ops.c.testCpuFeature feature

/--
Julia source: base/cpuid.jl:181-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Architectures accepted as the first argument of `@cpu_supports`.
const _CPU_SUPPORTS_ARCHES = (:x86_64, :aarch64, :riscv64)
```
-/
def cpuSupportsArchitectures : List String := ["x86_64", "aarch64", "riscv64"]

structure CodegenOnceSystem
    (World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source Token LockState TaskValue : Type) where
  runtime : JuliaLean.base.lock.Runtime Error World ReentrantLock Task Queue Lock Entry Slot Source
    Token LockState TaskValue
  operations : JuliaLean.base.lock.ProcessOnceOps Error World Once
    (Unit → M World SymbolSet) SymbolSet ReentrantLock

structure CodegenFeatureCache
    (World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source Token LockState TaskValue : Type) where
  system : CodegenOnceSystem World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source
    Token LockState TaskValue
  once : Once

/--
Julia source: base/cpuid.jl:184-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# LLVM features of the host architecture that codegen can enable.
const _codegen_feature_names = OncePerProcess{Set{Symbol}}() do
    names = ccall(:jl_cpu_codegen_features, Any, ())::String
    Set{Symbol}(Symbol(name) for name in eachsplit(names, ','; keepempty=false))
end
```
-/
def newCodegenFeatureCache {World Buffer Pointer FeatureSet SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source Token LockState TaskValue : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet)
    (system : CodegenOnceSystem World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source
      Token LockState TaskValue) : M World (CodegenFeatureCache World SymbolSet Once ReentrantLock Task Queue
        Lock Entry Slot Source Token LockState TaskValue) := do
  let once ← JuliaLean.base.lock.newOncePerProcess system.runtime system.operations (fun _ => do
    let names ← ops.c.codegenFeatures
    let pieces ← ops.splitComma names
    let features ← JuliaLean.base.io.whileLoop (fun (remaining, set) => do
      match remaining with
      | [] => pure (.inl set)
      | name :: rest => do
          let symbol ← ops.symbol name
          pure (.inr (rest, ops.symbolSets.push set symbol))) (pieces, ops.symbolSets.empty)
    pure features)
  pure ⟨system, once⟩

def codegenFeatureNames {World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source Token LockState TaskValue : Type}
    (cache : CodegenFeatureCache World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source
      Token LockState TaskValue) : M World SymbolSet :=
  JuliaLean.base.lock.oncePerProcess cache.system.runtime cache.system.operations cache.once

/--
Julia source: base/cpuid.jl:190-196 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Features a multiversioning clone targeting CPU `name` is compiled with, or
# `nothing` if `name` is not a known CPU.
function _cpu_model_features(name::String)
    result = ccall(:jl_cpu_target_features, Any, (Cstring,), name)
    result === nothing && return nothing
    return Symbol[Symbol(f) for f in eachsplit(result::String, ','; keepempty=false)]
end
```
-/
def cpuModelFeatures {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) (name : String) :
    M World (Option (List String)) := do
  match ← ops.c.targetFeatures name with
  | none => pure none
  | some value => do
      let names ← ops.splitComma value
      let symbols ← names.mapM ops.symbol
      pure (some symbols)

inductive CpuSupportsArg (Value : Type) where
  | symbol (name : String)
  | quoteNode (value : CpuSupportsArg Value)
  | string (value : String)
  | other (value : Value)

/--
Julia source: base/cpuid.jl:198-203 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cpu_supports_name(x)
    x isa Symbol && return x
    x isa QuoteNode && x.value isa Symbol && return x.value::Symbol
    x isa String && return Symbol(x)
    error("@cpu_supports: expected a literal name (Symbol or String), got $(repr(x))")
end
```
-/
def cpuSupportsName {World Value Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet)
    (reprArgument : CpuSupportsArg Value → M World String)
    (value : CpuSupportsArg Value) : M World String := do
  match value with
  | .symbol name => pure name
  | .quoteNode (.symbol name) => pure name
  | .string name => ops.symbol name
  | invalid => do
      let rendered ← reprArgument invalid
      throw (.errorException ("@cpu_supports: expected a literal name (Symbol or String), got " ++ rendered))

inductive CpuSupportsExpansion where
  | literalFalse
  | intrinsicCpuSupports (features : String)
  deriving DecidableEq, Repr

/--
Julia source: base/cpuid.jl:205-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    Base.@cpu_supports arch name1 [name2 ...] -> Bool

Compile-time CPU capability query, ANDed across names. `arch` is a literal
architecture name (`x86_64`, `aarch64` (or `arm64`), or `riscv64`) that scopes
the query; each `nameN` is a literal naming an LLVM target feature (`avx2`,
`fma`, `"sse4.2"`) or a CPU model (`haswell`, `znver4`, `"x86-64-v3"`).
Strings are required for names that contain `-` or `.`. CPU-model names
expand to the hardware features a clone targeting that CPU is compiled with. Names
that are not hardware features usable by Julia code (tuning hints, privileged
instructions) or CPU models error at macro-expansion time.

The answer is what Julia's code generation enables for the target, which can
be less than what the hardware supports: features Julia deliberately disables
(for example `rdrnd`, `rdseed`, `xsaveopt` and, on x86, `avx512bf16` along
with the AVX10 features that imply it) test false.

On a host whose arch doesn't match the prefix, the call expands to `false`
at macro-expansion time — letting you write cross-arch dispatch in a single
source file.

Mirrors GCC/Clang's `__builtin_cpu_supports`, folded against the function's
effective `target-features` / `target-cpu` (so multiversioning clones get
per-clone answers automatically).

# Patterns

Dispatch — the dead branch is eliminated:
```julia
function dot(xs, ys)
    if Base.@cpu_supports x86_64 avx2 fma
        ...  # 256-bit path
    elseif Base.@cpu_supports aarch64 neon
        ...  # NEON path
    else
        ...  # fallback
    end
end
```

Specialized kernel guard — the body after the assert is removed on clones
that don't satisfy it, so target-specific intrinsics inside never reach
backend lowering:
```julia
function kernel_avx512(xs)
    @assert Base.@cpu_supports x86_64 avx512f
    ...
end
```

!!! compat "Julia 1.14"
    This macro requires at least Julia 1.14.
"""
macro cpu_supports(args...)
    length(args) >= 2 ||
        error("@cpu_supports: usage is `@cpu_supports <arch> <name>...` where <arch> is one of $(join(_CPU_SUPPORTS_ARCHES, ", "))")
    arch_arg = _cpu_supports_name(args[1])
    arch = Symbol(normalize_arch(String(arch_arg)))
    arch in _CPU_SUPPORTS_ARCHES ||
        error("@cpu_supports: first argument must be one of $(join(_CPU_SUPPORTS_ARCHES, ", ")), got `$arch_arg`")
    names = map(_cpu_supports_name, args[2:end])
    # Only the host's feature and CPU tables are available to check names against.
    arch === Sys.ARCH || return false
    known = _codegen_feature_names()
    features = Symbol[]
    for name in names
        if name in known
            push!(features, name)
            continue
        end
        cpu_features = _cpu_model_features(String(name))
        cpu_features === nothing && error("@cpu_supports: `$name` is neither a hardware feature nor a CPU model of $arch")
        isempty(cpu_features) && error("@cpu_supports: CPU model `$name` has no features to test")
        append!(features, cpu_features)
    end
    # One query for all names, so even a large CPU model costs the inliner a single call.
    query = Symbol(join(sort!(unique!(features)), ','))
    return :(Core.Intrinsics.cpu_supports($(QuoteNode(query))))
end
````
-/
def cpuSupportsMacro
    {World Buffer Pointer FeatureSet SymbolSet MacroValue Once ReentrantLock Task Queue Lock Entry Slot
      Source Token LockState TaskValue : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet)
    (cache : CodegenFeatureCache World SymbolSet Once ReentrantLock Task Queue Lock Entry Slot Source
      Token LockState TaskValue)
    (reprArgument : CpuSupportsArg MacroValue → M World String)
    (normalize : Ops World Buffer Pointer FeatureSet SymbolSet → String → M World String)
    (args : List (CpuSupportsArg MacroValue)) : M World CpuSupportsExpansion := do
  match args with
  | [] | [_] => do
      let allowed ← ops.joinStrings ", " cpuSupportsArchitectures
      throw (.errorException ("@cpu_supports: usage is `@cpu_supports <arch> <name>...` where <arch> is one of " ++ allowed))
  | archInput :: firstName :: remainingNames => do
      let archArgument ← cpuSupportsName ops reprArgument archInput
      let arch ← normalize ops archArgument
      if !cpuSupportsArchitectures.contains arch then
        let allowed ← ops.joinStrings ", " cpuSupportsArchitectures
        throw (.errorException ("@cpu_supports: first argument must be one of " ++ allowed ++ ", got `" ++ archArgument ++ "`"))
      let names ← (firstName :: remainingNames).mapM (cpuSupportsName ops reprArgument)
      if arch != ops.hostArchitecture then return .literalFalse
      let known ← codegenFeatureNames cache
      let reverseFeatures ← JuliaLean.base.io.whileLoop (fun (remaining, collected) => do
        match remaining with
        | [] => pure (.inl collected)
        | name :: rest =>
            if ops.symbolSets.contains known name then
              pure (.inr (rest, name :: collected))
            else do
              match ← cpuModelFeatures ops name with
              | none => throw (.errorException ("@cpu_supports: `" ++ name ++ "` is neither a hardware feature nor a CPU model of " ++ arch))
              | some [] => throw (.errorException ("@cpu_supports: CPU model `" ++ name ++ "` has no features to test"))
              | some features => pure (.inr (rest, features.reverse ++ collected))) (names, [])
      let features := reverseFeatures.reverse
      let unique ← ops.uniqueSymbols features
      let sorted ← ops.sortSymbols unique
      pure (.intrinsicCpuSupports (← ops.joinStrings "," sorted))

/--
Julia source: base/cpuid.jl:285-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Normalize some variation in ARCH values (which typically come from `uname -m`)
function normalize_arch(arch::String)
    arch = lowercase(arch)
    if arch ∈ ("amd64",)
        arch = "x86_64"
    elseif arch ∈ ("i386", "i486", "i586")
        arch = "i686"
    elseif arch ∈ ("armv6",)
        arch = "armv6l"
    elseif arch ∈ ("arm", "armv7", "armv8", "armv8l")
        arch = "armv7l"
    elseif arch ∈ ("arm64",)
        arch = "aarch64"
    elseif arch ∈ ("ppc64le",)
        arch = "powerpc64le"
    end
    return arch
end
```
-/
def normalizeArch {World : Type}
    (lowercase : String → M World String) (arch : String) : M World String := do
  let mut arch ← lowercase arch
  if arch == "amd64" then
    arch := "x86_64"
  else if ["i386", "i486", "i586"].contains arch then
    arch := "i686"
  else if arch == "armv6" then
    arch := "armv6l"
  else if ["arm", "armv7", "armv8", "armv8l"].contains arch then
    arch := "armv7l"
  else if arch == "arm64" then
    arch := "aarch64"
  else if arch == "ppc64le" then
    arch := "powerpc64le"
  pure arch

/--
Julia source: base/cpuid.jl:304-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    cpu_isa()

Return the [`ISA`](@ref) (instruction set architecture) of the current CPU.
"""
function cpu_isa()
    return _host_isa()
end
```
-/
def cpuISA {World Buffer Pointer FeatureSet SymbolSet : Type}
    (ops : Ops World Buffer Pointer FeatureSet SymbolSet) : M World (ISA32 FeatureSet) :=
  hostISA ops

-- UNTRANSLATED
-- Source: base/cpuid.jl:313-313 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end # module CPUID
-- /Source
-- Reason: The closing Julia module marker is file structure supplied by the namespace boundary.


end JuliaLean.base.cpuid

section
namespace JuliaLean.RuntimeCov.CpuId

open JuliaLean.RuntimeCov

/-- `ISA(features::Set{UInt32})`, base/cpuid.jl:15-17: the feature bits,
modelled as a duplicate-free list. -/
structure ISA where
  features : List Nat
  deriving DecidableEq, Repr

/-- `a.features <= b.features` for sets: `issubset`. -/
def subset (a b : List Nat) : Bool := a.all (fun x => b.contains x)

/-- `Base.:<=(a::ISA, b::ISA)`, base/cpuid.jl:20. -/
def le (a b : ISA) : Bool := subset a.features b.features
/-- `Base.:<(a::ISA, b::ISA)`, base/cpuid.jl:21: `⊊` on sets. -/
def lt (a b : ISA) : Bool := subset a.features b.features && !subset b.features a.features
/-- `Base.isless(a::ISA, b::ISA)`, base/cpuid.jl:22. -/
def isless (a b : ISA) : Bool := lt a b

/-- The bits pushed for one byte `b` at byte index `i`, base/cpuid.jl:34-39. -/
def byteBits (i b : Nat) : List Nat :=
  if b = 0 then [] else
    (List.range 8).filterMap fun bit => if (b >>> bit) % 2 ≠ 0 then some (i * 8 + bit) else none

/-- `_featurebytes_to_isa(buf)`, base/cpuid.jl:31-43. -/
def featurebytesToIsa (buf : List Nat) : ISA :=
  ⟨(List.range buf.length).flatMap fun i => byteBits i (buf.getD i 0)⟩

/-- `_cross_lookup_cpu(arch, name)`, base/cpuid.jl:52-61: the library reports
the buffer size for `arch` and the bytes written with their buffer. -/
def crossLookupCpu (nbytes : Nat) (lookup : Nat × List Nat) : ISA :=
  if nbytes = 0 then ⟨[]⟩
  else if lookup.1 = 0 then ⟨[]⟩
  else featurebytesToIsa lookup.2

/-- `_build_bit_to_name(arch)`, base/cpuid.jl:68-79: for each feature index the
library returns a name pointer (`none` = `C_NULL`) and a bit (negative = skip);
later assignments to the same bit win. -/
def buildBitToName : List (Option String × Int) → List (Nat × String) → List (Nat × String)
  | [], acc => acc
  | (none, _) :: rest, acc => buildBitToName rest acc
  | (some nm, bit) :: rest, acc =>
    if bit < 0 then buildBitToName rest acc
    else buildBitToName rest ((bit.toNat, nm) :: acc.filter (fun p => p.1 ≠ bit.toNat))

/-- `get(mapping, bit, "unknown_$bit")`. -/
def nameOf (mapping : List (Nat × String)) (bit : Nat) : String :=
  match mapping.find? (fun p => p.1 = bit) with
  | some p => p.2
  | none => "unknown_" ++ toString bit

/-- `feature_names(arch, isa)`, base/cpuid.jl:103-106: names sorted. -/
def featureNamesIsa (entries : List (Option String × Int)) (isa : ISA) : List String :=
  (isa.features.map (nameOf (buildBitToName entries []))).mergeSort (fun a b => decide (a ≤ b))

/-- `feature_names(arch, cpu)`, base/cpuid.jl:99-102. -/
def featureNamesCpu (entries : List (Option String × Int)) (nbytes : Nat) (lookup : Nat × List Nat) :
    List String :=
  featureNamesIsa entries (crossLookupCpu nbytes lookup)

/-- `feature_names(isa)` and `feature_names()`, base/cpuid.jl:97-98: host
architecture (and host ISA). -/
def featureNamesHostIsa (hostEntries : List (Option String × Int)) (isa : ISA) : List String :=
  featureNamesIsa hostEntries isa
def featureNamesHost (hostEntries : List (Option String × Int)) (hostIsa : ISA) : List String :=
  featureNamesHostIsa hostEntries hostIsa

/-- `_lookup_cpu(name)`, base/cpuid.jl:114-120: nonzero return means not found. -/
def lookupCpu (ret : Int) (buf : List Nat) : ISA :=
  if ret ≠ 0 then ⟨[]⟩ else featurebytesToIsa buf

/-- `_host_isa()`, base/cpuid.jl:127-132, and `cpu_isa()`, lines 309-311. -/
def hostIsa (buf : List Nat) : ISA := featurebytesToIsa buf
def cpuIsa (buf : List Nat) : ISA := hostIsa buf

/-- `_make_isa_list(arch, entries)`, base/cpuid.jl:137-147, with the cross
lookup for each CPU name as an input. -/
def makeIsaList (cross : String → ISA) (entries : List (String × String)) : List (String × ISA) :=
  entries.map fun (label, cpu) => if cpu.isEmpty then (label, ⟨[]⟩) else (label, cross cpu)

/-- `test_cpu_feature(feature)`, base/cpuid.jl:179: the runtime's answer. -/
def testCpuFeature (runtime : Nat → Bool) (feature : Nat) : Bool := runtime feature

/-- `eachsplit(s, ','; keepempty=false)`. -/
def splitNonempty (s : String) : List String :=
  (s.splitOn ",").filter (fun t => !t.isEmpty)

/-- `_cpu_model_features(name)`, base/cpuid.jl:192-196. -/
def cpuModelFeatures (result : Option String) : Option (List String) :=
  result.map splitNonempty

/-- A macro argument of `@cpu_supports`. -/
inductive MacroArg where
  | sym (s : Sym)
  | quoteSym (s : Sym)
  | quoteOther
  | str (s : String)
  | other (reprText : String)

/-- `_cpu_supports_name(x)`, base/cpuid.jl:198-203. -/
def cpuSupportsName : MacroArg → Rt Sym
  | .sym s => .ok s
  | .quoteSym s => .ok s
  | .str s => .ok s
  | .quoteOther => .error (.errorException "@cpu_supports: expected a literal name")
  | .other r => .error (.errorException ("@cpu_supports: expected a literal name (Symbol or String), got " ++ r))

/-- `normalize_arch(arch)`, base/cpuid.jl:286-302, with Unicode `lowercase` as an input. -/
def normalizeArch (lower : String → String) (arch : String) : String :=
  let a := lower arch
  if a ∈ ["amd64"] then "x86_64"
  else if a ∈ ["i386", "i486", "i586"] then "i686"
  else if a ∈ ["armv6"] then "armv6l"
  else if a ∈ ["arm", "armv7", "armv8", "armv8l"] then "armv7l"
  else if a ∈ ["arm64"] then "aarch64"
  else if a ∈ ["ppc64le"] then "powerpc64le"
  else a

/-- `_CPU_SUPPORTS_ARCHES`, base/cpuid.jl:182. -/
def supportsArches : List Sym := ["x86_64", "aarch64", "riscv64"]

/-- The expansion of `@cpu_supports`. -/
inductive Expansion where
  | constFalse
  | query (q : List String)
  deriving DecidableEq, Repr

/-- Deduplicate keeping first occurrences (`unique!`). -/
def dedup : List String → List String
  | [] => []
  | x :: xs => x :: (dedup xs).filter (· ≠ x)

/-- Map `_cpu_supports_name` over arguments, stopping at the first error. -/
def mapNames : List MacroArg → Rt (List Sym)
  | [] => .ok []
  | a :: as => do let n ← cpuSupportsName a; let ns ← mapNames as; pure (n :: ns)

/-- Expand each name to features (`known` codegen features, else CPU-model features). -/
def expandFeatures (known : Sym → Bool) (model : Sym → Option (List String)) :
    List Sym → Rt (List String)
  | [] => .ok []
  | n :: ns =>
    if known n then do let r ← expandFeatures known model ns; pure (n :: r)
    else match model n with
      | none => .error (.errorException ("@cpu_supports: `" ++ n ++ "` is neither a hardware feature nor a CPU model"))
      | some [] => .error (.errorException ("@cpu_supports: CPU model `" ++ n ++ "` has no features to test"))
      | some fs => do let r ← expandFeatures known model ns; pure (fs ++ r)

/-- `@cpu_supports arch names...`, base/cpuid.jl:258-283. The query symbol is
the sorted, deduplicated feature list joined by commas; it is kept as the
sorted list. -/
def cpuSupports (lower : String → String) (hostArch : Sym) (known : Sym → Bool)
    (model : Sym → Option (List String)) (args : List MacroArg) : Rt Expansion :=
  match args with
  | [] | [_] => .error (.errorException "@cpu_supports: usage is `@cpu_supports <arch> <name>...`")
  | a0 :: rest => do
    let archArg ← cpuSupportsName a0
    let arch := normalizeArch lower archArg
    if arch ∉ supportsArches then
      .error (.errorException ("@cpu_supports: first argument must be one of x86_64, aarch64, riscv64, got `" ++ archArg ++ "`"))
    else do
      let names ← mapNames rest
      if arch ≠ hostArch then pure .constFalse
      else do
        let features ← expandFeatures known model names
        pure (.query ((dedup features).mergeSort (fun a b => decide (a ≤ b))))
end JuliaLean.RuntimeCov.CpuId
end
