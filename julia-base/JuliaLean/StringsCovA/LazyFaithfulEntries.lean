import JuliaLean.Registry.Types
import JuliaLean.StringsCovA.LazyFaithful

namespace JuliaLean.StringsCovA.LazyFaithfulRegistry

open JuliaLean.Registry

def entries : List Entry := [
  { id := "stringscova-lazy-private-ctor-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["_LazyString(parts, str)"]
    statement := "_LazyString converts the parts and cache fields in order, propagates conversion failures, and stores successful conversions with compact=false."
    source := "base/strings/lazy.jl:41", status := .proven
    prop := ``LazyFaithful.PrivateCtorProperty, thm := some ``LazyFaithful.privateCtor_proven },
  { id := "stringscova-lazy-ctor-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["LazyString(args...; compact::Bool=false)"]
    statement := "LazyString preserves every captured argument in its tuple, stores the Bool compact flag, and starts with an empty cache."
    source := "base/strings/lazy.jl:42", status := .proven
    prop := ``LazyFaithful.CtorProperty, thm := some ``LazyFaithful.ctor_proven },
  { id := "stringscova-lazy-macro-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["lazy_str(text, flags...)"]
    statement := "The lazy string macro rejects every flag tuple except () and (\"c\",), uses UTF-8 byte indices, passes the source filename to parseatom, escapes interpolations, and records the selected compact flag."
    source := "base/strings/lazy.jl:73-87", status := .proven
    prop := ``LazyFaithful.LazyStrProperty, thm := some ``LazyFaithful.lazyStr_proven },
  { id := "stringscova-lazy-string-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["String(::LazyString)"]
    statement := "String returns an acquired cache immediately, otherwise prints parts left-to-right with the selected compact and limit properties, preserves print failures and concurrent publication, and publishes one result with compare-exchange."
    source := "base/strings/lazy.jl:89-101", status := .proven
    prop := ``LazyFaithful.ToStringProperty, thm := some ``LazyFaithful.toString_proven },
  { id := "stringscova-lazy-hash-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["hash(::LazyString, ::UInt64)"]
    statement := "hash propagates materialization failures and otherwise calls String hash with the same seed."
    source := "base/strings/lazy.jl:103", status := .proven
    prop := ``LazyFaithful.HashProperty, thm := some ``LazyFaithful.hash_proven },
  { id := "stringscova-lazy-lastindex-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["lastindex(::LazyString)"]
    statement := "lastindex propagates materialization failures and otherwise returns the String last index."
    source := "base/strings/lazy.jl:104", status := .proven
    prop := ``LazyFaithful.LastindexProperty, thm := some ``LazyFaithful.lastindex_proven },
  { id := "stringscova-lazy-iterate0-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["iterate(::LazyString)"]
    statement := "Zero-state iteration propagates materialization failures and otherwise invokes String iteration."
    source := "base/strings/lazy.jl:105", status := .proven
    prop := ``LazyFaithful.Iterate0Property, thm := some ``LazyFaithful.iterate0_proven },
  { id := "stringscova-lazy-iterate-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["iterate(::LazyString, ::Integer)"]
    statement := "Stateful iteration preserves the Integer subtype and propagates materialization or delegated conversion failures."
    source := "base/strings/lazy.jl:106", status := .proven
    prop := ``LazyFaithful.IterateAtProperty, thm := some ``LazyFaithful.iterateAt_proven },
  { id := "stringscova-lazy-isequal-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["isequal(::LazyString, ::LazyString)"]
    statement := "isequal materializes left then right, stops at the first failure, and compares the resulting Strings."
    source := "base/strings/lazy.jl:107", status := .proven
    prop := ``LazyFaithful.IsequalProperty, thm := some ``LazyFaithful.isequal_proven },
  { id := "stringscova-lazy-eq-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["==(::LazyString, ::LazyString)"]
    statement := "LazyString equality materializes left then right, stops at the first failure, and applies String equality."
    source := "base/strings/lazy.jl:108", status := .proven
    prop := ``LazyFaithful.EqProperty, thm := some ``LazyFaithful.eq_proven },
  { id := "stringscova-lazy-ncodeunits-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["ncodeunits(::LazyString)"]
    statement := "ncodeunits propagates materialization failures and delegates to ncodeunits on the resulting String."
    source := "base/strings/lazy.jl:109", status := .proven
    prop := ``LazyFaithful.NcodeunitsProperty, thm := some ``LazyFaithful.ncodeunits_proven },
  { id := "stringscova-lazy-codeunit-type-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunit(::LazyString)"]
    statement := "codeunit(::LazyString) calls codeunit on the empty String and returns the UInt8 type."
    source := "base/strings/lazy.jl:110", status := .proven
    prop := ``LazyFaithful.CodeunitTypeProperty, thm := some ``LazyFaithful.codeunitType_proven },
  { id := "stringscova-lazy-codeunit-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunit(::LazyString, ::Integer)"]
    statement := "Indexed codeunit preserves the Integer subtype and propagates materialization or delegated conversion failures."
    source := "base/strings/lazy.jl:111", status := .proven
    prop := ``LazyFaithful.CodeunitAtProperty, thm := some ``LazyFaithful.codeunitAt_proven },
  { id := "stringscova-lazy-codeunits-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["codeunits(::LazyString)"]
    statement := "codeunits propagates materialization failures and constructs the String CodeUnits wrapper."
    source := "base/strings/lazy.jl:112", status := .proven
    prop := ``LazyFaithful.CodeunitsProperty, thm := some ``LazyFaithful.codeunits_proven },
  { id := "stringscova-lazy-isvalid-faithful", juliaFile := "base/strings/lazy.jl"
    juliaFns := ["isvalid(::LazyString, ::Integer)"]
    statement := "isvalid preserves the Integer subtype and propagates materialization or delegated conversion failures."
    source := "base/strings/lazy.jl:113", status := .proven
    prop := ``LazyFaithful.IsvalidProperty, thm := some ``LazyFaithful.isvalid_proven }
]

end JuliaLean.StringsCovA.LazyFaithfulRegistry
