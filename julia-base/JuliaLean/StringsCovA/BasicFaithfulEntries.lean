import JuliaLean.Registry.Types
import JuliaLean.StringsCovA.BasicPromises

namespace JuliaLean.StringsCovA.BasicFaithfulRegistry

open JuliaLean.Registry

private def rawEntries : List Entry := []

private def rewriteEntry (entry : Entry) : Entry :=
  if entry.id = "stringscova-basic-eltype-faithful" then
    { { entry with prop := ``BasicPromises.EltypeProperty } with
      thm := some ``BasicPromises.eltype_proven }
  else if entry.id = "stringscova-basic-firstindex-faithful" then
    { { entry with prop := ``BasicPromises.FirstindexProperty } with
      thm := some ``BasicPromises.firstindex_proven }
  else if entry.id = "stringscova-basic-getindex-faithful" then
    { { entry with prop := ``BasicPromises.GetindexProperty } with
      thm := some ``BasicPromises.getindex_proven }
  else if entry.id = "stringscova-basic-string-faithful" then
    { { entry with prop := ``BasicPromises.StringProperty } with
      thm := some ``BasicPromises.string_proven }
  else if entry.id = "stringscova-basic-convert-faithful" then
    { { entry with prop := ``BasicPromises.ConvertAllProperty } with
      thm := some ``BasicPromises.convertAll_proven }
  else if entry.id = "stringscova-basic-eachindex-faithful" then
    { { entry with prop := ``BasicPromises.EachIndexProperty } with
      thm := some ``BasicPromises.eachIndex_proven }
  else if entry.id = "stringscova-basic-isascii-char-faithful" then
    { { entry with prop := ``BasicPromises.IsasciiCharProperty } with
      thm := some ``BasicPromises.isasciiChar_proven }
  else if entry.id = "stringscova-basic-cu-indexstyle-faithful" then
    { { entry with prop := ``BasicPromises.CuIndexStyleProperty } with
      thm := some ``BasicPromises.cuIndexStyle_proven }
  else entry

def entries : List Entry := rawEntries.map rewriteEntry

end JuliaLean.StringsCovA.BasicFaithfulRegistry
