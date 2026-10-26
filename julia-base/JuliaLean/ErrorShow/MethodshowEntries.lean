import JuliaLean.Registry.Types
import JuliaLean.ErrorShow.MethodshowFaithful

namespace JuliaLean.ErrorShow.MethodshowEntries

open JuliaLean.Registry
open JuliaLean.ErrorShow.MethodshowFaithful

def entries : List Entry := [
  { id := "errorshow-methodshow-l6", juliaFile := "base/methodshow.jl", juliaFns := ["strip_gensym"]
    statement := "strip_gensym removes self and unused names, strips generated suffixes, and preserves ordinary symbols for every input."
    source := "base/methodshow.jl:6-11", status := .proven, prop := ``StripGensymExact, thm := some ``stripGensymExact },
  { id := "errorshow-methodshow-l13", juliaFile := "base/methodshow.jl", juliaFns := ["argtype_decl"]
    statement := "argtype_decl follows every ordinary, Any, unbounded Vararg, and fixed Vararg branch for all names and types."
    source := "base/methodshow.jl:13-47", status := .proven, prop := ``ArgtypeDeclExact, thm := some ``argtypeDeclExact },
  { id := "errorshow-methodshow-l49", juliaFile := "base/methodshow.jl", juliaFns := ["method_argnames"]
    statement := "method_argnames returns an empty runtime list unchanged or its first nargs names."
    source := "base/methodshow.jl:49-53", status := .proven, prop := ``MethodArgnamesExact, thm := some ``methodArgnamesExact },
  { id := "errorshow-methodshow-l55", juliaFile := "base/methodshow.jl", juliaFns := ["arg_decl_parts"]
    statement := "arg_decl_parts unwraps type variables and either maps all argument declarations or emits empty declarations when names are unavailable."
    source := "base/methodshow.jl:55-77", status := .proven, prop := ``ArgDeclPartsExact, thm := some ``argDeclPartsExact },
  { id := "errorshow-methodshow-l80", juliaFile := "base/methodshow.jl", juliaFns := ["kwarg_decl"]
    statement := "kwarg_decl rejects ineligible or absent sorters, filters hidden slots, moves the splat last, and uses the empty-splat marker."
    source := "base/methodshow.jl:80-123", status := .proven, prop := ``KwargDeclExact, thm := some ``kwargDeclExact },
  { id := "errorshow-methodshow-l125", juliaFile := "base/methodshow.jl", juliaFns := ["show_method_params"]
    statement := "show_method_params emits no suffix, one bare where parameter, or a braced comma-separated list for every input."
    source := "base/methodshow.jl:125-143", status := .proven, prop := ``ShowMethodParamsExact, thm := some ``showMethodParamsExact },
  { id := "errorshow-methodshow-l152", juliaFile := "base/methodshow.jl", juliaFns := ["fixup_stdlib_path"]
    statement := "fixup_stdlib_path applies the compiler-source replacement first, then the build-stdlib replacement, and otherwise preserves the path."
    source := "base/methodshow.jl:152-170", status := .proven, prop := ``FixupStdlibPathExact, thm := some ``fixupStdlibPathExact },
  { id := "errorshow-methodshow-l173", juliaFile := "base/methodshow.jl", juliaFns := ["updated_methodloc"]
    statement := "updated_methodloc uses a successful callback location and otherwise retains the method's original location."
    source := "base/methodshow.jl:173-183", status := .proven, prop := ``UpdatedMethodlocExact, thm := some ``updatedMethodlocExact },
  { id := "errorshow-methodshow-l185", juliaFile := "base/methodshow.jl", juliaFns := ["functionloc(::MethodInstance)"]
    statement := "MethodInstance functionloc delegates to the definition Method's checked location."
    source := "base/methodshow.jl:185", status := .proven, prop := ``FunctionlocMethodInstanceExact, thm := some ``functionlocMethodInstanceExact },
  { id := "errorshow-methodshow-l192", juliaFile := "base/methodshow.jl", juliaFns := ["functionloc(::Method)"]
    statement := "Method functionloc returns a positive updated location and errors for every nonpositive line."
    source := "base/methodshow.jl:192-198", status := .proven, prop := ``FunctionlocMethodExact, thm := some ``functionlocMethodExact },
  { id := "errorshow-methodshow-l205", juliaFile := "base/methodshow.jl", juliaFns := ["functionloc(f,types)"]
    statement := "Function-and-types functionloc delegates from which to the selected Method's checked location."
    source := "base/methodshow.jl:205", status := .proven, prop := ``FunctionlocFunctionTypesExact, thm := some ``functionlocFunctionTypesExact },
  { id := "errorshow-methodshow-l206", juliaFile := "base/methodshow.jl", juliaFns := ["functionloc(argtypes)"]
    statement := "Argument-tuple functionloc delegates from which to the selected Method's checked location."
    source := "base/methodshow.jl:206", status := .proven, prop := ``FunctionlocArgtypesExact, thm := some ``functionlocArgtypesExact },
  { id := "errorshow-methodshow-l208", juliaFile := "base/methodshow.jl", juliaFns := ["functionloc(f)"]
    statement := "Single-argument functionloc distinguishes no definitions, a unique method, multiple methods, and a noncallable object for every method list."
    source := "base/methodshow.jl:208-221", status := .proven, prop := ``FunctionlocSingleExact, thm := some ``functionlocSingleExact },
  { id := "errorshow-methodshow-l223", juliaFile := "base/methodshow.jl", juliaFns := ["sym_to_string"]
    statement := "sym_to_string preserves the ellipsis symbol, escapes a trailing-dot base before restoring dots, and otherwise uses show_sym."
    source := "base/methodshow.jl:223-233", status := .proven, prop := ``SymToStringExact, thm := some ``symToStringExact },
  { id := "errorshow-methodshow-l236", juliaFile := "base/methodshow.jl", juliaFns := ["show(::Method)"]
    statement := "Two-argument Method show sets compact=true and delegates to show_method with the same method and keywords."
    source := "base/methodshow.jl:236", status := .proven, prop := ``ShowMethodCompactFaithfulExact, thm := some ``showMethodCompactFaithfulExact },
  { id := "errorshow-methodshow-l238", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MIME\"text/plain\",::Method)"]
    statement := "Plain-text Method show delegates to show_method without forcing compact output."
    source := "base/methodshow.jl:238", status := .proven, prop := ``ShowMethodPlainFaithfulExact, thm := some ``showMethodPlainFaithfulExact },
  { id := "errorshow-methodshow-l240", juliaFile := "base/methodshow.jl", juliaFns := ["show_method"]
    statement := "show_method emits the positional declarations, keywords, where parameters, and conditional compact or multiline location in source order."
    source := "base/methodshow.jl:240-285", status := .proven, prop := ``ShowMethodExact, thm := some ``showMethodExact },
  { id := "errorshow-methodshow-l287", juliaFile := "base/methodshow.jl", juliaFns := ["show_method_list_header"]
    statement := "Method-list headers select singular or plural, callable kind, name, module, and nonempty colon exactly."
    source := "base/methodshow.jl:287-317", status := .proven, prop := ``MethodListHeaderExact, thm := some ``methodListHeaderExact },
  { id := "errorshow-methodshow-l320", juliaFile := "base/methodshow.jl", juliaFns := ["_modulecolor"]
    statement := "The active _modulecolor body returns nothing for every Method."
    source := "base/methodshow.jl:320-337", status := .proven, prop := ``ModuleColorExact, thm := some ``moduleColorExact },
  { id := "errorshow-methodshow-l339", juliaFile := "base/methodshow.jl", juliaFns := ["show_method_table"]
    statement := "show_method_table applies its optional header, numbered maximum, and exact omitted-method footer for every method list."
    source := "base/methodshow.jl:339-385", status := .proven, prop := ``ShowMethodTableExact, thm := some ``showMethodTableExact },
  { id := "errorshow-methodshow-l387", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MethodList)"]
    statement := "Two-argument MethodList show delegates exactly to show_method_table."
    source := "base/methodshow.jl:387", status := .proven, prop := ``ShowMethodListExact, thm := some ``showMethodListExact },
  { id := "errorshow-methodshow-l388", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MIME\"text/plain\",::MethodList)"]
    statement := "Plain-text MethodList show delegates exactly to show_method_table."
    source := "base/methodshow.jl:388", status := .proven, prop := ``ShowMethodListPlainExact, thm := some ``showMethodListPlainExact },
  { id := "errorshow-methodshow-l389", juliaFile := "base/methodshow.jl", juliaFns := ["show(::Core.MethodTable)"]
    statement := "Core.MethodTable show emits its module, name, method count, and fixed description exactly."
    source := "base/methodshow.jl:389", status := .proven, prop := ``ShowCoreMethodTableExact, thm := some ``showCoreMethodTableExact },
  { id := "errorshow-methodshow-l391", juliaFile := "base/methodshow.jl", juliaFns := ["inbase"]
    statement := "inbase walks parent modules and returns true exactly when the chain reaches Base."
    source := "base/methodshow.jl:391-398", status := .proven, prop := ``InBaseExact, thm := some ``inBaseExact },
  { id := "errorshow-methodshow-l399", juliaFile := "base/methodshow.jl", juliaFns := ["fileurl"]
    statement := "fileurl returns an empty string for an unresolved file and a file URL for a resolved path."
    source := "base/methodshow.jl:399", status := .proven, prop := ``FileUrlExact, thm := some ``fileUrlExact },
  { id := "errorshow-methodshow-l401", juliaFile := "base/methodshow.jl", juliaFns := ["url(::Method)"]
    statement := "Method URL selection follows invalid, tagged Base, committed Base, package repository, and local-file branches for every method location."
    source := "base/methodshow.jl:401-441", status := .proven, prop := ``MethodUrlExact, thm := some ``methodUrlExact },
  { id := "errorshow-methodshow-l443", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MIME\"text/html\",::Method)"]
    statement := "HTML Method show emits the same signature, module, and linked or plain source location selected by url."
    source := "base/methodshow.jl:443-482", status := .proven, prop := ``ShowMethodHtmlExact, thm := some ``showMethodHtmlExact },
  { id := "errorshow-methodshow-l484", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MIME\"text/html\",::MethodList)"]
    statement := "HTML MethodList show wraps every method in one list item after the source header."
    source := "base/methodshow.jl:484-493", status := .proven, prop := ``ShowMethodListHtmlExact, thm := some ``showMethodListHtmlExact },
  { id := "errorshow-methodshow-l496", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MIME\"text/plain\",::AbstractVector{Method})"]
    statement := "Plain Method-vector show emits numbered methods separated by newlines or the summary for an empty vector."
    source := "base/methodshow.jl:496-512", status := .proven, prop := ``ShowMethodVectorPlainExact, thm := some ``showMethodVectorPlainExact },
  { id := "errorshow-methodshow-l514", juliaFile := "base/methodshow.jl", juliaFns := ["show(::MIME\"text/html\",::AbstractVector{Method})"]
    statement := "HTML Method-vector show emits the summary and one list item per method exactly when nonempty."
    source := "base/methodshow.jl:514-525", status := .proven, prop := ``ShowMethodVectorHtmlExact, thm := some ``showMethodVectorHtmlExact }
]

end JuliaLean.ErrorShow.MethodshowEntries
