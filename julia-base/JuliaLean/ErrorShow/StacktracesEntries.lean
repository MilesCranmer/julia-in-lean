import JuliaLean.Registry.Types
import JuliaLean.ErrorShow.StacktracesFaithful

namespace JuliaLean.ErrorShow.StacktracesEntries

open JuliaLean.Registry
open JuliaLean.ErrorShow.StacktracesFaithful

def entries : List Entry := [
  { id := "errorshow-stacktraces-l82", juliaFile := "base/stacktraces.jl", juliaFns := ["StackFrame(7 args)"]
    statement := "The seven-argument StackFrame constructor fills the new pc and debuginfo fields with zero and nothing for every input."
    source := "base/stacktraces.jl:82-83", status := .proven, prop := ``StackFrameSevenExact, thm := some ``stackFrameSevenExact },
  { id := "errorshow-stacktraces-l84", juliaFile := "base/stacktraces.jl", juliaFns := ["StackFrame(3 args)"]
    statement := "The three-argument StackFrame constructor converts names and fills every remaining field with its source default."
    source := "base/stacktraces.jl:84-85", status := .proven, prop := ``StackFrameThreeExact, thm := some ``stackFrameThreeExact },
  { id := "errorshow-stacktraces-l103", juliaFile := "base/stacktraces.jl", juliaFns := ["==(::StackFrame,::StackFrame)"]
    statement := "StackFrame equality compares exactly line, C origin, function, file, and inline status for every pair."
    source := "base/stacktraces.jl:103-105", status := .proven, prop := ``FrameEqualExact, thm := some ``frameEqualExact },
  { id := "errorshow-stacktraces-l107", juliaFile := "base/stacktraces.jl", juliaFns := ["hash(::StackFrame)"]
    statement := "StackFrame hashing applies the seed xor and the five equality fields in source order."
    source := "base/stacktraces.jl:107-115", status := .proven, prop := ``FrameHashExact, thm := some ``frameHashExact },
  { id := "errorshow-stacktraces-l117", juliaFile := "base/stacktraces.jl", juliaFns := ["_add_linetable_frames!"]
    statement := "Line-table expansion appends the previous debug chain and its edge frames in source order."
    source := "base/stacktraces.jl:117-125", status := .proven, prop := ``AddLineTableFramesExact, thm := some ``addLineTableFramesExact },
  { id := "errorshow-stacktraces-l130", juliaFile := "base/stacktraces.jl", juliaFns := ["_add_di_frames!"]
    statement := "DebugInfo expansion appends its own frame, line-table frames, and direct edge frames in source order."
    source := "base/stacktraces.jl:130-146", status := .proven, prop := ``AddDebugFramesExact, thm := some ``addDebugFramesExact },
  { id := "errorshow-stacktraces-l155", juliaFile := "base/stacktraces.jl", juliaFns := ["lookup(::Ptr)"]
    statement := "Pointer lookup returns UNKNOWN for no records, maps raw records when debug info is unavailable, and reverses recovered DebugInfo frames otherwise."
    source := "base/stacktraces.jl:155-195", status := .proven, prop := ``LookupPointerExact, thm := some ``lookupPointerExact },
  { id := "errorshow-stacktraces-l201", juliaFile := "base/stacktraces.jl", juliaFns := ["lookup(::InterpreterIP)"]
    statement := "Interpreter lookup selects the source function, linfo, line, pc, and edge frames for every code-kind branch and returns innermost first."
    source := "base/stacktraces.jl:201-231", status := .proven, prop := ``LookupInterpreterExact, thm := some ``lookupInterpreterExact },
  { id := "errorshow-stacktraces-l240", juliaFile := "base/stacktraces.jl", juliaFns := ["stacktrace(trace,c_funcs)"]
    statement := "Explicit stacktrace flattens each lookup in trace order and filters exactly the C frames requested by c_funcs."
    source := "base/stacktraces.jl:240-251", status := .proven, prop := ``StacktraceFromLookupsExact, thm := some ``stacktraceFromLookupsExact },
  { id := "errorshow-stacktraces-l253", juliaFile := "base/stacktraces.jl", juliaFns := ["stacktrace(c_funcs)"]
    statement := "Implicit stacktrace removes its own frames and, when requested, the leading run of C frames."
    source := "base/stacktraces.jl:253-260", status := .proven, prop := ``StacktraceHereExact, thm := some ``stacktraceHereExact },
  { id := "errorshow-stacktraces-l270", juliaFile := "base/stacktraces.jl", juliaFns := ["remove_frames!(stack,name)"]
    statement := "Single-name frame removal retains exactly the suffix after the last matching frame."
    source := "base/stacktraces.jl:270-273", status := .proven, prop := ``RemoveFramesNameExact, thm := some ``removeFramesNameExact },
  { id := "errorshow-stacktraces-l275", juliaFile := "base/stacktraces.jl", juliaFns := ["remove_frames!(stack,names)"]
    statement := "Multi-name frame removal retains exactly the suffix after the last frame whose function belongs to the names."
    source := "base/stacktraces.jl:275-278", status := .proven, prop := ``RemoveFramesNamesExact, thm := some ``removeFramesNamesExact },
  { id := "errorshow-stacktraces-l285", juliaFile := "base/stacktraces.jl", juliaFns := ["remove_frames!(stack,module)"]
    statement := "Module frame removal filters exactly frames reported as originating from that module."
    source := "base/stacktraces.jl:285-288", status := .proven, prop := ``RemoveFramesModuleExact, thm := some ``removeFramesModuleExact },
  { id := "errorshow-stacktraces-l290", juliaFile := "base/stacktraces.jl", juliaFns := ["is_top_level_frame"]
    statement := "A frame is top level exactly for CodeInfo or for an unowned top-level-scope frame."
    source := "base/stacktraces.jl:290", status := .proven, prop := ``IsTopLevelFrameExact, thm := some ``isTopLevelFrameExact },
  { id := "errorshow-stacktraces-l292", juliaFile := "base/stacktraces.jl", juliaFns := ["frame_method_or_module"]
    statement := "frame_method_or_module returns the Method or Module selected from every linfo owner branch."
    source := "base/stacktraces.jl:292-299", status := .proven, prop := ``FrameMethodOrModuleExact, thm := some ``frameMethodOrModuleExact },
  { id := "errorshow-stacktraces-l301", juliaFile := "base/stacktraces.jl", juliaFns := ["frame_mi"]
    statement := "frame_mi returns exactly the MethodInstance selected from each supported linfo."
    source := "base/stacktraces.jl:301-307", status := .proven, prop := ``FrameMethodInstanceExact, thm := some ``frameMethodInstanceExact },
  { id := "errorshow-stacktraces-l309", juliaFile := "base/stacktraces.jl", juliaFns := ["frame_location"]
    statement := "frame_location uses debuginfo when available and otherwise the frame file, line, and correct pc or column fallback."
    source := "base/stacktraces.jl:309-328", status := .proven, prop := ``FrameLocationExact, thm := some ``frameLocationExact },
  { id := "errorshow-stacktraces-l330", juliaFile := "base/stacktraces.jl", juliaFns := ["show_spec_linfo"]
    statement := "show_spec_linfo selects the exact pointer, top-level, demangled, MethodInstance, custom CodeInstance, or Method display branch."
    source := "base/stacktraces.jl:330-362", status := .proven, prop := ``ShowSpecLinfoExact, thm := some ``showSpecLinfoExact },
  { id := "errorshow-stacktraces-l365", juliaFile := "base/stacktraces.jl", juliaFns := ["show_custom_spec_sig"]
    statement := "The default custom signature method obtains the CodeInstance MethodInstance and delegates with its specialized types."
    source := "base/stacktraces.jl:365-369", status := .proven, prop := ``ShowCustomSpecSigExact, thm := some ``showCustomSpecSigExact },
  { id := "errorshow-stacktraces-l371", juliaFile := "base/stacktraces.jl", juliaFns := ["show_spec_sig"]
    statement := "show_spec_sig normalizes unused names and emits either the positional call or the rearranged keyword call for every signature."
    source := "base/stacktraces.jl:371-398", status := .proven, prop := ``ShowSpecSigExact, thm := some ``showSpecSigExact },
  { id := "errorshow-stacktraces-l400", juliaFile := "base/stacktraces.jl", juliaFns := ["show(::StackFrame)"]
    statement := "StackFrame show emits its selected signature, optional basename and location, and inline suffix in source order."
    source := "base/stacktraces.jl:400-420", status := .proven, prop := ``ShowFrameExact, thm := some ``showFrameExact },
  { id := "errorshow-stacktraces-l422", juliaFile := "base/stacktraces.jl", juliaFns := ["parentmodule(::StackFrame)"]
    statement := "StackFrame parentmodule unwraps CodeInstance and ABIOverride and returns the exact MethodInstance, Method, Module, or unavailable branch."
    source := "base/stacktraces.jl:422-446", status := .proven, prop := ``ParentModuleExact, thm := some ``parentModuleExact },
  { id := "errorshow-stacktraces-l453", juliaFile := "base/stacktraces.jl", juliaFns := ["from(::StackFrame,::Module)"]
    statement := "from returns true exactly when parentmodule(frame) is the requested module."
    source := "base/stacktraces.jl:453-455", status := .proven, prop := ``FromModuleExact, thm := some ``fromModuleExact }
]

end JuliaLean.ErrorShow.StacktracesEntries
