import JuliaLean.Registry.Types
import JuliaLean.ErrorShow.MultimediaFaithful

namespace JuliaLean.ErrorShow.MultimediaEntries

open JuliaLean.Registry
open JuliaLean.ErrorShow.MultimediaFaithful

def entries : List Entry := [
  { id := "errorshow-multimedia-l73", juliaFile := "base/multimedia.jl", juliaFns := ["@MIME_str"]
    statement := "For every literal, @MIME_str places the same text in the MIME type parameter."
    source := "base/multimedia.jl:73-75", status := .proven, prop := ``MimeStrExact, thm := some ``mimeStrExact },
  { id := "errorshow-multimedia-l78", juliaFile := "base/multimedia.jl", juliaFns := ["show(::IO,::MIME\"text/plain\",x)"]
    statement := "The text/plain fallback returns exactly the two-argument show output for every value."
    source := "base/multimedia.jl:78", status := .proven, prop := ``ShowTextPlainFallbackExact, thm := some ``showTextPlainFallbackExact },
  { id := "errorshow-multimedia-l80", juliaFile := "base/multimedia.jl", juliaFns := ["MIME(s)"]
    statement := "MIME construction preserves every input media-type string."
    source := "base/multimedia.jl:80", status := .proven, prop := ``MimeConstructorExact, thm := some ``mimeConstructorExact },
  { id := "errorshow-multimedia-l81", juliaFile := "base/multimedia.jl", juliaFns := ["show(::IO,::MIME)"]
    statement := "show(::MIME) prefixes every MIME parameter with `MIME type `."
    source := "base/multimedia.jl:81", status := .proven, prop := ``ShowMimeExact, thm := some ``showMimeExact },
  { id := "errorshow-multimedia-l82", juliaFile := "base/multimedia.jl", juliaFns := ["print(::IO,::MIME)"]
    statement := "print(::MIME) emits exactly the MIME parameter text."
    source := "base/multimedia.jl:82", status := .proven, prop := ``PrintMimeExact, thm := some ``printMimeExact },
  { id := "errorshow-multimedia-l107", juliaFile := "base/multimedia.jl", juliaFns := ["showable(::MIME,x)"]
    statement := "Default showable returns the exact hasmethod result for every MIME and value type."
    source := "base/multimedia.jl:107", status := .proven, prop := ``ShowableMimeExact, thm := some ``showableMimeExact },
  { id := "errorshow-multimedia-l108", juliaFile := "base/multimedia.jl", juliaFns := ["showable(::AbstractString,x)"]
    statement := "String showable constructs the same MIME and delegates to MIME showable for every input."
    source := "base/multimedia.jl:108", status := .proven, prop := ``ShowableStringExact, thm := some ``showableStringExact },
  { id := "errorshow-multimedia-l154", juliaFile := "base/multimedia.jl", juliaFns := ["show(::IO,::AbstractString,x)"]
    statement := "String-MIME show constructs the same MIME and returns the delegated show result."
    source := "base/multimedia.jl:154", status := .proven, prop := ``ShowStringMimeExact, thm := some ``showStringMimeExact },
  { id := "errorshow-multimedia-l190", juliaFile := "base/multimedia.jl", juliaFns := ["repr(::MIME,x)"]
    statement := "repr(::MIME) selects its text or binary helper exactly according to istextmime for every input."
    source := "base/multimedia.jl:190", status := .proven, prop := ``ReprMimeExact, thm := some ``reprMimeExact },
  { id := "errorshow-multimedia-l191", juliaFile := "base/multimedia.jl", juliaFns := ["repr(::AbstractString,x)"]
    statement := "String-MIME repr constructs the same MIME and delegates without changing the result."
    source := "base/multimedia.jl:191", status := .proven, prop := ``ReprStringExact, thm := some ``reprStringExact },
  { id := "errorshow-multimedia-l194", juliaFile := "base/multimedia.jl", juliaFns := ["_textrepr(::MIME,x,context)"]
    statement := "Generic textual representation returns exactly String(__binrepr(...))."
    source := "base/multimedia.jl:194", status := .proven, prop := ``TextReprGenericExact, thm := some ``textReprGenericExact },
  { id := "errorshow-multimedia-l195", juliaFile := "base/multimedia.jl", juliaFns := ["_textrepr(::MIME,::AbstractString,context)"]
    statement := "Non-plain textual MIME representation returns every input string unchanged."
    source := "base/multimedia.jl:195", status := .proven, prop := ``TextReprRawStringExact, thm := some ``textReprRawStringExact },
  { id := "errorshow-multimedia-l196", juliaFile := "base/multimedia.jl", juliaFns := ["_textrepr(::MIME\"text/plain\",::AbstractString,context)"]
    statement := "text/plain string representation returns exactly the decoded __binrepr output."
    source := "base/multimedia.jl:196", status := .proven, prop := ``TextReprPlainStringExact, thm := some ``textReprPlainStringExact },
  { id := "errorshow-multimedia-l199", juliaFile := "base/multimedia.jl", juliaFns := ["__binrepr"]
    statement := "__binrepr selects the plain or IOContext show call by context presence and returns the resulting buffer bytes."
    source := "base/multimedia.jl:199-207", status := .proven, prop := ``BinreprBufferExact, thm := some ``binreprBufferExact },
  { id := "errorshow-multimedia-l208", juliaFile := "base/multimedia.jl", juliaFns := ["_binrepr(::MIME,x,context)"]
    statement := "Generic _binrepr delegates exactly to __binrepr."
    source := "base/multimedia.jl:208", status := .proven, prop := ``BinreprGenericExact, thm := some ``binreprGenericExact },
  { id := "errorshow-multimedia-l209", juliaFile := "base/multimedia.jl", juliaFns := ["_binrepr(::MIME,::Vector{UInt8},context)"]
    statement := "Byte-vector _binrepr returns every input vector unchanged."
    source := "base/multimedia.jl:209", status := .proven, prop := ``BinreprBytesExact, thm := some ``binreprBytesExact },
  { id := "errorshow-multimedia-l226", juliaFile := "base/multimedia.jl", juliaFns := ["istextmime(::MIME)"]
    statement := "The generic istextmime method tests exactly the `text/` prefix."
    source := "base/multimedia.jl:226", status := .proven, prop := ``IsTextMimePrefixExact, thm := some ``isTextMimePrefixExact },
  { id := "errorshow-multimedia-l227", juliaFile := "base/multimedia.jl", juliaFns := ["istextmime(::AbstractString)"]
    statement := "String istextmime constructs the same MIME and delegates to the generic method."
    source := "base/multimedia.jl:227", status := .proven, prop := ``IsTextMimeStringExact, thm := some ``isTextMimeStringExact },
  { id := "errorshow-multimedia-l236", juliaFile := "base/multimedia.jl", juliaFns := ["istextmime(::MIME{known})"]
    statement := "Every MIME specialization generated by the textual-MIME loop returns true."
    source := "base/multimedia.jl:229-236", status := .proven, prop := ``IsKnownTextMimeExact, thm := some ``isKnownTextMimeExact },
  { id := "errorshow-multimedia-l259", juliaFile := "base/multimedia.jl", juliaFns := ["display(d,::AbstractString,x)"]
    statement := "Backend string display constructs the same MIME and returns the delegated backend result."
    source := "base/multimedia.jl:259", status := .proven, prop := ``DisplayBackendStringExact, thm := some ``displayBackendStringExact },
  { id := "errorshow-multimedia-l260", juliaFile := "base/multimedia.jl", juliaFns := ["display(::AbstractString,x)"]
    statement := "Global string display constructs the same MIME and returns the delegated global result."
    source := "base/multimedia.jl:260", status := .proven, prop := ``DisplayGlobalStringExact, thm := some ``displayGlobalStringExact },
  { id := "errorshow-multimedia-l270", juliaFile := "base/multimedia.jl", juliaFns := ["displayable(d,::AbstractString)"]
    statement := "Backend string displayable constructs the same MIME and returns the backend predicate."
    source := "base/multimedia.jl:270", status := .proven, prop := ``DisplayableBackendStringExact, thm := some ``displayableBackendStringExact },
  { id := "errorshow-multimedia-l271", juliaFile := "base/multimedia.jl", juliaFns := ["displayable(::AbstractString)"]
    statement := "Global string displayable constructs the same MIME and returns the stack predicate."
    source := "base/multimedia.jl:271", status := .proven, prop := ``DisplayableGlobalStringExact, thm := some ``displayableGlobalStringExact },
  { id := "errorshow-multimedia-l285", juliaFile := "base/multimedia.jl", juliaFns := ["display(::TextDisplay,::MIME\"text/plain\",x)"]
    statement := "TextDisplay text/plain writes the selected show text followed by one newline."
    source := "base/multimedia.jl:285", status := .proven, prop := ``TextDisplayPlainExact, thm := some ``textDisplayPlainExact },
  { id := "errorshow-multimedia-l286", juliaFile := "base/multimedia.jl", juliaFns := ["display(::TextDisplay,x)"]
    statement := "Default TextDisplay delegates exactly to its text/plain method."
    source := "base/multimedia.jl:286", status := .proven, prop := ``TextDisplayDefaultExact, thm := some ``textDisplayDefaultExact },
  { id := "errorshow-multimedia-l289", juliaFile := "base/multimedia.jl", juliaFns := ["displayable(::TextDisplay,::MIME)"]
    statement := "TextDisplay displayability returns exactly istextmime for every MIME."
    source := "base/multimedia.jl:289", status := .proven, prop := ``TextDisplayableExact, thm := some ``textDisplayableExact },
  { id := "errorshow-multimedia-l290", juliaFile := "base/multimedia.jl", juliaFns := ["display(::TextDisplay,::MIME,x)"]
    statement := "Generic TextDisplay rejects binary MIME values or writes the show text and newline for textual MIME values."
    source := "base/multimedia.jl:290-293", status := .proven, prop := ``TextDisplayMimeExact, thm := some ``textDisplayMimeExact },
  { id := "errorshow-multimedia-l296", juliaFile := "base/multimedia.jl", juliaFns := ["flush(::TextDisplay)"]
    statement := "TextDisplay flush returns exactly the wrapped stream flush result."
    source := "base/multimedia.jl:296", status := .proven, prop := ``FlushTextDisplayExact, thm := some ``flushTextDisplayExact },
  { id := "errorshow-multimedia-l297", juliaFile := "base/multimedia.jl", juliaFns := ["close(::TextDisplay)"]
    statement := "TextDisplay close returns exactly the wrapped stream close result."
    source := "base/multimedia.jl:297", status := .proven, prop := ``CloseTextDisplayExact, thm := some ``closeTextDisplayExact },
  { id := "errorshow-multimedia-l312", juliaFile := "base/multimedia.jl", juliaFns := ["pushdisplay"]
    statement := "pushdisplay appends every backend to the end of the display vector."
    source := "base/multimedia.jl:312-315", status := .proven, prop := ``PushDisplayExact, thm := some ``pushDisplayExact },
  { id := "errorshow-multimedia-l324", juliaFile := "base/multimedia.jl", juliaFns := ["popdisplay()"]
    statement := "Zero-argument popdisplay removes and returns the top backend and errors on an empty stack."
    source := "base/multimedia.jl:324", status := .proven, prop := ``PopDisplayExact, thm := some ``popDisplayExact },
  { id := "errorshow-multimedia-l325", juliaFile := "base/multimedia.jl", juliaFns := ["popdisplay(d)"]
    statement := "Named popdisplay removes the last equal backend and raises KeyError exactly when none exists."
    source := "base/multimedia.jl:325-332", status := .proven, prop := ``PopNamedDisplayExact, thm := some ``popNamedDisplayExact },
  { id := "errorshow-multimedia-l333", juliaFile := "base/multimedia.jl", juliaFns := ["reinit_displays"]
    statement := "Display reinitialization empties the stack and leaves exactly TextDisplay(stdout)."
    source := "base/multimedia.jl:333-336", status := .proven, prop := ``ReinitDisplaysExact, thm := some ``reinitDisplaysExact },
  { id := "errorshow-multimedia-l338", juliaFile := "base/multimedia.jl", juliaFns := ["xdisplayable"]
    statement := "xdisplayable returns exactly applicable(display,D,args...)."
    source := "base/multimedia.jl:338", status := .proven, prop := ``XdisplayableExact, thm := some ``xdisplayableExact },
  { id := "errorshow-multimedia-l367", juliaFile := "base/multimedia.jl", juliaFns := ["display(x)"]
    statement := "Global display(x) checks backends from top to bottom, catches only display or show MethodErrors, and otherwise returns or rethrows the first outcome."
    source := "base/multimedia.jl:367-379", status := .proven, prop := ``DisplayAnyExact, thm := some ``displayAnyExact },
  { id := "errorshow-multimedia-l381", juliaFile := "base/multimedia.jl", juliaFns := ["display(::MIME,x)"]
    statement := "MIME display checks backends from top to bottom and catches only display MethodErrors."
    source := "base/multimedia.jl:381-393", status := .proven, prop := ``DisplayMimeExact, thm := some ``displayMimeExact },
  { id := "errorshow-multimedia-l395", juliaFile := "base/multimedia.jl", juliaFns := ["displayable(d,::MIME)"]
    statement := "Backend MIME displayable returns exactly the corresponding hasmethod result."
    source := "base/multimedia.jl:395-396", status := .proven, prop := ``DisplayableBackendMimeExact, thm := some ``displayableBackendMimeExact },
  { id := "errorshow-multimedia-l398", juliaFile := "base/multimedia.jl", juliaFns := ["displayable(::MIME)"]
    statement := "Global MIME displayable returns true exactly when some backend returns true."
    source := "base/multimedia.jl:398-403", status := .proven, prop := ``DisplayableGlobalMimeExact, thm := some ``displayableGlobalMimeExact },
  { id := "errorshow-multimedia-l426", juliaFile := "base/multimedia.jl", juliaFns := ["redisplay(x)"]
    statement := "redisplay(x) checks backends from top to bottom and catches exactly redisplay, display, or show MethodErrors."
    source := "base/multimedia.jl:426-438", status := .proven, prop := ``RedisplayAnyExact, thm := some ``redisplayAnyExact },
  { id := "errorshow-multimedia-l440", juliaFile := "base/multimedia.jl", juliaFns := ["redisplay(mime,x)"]
    statement := "MIME redisplay checks backends from top to bottom and catches exactly redisplay or display MethodErrors."
    source := "base/multimedia.jl:440-452", status := .proven, prop := ``RedisplayMimeExact, thm := some ``redisplayMimeExact },
  { id := "errorshow-multimedia-l455", juliaFile := "base/multimedia.jl", juliaFns := ["redisplay(d,x)"]
    statement := "Backend redisplay(x) delegates exactly to display(d,x)."
    source := "base/multimedia.jl:455", status := .proven, prop := ``RedisplayBackendDefaultExact, thm := some ``redisplayBackendDefaultExact },
  { id := "errorshow-multimedia-l456", juliaFile := "base/multimedia.jl", juliaFns := ["redisplay(d,mime,x)"]
    statement := "Backend MIME redisplay delegates exactly to display(d,mime,x)."
    source := "base/multimedia.jl:456", status := .proven, prop := ``RedisplayBackendMimeDefaultExact, thm := some ``redisplayBackendMimeDefaultExact }
]

end JuliaLean.ErrorShow.MultimediaEntries
