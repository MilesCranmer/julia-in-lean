import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.Printf.Parser
import JuliaLean.Printf.Model
import JuliaLean.Printf.Props
import JuliaLean.Printf.Refutations
import JuliaLean.Printf.Proofs

namespace JuliaLean.Printf

open JuliaLean.Registry

/-- The file every Printf entry is about. -/
private def file : String := "stdlib/Printf/src/Printf.jl"

/-- The duplicate searches run for every Printf entry (issues and PRs). -/
private def queries : String :=
  "queries: printf BigFloat; sprintf BigFloat; Printf mpfr; printf precision negative; printf negative width; " ++
  "printf dynamic width; printf %g exponent; printf %g style; printf %.0d; printf zero precision; printf #x; " ++
  "printf alternate form; printf octal; printf %+x; printf plus unsigned; printf BoundsError; " ++
  "Printf.Format BoundsError; printf %D; printf textwidth; printf ties even; printf %a zero; printf C compatible"

/-- Registry entries of this area. -/
def entries : List Entry := [
  -- proven
  { id := "printf-flags-any-order", juliaFile := file
    juliaFns := ["Printf.Format(::AbstractString)"]
    statement := "The flags - + space 0 # may appear in any order and repeat; the parsed Spec records each one, with 0 ignored after -."
    source := "C99 7.19.6.1p4,p6; Printf.jl:160-181", status := .proven
    prop := ``FlagsAnyOrder, thm := some ``flagsAnyOrder_proven },
  { id := "printf-literal-percent", juliaFile := file
    juliaFns := ["Printf.Format(::AbstractString)", "Printf.format(::Printf.Format)"]
    statement := "A format string without conversions prints its text, with each %% written as %, for every text below 2^40 bytes."
    source := "C99 7.19.6.1p8 (% conversion); Printf.jl:138-153,822-831", status := .proven
    prop := ``LiteralPercent, thm := some ``literalPercent_proven },
  { id := "printf-char-width", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Chars})", "Printf.plength"]
    statement := "@sprintf(\"%Wc\", c) and @sprintf(\"%-Wc\", c) are c padded with spaces to W textwidth columns, inside the computed buffer."
    source := "C99 7.19.6.1p4 (field width); Printf.jl:1002-1006 (textwidth)", status := .proven
    prop := ``CharWidth, thm := some ``charWidth_proven },
  { id := "printf-string-width", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Strings})", "Printf.plength"]
    statement := "@sprintf(\"%Ws\", s) and @sprintf(\"%-Ws\", s) are s padded with spaces to W textwidth columns, inside the computed buffer."
    source := "C99 7.19.6.1p4 (field width); Printf.jl:1002-1006 (textwidth)", status := .proven
    prop := ``StringWidth, thm := some ``stringWidth_proven },
  -- refuted
  { id := "printf-bigfloat-buffer-overflow", juliaFile := file
    juliaFns := ["Printf.format", "Printf.fmt(buf, pos, arg, ::Spec{<:Floats})"]
    statement := "Printing a finite BigFloat with %f after literal text never stores outside the buffer format allocated."
    source := "invariant (safe Julia code does not write out of bounds); Printf.jl:504-519", status := .refuted
    prop := ``BigFloatInBounds, thm := some ``bigFloatInBounds_refuted
    issue := "none found; related #44823 (open), #22126 (closed). " ++ queries
    notes := "\"a\"^100 then %f of a BigFloat with 401 integer digits: resize!(buf, 409) but mpfr_snprintf writes 409 bytes from index 101. The reproducer uses big\"1e400\" (same output length); its result differs from byte 410. Same in both versions." },
  { id := "printf-bigfloat-exact-fit-nul", juliaFile := file
    juliaFns := ["Printf.format", "Printf.fmt(buf, pos, arg, ::Spec{<:Floats})"]
    statement := "@sprintf(\"%Wf\", x) for a finite BigFloat x equals the C99 (MPFR) text of x with field width W."
    source := "C99 7.19.6.1p4,p8; Printf.jl:68 (C printf-compatible)", status := .refuted
    prop := ``BigFloatWidth, thm := some ``bigFloatWidth_refuted
    issue := "none found; related #22126 (closed, same symptom before the 2020 rewrite). " ++ queries
    notes := "@sprintf(\"%320f\", big\"2.0\") ends in NUL: the output exactly fills the 320 reserved bytes, and snprintf stores 319 characters plus NUL (Printf.jl:510 tests > instead of >=). Same in both versions." },
  { id := "printf-negative-precision-int-oob", juliaFile := file
    juliaFns := ["Printf.format", "Printf.plength(::Spec{<:Ints}, x)", "Printf.fmt(buf, pos, arg, ::Spec{<:Ints})"]
    statement := "Integer conversions with a dynamic precision (%.*d etc.) never store outside the buffer format allocated."
    source := "C99 7.19.6.1p5 (negative precision is omitted); invariant (no out-of-bounds stores)", status := .refuted
    prop := ``IntDigitsInBounds, thm := some ``intDigitsInBounds_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%.*d\", -6, 42) == \"4\\0\": plength gives max(0, -6 + 2 + 5) = 1 byte and the @inbounds digit loop stores 2. With --check-bounds=yes, %.*d with -24 and typemax(Int64) throws BoundsError. Same in both versions." },
  { id := "printf-dynamic-negative-precision", juliaFile := file
    juliaFns := ["Printf.format", "Printf.rmdynamic", "Printf.fmt(buf, pos, arg, ::Spec{<:Strings})"]
    statement := "For every negative p and ASCII string s, @sprintf(\"%.*s\", p, s) == @sprintf(\"%s\", s)."
    source := "C99 7.19.6.1p5: a negative precision argument is taken as if the precision were omitted", status := .refuted
    prop := ``NegativePrecision, thm := some ``negativePrecision_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%.*s\", -2, \"hello\") throws BoundsError. Floats: 1.13.2 prints \"0\" for %.*f with -1 and 0.5, master throws ArgumentError from Ryu (the model mirrors master)." },
  { id := "printf-dynamic-negative-width", juliaFile := file
    juliaFns := ["Printf.format", "Printf.rmdynamic"]
    statement := "For w > 0, @sprintf(\"%*d\", -w, x) == @sprintf(\"%-wd\", x)."
    source := "C99 7.19.6.1p5: a negative field width is a - flag and a positive width", status := .refuted
    prop := ``NegativeWidth, thm := some ``negativeWidth_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%*d\", -5, 42) == \"42\", @sprintf(\"%-5d\", 42) == \"42   \". Same for %*s and %*f. Same in both versions." },
  { id := "printf-general-style-rounding", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Floats})"]
    statement := "For P >= 1 and finite x, @sprintf(\"%.Pg\", x) chooses style f or e from the exponent of the style-e conversion with precision P - 1, as C99 does."
    source := "C99 7.19.6.1p8 (g); Printf.jl:530 (\"C11-compliant general format\")", status := .refuted
    prop := ``GeneralStyle, thm := some ``generalStyle_refuted
    issue := "none found; related #14360, #43129 (closed), PR #40689 (merged). " ++ queries
    notes := "@sprintf(\"%.3g\", 999.5) == \"1000\" (C: \"1e+03\"); @sprintf(\"%g\", 9.999999e-5) == \"1e-04\" (C: \"0.0001\"). Printf.jl:533 rounds to P + 1 digits. Same in both versions." },
  { id := "printf-hex-alternate-zero", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Ints})"]
    statement := "@sprintf(\"%#x\", 0) and @sprintf(\"%#X\", 0) are \"0\" for zero of every integer type."
    source := "C99 7.19.6.1p6 (#: a nonzero result has 0x prefixed)", status := .refuted
    prop := ``HexZeroPrefix, thm := some ``hexZeroPrefix_refuted
    issue := "none found. " ++ queries
    notes := "Prints \"0x0\"; stdlib/Printf/test/runtests.jl:656-657 assert this, so P3. Same in both versions." },
  { id := "printf-hex-zero-alternate-point", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Floats})"]
    statement := "@sprintf(\"%#a\", x) contains a decimal point for x = 0.0 and x = -0.0."
    source := "C99 7.19.6.1p6 (# with a/A: always a decimal-point character)", status := .refuted
    prop := ``HexZeroHash, thm := some ``hexZeroHash_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%#a\", 0.0) == \"0x0p+0\": the zero branch (Printf.jl:581-596) ignores hash. Same in both versions." },
  { id := "printf-incomplete-bounds", juliaFile := file
    juliaFns := ["Printf.Format(::AbstractString)"]
    statement := "Printf.Format(f) either succeeds or throws InvalidFormatStringError, for every format string f."
    source := "invariant of Format validation, Printf.jl:143-241; stdlib/Printf/test/runtests.jl:359-361", status := .refuted
    prop := ``FormatErrorsAreInvalidFormat, thm := some ``formatErrorsAreInvalidFormat_refuted
    issue := "PR #62674 (open) fixes it. " ++ queries
    notes := "Format(\"%1\"), Format(\"%5\"), Format(\"%*\") throw BoundsError (Printf.jl:188,193 read past the end). Same in both versions." },
  { id := "printf-integer-zero-precision", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Ints})"]
    statement := "%.0d %.0i %.0o %.0u %.0x %.0X print no characters for a zero value of every integer type."
    source := "C99 7.19.6.1p8 (a zero value with precision zero is no characters)", status := .refuted
    prop := ``IntegerZeroPrecision, thm := some ``integerZeroPrecision_refuted
    issue := "none found. " ++ queries
    notes := "All six print \"0\" (ndigits(..., pad=1) at Printf.jl:391). Same in both versions." },
  { id := "printf-octal-alternate-precision", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Ints})"]
    statement := "For x > 0, @sprintf(\"%#.Po\", x) is the octal digits of x padded with zeros to max(P, ndigits + 1) digits."
    source := "C99 7.19.6.1p6 (# with o increases the precision only if necessary)", status := .refuted
    prop := ``OctalHashPrecision, thm := some ``octalHashPrecision_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%#.5o\", UInt32(1)) == \"000001\" (C: \"00001\"); also %#o of 0 is \"00\" (tested in runtests.jl:655). Same in both versions." },
  { id := "printf-plus-unsigned", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Ints})"]
    statement := "For x >= 0 and c in o u x X, the + and space flags do not change @sprintf(\"%c\", x)."
    source := "C99 7.19.6.1p6 (+ and space apply to signed conversions)", status := .refuted
    prop := ``PlusUnsigned, thm := some ``plusUnsigned_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%+x\", 42) == \"+2a\"; asserted by stdlib/Printf/test/runtests.jl:617-621, so P3. Same in both versions." },
  { id := "printf-tie-rounding-doc", juliaFile := file
    juliaFns := ["Printf.@printf"]
    statement := "For finite x exactly halfway between two P-decimal strings, @sprintf(\"%.Pf\", x) is the one further from zero."
    source := "Printf.jl:989-991 (@printf caveat)", status := .refuted
    prop := ``TiesAway, thm := some ``tiesAway_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%.0f\", 0.5) == \"0\"; ties go to even, as the docstring's own example (Printf.jl:998-999) shows. Documentation bug, P3." },
  { id := "printf-uppercase-integer-dispatch", juliaFile := file
    juliaFns := ["Printf.Format(::AbstractString)", "Printf.format", "Printf.plength"]
    statement := "Every conversion Printf.Format accepts has a plength/fmt method, so formatting does not throw MethodError for it."
    source := "invariant; Printf.jl:241 (accepted set) and 14 (Ints)", status := .refuted
    prop := ``AcceptedHaveMethods, thm := some ``acceptedHaveMethods_refuted
    issue := "none found; related #41078 (closed, %n). " ++ queries
    notes := "Format(\"%D\"), \"%O\", \"%U\" succeed; format(f, 1) throws MethodError. Same in both versions." },
  { id := "printf-wide-precision-padding", juliaFile := file
    juliaFns := ["Printf.fmt(buf, pos, arg, ::Spec{<:Strings})"]
    statement := "@sprintf(\"%W.Ps\", s) is a whole-character prefix of s padded with spaces to W textwidth columns."
    source := "C99 7.19.6.1p4 (minimum field width); Printf.jl:1002-1006 (textwidth widths)", status := .refuted
    prop := ``StringFieldWidth, thm := some ``stringFieldWidth_refuted
    issue := "none found; related #41068 (closed). " ++ queries
    notes := "@sprintf(\"%5.1s\", \"你\") is four spaces (4 columns). Same in both versions." },
  { id := "printf-zero-flag-zero-precision", juliaFile := file
    juliaFns := ["Printf.Format(::AbstractString)", "Printf.rmdynamic"]
    statement := "For integer conversions with a precision, the 0 flag is ignored: @sprintf(\"%0W.Pd\", x) == @sprintf(\"%W.Pd\", x)."
    source := "C99 7.19.6.1p6 (0 flag ignored when a precision is specified)", status := .refuted
    prop := ``ZeroFlagPrecision, thm := some ``zeroFlagPrecision_refuted
    issue := "none found. " ++ queries
    notes := "@sprintf(\"%05.0d\", Int32(3)) == \"00003\" (C: \"    3\"); positive precisions are handled (Printf.jl:243,305 test > 0). Same in both versions." }
]

end JuliaLean.Printf
