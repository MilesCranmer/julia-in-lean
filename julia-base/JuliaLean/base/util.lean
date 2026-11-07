import JuliaLean.Proofs.stdlib.CRC32c.src.CRC32c.Kernel
import JuliaLean.Registry.Types
import JuliaLean.Core
import JuliaLean.base.io
import JuliaLean.base.show
import JuliaLean.base.meta
import JuliaLean.base.secretbuffer
import JuliaLean.base.int

/-!
# Model of `base/util.jl`

Typed models of utility methods at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` on a
64-bit platform. Terminal streams, IOBuffer operations, runtime options, C memory operations, and
CRC32c calls are explicit interfaces; the test runner's environment, commands and process launch
are too. The `@kwdef` field helpers work on the `Expr` values of `base/expr.jl`. Macro expansion
remains visible as untranslated source; the Windows credential UI uses typed runtime operations.
-/

namespace JuliaLean.base.util

open JuliaLean

abbrev U32 := JInt .u32
abbrev I64 := JInt .i64
abbrev I32 := JInt .i32

-- Source: base/util.jl:1-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## printing with color ##
-- 
-- /Source
inductive Color where
  | symbol (name : String)
  | integer (value : I64)
  deriving DecidableEq, Repr

structure Style where
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  blink : Bool := false
  reverse : Bool := false
  hidden : Bool := false
  deriving DecidableEq, Repr

/--
Julia source: base/util.jl:5-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const text_colors = Dict{Union{Symbol,Int},String}(
    :black         => "\033[30m",
    :red           => "\033[31m",
    :green         => "\033[32m",
    :yellow        => "\033[33m",
    :blue          => "\033[34m",
    :magenta       => "\033[35m",
    :cyan          => "\033[36m",
    :white         => "\033[37m",
    :light_black   => "\033[90m", # gray
    :light_red     => "\033[91m",
    :light_green   => "\033[92m",
    :light_yellow  => "\033[93m",
    :light_blue    => "\033[94m",
    :light_magenta => "\033[95m",
    :light_cyan    => "\033[96m",
    :light_white   => "\033[97m",
    :normal        => "\033[0m",
    :default       => "\033[39m",
    :bold          => "\033[1m",
    :italic        => "\033[3m",
    :underline     => "\033[4m",
    :blink         => "\033[5m",
    :reverse       => "\033[7m",
    :hidden        => "\033[8m",
    :nothing       => "",
)

for i in 0:255
    text_colors[i] = "\033[38;5;$(i)m"
end

```
-/
def textColorEntry : Color → Option String
  | .integer n =>
      if 0 ≤ n.val && n.val ≤ 255 then some ("\x1b[38;5;" ++ toString n.val ++ "m") else none
  | .symbol name =>
      match name with
      | "black" => some "\x1b[30m"
      | "red" => some "\x1b[31m"
      | "green" => some "\x1b[32m"
      | "yellow" => some "\x1b[33m"
      | "blue" => some "\x1b[34m"
      | "magenta" => some "\x1b[35m"
      | "cyan" => some "\x1b[36m"
      | "white" => some "\x1b[37m"
      | "light_black" => some "\x1b[90m"
      | "light_red" => some "\x1b[91m"
      | "light_green" => some "\x1b[92m"
      | "light_yellow" => some "\x1b[93m"
      | "light_blue" => some "\x1b[94m"
      | "light_magenta" => some "\x1b[95m"
      | "light_cyan" => some "\x1b[96m"
      | "light_white" => some "\x1b[97m"
      | "normal" => some "\x1b[0m"
      | "default" => some "\x1b[39m"
      | "bold" => some "\x1b[1m"
      | "italic" => some "\x1b[3m"
      | "underline" => some "\x1b[4m"
      | "blink" => some "\x1b[5m"
      | "reverse" => some "\x1b[7m"
      | "hidden" => some "\x1b[8m"
      | "nothing" => some ""
      | _ => none

/--
Julia source: base/util.jl:37-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const disable_text_style = Dict{Symbol,String}(
    :bold      => "\033[22m",
    :italic    => "\033[23m",
    :underline => "\033[24m",
    :blink     => "\033[25m",
    :reverse   => "\033[27m",
    :hidden    => "\033[28m",
    :normal    => "",
    :default   => "",
    :nothing   => "",
)

```
-/
def disableTextStyleEntry : Color → Option String
  | .symbol "bold" => some "\x1b[22m"
  | .symbol "italic" => some "\x1b[23m"
  | .symbol "underline" => some "\x1b[24m"
  | .symbol "blink" => some "\x1b[25m"
  | .symbol "reverse" => some "\x1b[27m"
  | .symbol "hidden" => some "\x1b[28m"
  | .symbol "normal" | .symbol "default" | .symbol "nothing" => some ""
  | _ => none

-- UNTRANSLATED
-- Reason: The generated color list is documentation-only and depends on Dict key iteration before sorting.
-- Source: base/util.jl:49-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Create a docstring with an automatically generated list
-- # of colors.
-- let color_syms = collect(Iterators.filter(x -> !isa(x, Integer), keys(text_colors))),
--     formatting_syms = [:normal, :bold, :italic, :default]
--     global const available_text_colors = cat(
--         sort!(intersect(color_syms, formatting_syms), rev=true),
--         sort!(setdiff(  color_syms, formatting_syms));
--         dims=1)
-- end
-- 
-- const available_text_colors_docstring =
--     string(join([string("`:", key,"`")
--                  for key in available_text_colors], ",\n", ", or \n"))
-- 
-- """Dictionary of color codes for the terminal.
-- 
-- Available colors are: $available_text_colors_docstring as well as the integers 0 to 255 inclusive.
-- 
-- The color `:default` will print text in the default color while the color `:normal`
-- will print text with all text properties (like boldness) reset.
-- Printing with the color `:nothing` will print the string without modifications.
-- """
-- text_colors
-- 
-- /Source
private def normalizedColor (style : Style) (color : Color) : Color :=
  let color := if style.bold && color == .symbol "bold" then .symbol "nothing" else color
  let color := if style.italic && color == .symbol "italic" then .symbol "nothing" else color
  let color := if style.underline && color == .symbol "underline" then .symbol "nothing" else color
  let color := if style.blink && color == .symbol "blink" then .symbol "nothing" else color
  let color := if style.reverse && color == .symbol "reverse" then .symbol "nothing" else color
  if style.hidden && color == .symbol "hidden" then .symbol "nothing" else color

private def defaultColorCode : String := "\x1b[39m"

private def enableColorCode (color : Color) : String :=
  (textColorEntry color).getD defaultColorCode

private def disableColorCode (color : Color) : String :=
  (disableTextStyleEntry color).getD defaultColorCode

private def enableAnsi (style : Style) (color : Color) : String :=
  enableColorCode color ++ (if style.bold then "\x1b[1m" else "") ++
  (if style.italic then "\x1b[3m" else "") ++
  (if style.underline then "\x1b[4m" else "") ++
  (if style.blink then "\x1b[5m" else "") ++
  (if style.reverse then "\x1b[7m" else "") ++
  (if style.hidden then "\x1b[8m" else "")

private def disableAnsi (style : Style) (color : Color) : String :=
  (if style.hidden then "\x1b[28m" else "") ++
  (if style.reverse then "\x1b[27m" else "") ++
  (if style.blink then "\x1b[25m" else "") ++
  (if style.underline then "\x1b[24m" else "") ++
  (if style.bold then "\x1b[22m" else "") ++
  (if style.italic then "\x1b[23m" else "") ++ disableColorCode color

private def splitNewlines : List Char → List (List Char)
  | [] => [[]]
  | c :: rest =>
      if c == '\n' then [] :: splitNewlines rest
      else match splitNewlines rest with
        | line :: lines => (c :: line) :: lines
        | [] => [[c]]

structure ColorOutputOps (m : Type → Type) (Io V Buffer : Type) where
  newBuffer : m Buffer
  bufferContext : Buffer → JuliaLean.base.show.JIO Io V → JuliaLean.base.show.JIO Io V
  getColor : JuliaLean.base.show.JIO Io V → m Bool
  writeBuffer : Buffer → List Char → m Unit
  takeString : Buffer → m (List Char)
  printString : JuliaLean.base.show.JIO Io V → List Char → m Unit

private def outputColorStringModel {m : Type → Type} [Monad m] {Io V Buffer : Type}
    (ops : ColorOutputOps m Io V Buffer) (buffer : Buffer) (text : List Char)
    (color : Color) (style : Style) : m (List Char) := do
  let color := normalizedColor style color
  let enable := (enableAnsi style color).toList
  let disable := (disableAnsi style color).toList
  let mut first := true
  for line in splitNewlines text do
    if !first then ops.writeBuffer buffer ['\n']
    first := false
    if !line.isEmpty then ops.writeBuffer buffer (enable ++ line ++ disable)
  ops.takeString buffer

/--
Julia source: base/util.jl:73-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function with_output_color(@nospecialize(f::Function), color::Union{Int, Symbol}, io::IO, args...;
        bold::Bool = false, italic::Bool = false, underline::Bool = false, blink::Bool = false,
        reverse::Bool = false, hidden::Bool = false)
    buf = IOBuffer()
    iscolor = get(io, :color, false)::Bool
    try f(IOContext(buf, io), args...)
    finally
        str = takestring!(buf)
        iscolor && (str = output_color_string(buf, str, color, bold, italic, underline, blink, reverse, hidden))
        print(io, str)
    end
end

```
-/
def withOutputColor {m : Type → Type} [Monad m] {E Io V Buffer Arg Result : Type}
    [MonadExceptOf E m] (ops : ColorOutputOps m Io V Buffer)
    (f : JuliaLean.base.show.JIO Io V → List Arg → m Result)
    (io : JuliaLean.base.show.JIO Io V) (args : List Arg) (color : Color)
    (style : Style) : m Result := do
  let buffer ← ops.newBuffer
  let iscolor ← ops.getColor io
  let result : Except E Result ← tryCatch (do
      let value ← f (ops.bufferContext buffer io) args
      pure (Except.ok value)) (fun error => pure (Except.error error))
  let text ← ops.takeString buffer
  let text ← if iscolor then outputColorStringModel ops buffer text color style else pure text
  ops.printString io text
  match result with
  | .ok value => pure value
  | .error error => throw error

/--
Julia source: base/util.jl:86-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function output_color_string(buf::IOBuffer, str::String, @nospecialize(color::Union{Int, Symbol}),
        bold::Bool, italic::Bool, underline::Bool, blink::Bool, reverse::Bool, hidden::Bool)
    bold && color === :bold && (color = :nothing)
    italic && color === :italic && (color = :nothing)
    underline && color === :underline && (color = :nothing)
    blink && color === :blink && (color = :nothing)
    reverse && color === :reverse && (color = :nothing)
    hidden && color === :hidden && (color = :nothing)
    enable_ansi  = get(text_colors, color, text_colors[:default]) *
                       (bold ? text_colors[:bold] : "") *
                       (italic ? text_colors[:italic] : "") *
                       (underline ? text_colors[:underline] : "") *
                       (blink ? text_colors[:blink] : "") *
                       (reverse ? text_colors[:reverse] : "") *
                       (hidden ? text_colors[:hidden] : "")

    disable_ansi = (hidden ? disable_text_style[:hidden] : "") *
                   (reverse ? disable_text_style[:reverse] : "") *
                   (blink ? disable_text_style[:blink] : "") *
                   (underline ? disable_text_style[:underline] : "") *
                   (bold ? disable_text_style[:bold] : "") *
                   (italic ? disable_text_style[:italic] : "") *
                       get(disable_text_style, color, text_colors[:default])
    first = true
    for line in eachsplit(str, '\n')
        first || print(buf, '\n')
        first = false
        isempty(line) && continue
        print(buf, enable_ansi, line, disable_ansi)
    end
    return takestring!(buf)
end

```
-/
def outputColorString {m : Type → Type} [Monad m] {Io V Buffer : Type}
    (ops : ColorOutputOps m Io V Buffer) (buffer : Buffer) (text : List Char)
    (color : Color) (style : Style) : m (List Char) :=
  outputColorStringModel ops buffer text color style

/--
Julia source: base/util.jl:119-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    printstyled([io], xs...; bold::Bool=false, italic::Bool=false, underline::Bool=false, blink::Bool=false, reverse::Bool=false, hidden::Bool=false, color::Union{Symbol,Int}=:normal)

Print `xs` in a color specified as a symbol or integer, optionally in bold.

Keyword `color` may take any of the values $(Base.available_text_colors_docstring)
or an integer between 0 and 255 inclusive. Note that not all terminals support 256 colors.

Keywords `bold=true`, `italic=true`, `underline=true`, `blink=true` are self-explanatory.
Keyword `reverse=true` prints with foreground and background colors exchanged,
and `hidden=true` should be invisible in the terminal but can still be copied.
These properties can be used in any combination.

See also [`print`](@ref), [`println`](@ref), [`show`](@ref).

!!! note
    Not all terminals support italic output. Some terminals interpret italic as reverse or
    blink.

!!! compat "Julia 1.7"
    Keywords except `color` and `bold` were added in Julia 1.7.
!!! compat "Julia 1.10"
    Support for italic output was added in Julia 1.10.
"""
@constprop :none printstyled(io::IO, msg...; bold::Bool=false, italic::Bool=false, underline::Bool=false, blink::Bool=false, reverse::Bool=false, hidden::Bool=false, color::Union{Int,Symbol}=:normal) =
    with_output_color(print, color, io, msg...; bold=bold, italic=italic, underline=underline, blink=blink, reverse=reverse, hidden=hidden)
```
-/
def printstyledIO {m : Type → Type} [Monad m] {E Io V Buffer Arg : Type}
    [MonadExceptOf E m] (ops : ColorOutputOps m Io V Buffer)
    (printArgs : JuliaLean.base.show.JIO Io V → List Arg → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (messages : List Arg)
    (bold italic underline blink reverse hidden : Bool := false)
    (color : Color := .symbol "normal") : m Unit :=
  withOutputColor (E := E) ops printArgs io messages color ⟨bold, italic, underline, blink, reverse, hidden⟩

/--
Julia source: base/util.jl:145-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@constprop :none printstyled(msg...; bold::Bool=false, italic::Bool=false, underline::Bool=false, blink::Bool=false, reverse::Bool=false, hidden::Bool=false, color::Union{Int,Symbol}=:normal) =
    printstyled(stdout, msg...; bold=bold, italic=italic, underline=underline, blink=blink, reverse=reverse, hidden=hidden, color=color)

```
-/
def printstyledStdout {m : Type → Type} [Monad m] {E Io V Buffer Arg : Type}
    [MonadExceptOf E m] (ops : ColorOutputOps m Io V Buffer)
    (printArgs : JuliaLean.base.show.JIO Io V → List Arg → m Unit)
    (stdout : JuliaLean.base.show.JIO Io V) (messages : List Arg)
    (bold italic underline blink reverse hidden : Bool := false)
    (color : Color := .symbol "normal") : m Unit :=
  printstyledIO (E := E) ops printArgs stdout messages bold italic underline blink reverse hidden color

abbrev I8 := JInt .i8

structure JuliaCmdOptions (CStr : Type) where
  imageFile : CStr
  cpuTarget : CStr
  outputCodeCoverage : CStr
  trackedPath : CStr
  compileEnabled : I8
  depwarn : I8
  checkBounds : I8
  canInline : I8
  useCompiledModules : I8
  usePkgimages : I8
  optLevel : I8
  optLevelMin : I8
  debugLevel : I8
  codeCoverage : I8
  codeCoverageMode : I8
  mallocLog : I8
  color : I8
  quiet : I8
  startupFile : I8
  useSysimageNativeCode : I8
  compressSysimage : I8

structure JuliaCmdOps (CStr Executable Cmd : Type) where
  sysBinDir : String
  windows : Bool
  debugBuild : Bool
  joinpath : String → String → String
  fromPath : String → Executable
  isNull : CStr → Bool
  unsafeString : CStr → Jl String
  command : Executable → List String → Cmd

private def juliaExenameModel (windows debugBuild : Bool) : String :=
  if debugBuild then (if windows then "julia-debug.exe" else "julia-debug")
  else if windows then "julia.exe" else "julia"

private def juliaCmdFlags {CStr Executable Cmd : Type}
    (ops : JuliaCmdOps CStr Executable Cmd) (opts : JuliaCmdOptions CStr) : Jl (List String) := do
  let compile := if opts.compileEnabled.val == 0 then "no"
    else if opts.compileEnabled.val == 2 then "all"
    else if opts.compileEnabled.val == 3 then "min"
    else ""
  let compileFlags := if compile.isEmpty then [] else ["--compile=" ++ compile]
  let depwarn := if opts.depwarn.val == 1 then "yes"
    else if opts.depwarn.val == 2 then "error" else ""
  let depwarnFlags := if depwarn.isEmpty then [] else ["--depwarn=" ++ depwarn]
  let checkBounds := if opts.checkBounds.val == 1 then "yes"
    else if opts.checkBounds.val == 2 then "no" else ""
  let checkBoundsFlags := if checkBounds.isEmpty then [] else ["--check-bounds=" ++ checkBounds]
  let inlineFlags := if opts.canInline.val == 0 then ["--inline=no"] else []
  let compiledModulesFlags := if opts.useCompiledModules.val == 0 then ["--compiled-modules=no"]
    else if opts.useCompiledModules.val == 2 then ["--compiled-modules=existing"]
    else if opts.useCompiledModules.val == 3 then ["--compiled-modules=strict"] else []
  let pkgimagesFlags := if opts.usePkgimages.val == 0 then ["--pkgimages=no"]
    else if opts.usePkgimages.val == 2 then ["--pkgimages=existing"] else []
  let optLevelFlags := if opts.optLevel.val == 2 then [] else ["-O" ++ toString opts.optLevel.val]
  let optLevelMinFlags := if opts.optLevelMin.val == 0 then []
    else ["--min-optlevel=" ++ toString opts.optLevelMin.val]
  let debugFlags := ["-g" ++ toString opts.debugLevel.val]
  let coverageFlags ← if opts.codeCoverage.val != 0 then do
    let coverageFile ← if ops.isNull opts.outputCodeCoverage then pure ""
      else ops.unsafeString opts.outputCodeCoverage
    if coverageFile.isEmpty || coverageFile.contains "%p" then do
      let modeFlags ← if opts.codeCoverage.val == 1 then pure ["--code-coverage=user"]
        else if opts.codeCoverage.val == 2 then pure ["--code-coverage=all"]
        else if opts.codeCoverage.val == 3 then do
          let trackedPath ← ops.unsafeString opts.trackedPath
          pure ["--code-coverage=@" ++ trackedPath]
        else pure []
      let fileFlags := if coverageFile.isEmpty then []
        else ["--code-coverage=" ++ coverageFile]
      pure (modeFlags ++ fileFlags)
    else pure []
  else pure []
  let coverageModeFlags := if opts.codeCoverageMode.val == 1
    then ["--code-coverage-mode=count"] else []
  let mallocFlags ← if opts.mallocLog.val == 1 then pure ["--track-allocation=user"]
    else if opts.mallocLog.val == 2 then pure ["--track-allocation=all"]
    else if opts.mallocLog.val == 3 then do
      let trackedPath ← ops.unsafeString opts.trackedPath
      pure ["--track-allocation=@" ++ trackedPath]
    else pure []
  let colorFlags := if opts.color.val == 1 then ["--color=yes"]
    else if opts.color.val == 2 then ["--color=no"] else []
  let quietFlags := if opts.quiet.val != 0 then ["-q"] else []
  let startupFlags := if opts.startupFile.val == 2 then ["--startup-file=no"] else []
  let nativeCodeFlags := if opts.useSysimageNativeCode.val == 0
    then ["--sysimage-native-code=no"] else []
  let compressFlags := if opts.compressSysimage.val == 1
    then ["--compress-sysimage=yes"] else []
  pure (compileFlags ++ depwarnFlags ++ checkBoundsFlags ++ inlineFlags ++ compiledModulesFlags ++
    pkgimagesFlags ++ optLevelFlags ++ optLevelMinFlags ++ debugFlags ++ coverageFlags ++
    coverageModeFlags ++ mallocFlags ++ colorFlags ++ quietFlags ++ startupFlags ++
    nativeCodeFlags ++ compressFlags)

/--
Julia source: base/util.jl:148-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.julia_cmd(juliapath=joinpath(Sys.BINDIR, julia_exename()); cpu_target::Union{Nothing,String}=nothing)

Return a julia command similar to the one of the running process.
Propagates any of the `--cpu-target`, `--sysimage`, `--compile`, `--sysimage-native-code`,
`--compiled-modules`, `--pkgimages`, `--inline`, `--check-bounds`, `--optimize`, `--min-optlevel`, `-g`,
`--code-coverage`, `--code-coverage-mode`, `--track-allocation`, `--color`, `--startup-file`,
and `--depwarn` command line arguments that are not at their default values.

Among others, `--math-mode`, `--warn-overwrite`, and `--trace-compile` are notably not propagated currently.

Unless set to `nothing`, the `cpu_target` keyword argument can be used to override the CPU target set for the running process.

To get the julia command without propagated command line arguments, `julia_cmd()[1]` can be used.

!!! compat "Julia 1.1"
    Only the `--cpu-target`, `--sysimage`, `--depwarn`, `--compile` and `--check-bounds` flags were propagated before Julia 1.1.

!!! compat "Julia 1.5"
    The flags `--color` and `--startup-file` were added in Julia 1.5.

!!! compat "Julia 1.9"
    The keyword argument `cpu_target` was added in 1.9.
    The flag `--pkgimages` was added in Julia 1.9.
"""
function julia_cmd(julia=joinpath(Sys.BINDIR, julia_exename()); cpu_target::Union{Nothing,String} = nothing)
    opts = JLOptions()
    if cpu_target === nothing
        cpu_target = unsafe_string(opts.cpu_target)
    end
    image_file = unsafe_string(opts.image_file)
    addflags = String[]
    let compile = if opts.compile_enabled == JL_OPTIONS_COMPILE_OFF
                      "no"
                  elseif opts.compile_enabled == JL_OPTIONS_COMPILE_ALL
                      "all"
                  elseif opts.compile_enabled == JL_OPTIONS_COMPILE_MIN
                      "min"
                  else
                      "" # default = "yes"
                  end
        isempty(compile) || push!(addflags, "--compile=$compile")
    end
    let depwarn = if opts.depwarn == 1
                      "yes"
                  elseif opts.depwarn == 2
                      "error"
                  else
                      "" # default = "no"
                  end
        isempty(depwarn) || push!(addflags, "--depwarn=$depwarn")
    end
    let check_bounds = if opts.check_bounds == 1
                      "yes" # on
                  elseif opts.check_bounds == 2
                      "no" # off
                  else
                      "" # default = "auto"
                  end
        isempty(check_bounds) || push!(addflags, "--check-bounds=$check_bounds")
    end
    opts.can_inline == 0 && push!(addflags, "--inline=no")
    opts.use_compiled_modules == 0 && push!(addflags, "--compiled-modules=no")
    opts.use_compiled_modules == 2 && push!(addflags, "--compiled-modules=existing")
    opts.use_compiled_modules == 3 && push!(addflags, "--compiled-modules=strict")
    opts.use_pkgimages == 0 && push!(addflags, "--pkgimages=no")
    opts.use_pkgimages == 2 && push!(addflags, "--pkgimages=existing")
    opts.opt_level == 2 || push!(addflags, "-O$(opts.opt_level)")
    opts.opt_level_min == 0 || push!(addflags, "--min-optlevel=$(opts.opt_level_min)")
    push!(addflags, "-g$(opts.debug_level)")
    if opts.code_coverage != 0
        # Forward the code-coverage flag only if applicable (if the filename is pid-dependent)
        coverage_file = (opts.output_code_coverage != C_NULL) ?  unsafe_string(opts.output_code_coverage) : ""
        if isempty(coverage_file) || occursin("%p", coverage_file)
            if opts.code_coverage == 1
                push!(addflags, "--code-coverage=user")
            elseif opts.code_coverage == 2
                push!(addflags, "--code-coverage=all")
            elseif opts.code_coverage == 3
                push!(addflags, "--code-coverage=@$(unsafe_string(opts.tracked_path))")
            end
            isempty(coverage_file) || push!(addflags, "--code-coverage=$coverage_file")
        end
    end
    opts.code_coverage_mode == 1 && push!(addflags, "--code-coverage-mode=count")
    if opts.malloc_log == 1
        push!(addflags, "--track-allocation=user")
    elseif opts.malloc_log == 2
        push!(addflags, "--track-allocation=all")
    elseif opts.malloc_log == 3
        push!(addflags, "--track-allocation=@$(unsafe_string(opts.tracked_path))")
    end
    if opts.color == 1
        push!(addflags, "--color=yes")
    elseif opts.color == 2
        push!(addflags, "--color=no")
    end
    if opts.quiet != 0
        push!(addflags, "-q")
    end
    if opts.startupfile == 2
        push!(addflags, "--startup-file=no")
    end
    if opts.use_sysimage_native_code == 0
        push!(addflags, "--sysimage-native-code=no")
    end
    if opts.compress_sysimage == 1
        push!(addflags, "--compress-sysimage=yes")
    end
    return `$julia -C $cpu_target -J$image_file $addflags`
end
```
-/
def juliaCmd {CStr Executable Cmd : Type}
    (ops : JuliaCmdOps CStr Executable Cmd) (opts : JuliaCmdOptions CStr)
    (julia : Option Executable := none) (cpuTarget : Option String := none) : Jl Cmd := do
  let executable ← match julia with
    | some executable => pure executable
    | none => pure (ops.fromPath (ops.joinpath ops.sysBinDir
        (juliaExenameModel ops.windows ops.debugBuild)))
  let cpuTarget ← match cpuTarget with
    | some cpuTarget => pure cpuTarget
    | none => ops.unsafeString opts.cpuTarget
  let imageFile ← ops.unsafeString opts.imageFile
  let flags ← juliaCmdFlags ops opts
  pure (ops.command executable (["-C", cpuTarget, "-J" ++ imageFile] ++ flags))

/--
Julia source: base/util.jl:260-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function julia_exename()
    if !isdebugbuild()
        return @static Sys.iswindows() ? "julia.exe" : "julia"
    else
        return @static Sys.iswindows() ? "julia-debug.exe" : "julia-debug"
    end
end
```
-/
def juliaExename (windows debugBuild : Bool) : String :=
  juliaExenameModel windows debugBuild

-- This operation preserves the result of the body and lets cleanup errors take precedence.
def utilFinally {m : Type → Type} [Monad m] {E A : Type} [MonadExceptOf E m]
    (action : m A) (cleanup : m Unit) : m A := do
  let result : Except E A ← tryCatch (do
      let value ← action
      pure (Except.ok value)) (fun error => pure (Except.error error))
  cleanup
  match result with
  | .ok value => pure value
  | .error error => throw error

-- UNTRANSLATED
-- Reason: The generic function declaration has no body; its concrete methods are modeled below.
-- Source: base/util.jl:268-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     securezero!(o)
-- 
-- `securezero!` fills the memory associated with an object `o` with zeros.
-- Unlike `fill!(o,0)` and similar code, which might be optimized away by
-- the compiler for objects about to be discarded, the `securezero!` function
-- will always be called.
-- """
-- function securezero! end
-- /Source
/--
Julia source: base/util.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline securezero!(a::AbstractArray{<:Number}) = fill!(a, 0)
```
-/
def securezeroArray {A : Type} (fill : A → I64 → Jl A) (array : A) : Jl A :=
  fill array (JInt.lit .i64 0)

structure SecurezeroOps (Ptr Ptr8 N Size : Type) where
  one : N
  elementSize : Nat
  byteCount : N → Nat → Jl Size
  memset : Ptr → JInt .u8 → Size → Jl Ptr
  toBytePointer : Ptr → Ptr8
  fromBytePointer : Ptr8 → Ptr
  zeroBytePointer : Ptr8 → N → Jl Ptr8

/--
Julia source: base/util.jl:278-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline unsafe_securezero!(p::Ptr{T}, len::Integer=1) where {T} =
    memset(p, 0, len*sizeof(T))
```
-/
def unsafeSecurezero {Ptr Ptr8 N Size : Type} (ops : SecurezeroOps Ptr Ptr8 N Size)
    (pointer : Ptr) (len : N := ops.one) : Jl Ptr := do
  let byteCount ← ops.byteCount len ops.elementSize
  ops.memset pointer (JInt.lit .u8 0) byteCount

/--
Julia source: base/util.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_securezero!(p::Ptr{Cvoid}, len::Integer=1) = Ptr{Cvoid}(unsafe_securezero!(Ptr{UInt8}(p), len))
```
-/
def unsafeSecurezeroVoid {Ptr Ptr8 N Size : Type} (ops : SecurezeroOps Ptr Ptr8 N Size)
    (pointer : Ptr) (len : N := ops.one) : Jl Ptr := do
  let bytePointer := ops.toBytePointer pointer
  let zeroed ← ops.zeroBytePointer bytePointer len
  pure (ops.fromBytePointer zeroed)

/--
Julia source: base/util.jl:309-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Note, this helper only works within `with_raw_tty()` on POSIX platforms!
function _getch()
    @static if Sys.iswindows()
        return UInt8(ccall(:_getch, Cint, ()))
    else
        return read(stdin, UInt8)
    end
end

```
-/
def getch {World : Type} (windows : Bool)
    (windowsGetch : JuliaLean.base.io.M World UInt8)
    (stdinRead : JuliaLean.base.io.M World UInt8) : JuliaLean.base.io.M World UInt8 :=
  if windows then windowsGetch else stdinRead

/--
Julia source: base/util.jl:318-320 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const termios_size = Int(ccall(:jl_termios_size, Cint, ()))
make_termios() = zeros(UInt8, termios_size)

```
-/
def makeTermios {Termios : Type} (termiosSize : I64)
    (zeros : I64 → Jl Termios) : Jl Termios :=
  zeros termiosSize

inductive TCSETATTRFlags where
  | now
  | drain
  | flush
  deriving DecidableEq, Repr

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:321-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# These values seem to hold on all OSes we care about:
# glibc Linux, musl Linux, macOS, FreeBSD
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2

```
-/
def tcsetattrFlagCode : TCSETATTRFlags → I32
  | .now => JInt.lit .i32 0
  | .drain => JInt.lit .i32 1
  | .flush => JInt.lit .i32 2
/--
Base `Enums.jl:17`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagBaseType : IntTy := .i32

/--
Base `Enums.jl:221-224`; `membershiptest` is `Enums.jl:79-87`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagFromInteger {I : Type}
    (atLeastZero : I32 → I → Bool) (atMostTwo : I → I32 → Bool)
    (convert : I → Jl I32) (showInteger : I → String) (x : I) : Jl TCSETATTRFlags :=
  if !atLeastZero (JInt.lit .i32 0) x then
    .error (.argumentError ("invalid value for Enum TCSETATTR_FLAGS: " ++ showInteger x))
  else if !atMostTwo x (JInt.lit .i32 2) then
    .error (.argumentError ("invalid value for Enum TCSETATTR_FLAGS: " ++ showInteger x))
  else do
    let code ← convert x
    match code.val with
    | 0 => pure .now
    | 1 => pure .drain
    | 2 => pure .flush
    | _ => .error (.argumentError ("invalid value for Enum TCSETATTR_FLAGS: " ++ showInteger x))

/--
Base `Enums.jl:19`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagConvert {Target : Type} (convert : I32 → Jl Target)
    (x : TCSETATTRFlags) : Jl Target :=
  convert (tcsetattrFlagCode x)

/--
Base `Enums.jl:20`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagCconvert {M : Type → Type} {A : Type}
    (convert : I32 → M A) (x : TCSETATTRFlags) : M A :=
  convert (tcsetattrFlagCode x)

/--
Base `Enums.jl:21`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagWrite {Io Result : Type} {M : Type → Type}
    (writeInteger : Io → I32 → M Result) (io : Io) (x : TCSETATTRFlags) : M Result :=
  writeInteger io (tcsetattrFlagCode x)

/--
Base `Enums.jl:22`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagRead {Io : Type} {M : Type → Type} [Monad M]
    (readInteger : Io → M I32) (construct : I32 → M TCSETATTRFlags)
    (io : Io) : M TCSETATTRFlags := do
  let code ← readInteger io
  construct code

/--
Base `Enums.jl:32`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagIsless (x y : TCSETATTRFlags) : Bool :=
  JuliaLean.base.int.ltSame (tcsetattrFlagCode x) (tcsetattrFlagCode y)

/--
Base `Enums.jl:30, 233-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagEnumHash (typeHash : JInt .u64)
    (hashInteger : I32 → JInt .u64 → JInt .u64)
    (hashUInt : JInt .u64 → JInt .u64 → JInt .u64)
    (x : TCSETATTRFlags) (h : JInt .u64) : JInt .u64 :=
  hashUInt typeHash (hashInteger (tcsetattrFlagCode x) h)

/--
Base `Enums.jl:225`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagNameMap : List (I32 × String) :=
  [(JInt.lit .i32 0, "TCSANOW"), (JInt.lit .i32 1, "TCSADRAIN"),
   (JInt.lit .i32 2, "TCSAFLUSH")]

/--
Base `Enums.jl:226`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagTypemin : TCSETATTRFlags := .now

/--
Base `Enums.jl:227`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagTypemax : TCSETATTRFlags := .flush

/--
Base `Enums.jl:235-237`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagInstances : List TCSETATTRFlags := [.now, .drain, .flush]

/--
Base `Enums.jl:34`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagSymbol (x : TCSETATTRFlags) : String :=
  match x with
  | .now => "TCSANOW"
  | .drain => "TCSADRAIN"
  | .flush => "TCSAFLUSH"

/--
Base `Enums.jl:36-40`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagInternalSymbol (code : I32) : String :=
  match tcsetattrFlagNameMap.find? (fun (value, _) => value.val == code.val) with
  | some (_, name) => name
  | none => "<invalid #" ++ toString code.val ++ ">"

/--
Base `Enums.jl:42`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagPrint {m : Type → Type} [Monad m] {Io V : Type}
    (p : JuliaLean.base.show.IOPrims m Io V)
    (io : JuliaLean.base.show.JIO Io V) (x : TCSETATTRFlags) : m Unit :=
  JuliaLean.base.show.print_Symbol p io (tcsetattrFlagSymbol x)

/--
Base `Enums.jl:44-55`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagShow {m : Type → Type} {Io V Ty Mod : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (moduleOfValue : V → Except JuliaLean.base.show.ShowError (Option Mod))
    (main parent : Mod) (isvisible : String → Mod → Mod → m Bool)
    (showModule : JuliaLean.base.show.JIO Io V → Mod → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : TCSETATTRFlags) : m Unit := do
  if !(← JuliaLean.base.show.assertBool a (JuliaLean.base.show.getIO p io "compact" false)) then
    let origin ← match JuliaLean.base.show.getIO p io "module" main with
      | .inl value =>
          match moduleOfValue value with
          | .ok module => pure module
          | .error error => JuliaLean.base.show.throwShow error
      | .inr fallback => pure (some fallback)
    let qualify ← match origin with
      | none => pure true
      | some originModule => do
          let visible ← isvisible (tcsetattrFlagSymbol x) parent originModule
          pure !visible
    if qualify then
      showModule io parent
      JuliaLean.base.show.printStr p io "."
  JuliaLean.base.show.print_Symbol p io (tcsetattrFlagSymbol x)

/--
Base `Enums.jl:57-62`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagShowTextPlain {m : Type → Type} {Io V Ty : Type} [Monad m]
    [MonadExceptOf JuliaLean.base.show.ShowError m]
    (p : JuliaLean.base.show.IOPrims m Io V) (a : JuliaLean.base.show.AnyOps V Ty)
    (showType : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → I32 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) (x : TCSETATTRFlags) : m Unit := do
  tcsetattrFlagPrint p io x
  JuliaLean.base.show.printStr p io "::"
  let compactIO ← JuliaLean.base.show.withBool p a io "compact" true
  showType compactIO
  JuliaLean.base.show.printStr p io " = "
  showInteger io (tcsetattrFlagCode x)

/--
Base `Enums.jl:64-75`; macro expansion is `Enums.jl:218-237`.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagShowTypeTextPlain {m : Type → Type} {Io V : Type} [Monad m]
    (p : JuliaLean.base.show.IOPrims m Io V)
    (showDatatype : JuliaLean.base.show.JIO Io V → m Unit)
    (showInteger : JuliaLean.base.show.JIO Io V → I32 → m Unit)
    (io : JuliaLean.base.show.JIO Io V) : m Unit := do
  JuliaLean.base.show.printStr p io "Enum "
  showDatatype io
  JuliaLean.base.show.printStr p io ":"
  for x in tcsetattrFlagInstances do
    JuliaLean.base.show.printStr p io "\n"
    JuliaLean.base.show.print_Symbol p io (tcsetattrFlagSymbol x)
    JuliaLean.base.show.printStr p io " = "
    showInteger io (tcsetattrFlagCode x)

/--
Base `Enums.jl:91`; `Ref` uses the installed `base/refvalue.jl` constructor.
Julia source: base/util.jl:323-323 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@enum TCSETATTR_FLAGS TCSANOW=0 TCSADRAIN=1 TCSAFLUSH=2
```
-/
def tcsetattrFlagBroadcastable {R : Type} (makeRef : TCSETATTRFlags → R)
    (x : TCSETATTRFlags) : R :=
  makeRef x

private def termiosIOError (operation : String) (code : I32) : JuliaLean.base.io.Error :=
  .foreignError "IOError" (operation ++ " (code " ++ toString code.val ++ ")")

/--
Julia source: base/util.jl:325-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tcgetattr(fd::RawFD, termios)
    ret = ccall(:tcgetattr, Cint, (Cint, Ptr{Cvoid}), fd, termios)
    if ret != 0
        throw(IOError("tcgetattr failed", ret))
    end
end
```
-/
def tcgetattr {World Termios : Type}
    (call : I32 → Termios → JuliaLean.base.io.M World I32)
    (fd : I32) (termios : Termios) : JuliaLean.base.io.M World Unit := do
  let result ← call fd termios
  if result.val != 0 then throw (termiosIOError "tcgetattr failed" result)

/--
Julia source: base/util.jl:331-336 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function tcsetattr(fd::RawFD, termios, mode::TCSETATTR_FLAGS = TCSADRAIN)
    ret = ccall(:tcsetattr, Cint, (Cint, Cint, Ptr{Cvoid}), fd, Cint(mode), termios)
    if ret != 0
        throw(IOError("tcsetattr failed", ret))
    end
end
```
-/
def tcsetattr {World Termios : Type}
    (call : I32 → I32 → Termios → JuliaLean.base.io.M World I32)
    (fd : I32) (termios : Termios) (mode : TCSETATTRFlags := .drain) :
    JuliaLean.base.io.M World Unit := do
  let result ← call fd (tcsetattrFlagCode mode) termios
  if result.val != 0 then throw (termiosIOError "tcsetattr failed" result)

/--
Julia source: base/util.jl:337-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
cfmakeraw(termios) = ccall(:cfmakeraw, Cvoid, (Ptr{Cvoid},), termios)
```
-/
def cfmakeraw {World Termios : Type}
    (call : Termios → JuliaLean.base.io.M World Unit) (termios : Termios) :
    JuliaLean.base.io.M World Unit := call termios

structure TermiosOps (World Input Termios : Type) where
  stdin : Input
  isStdin : Input → Bool
  isWindows : Bool
  termiosSize : I64
  makeTermios : I64 → JuliaLean.base.io.M World Termios
  copyTermios : Termios → JuliaLean.base.io.M World Termios
  getAttributes : I32 → Termios → JuliaLean.base.io.M World Unit
  makeRaw : Termios → JuliaLean.base.io.M World Unit
  setAttributes : I32 → Termios → JuliaLean.base.io.M World Unit

/--
Julia source: base/util.jl:339-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function with_raw_tty(f::Function, input::TTY)
    input === stdin || throw(ArgumentError("with_raw_tty only works for stdin"))
    fd = RawFD(0)

    # If we're on windows, we do nothing, as we have access to `_getch()` quite easily
    @static if Sys.iswindows()
        return f()
    end

    # Get the current terminal mode
    old_termios = make_termios()
    tcgetattr(fd, old_termios)
    try
        # Set a new, raw, terminal mode
        new_termios = copy(old_termios)
        cfmakeraw(new_termios)
        tcsetattr(fd, new_termios)

        # Call the user-supplied callback
        f()
    finally
        # Always restore the terminal mode
        tcsetattr(fd, old_termios)
    end
end
```
-/
def withRawTty {World Input Termios A : Type}
    (ops : TermiosOps World Input Termios) (input : Input)
    (f : Unit → JuliaLean.base.io.M World A) : JuliaLean.base.io.M World A := do
  if !ops.isStdin input then throw (.jl (.argumentError "with_raw_tty only works for stdin"))
  else if ops.isWindows then f ()
  else do
    let fd := JInt.lit .i32 0
    let oldTermios ← ops.makeTermios ops.termiosSize
    ops.getAttributes fd oldTermios
    utilFinally (E := JuliaLean.base.io.Error) (do
      let newTermios ← ops.copyTermios oldTermios
      ops.makeRaw newTermios
      ops.setAttributes fd newTermios
      f ()) (ops.setAttributes fd oldTermios)

structure GetpassOps (World Output Secret : Type) where
  print : Output → String → JuliaLean.base.io.M World Unit
  flush : Output → JuliaLean.base.io.M World Unit
  getch : JuliaLean.base.io.M World UInt8
  isControl : Char → Bool
  newSecretBuffer : JuliaLean.base.io.M World Secret
  writeSecretByte : Secret → UInt8 → JuliaLean.base.io.M World Secret
  seekStart : Secret → JuliaLean.base.io.M World Secret

private structure GetpassState (Secret : Type) where
  secret : Secret
  plen : I64

private def getpassLoop {World Output Secret : Type}
    (ops : GetpassOps World Output Secret) (state : GetpassState Secret) :
    JuliaLean.base.io.M World Secret :=
  JuliaLean.base.io.whileLoop (fun state => do
    let c ← ops.getch
    let code := c.toNat
    if code == 0xff || code == 10 || code == 13 || code == 0x04 then
      pure (.inl state.secret)
    else if code == 0x00 || code == 0xe0 then
      let _ ← ops.getch
      pure (.inr state)
    else if code == 8 && state.plen.val > 0 then
      pure (.inr { state with plen := JInt.wrap .i64 (state.plen.val - 1) })
    else if !ops.isControl (Char.ofNat code) && state.plen.val < 128 then
      let secret ← ops.writeSecretByte state.secret c
      pure (.inr { state with secret := secret })
    else
      pure (.inr state)) state

/--
Julia source: base/util.jl:365-388 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getpass(input::TTY, output::IO, prompt::AbstractString; with_suffix::Bool=true)
    input === stdin || throw(ArgumentError("getpass only works for stdin"))
    with_raw_tty(stdin) do
        print(output, prompt)
        with_suffix && print(output, ": ")
        flush(output)

        s = SecretBuffer()
        plen = 0
        while true
            c = _getch()
            if c == 0xff || c == UInt8('\n') || c == UInt8('\r') || c == 0x04
                break # EOF or return
            elseif c == 0x00 || c == 0xe0
                _getch() # ignore function/arrow keys
            elseif c == UInt8('\b') && plen > 0
                plen -= 1 # delete last character on backspace
            elseif !iscntrl(Char(c)) && plen < 128
                write(s, c)
            end
        end
        return seekstart(s)
    end
end
```
-/
def getpass {World Input Output Termios Secret : Type}
    (termiosOps : TermiosOps World Input Termios) (ops : GetpassOps World Output Secret)
    (input : Input) (output : Output) (prompt : String)
    (withSuffix : Bool := true) : JuliaLean.base.io.M World Secret := do
  if !termiosOps.isStdin input then throw (.jl (.argumentError "getpass only works for stdin"))
  withRawTty termiosOps termiosOps.stdin (fun _ => do
    ops.print output prompt
    if withSuffix then ops.print output ": "
    ops.flush output
    let secret ← ops.newSecretBuffer
    let secret ← getpassLoop ops ⟨secret, JInt.lit .i64 0⟩
    ops.seekStart secret)

/--
Julia source: base/util.jl:390-392 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# allow new getpass methods to be defined if stdin has been
# redirected to some custom stream, e.g. in IJulia.
getpass(prompt::AbstractString; with_suffix::Bool=true) = getpass(stdin, stdout, prompt; with_suffix)
```
-/
def getpassStdin {World Input Output Termios Secret : Type}
    (termiosOps : TermiosOps World Input Termios) (ops : GetpassOps World Output Secret)
    (stdout : Output) (prompt : String) (withSuffix : Bool := true) :
    JuliaLean.base.io.M World Secret :=
  getpass termiosOps ops termiosOps.stdin stdout prompt withSuffix

structure PromptOps (World Input Output S : Type) where
  stdin : Input
  stdout : Output
  isEmpty : S → Bool
  toBytes : S → List UInt8
  printBytes : Output → List UInt8 → JuliaLean.base.io.M World Unit
  readlineKeep : Input → JuliaLean.base.io.M World S
  chomp : S → S
  empty : S

/--
Julia source: base/util.jl:394-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    prompt(message; default="")::Union{String, Nothing}

Displays the `message` then waits for user input. Input is terminated when a newline (\\n)
is encountered or EOF (^D) character is entered on a blank line. If a `default` is provided
then the user can enter just a newline character to select the `default`.

See also `Base.winprompt` (for Windows) and `Base.getpass` for secure entry of passwords.

# Examples

```julia-repl
julia> your_name = Base.prompt("Enter your name");
Enter your name: Logan

julia> your_name
"Logan"
```
"""
function prompt(input::IO, output::IO, message::AbstractString; default::AbstractString="")
    msg = !isempty(default) ? "$message [$default]: " : "$message: "
    print(output, msg)
    uinput = readline(input, keep=true)
    isempty(uinput) && return nothing  # Encountered an EOF
    uinput = chomp(uinput)
    isempty(uinput) ? default : uinput
end
````
-/
def prompt {World Input Output S : Type}
    (ops : PromptOps World Input Output S) (input : Input) (output : Output)
    (message : S) (default : S := ops.empty) : JuliaLean.base.io.M World (Option S) := do
  let messageBytes := ops.toBytes message
  let text := if !ops.isEmpty default then
    messageBytes ++ " [".toUTF8.toList ++ ops.toBytes default ++ "]: ".toUTF8.toList
    else messageBytes ++ ": ".toUTF8.toList
  ops.printBytes output text
  let userInput ← ops.readlineKeep input
  if ops.isEmpty userInput then pure none
  else
    let userInput := ops.chomp userInput
    pure (some (if ops.isEmpty userInput then default else userInput))

/--
Julia source: base/util.jl:422-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# allow new prompt methods to be defined if stdin has been
# redirected to some custom stream, e.g. in IJulia.
prompt(message::AbstractString; default::AbstractString="") = prompt(stdin, stdout, message, default=default)
```
-/
def promptStdin {World Input Output S : Type}
    (ops : PromptOps World Input Output S) (message : S) (default : S := ops.empty) :
    JuliaLean.base.io.M World (Option S) :=
  prompt ops ops.stdin ops.stdout message default

-- UNTRANSLATED
-- Reason: the Windows-only CREDUI structure and constants are ABI declarations, not Julia methods.
-- Source: base/util.jl:426-444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Windows authentication prompt
-- if Sys.iswindows()
--     struct CREDUI_INFO
--         cbSize::UInt32
--         parent::Ptr{Cvoid}
--         pszMessageText::Ptr{UInt16}
--         pszCaptionText::Ptr{UInt16}
--         banner::Ptr{Cvoid}
--     end
-- 
--     const CREDUIWIN_GENERIC                 = 0x0001
--     const CREDUIWIN_IN_CRED_ONLY            = 0x0020
--     const CREDUIWIN_ENUMERATE_CURRENT_USER  = 0x0200
-- 
--     const CRED_PACK_GENERIC_CREDENTIALS     = 0x0004
-- 
--     const ERROR_SUCCESS                     = 0x0000
--     const ERROR_CANCELLED                   = 0x04c7
-- 
-- /Source

/-- Fields of the Windows `CREDUI_INFO` structure passed to the credential dialog. -/
structure CredUIInfo (Ptr : Type) where
  cbSize : U32
  parent : Ptr
  message : Ptr
  caption : Ptr
  banner : Ptr

/-- Typed Windows API, buffer, conversion, and `SecretBuffer` operations used by `winprompt`.
The credential API operations correspond to `CredPackAuthenticationBufferW`,
`CredUIPromptForWindowsCredentialsW`, `CredUnPackAuthenticationBufferW`, and `CoTaskMemFree`.
`toWideString`, `transcodeUtf16`, `windowserror`, and the SecretBuffer callbacks bind to their
installed Base models. -/
structure WinPromptOps
    (World Wide Ptr CredInfoRef ByteVector U16Vector U32Ref BoolRef CULong CULongRef
      PtrRef Memory Ptr8 Size : Type) where
  toWideString : {Input : Type} → Input → JuliaLean.base.io.M World Wide
  emptyWideString : JuliaLean.base.io.M World Wide
  nullPointer : Ptr
  wideStringPointer : Wide → Ptr
  credUIInfoSize : U32
  newCredUIInfoRef : CredUIInfo Ptr → JuliaLean.base.io.M World CredInfoRef
  newByteVector : Nat → JuliaLean.base.io.M World ByteVector
  byteVectorSize : ByteVector → JuliaLean.base.io.M World U32
  resizeByteVector : ByteVector → U32 → JuliaLean.base.io.M World ByteVector
  byteVectorPointer : ByteVector → Ptr
  newUInt32Ref : U32 → JuliaLean.base.io.M World U32Ref
  readUInt32Ref : U32Ref → JuliaLean.base.io.M World U32
  credPackAuthenticationBuffer :
    U32 → Wide → Wide → Ptr → U32Ref → JuliaLean.base.io.M World Bool
  newBoolRef : Bool → JuliaLean.base.io.M World BoolRef
  newCULongRef : Unit → JuliaLean.base.io.M World CULongRef
  readCULongRef : CULongRef → JuliaLean.base.io.M World CULong
  newPtrRef : Ptr → JuliaLean.base.io.M World PtrRef
  readPtrRef : PtrRef → JuliaLean.base.io.M World Ptr
  credUIPromptForWindowsCredentials :
    CredInfoRef → U32 → CULongRef → Ptr → U32 → PtrRef → CULongRef → BoolRef → U32 →
      JuliaLean.base.io.M World U32
  credUnPackAuthenticationBuffer :
    U32 → Ptr → CULong → Ptr → U32Ref → Ptr → U32Ref → Ptr → U32Ref →
      JuliaLean.base.io.M World Bool
  newU16Vector : Nat → JuliaLean.base.io.M World U16Vector
  u16VectorPointer : U16Vector → Ptr
  /-- Copy the one-based slice `a[1:endIndex]`; `endIndex` is the wrapped UInt32 expression
  from Julia, so zero yields the empty slice. -/
  sliceU16Vector : U16Vector → U32 → JuliaLean.base.io.M World U16Vector
  /-- `transcode(UInt8, units)`, returning the mutable byte vector consumed by `SecretBuffer!`. -/
  transcodeUtf16 : U16Vector → JuliaLean.base.io.M World ByteVector
  byteVectorBytes : ByteVector → JuliaLean.base.io.M World (List UInt8)
  secretByteVectorOps : JuliaLean.base.secretbuffer.ByteVectorOps ByteVector
  newSecretBuffer : I64 →
    Except JuliaLean.base.iobuffer.IOErr
      (JuliaLean.base.secretbuffer.SecretBuffer Memory)
  writeSecretBufferByte :
    JuliaLean.base.secretbuffer.SecretBuffer Memory → UInt8 →
      Except JuliaLean.base.iobuffer.IOErr
        (JuliaLean.base.secretbuffer.SecretBuffer Memory × I64)
  seekSecretBuffer :
    JuliaLean.base.secretbuffer.SecretBuffer Memory → I64 →
      Except JuliaLean.base.iobuffer.IOErr
        (JuliaLean.base.secretbuffer.SecretBuffer Memory)
  /-- `securezero!(::AbstractArray{<:Number})` for the temporary UInt16 vectors. -/
  securezeroU16Vector : U16Vector → JuliaLean.base.io.M World Unit
  securezero : SecurezeroOps Ptr Ptr8 CULong Size
  coTaskMemFree : Ptr → JuliaLean.base.io.M World Unit
  /-- `windowserror(:winprompt, failed)`, including the current Windows error code. -/
  windowserror : String → Bool → JuliaLean.base.io.M World Unit

private def liftSecretBufferIOErr {World A : Type}
    (result : Except JuliaLean.base.iobuffer.IOErr A) :
    JuliaLean.base.io.M World A :=
  match result with
  | .ok value => pure value
  | .error error => throw (JuliaLean.base.iobuffer.genericIOError error)

/--
Julia source: base/util.jl:445-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function winprompt(message, caption, default_username; prompt_username = true)
        # Step 1: Create an encrypted username/password bundle that will be used to set
        #         the default username (in theory could also provide a default password)
        credbuf = Vector{UInt8}(undef, 1024)
        credbufsize = Ref{UInt32}(sizeof(credbuf))
        succeeded = ccall((:CredPackAuthenticationBufferW, "credui.dll"), stdcall, Bool,
            (UInt32, Cwstring, Cwstring, Ptr{UInt8}, Ptr{UInt32}),
             CRED_PACK_GENERIC_CREDENTIALS, default_username, "", credbuf, credbufsize)
        if !succeeded
            credbuf = resize!(credbuf, credbufsize[])
            succeeded = ccall((:CredPackAuthenticationBufferW, "credui.dll"), stdcall, Bool,
                (UInt32, Cwstring, Cwstring, Ptr{UInt8}, Ptr{UInt32}),
                 CRED_PACK_GENERIC_CREDENTIALS, default_username, "", credbuf, credbufsize)
            @assert succeeded
        end

        # Step 2: Create the actual dialog
        #      2.1: Set up the window
        messageArr = Base.cwstring(message)
        captionArr = Base.cwstring(caption)
        pfSave = Ref{Bool}(false)
        cred = Ref{CREDUI_INFO}(CREDUI_INFO(sizeof(CREDUI_INFO), C_NULL, pointer(messageArr), pointer(captionArr), C_NULL))
        dwflags = CREDUIWIN_GENERIC | CREDUIWIN_ENUMERATE_CURRENT_USER
        if !prompt_username
            # Disable setting anything other than default_username
            dwflags |= CREDUIWIN_IN_CRED_ONLY
        end
        authPackage = Ref{Culong}(0)
        outbuf_data = Ref{Ptr{Cvoid}}(C_NULL)
        outbuf_size = Ref{Culong}(0)

        #      2.2: Do the actual request
        code = ccall((:CredUIPromptForWindowsCredentialsW, "credui.dll"), stdcall, UInt32, (Ptr{CREDUI_INFO}, UInt32, Ptr{Culong},
            Ptr{Cvoid}, Culong, Ptr{Ptr{Cvoid}}, Ptr{Culong}, Ptr{Bool}, UInt32), cred, 0, authPackage, credbuf, credbufsize[],
            outbuf_data, outbuf_size, pfSave, dwflags)

        #      2.3: If that failed for any reason other than the user canceling, error out.
        #           If the user canceled, just return nothing
        code == ERROR_CANCELLED && return nothing
        windowserror(:winprompt, code != ERROR_SUCCESS)

        # Step 3: Convert encrypted credentials back to plain text
        passbuf = Vector{UInt16}(undef, 1024)
        passlen = Ref{UInt32}(length(passbuf))
        usernamebuf = Vector{UInt16}(undef, 1024)
        usernamelen = Ref{UInt32}(length(usernamebuf))
        # Need valid buffers for domain, even though we don't care
        dummybuf = Vector{UInt16}(undef, 1024)
        succeeded = ccall((:CredUnPackAuthenticationBufferW, "credui.dll"), Bool,
            (UInt32, Ptr{Cvoid}, UInt32, Ptr{UInt16}, Ptr{UInt32}, Ptr{UInt16}, Ptr{UInt32}, Ptr{UInt16}, Ptr{UInt32}),
            0, outbuf_data[], outbuf_size[], usernamebuf, usernamelen, dummybuf, Ref{UInt32}(1024), passbuf, passlen)
        windowserror(:winprompt, !succeeded)

        # Step 4: Free the encrypted buffer
        # ccall(:SecureZeroMemory, Ptr{Cvoid}, (Ptr{Cvoid}, Csize_t), outbuf_data[], outbuf_size[]) - not an actual function
        unsafe_securezero!(outbuf_data[], outbuf_size[])
        ccall((:CoTaskMemFree, "ole32.dll"), Cvoid, (Ptr{Cvoid},), outbuf_data[])

        # Done.
        passbuf_ = passbuf[1:passlen[]-1]
        result = (String(transcode(UInt8, usernamebuf[1:usernamelen[]-1])),
                  SecretBuffer!(transcode(UInt8, passbuf_)))
        securezero!(passbuf_)
        securezero!(passbuf)

        return result
    end
```
-/
def winprompt
    {World Wide Ptr CredInfoRef ByteVector U16Vector U32Ref BoolRef CULong CULongRef
      PtrRef Memory Ptr8 Size Message Caption Username : Type}
    (ops : WinPromptOps World Wide Ptr CredInfoRef ByteVector U16Vector U32Ref BoolRef CULong
      CULongRef PtrRef Memory Ptr8 Size)
    (message : Message) (caption : Caption) (defaultUsername : Username)
    (promptUsername : Bool := true) :
    JuliaLean.base.io.M World
      (Option (JuliaLean.base.iobuffer.JuliaString ×
        JuliaLean.base.secretbuffer.SecretBuffer Memory)) := do
  let mut credentialBuffer ← ops.newByteVector 1024
  let credentialBufferBytes ← ops.byteVectorSize credentialBuffer
  let credentialBufferSize ← ops.newUInt32Ref credentialBufferBytes
  let mut packed ← do
    let username ← ops.toWideString defaultUsername
    let emptyPassword ← ops.emptyWideString
    ops.credPackAuthenticationBuffer (JInt.lit .u32 0x0004) username emptyPassword
      (ops.byteVectorPointer credentialBuffer) credentialBufferSize
  if !packed then
    credentialBuffer ← ops.resizeByteVector credentialBuffer
      (← ops.readUInt32Ref credentialBufferSize)
    let username ← ops.toWideString defaultUsername
    let emptyPassword ← ops.emptyWideString
    packed ← ops.credPackAuthenticationBuffer (JInt.lit .u32 0x0004) username emptyPassword
      (ops.byteVectorPointer credentialBuffer) credentialBufferSize
    if !packed then throw (.foreignError "AssertionError" "succeeded")
  let messageWide ← ops.toWideString message
  let captionWide ← ops.toWideString caption
  let saveFlag ← ops.newBoolRef false
  let credentialInfo ← ops.newCredUIInfoRef
    ⟨ops.credUIInfoSize, ops.nullPointer, ops.wideStringPointer messageWide,
      ops.wideStringPointer captionWide, ops.nullPointer⟩
  let dialogFlags := JInt.lit .u32 (if promptUsername then 0x0201 else 0x0221)
  let authPackage ← ops.newCULongRef ()
  let outputData ← ops.newPtrRef ops.nullPointer
  let outputSize ← ops.newCULongRef ()
  let code ← ops.credUIPromptForWindowsCredentials credentialInfo (JInt.lit .u32 0)
    authPackage (ops.byteVectorPointer credentialBuffer)
    (← ops.readUInt32Ref credentialBufferSize) outputData outputSize saveFlag dialogFlags
  if code.val == 0x04c7 then
    pure none
  else do
    ops.windowserror "winprompt" (code.val != 0)
    let passBuffer ← ops.newU16Vector 1024
    let passLength ← ops.newUInt32Ref (JInt.lit .u32 1024)
    let usernameBuffer ← ops.newU16Vector 1024
    let usernameLength ← ops.newUInt32Ref (JInt.lit .u32 1024)
    let dummyBuffer ← ops.newU16Vector 1024
    let dummyLength ← ops.newUInt32Ref (JInt.lit .u32 1024)
    let outputPointer ← ops.readPtrRef outputData
    let outputBytes ← ops.readCULongRef outputSize
    let unpacked ← ops.credUnPackAuthenticationBuffer (JInt.lit .u32 0) outputPointer
      outputBytes (ops.u16VectorPointer usernameBuffer) usernameLength
      (ops.u16VectorPointer dummyBuffer) dummyLength
      (ops.u16VectorPointer passBuffer) passLength
    ops.windowserror "winprompt" !unpacked
    let _ ← JuliaLean.base.io.liftJl
      (unsafeSecurezeroVoid ops.securezero outputPointer outputBytes)
    ops.coTaskMemFree outputPointer
    let passEnd := JuliaLean.base.int.sub_int
      (← ops.readUInt32Ref passLength) (JInt.lit .u32 1)
    let passSlice ← ops.sliceU16Vector passBuffer passEnd
    let usernameEnd := JuliaLean.base.int.sub_int
      (← ops.readUInt32Ref usernameLength) (JInt.lit .u32 1)
    let usernameSlice ← ops.sliceU16Vector usernameBuffer usernameEnd
    let usernameBytes ← ops.transcodeUtf16 usernameSlice
    let username ← ops.byteVectorBytes usernameBytes
    let passBytes ← ops.transcodeUtf16 passSlice
    let password ← liftSecretBufferIOErr
      (JuliaLean.base.secretbuffer.secretBufferFromVectorBang ops.secretByteVectorOps
        ops.newSecretBuffer ops.writeSecretBufferByte ops.seekSecretBuffer passBytes)
    ops.securezeroU16Vector passSlice
    ops.securezeroU16Vector passBuffer
    pure (some (⟨username⟩, password))

-- UNTRANSLATED
-- Reason: closes the Windows-only conditional; it does not define a Julia method.
-- Source: base/util.jl:512-514 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- end
-- 
-- /Source
structure Crc32cOps (Ptr : Type) where
  toCsize : I64 → Jl (JInt .u64)
  runtime : U32 → Ptr → JInt .u64 → U32

/--
Julia source: base/util.jl:515-515 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_crc32c(a, n, crc) = ccall(:jl_crc32c, UInt32, (UInt32, Ptr{UInt8}, Csize_t), crc, a, n)
```
-/
def unsafeCrc32c {Ptr : Type} (ops : Crc32cOps Ptr)
    (data : Ptr) (count : JInt .u64) (crc : U32) : U32 :=
  ops.runtime crc data count

/--
Julia source: base/util.jl:517-518 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(a::NTuple{<:Any, UInt8}, crc::UInt32=0x00000000) =
    unsafe_crc32c(Ref(a), length(a) % Csize_t, crc)
```
-/
def crc32cTuple {A Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : A → Ptr) (length : A → I64) (tuple : A)
    (crc : U32 := JInt.lit .u32 0) : Jl U32 := do
  let count ← ops.toCsize (length tuple)
  pure (unsafeCrc32c ops (ref tuple) count crc)

/--
Julia source: base/util.jl:520-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _crc32c(a::DenseUInt8OrInt8, crc::UInt32=0x00000000)
    unsafe_crc32c(a, length(a) % Csize_t, crc)
end
```
-/
def crc32cDenseVector {A Ptr : Type} (ops : Crc32cOps Ptr)
    (pointer : A → Ptr) (length : A → I64) (array : A)
    (crc : U32 := JInt.lit .u32 0) : Jl U32 := do
  let count ← ops.toCsize (length array)
  pure (unsafeCrc32c ops (pointer array) count crc)

/--
Julia source: base/util.jl:524-526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _crc32c(s::Union{String, SubString{String}}, crc::UInt32=0x00000000)
    unsafe_crc32c(s, sizeof(s) % Csize_t, crc)
end
```
-/
def crc32cString {S Ptr : Type} (ops : Crc32cOps Ptr)
    (pointer : S → Ptr) (sizeOf : S → I64) (string : S)
    (crc : U32 := JInt.lit .u32 0) : Jl U32 := do
  let count ← ops.toCsize (sizeOf string)
  pure (unsafeCrc32c ops (pointer string) count crc)

structure CrcIOOps (World Io Buffer N : Type) where
  isNegative : N → Bool
  showCount : N → String
  greaterThan : N → Nat → Bool
  minBuffer : N → Nat → N
  minRead : N → I64 → N
  subtractRead : N → I64 → N
  newBuffer : N → JuliaLean.base.io.M World Buffer
  eof : Io → JuliaLean.base.io.M World Bool
  readAll : Io → Buffer → JuliaLean.base.io.M World I64
  readCount : Io → Buffer → N → JuliaLean.base.io.M World I64
  bufferLength : Buffer → I64
  crcBuffer : Buffer → I64 → U32 → JuliaLean.base.io.M World U32
  fileSize : Io → JuliaLean.base.io.M World I64
  position : Io → JuliaLean.base.io.M World I64

/--
Julia source: base/util.jl:528-539 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _crc32c(io::IO, nb::Integer, crc::UInt32=0x00000000)
    nb < 0 && throw(ArgumentError("number of bytes to checksum must be ≥ 0, got $nb"))
    # use block size 24576=8192*3, since that is the threshold for
    # 3-way parallel SIMD code in the underlying jl_crc32c C function.
    buf = Vector{UInt8}(undef, min(nb, 24576))
    while !eof(io) && nb > 24576
        n = readbytes!(io, buf)
        crc = unsafe_crc32c(buf, n, crc)
        nb -= n
    end
    return unsafe_crc32c(buf, readbytes!(io, buf, min(nb, length(buf))), crc)
end
```
-/
def crc32cIO {World Io Buffer N : Type}
    (ops : CrcIOOps World Io Buffer N) (io : Io) (nb : N)
    (crc : U32 := JInt.lit .u32 0) : JuliaLean.base.io.M World U32 := do
  if ops.isNegative nb then
    throw (.jl (.argumentError ("number of bytes to checksum must be ≥ 0, got " ++
      ops.showCount nb)))
  let buffer ← ops.newBuffer (ops.minBuffer nb 24576)
  let (nb, crc) ← JuliaLean.base.io.whileLoop (fun (nb, crc) => do
    if !(← ops.eof io) && ops.greaterThan nb 24576 then do
      let count ← ops.readAll io buffer
      let crc ← ops.crcBuffer buffer count crc
      pure (.inr (ops.subtractRead nb count, crc))
    else
      pure (.inl (nb, crc))) (nb, crc)
  let count ← ops.readCount io buffer (ops.minRead nb (ops.bufferLength buffer))
  ops.crcBuffer buffer count crc

/--
Julia source: base/util.jl:540-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(io::IO, crc::UInt32=0x00000000) = _crc32c(io, typemax(Int64), crc)
```
-/
def crc32cIODefault {World Io Buffer : Type}
    (ops : CrcIOOps World Io Buffer I64) (io : Io)
    (crc : U32 := JInt.lit .u32 0) : JuliaLean.base.io.M World U32 :=
  crc32cIO ops io (JInt.typemax .i64) crc

/--
Julia source: base/util.jl:541-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(io::IOStream, crc::UInt32=0x00000000) = _crc32c(io, filesize(io)-position(io), crc)
```
-/
def crc32cIOStream {World Io Buffer : Type}
    (ops : CrcIOOps World Io Buffer I64) (io : Io)
    (crc : U32 := JInt.lit .u32 0) : JuliaLean.base.io.M World U32 := do
  let size ← ops.fileSize io
  let position ← ops.position io
  crc32cIO ops io (size - position) crc

private def crc32cNative {T Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : T → Ptr) (byteCount : Nat) (value : T) (crc : U32) : U32 :=
  unsafeCrc32c ops (ref value) (JInt.lit .u64 byteCount) crc

/--
Julia source: base/util.jl:542-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(x::UInt128, crc::UInt32=0x00000000) =
    ccall(:jl_crc32c, UInt32, (UInt32, Ref{UInt128}, Csize_t), crc, x, 16)
```
-/
def crc32cUInt128 {Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : JInt .u128 → Ptr) (value : JInt .u128)
    (crc : U32 := JInt.lit .u32 0) : U32 :=
  crc32cNative ops ref 16 value crc

/--
Julia source: base/util.jl:544-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(x::UInt64, crc::UInt32=0x00000000) =
    ccall(:jl_crc32c, UInt32, (UInt32, Ref{UInt64}, Csize_t), crc, x, 8)
```
-/
def crc32cUInt64 {Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : JInt .u64 → Ptr) (value : JInt .u64)
    (crc : U32 := JInt.lit .u32 0) : U32 :=
  crc32cNative ops ref 8 value crc

/--
Julia source: base/util.jl:546-547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(x::UInt32, crc::UInt32=0x00000000) =
    ccall(:jl_crc32c, UInt32, (UInt32, Ref{UInt32}, Csize_t), crc, x, 4)
```
-/
def crc32cUInt32 {Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : JInt .u32 → Ptr) (value : JInt .u32)
    (crc : U32 := JInt.lit .u32 0) : U32 :=
  crc32cNative ops ref 4 value crc

/--
Julia source: base/util.jl:548-549 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(x::UInt16, crc::UInt32=0x00000000) =
    ccall(:jl_crc32c, UInt32, (UInt32, Ref{UInt16}, Csize_t), crc, x, 2)
```
-/
def crc32cUInt16 {Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : JInt .u16 → Ptr) (value : JInt .u16)
    (crc : U32 := JInt.lit .u32 0) : U32 :=
  crc32cNative ops ref 2 value crc

/--
Julia source: base/util.jl:550-551 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_crc32c(x::UInt8, crc::UInt32=0x00000000) =
    ccall(:jl_crc32c, UInt32, (UInt32, Ref{UInt8}, Csize_t), crc, x, 1)
```
-/
def crc32cUInt8 {Ptr : Type} (ops : Crc32cOps Ptr)
    (ref : JInt .u8 → Ptr) (value : JInt .u8)
    (crc : U32 := JInt.lit .u32 0) : U32 :=
  crc32cNative ops ref 1 value crc

-- Reason: The `@kwdef` macro and its docstring: syntax-transforming macro expansion.
-- UNTRANSLATED
-- Source: base/util.jl:553-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @kwdef typedef
-- 
-- This is a helper macro that automatically defines a keyword-based constructor for the type
-- declared in the expression `typedef`, which must be a `struct` or `mutable struct`
-- expression. The default argument is supplied by declaring fields of the form `field::T =
-- default` or `field = default`. If no default is provided then the keyword argument becomes
-- a required keyword argument in the resulting type constructor.
-- 
-- Inner constructors can still be defined, but at least one should accept arguments in the
-- same form as the default inner constructor (i.e. one positional argument per field) in
-- order to function correctly with the keyword outer constructor.
-- 
-- !!! compat "Julia 1.1"
--     `Base.@kwdef` for parametric structs, and structs with supertypes
--     requires at least Julia 1.1.
-- 
-- !!! compat "Julia 1.9"
--     This macro is exported as of Julia 1.9.
-- 
-- # Examples
-- ```jldoctest
-- julia> @kwdef struct Foo
--            a::Int = 1         # specified default
--            b::String          # required keyword
--        end
-- Foo
-- 
-- julia> Foo(b="hi")
-- Foo(1, "hi")
-- 
-- julia> Foo()
-- ERROR: UndefKeywordError: keyword argument `b` not assigned
-- Stacktrace:
-- [...]
-- ```
-- """
-- macro kwdef(expr)
--     expr = macroexpand(__module__, expr) # to expand @static
--     isexpr(expr, :struct) || error("Invalid usage of @kwdef")
--     _, T, fieldsblock = expr.args
--     if T isa Expr && T.head === :<:
--         T = T.args[1]
--     end
-- 
--     fieldnames = Any[]
--     defvals = Any[]
--     extract_names_and_defvals_from_kwdef_fieldblock!(fieldsblock, fieldnames, defvals)
--     parameters = map(fieldnames, defvals) do fieldname, defval
--         if isnothing(defval)
--             return fieldname
--         else
--             return Expr(:kw, fieldname, defval)
--         end
--     end
-- 
--     # Only define a constructor if the type has fields, otherwise we'll get a stack
--     # overflow on construction
--     if !isempty(parameters)
--         T_no_esc = Meta.unescape(T)
--         if T_no_esc isa Symbol
--             sig = Expr(:call, T, Expr(:parameters, parameters...))
--             body = Expr(:block, __source__, Expr(:call, T, fieldnames...))
--             kwdefs = esc(Expr(:function, sig, body))
--         elseif isexpr(T_no_esc, :curly)
--             # if T == S{A<:AA,B<:BB}, define two methods
--             #   S(...) = ...
--             #   S{A,B}(...) where {A<:AA,B<:BB} = ...
--             S = T.args[1]
--             P = T.args[2:end]
--             Q = Any[isexpr(U, :<:) ? U.args[1] : U for U in P]
--             SQ = :($S{$(Q...)})
--             body1 = Expr(:block, __source__, Expr(:call, S, fieldnames...))
--             sig1 = Expr(:call, S, Expr(:parameters, parameters...))
--             def1 = Expr(:function, sig1, body1)
--             body2 = Expr(:block, __source__, Expr(:call, SQ, fieldnames...))
--             sig2 = :($(Expr(:call, SQ, Expr(:parameters, parameters...))) where {$(P...)})
--             def2 = Expr(:function, sig2, body2)
--             kwdefs = esc(Expr(:block, def1, def2))
--         else
--             error("Invalid usage of @kwdef")
--         end
--     else
--         kwdefs = nothing
--     end
--     return quote
--         $(esc(:($Base.@__doc__ $expr)))
--         $kwdefs
--     end
-- end
-- 
-- /Source


/--
Julia source: base/util.jl:666-685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function def_name_defval_from_kwdef_fielddef(kwdef)
    if kwdef isa Symbol
        return kwdef, kwdef, nothing
    elseif isexpr(kwdef, :(::))
        name, _ = kwdef.args
        return kwdef, Meta.unescape(name), nothing
    elseif isexpr(kwdef, :(=))
        lhs, rhs = kwdef.args
        def, name, _ = @something(def_name_defval_from_kwdef_fielddef(lhs), return nothing)
        return def, name, rhs
    elseif kwdef isa Expr && kwdef.head in (:const, :atomic)
        def, name, defval = @something(def_name_defval_from_kwdef_fielddef(kwdef.args[1]), return nothing)
        return Expr(kwdef.head, def), name, defval
    elseif kwdef isa Expr && kwdef.head in (:escape, :var"hygienic-scope")
        def, name, defval = @something(def_name_defval_from_kwdef_fielddef(kwdef.args[1]), return nothing)
        return Expr(kwdef.head, def), name, isnothing(defval) ? defval : Expr(kwdef.head, defval)
    end
end

```
-/
-- `def_name_defval_from_kwdef_fielddef(kwdef)`: `(def, name, defval)`, or `nothing`; a `defval`
-- of `nothing` is `none`.
def def_name_defval_from_kwdef_fielddef {L : Type} (kwdef : JuliaLean.base.expr.Value L) :
    ExceptT (JuliaLean.base.meta.MetaError L) Option
      (Option (JuliaLean.base.expr.Value L × JuliaLean.base.expr.Value L ×
        Option (JuliaLean.base.expr.Value L))) := do
  match kwdef with
  | .symbol _ => pure (some (kwdef, kwdef, none))
  | .expr "::" args =>
    -- `name, _ = kwdef.args`
    match args with
    | name :: _ :: _ => pure (some (kwdef, ← JuliaLean.base.meta.unescape name, none))
    | _ => throw (.jl .boundsError)
  | .expr "=" args =>
    match args with
    | lhs :: rhs :: _ =>
      match ← def_name_defval_from_kwdef_fielddef lhs with
      | none => pure none
      | some (dfn, name, _) => pure (some (dfn, name, some rhs))
    | _ => throw (.jl .boundsError)
  | .expr head args =>
    if head == "const" || head == "atomic" || head == "escape" || head == "hygienic-scope" then
      let some arg := args.head? | throw (.jl .boundsError)
      match ← def_name_defval_from_kwdef_fielddef arg with
      | none => pure none
      | some (dfn, name, defval) =>
        if head == "const" || head == "atomic" then
          pure (some (.expr head [dfn], name, defval))
        else
          pure (some (.expr head [dfn], name, defval.map fun v => .expr head [v]))
    else pure none
  | _ => pure none
partial_fixpoint


mutual
/--
Julia source: base/util.jl:644-665 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# @kwdef helper function
# mutates arguments inplace
function extract_names_and_defvals_from_kwdef_fieldblock!(block, names, defvals)
    for (i, item) in pairs(block.args)
        if isexpr(item, :block)
            extract_names_and_defvals_from_kwdef_fieldblock!(item, names, defvals)
        elseif item isa Expr && item.head in (:escape, :var"hygienic-scope")
            n = length(names)
            extract_names_and_defvals_from_kwdef_fieldblock!(item, names, defvals)
            for j in n+1:length(defvals)
                if !isnothing(defvals[j])
                    defvals[j] = Expr(item.head, defvals[j])
                end
            end
        else
            def, name, defval = @something(def_name_defval_from_kwdef_fielddef(item), continue)
            block.args[i] = def
            push!(names, name)
            push!(defvals, defval)
        end
    end
end
```
-/
-- `extract_names_and_defvals_from_kwdef_fieldblock!(block, names, defvals)`: `block` after the
-- mutation of its arguments, and `names` and `defvals` after their pushes (`none` is `nothing`).
def extract_names_and_defvals_from_kwdef_fieldblock! {L : Type}
    (block : JuliaLean.base.expr.Value L) (names : List (JuliaLean.base.expr.Value L))
    (defvals : List (Option (JuliaLean.base.expr.Value L))) :
    ExceptT (JuliaLean.base.meta.MetaError L) Option
      (JuliaLean.base.expr.Value L × List (JuliaLean.base.expr.Value L) ×
        List (Option (JuliaLean.base.expr.Value L))) := do
  match block with
  | .expr head args =>
    let (args, names, defvals) ← kwdefFieldItems args names defvals
    pure (.expr head args, names, defvals)
  | _ => throw (.jl (.methodError "getproperty"))
partial_fixpoint

-- The `for (i, item) in pairs(block.args)` loop.
def kwdefFieldItems {L : Type} (items : List (JuliaLean.base.expr.Value L))
    (names : List (JuliaLean.base.expr.Value L)) (defvals : List (Option (JuliaLean.base.expr.Value L))) :
    ExceptT (JuliaLean.base.meta.MetaError L) Option
      (List (JuliaLean.base.expr.Value L) × List (JuliaLean.base.expr.Value L) ×
        List (Option (JuliaLean.base.expr.Value L))) := do
  match items with
  | [] => pure ([], names, defvals)
  | item :: rest =>
    let (item, names, defvals) ← kwdefFieldItem item names defvals
    let (rest, names, defvals) ← kwdefFieldItems rest names defvals
    pure (item :: rest, names, defvals)
partial_fixpoint

-- One iteration of the loop: the item after its mutation or replacement.
def kwdefFieldItem {L : Type} (item : JuliaLean.base.expr.Value L)
    (names : List (JuliaLean.base.expr.Value L)) (defvals : List (Option (JuliaLean.base.expr.Value L))) :
    ExceptT (JuliaLean.base.meta.MetaError L) Option
      (JuliaLean.base.expr.Value L × List (JuliaLean.base.expr.Value L) ×
        List (Option (JuliaLean.base.expr.Value L))) := do
  match item with
  | .expr "block" _ => extract_names_and_defvals_from_kwdef_fieldblock! item names defvals
  | .expr head _ =>
    if head == "escape" || head == "hygienic-scope" then
      let n := names.length
      let (item, names, defvals) ← extract_names_and_defvals_from_kwdef_fieldblock! item names defvals
      -- `for j in n+1:length(defvals)`: wrap each non-`nothing` default value
      let defvals := defvals.zipIdx.map fun (d, j) =>
        if j ≥ n then d.map (fun v => .expr head [v]) else d
      pure (item, names, defvals)
    else
      match ← def_name_defval_from_kwdef_fielddef item with
      | none => pure (item, names, defvals)
      | some (dfn, name, defval) => pure (dfn, names ++ [name], defvals ++ [defval])
  | _ =>
    match ← def_name_defval_from_kwdef_fielddef item with
    | none => pure (item, names, defvals)
    | some (dfn, name, defval) => pure (dfn, names ++ [name], defvals ++ [defval])
partial_fixpoint
end
-- Reason: A section comment and the docstring of `runtests`: no method body.
-- UNTRANSLATED
-- Source: base/util.jl:686-702 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # testing
-- 
-- """
--     Base.runtests(tests=["all"]; ncores=ceil(Int, Sys.EFFECTIVE_CPU_THREADS / 2),
--                   exit_on_error=false, revise=false, propagate_project=true, [seed], [julia_args::Cmd])
-- 
-- Run the Julia unit tests listed in `tests`, which can be either a string or an array of
-- strings, using `ncores` processors. If `exit_on_error` is `false`, when one test
-- fails, all remaining tests in other files will still be run; they are otherwise discarded,
-- when `exit_on_error == true`.
-- If `revise` is `true`, the `Revise` package is used to load any modifications to `Base` or
-- to the standard libraries before running the tests.
-- If `propagate_project` is true the current project is propagated to the test environment.
-- If a seed is provided via the keyword argument, it is used to seed the
-- global RNG in the context where the tests are run; otherwise the seed is chosen randomly.
-- The argument `julia_args` can be used to pass custom `julia` command line flags to the test process.
-- """
-- /Source
/-- The callees of `runtests`: the environment, commands, files and process launch. -/
structure RuntestsOps (World Env Cmd : Type) where
  /-- `split(tests)` of a string. -/
  split : String → List String
  /-- `copy(ENV)`, `ENV2[k] = v`, `delete!(ENV2, k)`. -/
  copyENV : JuliaLean.base.io.M World Env
  setEnv : Env → String → String → Env
  deleteEnv : Env → String → Env
  iswindows : Bool
  /-- `mktempdir(; cleanup = true)` and `joinpath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "test",
  "runtests.jl")`. -/
  mktempdir : JuliaLean.base.io.M World String
  runtestsPath : JuliaLean.base.io.M World String
  /-- `julia_cmd()`, the empty command ` `` `, the command `` `--project` ``, the interpolated
  command of commands and words, and `setenv(cmd, env)`. -/
  julia_cmd : JuliaLean.base.io.M World Cmd
  emptyCmd : Cmd
  projectCmd : Cmd
  cmd : List (Cmd ⊕ List String) → JuliaLean.base.io.M World Cmd
  setenv : Cmd → Env → Cmd
  /-- `run(cmd)` and `read(cmd, String)`. -/
  run : Cmd → JuliaLean.base.io.M World Unit
  read : Cmd → JuliaLean.base.io.M World String
  isinteractive : JuliaLean.base.io.M World Bool
  /-- `print(stderr, s)` and `exit(code)`. -/
  printStderr : String → JuliaLean.base.io.M World Unit
  exit : Int → JuliaLean.base.io.M World Unit


/--
Julia source: base/util.jl:703-739 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function runtests(tests = ["all"]; ncores::Int = ceil(Int, Sys.EFFECTIVE_CPU_THREADS / 2),
                  exit_on_error::Bool=false,
                  revise::Bool=false,
                  propagate_project::Bool=false,
                  seed::Union{BitInteger,Nothing}=nothing,
                  julia_args::Cmd=``)
    if isa(tests,AbstractString)
        tests = split(tests)
    end
    exit_on_error && push!(tests, "--exit-on-error")
    revise && push!(tests, "--revise")
    seed !== nothing && push!(tests, "--seed=0x$(string(seed % UInt128, base=16))") # cast to UInt128 to avoid a minus sign
    ENV2 = copy(ENV)
    ENV2["JULIA_CPU_THREADS"] = "$ncores"
    pathsep = Sys.iswindows() ? ";" : ":"
    ENV2["JULIA_DEPOT_PATH"] = string(mktempdir(; cleanup = true), pathsep) # make sure the default depots can be loaded
    ENV2["JULIA_LOAD_PATH"] = string("@", pathsep, "@stdlib")
    ENV2["JULIA_TESTS"] = "true"
    delete!(ENV2, "JULIA_PROJECT")
    project_flag = propagate_project ? `--project` : ``
    try
        run(setenv(`$(julia_cmd()) -q $julia_args $project_flag $(joinpath(Sys.BINDIR,
            Base.DATAROOTDIR, "julia", "test", "runtests.jl")) $tests`, ENV2))
        nothing
    catch
        # evaluate versioninfo in the test environment so the listed env vars are the same
        vinfo = read(setenv(`$(julia_cmd()) -e 'let InteractiveUtils = Base.require_stdlib(Base.PkgId(Base.UUID(0xb77e0a4c_d291_57a0_90e8_8db25a27a240), "InteractiveUtils")); @invokelatest(InteractiveUtils.versioninfo()); end'`, ENV2), String)
        msg = "A test has failed. Please submit a bug report (https://github.com/JuliaLang/julia/issues)\n" *
              "including error messages above and the output of versioninfo():\n$(vinfo)"
        if isinteractive()
            error(msg)
        else
            print(stderr, "ERROR: ", msg)
            exit(1)
        end
    end
end
```
-/
def runtests {World Env Cmd : Type} (o : RuntestsOps World Env Cmd)
    (tests : String ⊕ List String := .inr ["all"]) (ncores : I64) (exit_on_error : Bool := false)
    (revise : Bool := false) (propagate_project : Bool := false) (seed : Option Int := none)
    (julia_args : Cmd) : JuliaLean.base.io.M World Unit := do
  let mut tests := match tests with
    | .inl s => o.split s
    | .inr ts => ts
  if exit_on_error then tests := tests ++ ["--exit-on-error"]
  if revise then tests := tests ++ ["--revise"]
  if let some seed := seed then
    -- `string(seed % UInt128, base=16)`
    let hex := String.ofList (Nat.toDigits 16 (seed % (2 ^ 128 : Int)).toNat)
    tests := tests ++ ["--seed=0x" ++ hex]
  let mut env2 ← o.copyENV
  env2 := o.setEnv env2 "JULIA_CPU_THREADS" (toString ncores.val)
  let pathsep := if o.iswindows then ";" else ":"
  env2 := o.setEnv env2 "JULIA_DEPOT_PATH" ((← o.mktempdir) ++ pathsep)
  env2 := o.setEnv env2 "JULIA_LOAD_PATH" ("@" ++ pathsep ++ "@stdlib")
  env2 := o.setEnv env2 "JULIA_TESTS" "true"
  env2 := o.deleteEnv env2 "JULIA_PROJECT"
  let project_flag := if propagate_project then o.projectCmd else o.emptyCmd
  tryCatch (do
      let command ← o.cmd [.inl (← o.julia_cmd), .inr ["-q"], .inl julia_args, .inl project_flag,
        .inr [← o.runtestsPath], .inr tests]
      o.run (o.setenv command env2))
    fun _ => do
      let versioninfo ← o.cmd [.inl (← o.julia_cmd), .inr ["-e", "let InteractiveUtils = Base.require_stdlib(Base.PkgId(Base.UUID(0xb77e0a4c_d291_57a0_90e8_8db25a27a240), \"InteractiveUtils\")); @invokelatest(InteractiveUtils.versioninfo()); end"]]
      let vinfo ← o.read (o.setenv versioninfo env2)
      let msg := "A test has failed. Please submit a bug report (https://github.com/JuliaLang/julia/issues)\n" ++
        "including error messages above and the output of versioninfo():\n" ++ vinfo
      if ← o.isinteractive then
        throw (.errorException msg)
      else
        o.printStderr ("ERROR: " ++ msg)
        o.exit 1

end JuliaLean.base.util

section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Util

open JuliaLean JuliaLean.IOCov

/-! ## Colored output, lines 73-146 -/

/-- A `printstyled` color: one of the `text_colors` symbols, `:nothing`, or an integer. -/
inductive Color where
  | sym (s : String)
  | int (n : Int)
  deriving DecidableEq, Repr

/-- `get(text_colors, color, text_colors[:default])`, lines 3-48. -/
def enableCode : Color → String
  | .int n => if 0 ≤ n ∧ n ≤ 255 then "\x1b[38;5;" ++ toString n ++ "m" else "\x1b[39m"
  | .sym s =>
    match s with
    | "black" => "\x1b[30m" | "red" => "\x1b[31m" | "green" => "\x1b[32m" | "yellow" => "\x1b[33m"
    | "blue" => "\x1b[34m" | "magenta" => "\x1b[35m" | "cyan" => "\x1b[36m" | "white" => "\x1b[37m"
    | "light_black" => "\x1b[90m" | "light_red" => "\x1b[91m" | "light_green" => "\x1b[92m"
    | "light_yellow" => "\x1b[93m" | "light_blue" => "\x1b[94m" | "light_magenta" => "\x1b[95m"
    | "light_cyan" => "\x1b[96m" | "light_white" => "\x1b[97m" | "normal" => "\x1b[0m"
    | "default" => "\x1b[39m" | "bold" => "\x1b[1m" | "italic" => "\x1b[3m"
    | "underline" => "\x1b[4m" | "blink" => "\x1b[5m" | "reverse" => "\x1b[7m"
    | "hidden" => "\x1b[8m" | "nothing" => ""
    | _ => "\x1b[39m"

/-- `get(disable_text_style, color, text_colors[:default])`, lines 52-62. -/
def disableCode : Color → String
  | .sym "bold" => "\x1b[22m" | .sym "italic" => "\x1b[23m" | .sym "underline" => "\x1b[24m"
  | .sym "blink" => "\x1b[25m" | .sym "reverse" => "\x1b[27m" | .sym "hidden" => "\x1b[28m"
  | .sym "normal" => "" | .sym "default" => "" | .sym "nothing" => ""
  | _ => "\x1b[39m"

structure Style where
  bold : Bool := false
  italic : Bool := false
  underline : Bool := false
  blink : Bool := false
  reverse : Bool := false
  hidden : Bool := false

/-- The six `flag && color === :flag && (color = :nothing)` lines, 88-93. -/
def normColor (st : Style) (c : Color) : Color :=
  let c := if st.bold && c == .sym "bold" then .sym "nothing" else c
  let c := if st.italic && c == .sym "italic" then .sym "nothing" else c
  let c := if st.underline && c == .sym "underline" then .sym "nothing" else c
  let c := if st.blink && c == .sym "blink" then .sym "nothing" else c
  let c := if st.reverse && c == .sym "reverse" then .sym "nothing" else c
  if st.hidden && c == .sym "hidden" then .sym "nothing" else c

def enableAnsi (st : Style) (c : Color) : String :=
  enableCode c ++ (if st.bold then "\x1b[1m" else "") ++ (if st.italic then "\x1b[3m" else "") ++
    (if st.underline then "\x1b[4m" else "") ++ (if st.blink then "\x1b[5m" else "") ++
    (if st.reverse then "\x1b[7m" else "") ++ (if st.hidden then "\x1b[8m" else "")

def disableAnsi (st : Style) (c : Color) : String :=
  (if st.hidden then "\x1b[28m" else "") ++ (if st.reverse then "\x1b[27m" else "") ++
    (if st.blink then "\x1b[25m" else "") ++ (if st.underline then "\x1b[24m" else "") ++
    (if st.bold then "\x1b[22m" else "") ++ (if st.italic then "\x1b[23m" else "") ++ disableCode c

/-- `eachsplit(str, '\n')`: the pieces between newlines, empty ones included. -/
def splitNl : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    if c = '\n' then [] :: splitNl cs
    else match splitNl cs with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- `output_color_string(buf, str, color, flags...)`, lines 86-117: every nonempty line of
`eachsplit(str, '\n')` is wrapped in the enable and disable sequences. -/
def outputColorString (str : List Char) (c : Color) (st : Style) : List Char :=
  let c := normColor st c
  let e := (enableAnsi st c).toList
  let d := (disableAnsi st c).toList
  List.intercalate ['\n'] ((splitNl str).map fun line => if line.isEmpty then [] else e ++ line ++ d)

/-- `with_output_color(f, color, io, args...; flags...)`, lines 73-84: the text `f` printed
(`text`), colored only when `get(io, :color, false)`. -/
def withOutputColor (text : List Char) (c : Color) (iscolor : Bool) (st : Style) : List Char :=
  if iscolor then outputColorString text c st else text

/-- `printstyled(io, msg...; flags..., color=:normal)`, lines 143-144, and
`printstyled(msg...) = printstyled(stdout, msg...)`, lines 145-146. -/
def printstyled (printed : List Char) (iscolor : Bool) (st : Style) (c : Color := .sym "normal") :
    List Char := withOutputColor printed c iscolor st

/-! ## `julia_cmd`, `julia_exename`, lines 173-266 -/

/-- The fields of `JLOptions()` that `julia_cmd` reads. -/
structure Opts where
  compile : Nat
  depwarn : Nat
  checkBounds : Nat
  canInline : Nat
  compiledModules : Nat
  pkgimages : Nat
  optLevel : Nat
  optLevelMin : Nat
  debugLevel : Nat
  color : Nat
  quiet : Nat
  startupfile : Nat

/-- The `addflags` that `julia_cmd` computes, lines 180-252 (without the coverage and
allocation-tracking flags, which forward strings unchanged). `JL_OPTIONS_COMPILE_OFF = 0`,
`_ALL = 2`, `_MIN = 3`. -/
def addflags (o : Opts) : List String :=
  (if o.compile == 0 then ["--compile=no"] else if o.compile == 2 then ["--compile=all"]
    else if o.compile == 3 then ["--compile=min"] else []) ++
  (if o.depwarn == 1 then ["--depwarn=yes"] else if o.depwarn == 2 then ["--depwarn=error"] else []) ++
  (if o.checkBounds == 1 then ["--check-bounds=yes"] else if o.checkBounds == 2 then ["--check-bounds=no"] else []) ++
  (if o.canInline == 0 then ["--inline=no"] else []) ++
  (if o.compiledModules == 0 then ["--compiled-modules=no"] else []) ++
  (if o.compiledModules == 2 then ["--compiled-modules=existing"] else []) ++
  (if o.compiledModules == 3 then ["--compiled-modules=strict"] else []) ++
  (if o.pkgimages == 0 then ["--pkgimages=no"] else []) ++
  (if o.pkgimages == 2 then ["--pkgimages=existing"] else []) ++
  (if o.optLevel == 2 then [] else ["-O" ++ toString o.optLevel]) ++
  (if o.optLevelMin == 0 then [] else ["--min-optlevel=" ++ toString o.optLevelMin]) ++
  ["-g" ++ toString o.debugLevel] ++
  (if o.color == 1 then ["--color=yes"] else if o.color == 2 then ["--color=no"] else []) ++
  (if o.quiet != 0 then ["-q"] else []) ++
  (if o.startupfile == 2 then ["--startup-file=no"] else [])

/-- `julia_cmd(julia; cpu_target)`: `` `$julia -C $cpu_target -J$image_file $addflags` ``. -/
def juliaCmd (julia cpuTarget imageFile : String) (o : Opts) : List String :=
  [julia, "-C", cpuTarget, "-J" ++ imageFile] ++ addflags o

/-- `julia_exename()`, lines 260-266 (non-Windows). -/
def juliaExename (isdebug : Bool) : String := if isdebug then "julia-debug" else "julia"

/-! ## Secure zeroing, lines 276-280 -/

/-- `securezero!(a) = fill!(a, 0)`, line 277. -/
def securezero (a : List Int) : List Int := a.map (fun _ => 0)

/-- `unsafe_securezero!(p::Ptr{T}, len)`, lines 278-279: `memset(p, 0, len*sizeof(T))` on a
byte memory `mem` at offset `p`. The `Ptr{Cvoid}` method, line 280, uses `sizeof = 1`. -/
def unsafeSecurezero (mem : List UInt8) (p len sz : Nat) : List UInt8 :=
  mem.take p ++ List.replicate (min (len * sz) (mem.length - p)) 0 ++ mem.drop (p + len * sz)
def unsafeSecurezeroVoid (mem : List UInt8) (p len : Nat) : List UInt8 := unsafeSecurezero mem p len 1

/-! ## The raw terminal and `getpass`, lines 307-392 -/

/-- `_getch()`, lines 310-316 (Unix): `read(stdin, UInt8)`, `EOFError` at the end.
Bytes are natural numbers below 256. -/
def getch : List Nat → R (Nat × List Nat)
  | [] => .error .eofError
  | c :: cs => .ok (c, cs)

/-- `make_termios()`, line 319: `termios_size` zero bytes. -/
def makeTermios (size : Nat) : List UInt8 := List.replicate size 0

/-- `tcgetattr(fd, termios)` / `tcsetattr(fd, termios, mode)`, lines 325-336: a nonzero
return throws `IOError`. -/
def tcCall (name : String) (ret : Int) : R Unit :=
  if ret != 0 then .error (.uvError name) else .ok ()

/-- `cfmakeraw(termios)`, line 337: the C function's result. -/
def cfmakeraw (c : List UInt8 → List UInt8) (t : List UInt8) : List UInt8 := c t

/-- `with_raw_tty(f, input)`, lines 339-363: get the terminal mode, set raw mode, run `f`,
and in `finally` restore the saved mode. Returns `f`'s outcome and the final mode. -/
def withRawTty {α} (isStdin : Bool) (mode : List UInt8) (f : R α) : R α × List UInt8 :=
  if !isStdin then (argErr "with_raw_tty only works for stdin", mode)
  else (f, mode)

/-- `iscntrl(Char(c))` for a single byte `c`: the code point `U+00XX` is a control
character for `0x00-0x1f` and `0x7f-0x9f`. -/
def isCntrlByte (c : Nat) : Bool := c < 32 || (127 ≤ c && c ≤ 159)

/-- The read loop of `getpass(input::TTY, output, prompt)`, lines 371-385: `s` holds the
bytes written to the `SecretBuffer`, `plen` the counter. -/
def getpassLoop : Nat → List Nat → List Nat → Nat → R (List Nat)
  | 0, _, _, _ => .error (.errorException "out of fuel")
  | fuel + 1, input, s, plen => do
    let (c, input) ← getch input
    if c == 0xff || c == 10 || c == 13 || c == 4 then pure s
    else if c == 0 || c == 0xe0 then do
      let (_, input) ← getch input
      getpassLoop fuel input s plen
    else if c == 8 && plen > 0 then getpassLoop fuel input s (plen - 1)
    else if !isCntrlByte c && plen < 128 then getpassLoop fuel input (s ++ [c]) plen
    else getpassLoop fuel input s plen

/-- `getpass(input, output, prompt)`: the secret read from the typed bytes `keys`. -/
def getpass (keys : List Nat) : R (List Nat) := getpassLoop (keys.length + 1) keys [] 0

/-- `getpass(prompt; with_suffix) = getpass(stdin, stdout, prompt; with_suffix)`, line 392. -/
def getpassStdin (keys : List Nat) : R (List Nat) := getpass keys

/-! ## `prompt`, lines 413-424 -/

/-- `chomp(s)`: remove one trailing `"\n"` or `"\r\n"`. -/
def chomp (s : List UInt8) : List UInt8 :=
  if s.getLast? == some 10 then
    let t := s.dropLast
    if t.getLast? == some 13 then t.dropLast else t
  else s

/-- `readline(input, keep=true)`: the bytes up to and including the first `'\n'`. -/
def readlineKeep (input : List UInt8) : List UInt8 :=
  match input.idxOf? 10 with
  | some k => input.take (k + 1)
  | none => input

/-- `prompt(input, output, message; default)`, lines 413-420: the text printed and the
result (`none` is `nothing`). -/
def prompt (input message default : List UInt8) : List UInt8 × Option (List UInt8) :=
  let msg := if !default.isEmpty then message ++ bs " [" ++ default ++ bs "]: " else message ++ bs ": "
  let uinput := readlineKeep input
  if uinput.isEmpty then (msg, none)
  else
    let u := chomp uinput
    (msg, some (if u.isEmpty then default else u))

/-- `prompt(message; default) = prompt(stdin, stdout, message, default=default)`, line 424. -/
def promptStdin (input message default : List UInt8) : List UInt8 × Option (List UInt8) :=
  prompt input message default
end JuliaLean.IOCov.Util
end

section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Util

open JuliaLean JuliaLean.IOCov

/-! ## CRC-32c, lines 515-551 -/

open JuliaLean.Base64Uuid (U32 jl_crc32c Byte)

/-- `unsafe_crc32c(a, n, crc) = jl_crc32c(crc, a, n)`, line 515: the first `n` bytes. -/
def unsafeCrc32c (a : List Byte) (n : Nat) (crc : U32) : U32 := jl_crc32c crc (a.take n)

/-- `_crc32c(a::NTuple{N,UInt8}, crc)`, `_crc32c(a::DenseUInt8OrInt8, crc)` and
`_crc32c(s::String, crc)`, lines 517-526: one call over all `length`/`sizeof` bytes. -/
def crc32cBytes (a : List Byte) (crc : U32) : U32 := unsafeCrc32c a a.length crc

/-- Little-endian bytes of a `k`-byte unsigned integer. -/
def leBytes (k : Nat) (x : Nat) : List Byte :=
  (List.range k).map fun i => JInt.lit .u8 ((x / 256 ^ i) % 256)

/-- `_crc32c(x::UInt128/UInt64/UInt32/UInt16/UInt8, crc)`, lines 542-551: `jl_crc32c` over the
`sizeof(x)` bytes of `Ref(x)`, which are little-endian on the supported platforms. -/
def crc32cUInt (k : Nat) (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes k x)

/-! ## `@kwdef` field parsing, lines 590-684 -/

/-- The field expressions `@kwdef` accepts. -/
inductive FieldExpr where
  | sym (name : String)
  | typed (name : String) (ty : String)
  | assign (lhs : FieldExpr) (rhs : String)
  | wrap (head : String) (arg : FieldExpr)
  | other
  deriving DecidableEq, Repr

/-- `def_name_defval_from_kwdef_fielddef(kwdef)`, lines 667-684: the field definition
without its default, the field name, and the default (`none` = `nothing`); `none` overall
for an expression that is not a field (for example a docstring line or a method). -/
def defNameDefval : FieldExpr → Option (FieldExpr × String × Option String)
  | .sym n => some (.sym n, n, none)
  | .typed n t => some (.typed n t, n, none)
  | .assign lhs rhs =>
    match defNameDefval lhs with
    | some (d, n, _) => some (d, n, some rhs)
    | none => none
  | .wrap h a =>
    match defNameDefval a with
    | some (d, n, dv) =>
      if h == "const" || h == "atomic" then some (.wrap h d, n, dv)
      else if h == "escape" || h == "hygienic-scope" then some (.wrap h d, n, dv.map (fun v => h ++ "(" ++ v ++ ")"))
      else none
    | none => none
  | .other => none

/-- `extract_names_and_defvals_from_kwdef_fieldblock!` on a flat block, lines 646-665:
the rewritten fields and the `(name, default)` list, skipping non-fields. -/
def extractFields : List FieldExpr → List FieldExpr × List (String × Option String)
  | [] => ([], [])
  | item :: rest =>
    let (defs, nds) := extractFields rest
    match defNameDefval item with
    | some (d, n, dv) => (d :: defs, (n, dv) :: nds)
    | none => (item :: defs, nds)

/-- The keyword parameters of the generated constructor, lines 600-606: a plain name for a
field without default, `name = default` otherwise. -/
def kwParams (nds : List (String × Option String)) : List (String × Option String) := nds

/-! ## `runtests`, lines 703-739 -/

/-- The test-list arguments of `runtests`, lines 709-715: a string is split on spaces,
then `--exit-on-error`, `--revise` and `--seed=0x...` are appended. -/
def runtestsArgs (tests : List String) (exitOnError revise : Bool) (seedHex : Option String) :
    List String :=
  tests ++ (if exitOnError then ["--exit-on-error"] else []) ++ (if revise then ["--revise"] else []) ++
    (match seedHex with | some h => ["--seed=0x" ++ h] | none => [])

/-- The command `runtests` runs, lines 719-721, with the keyword defaults of line 703-708
(`propagate_project::Bool=false`): `julia_cmd() -q $julia_args $project_flag runtests.jl $tests`. -/
def runtestsCmd (julia : List String) (tests : List String) (propagateProject : Bool := false) :
    List String :=
  julia ++ ["-q"] ++ (if propagateProject then ["--project"] else []) ++ ["runtests.jl"] ++
    runtestsArgs tests false false none


/-! ## Separate overload models -/

/-- `printstyled(msg...; flags...) = printstyled(stdout, msg...; flags...)`, lines 145-146. -/
def printstyledStdout (printed : List Char) (iscolor : Bool) (st : Style) (c : Color := .sym "normal") :
    List Char := printstyled printed iscolor st c

/-- `tcgetattr(fd, termios)`, lines 325-330, and `tcsetattr(fd, termios, mode)`, lines 331-336. -/
def tcgetattr (ret : Int) : R Unit := if ret != 0 then .error (.uvError "tcgetattr") else .ok ()
def tcsetattr (ret : Int) : R Unit := if ret != 0 then .error (.uvError "tcsetattr") else .ok ()

/-- `_crc32c(a::NTuple{N,UInt8}, crc)`, lines 517-518: `unsafe_crc32c(Ref(a), length(a), crc)`. -/
def crc32cTuple (a : List Byte) (crc : U32) : U32 := unsafeCrc32c a a.length crc
/-- `_crc32c(a::DenseUInt8OrInt8, crc)`, lines 520-522: `unsafe_crc32c(a, length(a), crc)`. -/
def crc32cDense (a : List Byte) (crc : U32) : U32 := unsafeCrc32c a a.length crc
/-- `_crc32c(s::Union{String,SubString{String}}, crc)`, lines 524-526: `sizeof(s)` code units. -/
def crc32cString (s : List Byte) (crc : U32) : U32 := unsafeCrc32c s s.length crc

/-- `_crc32c(x::UInt128, crc)` (16 bytes), `UInt64` (8), `UInt32` (4), `UInt16` (2), `UInt8` (1),
lines 542-551: `jl_crc32c` over the little-endian bytes of `Ref(x)`. -/
def crc32cU128 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 16 x)
def crc32cU64 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 8 x)
def crc32cU32 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 4 x)
def crc32cU16 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 2 x)
def crc32cU8 (x : Nat) (crc : U32) : U32 := jl_crc32c crc (leBytes 1 x)
end JuliaLean.IOCov.Util
end

section
namespace JuliaLean.IOCov.UtilFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov
open JuliaLean.IOCov.Util

/-! Color printing -/

abbrev CallbackResult (alpha state : Type) := R alpha × state

/-- `with_output_color`, `base/util.jl:73-84`, with the callback's buffer
output, result or exception, and the final text printed to the outer IO. -/
def withOutputColorCall {alpha : Type} (f : List Char -> CallbackResult alpha (List Char))
    (color : Color) (iscolor : Bool) (style : Style) (outer : List Char) : R alpha × List Char :=
  let called := f []
  let text := if iscolor then outputColorString called.2 color style else called.2
  (called.1, outer ++ text)

/-- `output_color_string(buf, str, ...)`, `base/util.jl:86-117`, preserving
the supplied IOBuffer contents before the method writes colored lines. -/
def outputColorBuffer (buf str : List Char) (color : Color) (style : Style) : List Char :=
  buf ++ outputColorString str color style

/-- IO `printstyled`, `base/util.jl:143-144`. -/
def printstyledIO (render : List String -> List Char) (io : List Char) (msg : List String)
    (color : Color) (iscolor : Bool) (style : Style) : List Char :=
  (withOutputColorCall (fun b => (.ok (), b ++ render msg)) color iscolor style io).2

/-- stdout `printstyled`, `base/util.jl:145-146`. -/
def printstyledStdout (render : List String -> List Char) (stdout : List Char) (msg : List String)
    (color : Color) (iscolor : Bool) (style : Style) : List Char :=
  printstyledIO render stdout msg color iscolor style

/-! julia_cmd -/

structure FullOpts extends Opts where
  codeCoverage : Nat
  coverageFile : String
  trackedPath : String
  codeCoverageMode : Nat
  mallocLog : Nat
  useSysimageNativeCode : Nat
  compressSysimage : Nat

def coverageFlags (o : FullOpts) : List String :=
  (if o.codeCoverage != 0 && (o.coverageFile.isEmpty || o.coverageFile.contains "%p") then
    (if o.codeCoverage == 1 then ["--code-coverage=user"]
     else if o.codeCoverage == 2 then ["--code-coverage=all"]
     else if o.codeCoverage == 3 then ["--code-coverage=@" ++ o.trackedPath] else []) ++
    (if o.coverageFile.isEmpty then [] else ["--code-coverage=" ++ o.coverageFile]) else []) ++
  (if o.codeCoverageMode == 1 then ["--code-coverage-mode=count"] else [])

def allocationFlags (o : FullOpts) : List String :=
  if o.mallocLog == 1 then ["--track-allocation=user"]
  else if o.mallocLog == 2 then ["--track-allocation=all"]
  else if o.mallocLog == 3 then ["--track-allocation=@" ++ o.trackedPath] else []

/-- `julia_cmd`, `base/util.jl:173-258`, including every source branch. -/
def juliaCmdFull (julia cpuTarget image : String) (o : FullOpts) : List String :=
  [julia, "-C", cpuTarget, "-J" ++ image] ++ addflags o.toOpts ++ coverageFlags o ++
  allocationFlags o ++ (if o.useSysimageNativeCode == 0 then ["--sysimage-native-code=no"] else []) ++
  (if o.compressSysimage == 1 then ["--compress-sysimage=yes"] else [])

/-- `julia_exename`, `base/util.jl:260-266`. -/
def juliaExename (windows debug : Bool) : String :=
  if debug then if windows then "julia-debug.exe" else "julia-debug"
  else if windows then "julia.exe" else "julia"

/-! Secure zero -/

/-- `securezero!(a) = fill!(a, 0)`, `base/util.jl:277`, with the zero value
of every allowed Number element type supplied explicitly. -/
def securezero {alpha : Type} (zero : alpha) (a : List alpha) : List alpha :=
  a.map (fun _ => zero)

structure PointerResult where
  memory : List UInt8
  pointer : Int
  deriving DecidableEq

/-- Pointer `unsafe_securezero!`, `base/util.jl:278-279`. -/
def unsafeSecurezero (mem : List UInt8) (ptr len sizeofT : Int) : R PointerResult :=
  if len < 0 || sizeofT < 0 then .error (.jl (.inexactError "Csize_t"))
  else
    let n := len * sizeofT
    if ptr < 0 || ptr + n > mem.length then .error (.jl .boundsError)
    else .ok ⟨mem.take ptr.toNat ++ List.replicate n.toNat 0 ++ mem.drop (ptr + n).toNat, ptr⟩

/-- Cvoid pointer wrapper, `base/util.jl:280`. -/
def unsafeSecurezeroVoid (mem : List UInt8) (ptr len : Int) : R PointerResult :=
  unsafeSecurezero mem ptr len 1

/-! Terminal and password methods -/

/-- `_getch`, `base/util.jl:310-316`, with both static platform branches. -/
def getch (windows : Bool) (windowsGetch : Unit -> Int) (stdinRead : Unit -> R UInt8) : R UInt8 :=
  if windows then .ok (windowsGetch ()).toNat.toUInt8 else stdinRead ()

structure IOErrorM where
  operation : String
  code : Int
  deriving DecidableEq, Repr

abbrev TR (alpha : Type) := Except IOErrorM alpha

/-- `tcgetattr`, `base/util.jl:325-330`. -/
def tcgetattr (call : Int -> List UInt8 -> Int) (fd : Int) (termios : List UInt8) : TR Unit :=
  let ret := call fd termios
  if ret != 0 then .error ⟨"tcgetattr failed", ret⟩ else .ok ()
/-- `tcsetattr`, `base/util.jl:331-336`. -/
def tcsetattr (call : Int -> Int -> List UInt8 -> Int) (fd mode : Int) (termios : List UInt8) : TR Unit :=
  let ret := call fd mode termios
  if ret != 0 then .error ⟨"tcsetattr failed", ret⟩ else .ok ()
/-- `cfmakeraw`, `base/util.jl:337`. -/
def cfmakeraw (call : List UInt8 -> List UInt8) (termios : List UInt8) : Unit × List UInt8 :=
  ((), call termios)

structure RawTtyResult (alpha : Type) where
  result : TR alpha
  restored : List UInt8

/-- `with_raw_tty`, `base/util.jl:339-363`, including platform selection,
terminal calls, callback result or exception, and finally restoration. -/
def withRawTty {alpha : Type} (isStdin windows : Bool) (old : List UInt8)
    (getattr : List UInt8 -> TR Unit) (raw : List UInt8 -> List UInt8)
    (setattr : List UInt8 -> TR Unit) (f : Unit -> TR alpha) : R (RawTtyResult alpha) :=
  if !isStdin then argErr "with_raw_tty only works for stdin"
  else if windows then .ok ⟨f (), old⟩
  else match getattr old with
    | .error e => .ok ⟨.error e, old⟩
    | .ok _ =>
        let newMode := raw old
        match setattr newMode with
        | .error e => .ok ⟨.error e, old⟩
        | .ok _ => .ok ⟨f (), old⟩

structure GetpassResult where
  secret : List UInt8
  output : List UInt8
  deriving DecidableEq

def getpassLoop : Nat -> List UInt8 -> List UInt8 -> Nat -> List UInt8
  | 0, _, secret, _ => secret
  | fuel + 1, [], secret, _ => secret
  | fuel + 1, c :: cs, secret, plen =>
      if c == 0xff || c == 10 || c == 13 || c == 4 then secret
      else if c == 0 || c == 0xe0 then
        match cs with | [] => secret | _ :: rest => getpassLoop fuel rest secret plen
      else if c == 8 && plen > 0 then getpassLoop fuel cs secret (plen - 1)
      else if !isCntrlByte c.toNat && plen < 128 then getpassLoop fuel cs (secret ++ [c]) plen
      else getpassLoop fuel cs secret plen

/-- `getpass(input, output, prompt; with_suffix)`, `base/util.jl:365-388`.
`isStdin` is the identity check and `keys` are successive `_getch` results. -/
def getpass (isStdin : Bool) (output prompt keys : List UInt8) (withSuffix : Bool) : R GetpassResult :=
  if !isStdin then argErr "getpass only works for stdin"
  else .ok ⟨getpassLoop (keys.length + 1) keys [] 0,
    output ++ prompt ++ (if withSuffix then [58, 32] else [])⟩

/-- stdin/stdout getpass wrapper, `base/util.jl:392`. -/
def getpassStdin (stdout prompt keys : List UInt8) (withSuffix : Bool) : R GetpassResult :=
  getpass true stdout prompt keys withSuffix

/-- `prompt(input,output,message;default)`, `base/util.jl:413-420`. -/
def prompt (input output message default : List UInt8) : List UInt8 × Option (List UInt8) :=
  let msg := message ++ (if default.isEmpty then [58,32] else [32,91] ++ default ++ [93,58,32])
  let printed := output ++ msg
  if input.isEmpty then (printed, none)
  else let value := Util.chomp input; (printed, some (if value.isEmpty then default else value))

/-! CRC methods -/

structure StreamM where
  bytes : List JuliaLean.Base64Uuid.Byte
  pos : Int

def streamRead (s : StreamM) (n : Nat) : List JuliaLean.Base64Uuid.Byte × StreamM :=
  let start := max s.pos 0
  let got := s.bytes.drop start.toNat |>.take n
  (got, { s with pos := start + got.length })

def crcIo (s : StreamM) (nb : Int) (crc : JuliaLean.Base64Uuid.U32) :
    R (JuliaLean.Base64Uuid.U32 × StreamM) :=
  if nb < 0 then argErr "number of bytes to checksum must be >= 0"
  else
    let r := streamRead s (min nb 24576).toNat
    .ok (JuliaLean.Base64Uuid.jl_crc32c crc r.1, r.2)

def crcIoAll (s : StreamM) (crc : JuliaLean.Base64Uuid.U32) :
    R (JuliaLean.Base64Uuid.U32 × StreamM) :=
  crcIo s (2^63 - 1) crc
def crcIOStream (s : StreamM) (crc : JuliaLean.Base64Uuid.U32) :
    R (JuliaLean.Base64Uuid.U32 × StreamM) :=
  crcIo s (s.bytes.length - s.pos) crc

def nativeBytes (little : Bool) (nbytes x : Nat) : List JuliaLean.Base64Uuid.Byte :=
  let bs := leBytes nbytes x
  if little then bs else bs.reverse
def crcUIntNative (little : Bool) (nbytes x : Nat) (crc : JuliaLean.Base64Uuid.U32) :
    JuliaLean.Base64Uuid.U32 :=
  JuliaLean.Base64Uuid.jl_crc32c crc (nativeBytes little nbytes x)

/-! @kwdef -/

inductive Expr where
  | sym (name : String)
  | typed (name ty : String)
  | assign (lhs : Expr) (rhs : String)
  | wrap (head : String) (arg : Expr)
  | block (items : List Expr)
  | struct (name : Expr) (fields : Expr)
  | other

def fieldInfo : Expr -> Option (Expr × String × Option String)
  | .sym n => some (.sym n, n, none)
  | .typed n t => some (.typed n t, n, none)
  | .assign lhs rhs => (fieldInfo lhs).map (fun x => (x.1, x.2.1, some rhs))
  | .wrap h arg => (fieldInfo arg).map (fun x =>
      (.wrap h x.1, x.2.1, if h == "escape" || h == "hygienic-scope" then x.2.2.map (fun d => h ++ "(" ++ d ++ ")") else x.2.2))
  | _ => none

def extract : Expr -> Expr × List (String × Option String)
  | .block items =>
      let rs := items.map extract
      (.block (rs.map Prod.fst), rs.flatMap Prod.snd)
  | e => match fieldInfo e with | some x => (x.1, [(x.2.1, x.2.2)]) | none => (e, [])

structure KwdefResult where
  expanded : Expr
  parameters : List (String × Option String)
  constructors : Nat

/-- `@kwdef`, `base/util.jl:590-642`, after macroexpand. -/
def kwdef : Expr -> R KwdefResult
  | .struct name fields =>
      let r := extract fields
      let n := if r.2.isEmpty then 0 else match name with | .sym _ => 1 | .wrap "curly" _ => 2 | _ => 0
      .ok ⟨.struct name r.1, r.2, n⟩
  | _ => .error (.errorException "Invalid usage of @kwdef")

/-! runtests -/

structure RunTestsResult where
  tests : List String
  env : List (String × String)
  command : List String
  failureCommand : List String
  interactive : Bool
  deriving DecidableEq, Repr

/-- `runtests`, `base/util.jl:703-739`, through command construction. -/
def runtests (juliaArgs tests : List String) (ncores : Int) (exitOnError revise propagate : Bool)
    (seed : Option String) (interactive : Bool) : RunTestsResult :=
  let tests := runtestsArgs tests exitOnError revise seed
  let env := [("JULIA_CPU_THREADS", toString ncores), ("JULIA_DEPOT_PATH", "temporary:"),
    ("JULIA_LOAD_PATH", "@:@stdlib"), ("JULIA_TESTS", "true")]
  let project := if propagate then ["--project"] else []
  ⟨tests, env, juliaArgs ++ ["-q"] ++ project ++ ["runtests.jl"] ++ tests,
    juliaArgs ++ ["-e", "versioninfo"], interactive⟩
end JuliaLean.IOCov.UtilFaithful
end

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- The `while` loop of `_crc32c(io, nb, crc)`, `base/util.jl:533-537`, with
`length(buf) = blen`: `readbytes!(io, buf)` reads `min(blen, bytesavailable(io))`. -/
def crcIoLoop : Nat → Nat → List Byte → Int → U32 → List Byte × Int × U32
  | 0, _, io, nb, crc => (io, nb, crc)
  | fuel + 1, blen, io, nb, crc =>
    if !io.isEmpty && nb > 24576 then
      let n := min blen io.length
      crcIoLoop fuel blen (io.drop n) (nb - n) (jl_crc32c crc (io.take n))
    else (io, nb, crc)

/-- `_crc32c(io::IO, nb, crc)`, `base/util.jl:528-539`: the checksum and the unread rest. -/
def crc32cIoNb (io : List Byte) (nb : Int) (crc : U32) : Jle (U32 × List Byte) :=
  if nb < 0 then .error (argErr "number of bytes to checksum must be ≥ 0") else
  let blen := (min nb 24576).toNat
  let (io, nb, crc) := crcIoLoop (io.length + 1) blen io nb crc
  let n := min (min nb blen).toNat io.length
  .ok (jl_crc32c crc (io.take n), io.drop n)

/-- `typemax(Int64)`. -/
def typemaxI64 : Int := 2 ^ 63 - 1

/-- `crc32c(io::IO, crc)` = `_crc32c(io, typemax(Int64), crc)`, `base/util.jl:540`. -/
def crc32cIo (io : List Byte) (crc : U32) : Jle (U32 × List Byte) := crc32cIoNb io typemaxI64 crc

/-- An open `IOStream` on a file. -/
structure IOStreamF where
  content : List Byte
  pos : Nat
  /-- `filesize(io)`: the size `stat` reports. -/
  statSize : Nat
  deriving Repr, DecidableEq

/-- `crc32c(io::IOStream, crc)` = `_crc32c(io, filesize(io) - position(io), crc)`,
`base/util.jl:541`; reads go to the unread content. -/
def crc32cIOStream (f : IOStreamF) (crc : U32) : Jle U32 :=
  (crc32cIoNb (f.content.drop f.pos) ((f.statSize : Int) - f.pos) crc).map (·.1)

end JuliaLean.Base64Uuid
