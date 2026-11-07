import JuliaLean.base.coreio
import JuliaLean.base.io

/-!
# Model of `base/terminfo.jl`

Typed source-mirrored model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Parser operations use `base.io.M`, preserving stream position on errors. Integer
operations wrap at Julia widths. Dictionaries are finite association lists; input
iteration order is explicit. String conversion, symbol interning, filesystem,
environment, and process-local caches are typed callees. Capability tables come
from `terminfo_data.jl` through `Tables`, without duplicating that file's data.
Terminal names and capability string values use the installed `JStr` byte-string
model, including malformed UTF-8. Symbols use their interned identities.
-/

namespace JuliaLean.base.terminfo
open JuliaLean
open JuliaLean.base.io (M Error whileLoop)
abbrev I := JInt64
abbrev Bytes := List (JInt .u8)
abbrev JString := JuliaLean.Strings.JStr
def fallbackSetaf : JString := ⟨[27, 91, 51, 37, 112, 49, 37, 100, 109], by decide⟩
def i (z : Int) : I := JInt.wrap .i64 z

def lookup {A : Type} (entries : List (String × A)) (key : String) : Option A :=
  (entries.find? (fun entry => entry.1 == key)).map Prod.snd

def put {A : Type} (entries : List (String × A)) (key : String) (value : A) : List (String × A) :=
  if entries.any (fun entry => entry.1 == key) then
    entries.map (fun entry => if entry.1 == key then (key, value) else entry)
  else entries ++ [(key, value)]

inductive Capability where
  | flag (value : Bool)
  | number (value : I)
  | string (value : JString)
  | absent
  deriving DecidableEq

structure CapabilityName where
  name : String
  capname : String

structure Tables where
  flags : List CapabilityName
  numbers : List CapabilityName
  strings : List CapabilityName
  userAlias : String → Capability → Option String

structure ParserOps (World Stream : Type) where
  readByte : Stream → M World (JInt .u8)
  readUInt16LE : Stream → M World (JInt .u16)
  readInt16LE : Stream → M World (JInt .i16)
  readExact : Stream → I → M World Bytes
  position : Stream → M World I
  eof : Stream → M World Bool
  reinterpret16LE : Bytes → M World (List (JInt .i16))
  reinterpret32LE : Bytes → M World (List (JInt .i32))
  string : Bytes → M World JString
  splitNames : JString → List JString
  ncodeunits : JString → I
  symbol : Option JString → M World String
  viewFrom : Bytes → I → M World Bytes
  slice : Bytes → I → I → M World Bytes

inductive NumberFormat where
  | int16 | int32
  deriving DecidableEq

def numberBytes : NumberFormat → I
  | .int16 => i 2
  | .int32 => i 4

def readNumbers {World Stream : Type} (ops : ParserOps World Stream)
    (stream : Stream) (format : NumberFormat) (count : I) : M World (List I) := do
  let bytes ← ops.readExact stream (count * numberBytes format)
  match format with
  | .int16 => return (← ops.reinterpret16LE bytes).map (fun n => i n.val)
  | .int32 => return (← ops.reinterpret32LE bytes).map (fun n => i n.val)

def requireNull {World Stream : Type} (ops : ParserOps World Stream)
    (stream : Stream) (message : String) : M World Unit := do
  if (← ops.readByte stream).val != 0 then throw (.jl (.argumentError message))

structure FilesystemOps (World : Type) where
  env : String → M World (Option String)
  home : M World String
  joinpath : List String → M World String
  normpath : List String → M World String
  bindir : String
  datarootdir : String
  isunix : Bool
  iswindows : Bool
  isseparator : Char → Bool
  firstCharacter : String → M World String
  firstCodeunitHex : String → M World String
  isvalid : String → Bool
  lowercase : String → String
  isdir : String → M World Bool
  isfile : String → M World Bool
  isIOError : Error → Bool

/--
Julia source: base/terminfo.jl:33-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TermInfoRaw
    names::Vector{String}
    flags::BitVector
    numbers::Vector{Int}
    strings::Vector{Union{String, Nothing}}
    extended::Union{Nothing, Dict{Symbol, Union{Bool, Int, String, Nothing}}}
end
```
-/
structure TermInfoRaw where
  names : List JString
  flags : List Bool
  numbers : List I
  strings : List (Option JString)
  extended : Option (List (String × Capability))

/--
Julia source: base/terminfo.jl:60-67 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TermInfo
    names::Vector{String}
    flags::Dict{Symbol, Bool}
    numbers::Dict{Symbol, Int}
    strings::Dict{Symbol, String}
    extensions::Union{Nothing, Set{Symbol}}
    aliases::Dict{Symbol, Symbol}
end
```
-/
structure TermInfo where
  names : List JString
  flags : List (String × Bool)
  numbers : List (String × I)
  strings : List (String × JString)
  extensions : Option (List String)
  aliases : List (String × String)

/--
Julia source: base/terminfo.jl:69-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
TermInfo() = TermInfo(String[], Dict{Symbol, Bool}(), Dict{Symbol, Int}(), Dict{Symbol, String}(), nothing, Dict{Symbol, Symbol}())
```
-/
def empty : TermInfo := ⟨[], [], [], [], none, []⟩

/--
Julia source: base/terminfo.jl:72-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_terminfo_read_bytes(data::IO, nbytes::Integer) = read!(data, Vector{UInt8}(undef, nbytes))
```
-/
def readBytes {World Stream Integer Buffer : Type}
    (allocate : Integer → M World Buffer) (readInto : Stream → Buffer → M World Buffer)
    (data : Stream) (nbytes : Integer) : M World Buffer := do
  readInto data (← allocate nbytes)

/--
Julia source: base/terminfo.jl:163-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _terminfo_read_strings(table::Vector{UInt8}, indices::Vector{Int16})
    strings = Vector{Union{Nothing, String}}(undef, length(indices))
    map!(strings, indices) do idx
        if idx >= 0
            len = findfirst(==(0x00), view(table, 1+idx:length(table)))
            !isnothing(len) ||
                throw(ArgumentError("Terminfo table entry @$idx does not terminate with a null byte"))
            String(table[1+idx:idx+len-1])
        elseif idx ∈ (-1, -2)
        else
            throw(ArgumentError("Terminfo table index is invalid: -2 ≰ $idx"))
        end
    end
    strings
end
```
-/
def readStrings {World Stream : Type} (ops : ParserOps World Stream)
    (table : Bytes) (indices : List (JInt .i16)) : M World (List (Option JString)) := do
  indices.mapM fun idx => do
    if idx.val ≥ 0 then
      let view ← ops.viewFrom table (i 1 + i idx.val)
      let len := view.findIdx? (fun byte => byte.val == 0)
      match len with
      | none => throw (.jl (.argumentError
          ("Terminfo table entry @" ++ toString idx.val ++ " does not terminate with a null byte")))
      | some len =>
        let start := i 1 + i idx.val
        let stop := i idx.val + i (Int.ofNat (len + 1)) - i 1
        return some (← ops.string (← ops.slice table start stop))
    else if idx.val == -1 || idx.val == -2 then pure none
    else throw (.jl (.argumentError ("Terminfo table index is invalid: -2 ≰ " ++ toString idx.val)))

/--
Julia source: base/terminfo.jl:117-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function extendedterminfo(data::IO, NumInt::Union{Type{Int16}, Type{Int32}})
    # Extended info
    if position(data) % 2 != 0
        0x00 == read(data, UInt8) ||
            throw(ArgumentError("Terminfo did not contain a null byte before the extended section; expected to position the start on an even byte"))
    end
    # Extended header
    flag_bytes, numbers_count, string_count, table_count, table_bytes =
        @ntuple 5 _->read(data, Int16) |> ltoh
    min(flag_bytes, numbers_count, string_count, table_count, table_bytes) >= 0 &&
        string_count <= table_count ||
        throw(ArgumentError("Terminfo extended header contains an invalid section size"))
    # Extended flags/numbers/strings
    flags = map(==(0x01), _terminfo_read_bytes(data, flag_bytes))
    if flag_bytes % 2 != 0
        0x00 == read(data, UInt8) ||
            throw(ArgumentError("Terminfo did not contain a null byte after the extended flag section; expected to position the start of the numbers section on an even byte"))
    end
    numbers = map(Int ∘ ltoh, reinterpret(NumInt, _terminfo_read_bytes(data, numbers_count * sizeof(NumInt))))
    table_indices = map(ltoh, reinterpret(Int16, _terminfo_read_bytes(data, table_count * sizeof(Int16))))
    table_data = _terminfo_read_bytes(data, table_bytes)
    strings = _terminfo_read_strings(table_data, table_indices[1:string_count])
    # The capability names follow the last string value that is present (some
    # values may be absent, including the last one), and their indices are
    # relative to the start of the names.
    names_offset = 0
    for (idx, str) in zip(table_indices, strings)
        isnothing(str) || (names_offset = max(names_offset, idx + ncodeunits(str) + 1))
    end
    for index in string_count+1:lastindex(table_indices)
        0 <= table_indices[index] <= typemax(Int16) - names_offset ||
            throw(ArgumentError("Terminfo extended capability name index is invalid"))
        table_indices[index] += names_offset
    end
    labels = map(Symbol, _terminfo_read_strings(table_data, table_indices[string_count+1:end]))
    Dict{Symbol, Union{Bool, Int, String, Nothing}}(
        zip(labels, Iterators.flatten((flags, numbers, strings))))
end
```
-/
def extendedterminfo {World Stream : Type} (ops : ParserOps World Stream)
    (data : Stream) (format : NumberFormat) : M World (List (String × Capability)) := do
  if (← ops.position data).val % 2 != 0 then
    requireNull ops data "Terminfo did not contain a null byte before the extended section; expected to position the start on an even byte"
  let flagBytes := i (← ops.readInt16LE data).val
  let numbersCount := i (← ops.readInt16LE data).val
  let stringCount := i (← ops.readInt16LE data).val
  let tableCount := i (← ops.readInt16LE data).val
  let tableBytes := i (← ops.readInt16LE data).val
  if !(flagBytes.val ≥ 0 && numbersCount.val ≥ 0 && stringCount.val ≥ 0 &&
      tableCount.val ≥ 0 && tableBytes.val ≥ 0 && stringCount ≤ tableCount) then
    throw (.jl (.argumentError "Terminfo extended header contains an invalid section size"))
  let flags := (← ops.readExact data flagBytes).map (fun b => Capability.flag (b.val == 1))
  if flagBytes.val % 2 != 0 then
    requireNull ops data "Terminfo did not contain a null byte after the extended flag section; expected to position the start of the numbers section on an even byte"
  let numbers ← readNumbers ops data format numbersCount
  let mut tableIndices ← ops.reinterpret16LE (← ops.readExact data (tableCount * i 2))
  let tableData ← ops.readExact data tableBytes
  let strings ← readStrings ops tableData (tableIndices.take stringCount.val.toNat)
  let mut namesOffset := i 0
  for (idx, str) in tableIndices.zip strings do
    if let some str := str then
      namesOffset := max namesOffset (i idx.val + ops.ncodeunits str + i 1)
  let mut suffix := []
  for idx in tableIndices.drop stringCount.val.toNat do
    if !(0 ≤ idx.val && idx.val ≤ ((i (IntTy.max .i16)) - namesOffset).val) then
      throw (.jl (.argumentError "Terminfo extended capability name index is invalid"))
    let value ← JuliaLean.base.io.liftJl (JInt.convert "convert" .i16 (i idx.val + namesOffset).val)
    suffix := suffix ++ [value]
  tableIndices := tableIndices.take stringCount.val.toNat ++ suffix
  let labels ← (← readStrings ops tableData (tableIndices.drop stringCount.val.toNat)).mapM ops.symbol
  let values := flags ++ numbers.map Capability.number ++ strings.map
    (fun value => match value with | none => .absent | some s => .string s)
  pure ((labels.zip values).foldl (fun acc (key, value) => put acc key value) [])

/--
Julia source: base/terminfo.jl:74-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(data::IO, ::Type{TermInfoRaw})
    # Parse according to `term(5)`
    # Header
    magic = read(data, UInt16) |> ltoh
    NumInt = if magic == 0o0432
        Int16
    elseif magic == 0o01036
        Int32
    else
        throw(ArgumentError("Terminfo data did not start with the magic number 0o0432 or 0o01036"))
    end
    name_bytes, flag_bytes, numbers_count, string_count, table_bytes =
        @ntuple 5 _->read(data, Int16) |> ltoh
    name_bytes >= 1 && min(flag_bytes, numbers_count, string_count, table_bytes) >= 0 ||
        throw(ArgumentError("Terminfo header contains an invalid section size"))
    # Terminal Names
    term_names = map(String, split(String(_terminfo_read_bytes(data, name_bytes - 1)), '|'))
    0x00 == read(data, UInt8) ||
        throw(ArgumentError("Terminfo data did not contain a null byte after the terminal names section"))
    # Boolean Flags
    flags = map(==(0x01), _terminfo_read_bytes(data, flag_bytes))
    if position(data) % 2 != 0
        0x00 == read(data, UInt8) ||
            throw(ArgumentError("Terminfo did not contain a null byte after the flag section, expected to position the start of the numbers section on an even byte"))
    end
    # Numbers, Strings, Table
    numbers = map(Int ∘ ltoh, reinterpret(NumInt, _terminfo_read_bytes(data, numbers_count * sizeof(NumInt))))
    string_indices = map(ltoh, reinterpret(Int16, _terminfo_read_bytes(data, string_count * sizeof(Int16))))
    strings_table = _terminfo_read_bytes(data, table_bytes)
    strings = _terminfo_read_strings(strings_table, string_indices)
    TermInfoRaw(term_names, flags, numbers, strings,
                if !eof(data) extendedterminfo(data, NumInt) end)
end
```
-/
def readRaw {World Stream : Type} (ops : ParserOps World Stream)
    (data : Stream) : M World TermInfoRaw := do
  let magic ← ops.readUInt16LE data
  let format ← if magic.val == 282 then pure NumberFormat.int16
    else if magic.val == 542 then pure NumberFormat.int32
    else throw (.jl (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"))
  let nameBytes := i (← ops.readInt16LE data).val
  let flagBytes := i (← ops.readInt16LE data).val
  let numbersCount := i (← ops.readInt16LE data).val
  let stringCount := i (← ops.readInt16LE data).val
  let tableBytes := i (← ops.readInt16LE data).val
  if !(nameBytes.val ≥ 1 && flagBytes.val ≥ 0 && numbersCount.val ≥ 0 &&
      stringCount.val ≥ 0 && tableBytes.val ≥ 0) then
    throw (.jl (.argumentError "Terminfo header contains an invalid section size"))
  let termNames := ops.splitNames (← ops.string (← ops.readExact data (nameBytes - i 1)))
  requireNull ops data "Terminfo data did not contain a null byte after the terminal names section"
  let flags := (← ops.readExact data flagBytes).map (fun b => b.val == 1)
  if (← ops.position data).val % 2 != 0 then
    requireNull ops data "Terminfo did not contain a null byte after the flag section, expected to position the start of the numbers section on an even byte"
  let numbers ← readNumbers ops data format numbersCount
  let stringIndices ← ops.reinterpret16LE (← ops.readExact data (stringCount * i 2))
  let stringsTable ← ops.readExact data tableBytes
  let strings ← readStrings ops stringsTable stringIndices
  let extended ← if !(← ops.eof data) then do
      pure (some (← extendedterminfo ops data format))
    else pure none
  pure ⟨termNames, flags, numbers, strings, extended⟩

/--
Julia source: base/terminfo.jl:209-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        longalias(key, value) = first(get(TERM_USER, (typeof(value), key), (nothing, "")))
```
-/
def longalias (tables : Tables) (key : String) (value : Capability) : Option String :=
  tables.userAlias key value

/--
Julia source: base/terminfo.jl:185-227 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function TermInfo(raw::TermInfoRaw)
    capabilities = Dict{Symbol, Union{Bool, Int, String}}()
    sizehint!(capabilities, 2 * (length(raw.flags) + length(raw.numbers) + length(raw.strings)))
    flags = Dict{Symbol, Bool}()
    numbers = Dict{Symbol, Int}()
    strings = Dict{Symbol, String}()
    aliases = Dict{Symbol, Symbol}()
    extensions = nothing
    for (flag, value) in zip(TERM_FLAGS, raw.flags)
        flags[flag.name] = value
        aliases[flag.capname] = flag.name
    end
    for (num, value) in zip(TERM_NUMBERS, raw.numbers)
        numbers[num.name] = Int(value)
        aliases[num.capname] = num.name
    end
    for (str, value) in zip(TERM_STRINGS, raw.strings)
        if !isnothing(value)
            strings[str.name] = value
            aliases[str.capname] = str.name
        end
    end
    if !isnothing(raw.extended)
        extensions = Set{Symbol}()
        longalias(key, value) = first(get(TERM_USER, (typeof(value), key), (nothing, "")))
        for (short, value) in raw.extended
            long = longalias(short, value)
            key = something(long, short)
            push!(extensions, key)
            if value isa Bool
                flags[key] = value
            elseif value isa Int
                numbers[key] = value
            elseif value isa String
                strings[key] = value
            end
            if !isnothing(long)
                aliases[short] = long
            end
        end
    end
    TermInfo(raw.names, flags, numbers, strings, extensions, aliases)
end
```
-/
def fromRaw (tables : Tables) (raw : TermInfoRaw) : TermInfo := Id.run do
  let capabilities : List (String × Capability) := []
  let _sizehint := i 2 * (i raw.flags.length + i raw.numbers.length + i raw.strings.length)
  let _ := capabilities
  let mut flags := []
  let mut numbers := []
  let mut strings := []
  let mut aliases := []
  let mut extensions := none
  for (flag, value) in tables.flags.zip raw.flags do
    flags := put flags flag.name value
    aliases := put aliases flag.capname flag.name
  for (num, value) in tables.numbers.zip raw.numbers do
    numbers := put numbers num.name value
    aliases := put aliases num.capname num.name
  for (str, value) in tables.strings.zip raw.strings do
    if let some value := value then
      strings := put strings str.name value
      aliases := put aliases str.capname str.name
  if let some extended := raw.extended then
    let mut names := []
    for (short, value) in extended do
      let long := longalias tables short value
      let key := long.getD short
      if !names.contains key then names := names ++ [key]
      match value with
      | .flag value => flags := put flags key value
      | .number value => numbers := put numbers key value
      | .string value => strings := put strings key value
      | .absent => pure ()
      if let some long := long then aliases := put aliases short long
    extensions := some names
  pure ⟨raw.names, flags, numbers, strings, extensions, aliases⟩

/--
Julia source: base/terminfo.jl:229-229 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(ti::TermInfo, key::Symbol, default::Bool)   = get(ti.flags,   get(ti.aliases, key, key), default)
```
-/
def getBool (ti : TermInfo) (key : String) (default : Bool) : Bool :=
  (lookup ti.flags ((lookup ti.aliases key).getD key)).getD default

/--
Julia source: base/terminfo.jl:230-230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(ti::TermInfo, key::Symbol, default::Int)    = get(ti.numbers, get(ti.aliases, key, key), default)
```
-/
def getInt (ti : TermInfo) (key : String) (default : I) : I :=
  (lookup ti.numbers ((lookup ti.aliases key).getD key)).getD default

/--
Julia source: base/terminfo.jl:231-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(ti::TermInfo, key::Symbol, default::String) = get(ti.strings, get(ti.aliases, key, key), default)
```
-/
def getString (ti : TermInfo) (key : String) (default : JString) : JString :=
  (lookup ti.strings ((lookup ti.aliases key).getD key)).getD default

/--
Julia source: base/terminfo.jl:233-234 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(ti::TermInfo, key::Symbol) =
    haskey(ti.flags, key) || haskey(ti.numbers, key) || haskey(ti.strings, key) || haskey(ti.aliases, key)
```
-/
def haskey (ti : TermInfo) (key : String) : Bool :=
  (lookup ti.flags key).isSome || (lookup ti.numbers key).isSome ||
  (lookup ti.strings key).isSome || (lookup ti.aliases key).isSome

/--
Julia source: base/terminfo.jl:236-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function getindex(ti::TermInfo, key::Symbol)
    haskey(ti.flags, key) && return ti.flags[key]
    haskey(ti.numbers, key) && return ti.numbers[key]
    haskey(ti.strings, key) && return ti.strings[key]
    haskey(ti.aliases, key) && return getindex(ti, ti.aliases[key])
    throw(KeyError(key))
end
```
-/
def getindex {World : Type} (ti : TermInfo) (key : String) : M World Capability :=
  whileLoop (fun key => do
    if let some value := lookup ti.flags key then return .inl (.flag value)
    if let some value := lookup ti.numbers key then return .inl (.number value)
    if let some value := lookup ti.strings key then return .inl (.string value)
    if let some alias := lookup ti.aliases key then return .inr alias
    throw (.foreignError "KeyError" key)) key

/--
Julia source: base/terminfo.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keys(ti::TermInfo) = keys(ti.flags) ∪ keys(ti.numbers) ∪ keys(ti.strings) ∪ keys(ti.aliases)
```
-/
def keys (ti : TermInfo) : List String :=
  (ti.flags.map Prod.fst ++ ti.numbers.map Prod.fst ++ ti.strings.map Prod.fst ++
    ti.aliases.map Prod.fst).foldl (fun acc key => if acc.contains key then acc else acc ++ [key]) []

/--
Julia source: base/terminfo.jl:246-252 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", ti::TermInfo)
    print(io, "TermInfo(", ti.names, "; ", length(ti.flags), " flags, ",
          length(ti.numbers), " numbers, ", length(ti.strings), " strings")
    !isnothing(ti.extensions) &&
        print(io, ", ", length(ti.extensions), " extended capabilities")
    print(io, ')')
end
```
-/
def showTermInfo {World Stream : Type} (print : Stream → String → M World Unit)
    (showNames : List JString → String) (io : Stream) (ti : TermInfo) : M World Unit := do
  print io ("TermInfo(" ++ showNames ti.names ++ "; " ++ toString ti.flags.length ++ " flags, " ++
    toString ti.numbers.length ++ " numbers, " ++ toString ti.strings.length ++ " strings")
  if let some extensions := ti.extensions then
    print io (", " ++ toString extensions.length ++ " extended capabilities")
  print io ")"

/--
Julia source: base/terminfo.jl:255-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _terminfo_stat_check(check::Function, path::String)
    try
        check(path)
    catch err
        err isa IOError || rethrow()
        false
    end
end
```
-/
def statCheck {World : Type} (isIOError : Error → Bool)
    (check : String → M World Bool) (path : String) : M World Bool := do
  try check path
  catch error => if isIOError error then pure false else throw error

/--
Julia source: base/terminfo.jl:273-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function find_terminfo_file(term::String)
    # Like ncurses, reject names that could escape the terminfo directories
    (isempty(term) || any(Filesystem.isseparator, term)) && return
    chr, chrcode = string(first(term)), string(codeunit(term, 1), base=16, pad=2)
    terminfo_dirs = if haskey(ENV, "TERMINFO")
        [ENV["TERMINFO"]]
    elseif _terminfo_stat_check(isdir, joinpath(homedir(), ".terminfo"))
        [joinpath(homedir(), ".terminfo")]
    else
        String[]
    end
    haskey(ENV, "TERMINFO_DIRS") &&
        append!(terminfo_dirs,
                String[isempty(d) ? "/usr/share/terminfo" : String(d)
                       for d in split(ENV["TERMINFO_DIRS"], ':')])
    push!(terminfo_dirs, normpath(Sys.BINDIR, DATAROOTDIR, "julia", "terminfo"))
    Sys.isunix() &&
        push!(terminfo_dirs, "/etc/terminfo", "/lib/terminfo", "/usr/share/terminfo")
    # The vendored terminfo database is fully lowercase to avoid issues on
    # case-sensitive filesystems. On Unix-like systems, terminfo files with
    # different cases are hard links to one another, so the last candidate is
    # still correct for non-vendored terminfo, just redundant.
    lchr, lterm = isvalid(term) ? (lowercase(chr), lowercase(term)) : (chr, term)
    candidates = ((chr, term), (chrcode, term), (lchr, lterm))
    for dir in terminfo_dirs, (subdir, name) in candidates
        path = joinpath(dir, subdir, name)
        _terminfo_stat_check(isfile, path) && return path
    end
    return nothing
end
```
-/
def findTerminfoFile {World : Type} (ops : FilesystemOps World)
    (term : String) : M World (Option String) := do
  if term.isEmpty || term.toList.any ops.isseparator then return none
  let chr ← ops.firstCharacter term
  let chrcode ← ops.firstCodeunitHex term
  let mut dirs ← match ← ops.env "TERMINFO" with
    | some dir => pure [dir]
    | none => do
      let homePath ← ops.joinpath [← ops.home, ".terminfo"]
      if ← statCheck ops.isIOError ops.isdir homePath then
        pure [← ops.joinpath [← ops.home, ".terminfo"]]
      else pure []
  if let some value ← ops.env "TERMINFO_DIRS" then
    dirs := dirs ++ (value.splitOn ":").map (fun dir => if dir.isEmpty then "/usr/share/terminfo" else dir)
  dirs := dirs ++ [← ops.normpath [ops.bindir, ops.datarootdir, "julia", "terminfo"]]
  if ops.isunix then dirs := dirs ++ ["/etc/terminfo", "/lib/terminfo", "/usr/share/terminfo"]
  let (lchr, lterm) := if ops.isvalid term then (ops.lowercase chr, ops.lowercase term) else (chr, term)
  let candidates := [(chr, term), (chrcode, term), (lchr, lterm)]
  for dir in dirs do
    for (subdir, name) in candidates do
      let path ← ops.joinpath [dir, subdir, name]
      if ← statCheck ops.isIOError ops.isfile path then return some path
  pure none

/--
Julia source: base/terminfo.jl:312-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_terminfo(term::String)
    try
        file = find_terminfo_file(term)
        isnothing(file) && return TermInfo()
        TermInfo(read(file, TermInfoRaw))
    catch err
        if err isa ArgumentError || err isa IOError || err isa EOFError || err isa SystemError
            TermInfo()
        else
            rethrow()
        end
    end
end
```
-/
def loadTerminfo {World : Type} (ops : FilesystemOps World) (tables : Tables)
    (readFile : String → M World TermInfoRaw)
    (term : String) : M World TermInfo := do
  try
    let file ← findTerminfoFile ops term
    match file with
    | none => pure empty
    | some file => return fromRaw tables (← readFile file)
  catch error =>
    match error with
    | .jl (.argumentError _) => pure empty
    | .eofError => pure empty
    | .foreignError "IOError" _ => pure empty
    | .foreignError "SystemError" _ => pure empty
    | _ => throw error

/--
Julia source: base/terminfo.jl:329-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const current_terminfo = OncePerProcess{TermInfo}() do
    term_env = get(ENV, "TERM", @static Sys.iswindows() ? "" : "dumb")
    terminfo = load_terminfo(term_env)
    # Ensure setaf is set for xterm terminals
    if !haskey(terminfo, :setaf) && startswith(term_env, "xterm")
        # For xterm-like terminals without setaf, add a reasonable default
        terminfo.strings[:setaf] = "\e[3%p1%dm"
    end
    return terminfo
end
```
-/
def initializeCurrent {World : Type} (ops : FilesystemOps World)
    (load : String → M World TermInfo) : M World TermInfo := do
  let termEnv := (← ops.env "TERM").getD (if ops.iswindows then "" else "dumb")
  let mut terminfo ← load termEnv
  if !haskey terminfo "setaf" && termEnv.startsWith "xterm" then
    terminfo := { terminfo with strings := put terminfo.strings "setaf" fallbackSetaf }
  pure terminfo

/--
Julia source: base/terminfo.jl:329-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const current_terminfo = OncePerProcess{TermInfo}() do
    term_env = get(ENV, "TERM", @static Sys.iswindows() ? "" : "dumb")
    terminfo = load_terminfo(term_env)
    # Ensure setaf is set for xterm terminals
    if !haskey(terminfo, :setaf) && startswith(term_env, "xterm")
        # For xterm-like terminals without setaf, add a reasonable default
        terminfo.strings[:setaf] = "\e[3%p1%dm"
    end
    return terminfo
end
```
-/
def currentTerminfo {World OncePerProcess : Type}
    (construct : M World TermInfo → M World OncePerProcess)
    (ops : FilesystemOps World) (load : String → M World TermInfo) : M World OncePerProcess :=
  construct (initializeCurrent ops load)

/--
Julia source: base/terminfo.jl:343-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    ttyhascolor() = true
```
-/
def ttyhascolorWindows : Bool := true

/--
Julia source: base/terminfo.jl:345-347 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function ttyhascolor()
        haskey(current_terminfo(), :setaf)
    end
```
-/
def ttyhascolorUnix {World : Type} (current : M World TermInfo) : M World Bool := do
  pure (haskey (← current) "setaf")

/--
Julia source: base/terminfo.jl:383-400 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ttyhastruecolor()
    # Lasciate ogne speranza, voi ch'intrate
    get(ENV, "COLORTERM", "") ∈ ("truecolor", "24bit") ||
        get(current_terminfo(), :RGB, false) || get(current_terminfo(), :Tc, false) ||
        (haskey(current_terminfo(), :setrgbf) && haskey(current_terminfo(), :setrgbb)) ||
        @static if Sys.isunix() get(current_terminfo(), :colors, 0) > 256 else false end ||
        (Sys.iswindows() && Sys.windows_version() ≥ v"10.0.14931") || # See <https://devblogs.microsoft.com/commandline/24-bit-color-in-the-windows-console/>
        something(tryparse(Int, get(ENV, "VTE_VERSION", "")), 0) >= 3600 || # Per GNOME bug #685759 <https://bugzilla.gnome.org/show_bug.cgi?id=685759>
        haskey(ENV, "XTERM_VERSION") ||
        get(ENV, "TERMINAL_PROGRAM", "") == "iTerm.app" || # Why does Apple need to be special?
        haskey(ENV, "KONSOLE_PROFILE_NAME") || # Per commentary in VT102Emulation.cpp
        haskey(ENV, "KONSOLE_DBUS_SESSION") ||
        let term = get(ENV, "TERM", "")
            startswith(term, "linux") || # Linux 4.8+ supports true-colour SGR.
                startswith(term, "rxvt") || # See <http://lists.schmorp.de/pipermail/rxvt-unicode/2016q2/002261.html>
                startswith(term, "st") # From experimentation
        end
end
```
-/
def ttyhastruecolor {World : Type} (env : String → M World (Option String))
    (current : M World TermInfo) (isunix iswindows : Bool) (windowsAtLeast14931 : M World Bool)
    (tryparseInt : String → Option I) : M World Bool := do
  let colorterm := (← env "COLORTERM").getD ""
  if colorterm == "truecolor" || colorterm == "24bit" then return true
  if getBool (← current) "RGB" false then return true
  if getBool (← current) "Tc" false then return true
  if haskey (← current) "setrgbf" then
    if haskey (← current) "setrgbb" then return true
  if isunix then
    if (getInt (← current) "colors" (i 0)).val > 256 then return true
  if iswindows then
    if ← windowsAtLeast14931 then return true
  if ((tryparseInt ((← env "VTE_VERSION").getD "")).getD (i 0)).val ≥ 3600 then return true
  if (← env "XTERM_VERSION").isSome then return true
  if (← env "TERMINAL_PROGRAM").getD "" == "iTerm.app" then return true
  if (← env "KONSOLE_PROFILE_NAME").isSome then return true
  if (← env "KONSOLE_DBUS_SESSION").isSome then return true
  let term := (← env "TERM").getD ""
  pure (term.startsWith "linux" || term.startsWith "rxvt" || term.startsWith "st")

/--
Julia source: base/terminfo.jl:402-406 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_have_color()
    global have_color
    have_color === nothing && (have_color = ttyhascolor())
    return have_color::Bool
end
```
-/
def getHaveColor {World : Type} (getCache : M World (Option Bool))
    (setCache : Bool → M World Unit) (detect : M World Bool) : M World Bool := do
  if (← getCache).isNone then setCache (← detect)
  match ← getCache with
  | some value => pure value
  | none => throw (.foreignError "TypeError" "expected Bool")

/--
Julia source: base/terminfo.jl:408-412 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_have_truecolor()
    global have_truecolor
    have_truecolor === nothing && (have_truecolor = ttyhastruecolor())
    return have_truecolor::Bool
end
```
-/
def getHaveTruecolor {World : Type} (getCache : M World (Option Bool))
    (setCache : Bool → M World Unit) (detect : M World Bool) : M World Bool := do
  if (← getCache).isNone then setCache (← detect)
  match ← getCache with
  | some value => pure value
  | none => throw (.foreignError "TypeError" "expected Bool")

/--
Julia source: base/terminfo.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
in(key_value::Pair{Symbol,Bool}, ::TTY) = key_value.first === :color && key_value.second === get_have_color()
```
-/
def containsTTY {World : Type} (getHaveColor : M World Bool)
    (keyValue : String × Bool) : M World Bool := do
  if keyValue.1 != "color" then return false
  return keyValue.2 == (← getHaveColor)

/--
Julia source: base/terminfo.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
haskey(::TTY, key::Symbol) = key === :color
```
-/
def haskeyTTY (key : String) : Bool := key == "color"

/--
Julia source: base/terminfo.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
getindex(::TTY, key::Symbol) = key === :color ? get_have_color() : throw(KeyError(key))
```
-/
def getindexTTY {World : Type} (getHaveColor : M World Bool) (key : String) : M World Bool := do
  if key == "color" then getHaveColor else throw (.foreignError "KeyError" key)

/--
Julia source: base/terminfo.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
get(::TTY, key::Symbol, default) = key === :color ? get_have_color() : default
```
-/
def getTTY {World Value : Type} (ofBool : Bool → Value)
    (getHaveColor : M World Bool) (key : String) (default : Value) : M World Value := do
  if key == "color" then return ofBool (← getHaveColor) else pure default


/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/terminfo.jl:1-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # Since this code is in the startup-path, we go to some effort to
-- # be easier on the compiler, such as using `map` over broadcasting.
-- 
-- include("terminfo_data.jl")
-- 
-- """
--     struct TermInfoRaw
-- 
-- A structured representation of a terminfo file, without any knowledge of
-- particular capabilities, solely based on `term(5)`.
-- 
-- !!! warning
--     This is not part of the public API, and thus subject to change without notice.
-- 
-- # Fields
-- 
-- - `names::Vector{String}`: The names this terminal is known by.
-- - `flags::BitVector`: A list of 0–$(length(TERM_FLAGS)) flag values.
-- - `numbers::Union{Vector{Int16}, Vector{Int32}}`: A list of 0–$(length(TERM_NUMBERS))
--   number values. A value of `typemax(eltype(numbers))` is used to skip over
--   unspecified capabilities while ensuring value indices are correct.
-- - `strings::Vector{Union{String, Nothing}}`: A list of 0–$(length(TERM_STRINGS))
--   string values. A value of `nothing` is used to skip over unspecified
--   capabilities while ensuring value indices are correct.
-- - `extended::Union{Nothing, Dict{Symbol, Union{Bool, Int, String}}}`: Should an
--   extended info section exist, this gives the entire extended info as a
--   dictionary. Otherwise `nothing`.
-- 
-- See also: `TermInfo` and `TermCapability`.
-- """
-- /Source

-- Source: base/terminfo.jl:40-59 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     struct TermInfo
-- 
-- A parsed terminfo paired with capability information.
-- 
-- !!! warning
--     This is not part of the public API, and thus subject to change without notice.
-- 
-- # Fields
-- 
-- - `names::Vector{String}`: The names this terminal is known by.
-- - `flags::Dict{Symbol, Bool}`: A mapping of flag capability names to their values.
-- - `numbers::Dict{Symbol, Int}`: A mapping of number capability names to their values.
-- - `strings::Dict{Symbol, String}`: A mapping of string capability names to their values.
-- - `extensions::Union{Nothing, Set{Symbol}}`: The set of extended capability names, or `nothing` if there are no extensions.
-- - `aliases::Dict{Symbol, Symbol}`: A mapping of alias names to their corresponding capability names in any of the above categories.
-- 
-- See also: `TermInfoRaw` and `TermCapability`.
-- """
-- /Source

-- Source: base/terminfo.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:70-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Read exactly `nbytes` bytes, throwing an `EOFError` if `data` is too short
-- /Source

-- Source: base/terminfo.jl:73-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:107-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     extendedterminfo(data::IO; NumInt::Union{Type{Int16}, Type{Int32}})
-- 
-- Read an extended terminfo section from `data`, with `NumInt` as the numbers type.
-- 
-- This will accept any terminfo content that conforms with `term(5)`.
-- 
-- See also: `read(::IO, ::Type{TermInfoRaw})`
-- """
-- /Source

-- Source: base/terminfo.jl:155-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     _terminfo_read_strings(table::Vector{UInt8}, indices::Vector{Int16})
-- 
-- From `table`, read a string starting at each position in `indices`. Each string
-- must be null-terminated. Should an index be -1 or -2, `nothing` is given instead
-- of a string.
-- """
-- /Source

-- Source: base/terminfo.jl:178-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     TermInfo(raw::TermInfoRaw)
-- 
-- Construct a `TermInfo` from `raw`, using known terminal capabilities (as of
-- NCurses 6.3, see `TERM_FLAGS`, `TERM_NUMBERS`, and `TERM_STRINGS`).
-- """
-- /Source

-- Source: base/terminfo.jl:228-228 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:232-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:235-235 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:253-254 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Treat paths that cannot be accessed (e.g. EACCES or ELOOP) as absent, as ncurses does
-- /Source

-- Source: base/terminfo.jl:263-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     find_terminfo_file(term::String)
-- 
-- Locate the terminfo file for `term`, return `nothing` if none could be found.
-- 
-- The lookup policy is described in `terminfo(5)` "Fetching Compiled
-- Descriptions". A terminfo database is included by default with Julia and is
-- taken to be the first entry of `@TERMINFO_DIRS@`.
-- """
-- /Source

-- Source: base/terminfo.jl:303-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
--     load_terminfo(term::String)
-- 
-- Load the `TermInfo` for `term`, falling back on a blank `TermInfo`.
-- 
-- This is used to initialize `current_terminfo`, which is needed to start the REPL
-- and to print errors, so an unreadable or malformed terminfo file must not be fatal.
-- """
-- /Source

-- Source: base/terminfo.jl:325-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- """
-- The terminfo of the current terminal.
-- """
-- /Source

-- Source: base/terminfo.jl:339-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Legacy/TTY methods and the `:color` parameter
-- 
-- if Sys.iswindows()
-- /Source

-- Source: base/terminfo.jl:344-344 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- else
-- /Source

-- Source: base/terminfo.jl:348-382 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- end
-- 
-- """
--     ttyhastruecolor()
-- 
-- Return a boolean signifying whether the current terminal supports 24-bit colors.
-- 
-- Multiple conditions are taken as signifying truecolor support, specifically any of the following:
-- - The `COLORTERM` environment variable is set to `"truecolor"` or `"24bit"`
-- - The current terminfo sets the [`RGB`
--   capability](https://invisible-island.net/ncurses/man/user_caps.5.html#h3-Recognized-Capabilities)[^1]
--   (or the legacy `Tc` capability[^2]) flag
-- - The current terminfo provides `setrgbf` and `setrgbb` strings[^3]
-- - The current terminfo has a `colors` number greater that `256`, on a unix system
-- - The VTE version is at least 3600 (detected via the `VTE_VERSION` environment variable)
-- - The current terminal has the `XTERM_VERSION` environment variable set
-- - The current terminal appears to be iTerm according to the `TERMINAL_PROGRAM` environment variable
-- - The `TERM` environment variable corresponds to: linuxvt, rxvt, or st
-- 
-- [^1]: Added to Ncurses 6.1, and used in `TERM=*-direct` terminfos.
-- [^2]: Convention [added to tmux in 2016](https://github.com/tmux/tmux/commit/427b8204268af5548d09b830e101c59daa095df9),
--       superseded by `RGB`.
-- [^3]: Proposed by [Rüdiger Sonderfeld in 2013](https://lists.gnu.org/archive/html/bug-ncurses/2013-10/msg00007.html),
--       adopted by a few terminal emulators.
-- 
-- !!! note
--     The set of conditions is messy, because the situation is a mess, and there's
--     no resolution in sight. `COLORTERM` is widely accepted, but an imperfect
--     solution because only `TERM` is passed across `ssh` sessions. Terminfo is
--     the obvious place for a terminal to declare capabilities, but it's taken
--     enough years for ncurses/terminfo to declare a standard capability (`RGB`)
--     that a number of other approaches have taken root. Furthermore, the official
--     `RGB` capability is *incompatible* with 256-color operation, and so is
--     unable to resolve the fragmentation in the terminal ecosystem.
-- """
-- /Source

-- Source: base/terminfo.jl:401-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:407-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/terminfo.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.terminfo


/-!
# `base/terminfo.jl`

The terminfo reader runs on an `IOBuffer` over a byte list (`Rd`): `position`
is the number of bytes consumed, `read(io, nb)` returns
`min(nb, bytesavailable(io))` bytes, and reading a fixed-size integer past the
end throws `EOFError`. Integers are little-endian (`ltoh` is the identity on
the little-endian hosts Julia supports).

A `TermInfo` keeps its dictionaries as association lists in insertion order;
`setKey` overwrites an existing key in place, as `Dict` assignment does.
The capability tables `TERM_FLAGS`, `TERM_NUMBERS`, `TERM_STRINGS` (name,
capname pairs) and `TERM_USER` are parameters.
-/

namespace JuliaLean.ShowCov.TermInfo

open JuliaLean.ShowCov

/-- An `IOBuffer` over `data`, positioned after `pos` bytes. -/
structure Rd where
  data : List UInt8
  pos : Nat
  deriving DecidableEq, Repr

def Rd.rest (r : Rd) : List UInt8 := r.data.drop r.pos

/-- `eof(data)`. -/
def Rd.eof (r : Rd) : Bool := r.data.length ≤ r.pos

/-- `read(data, nb)` on an `IOBuffer`: `read!(io, StringVector(min(nb, bytesavailable(io))))`.
A negative length fails converting to the `UInt` allocation size
(`InexactError`, observed on both pinned versions). -/
def readN (r : Rd) (nb : Int) : R (List UInt8 × Rd) :=
  let k := min nb (r.data.length - r.pos : Nat)
  if k < 0 then .error (.inexactError "convert")
  else .ok (r.rest.take k.toNat, { r with pos := r.pos + k.toNat })

/-- `_terminfo_read_bytes`, `base/terminfo.jl:72`: a short read throws EOF. -/
def readExact (r : Rd) (nb : Nat) : R (List UInt8 × Rd) :=
  if nb ≤ r.rest.length then
    .ok (r.rest.take nb, { r with pos := r.pos + nb })
  else .error .eofError

/-- Negative vector dimensions fail before reading. -/
def terminfoReadBytes (r : Rd) (nb : Int) : R (List UInt8 × Rd) :=
  if nb < 0 then .error (.argumentError "invalid Array dimensions")
  else readExact r nb.toNat



/-- `read(data, UInt8)`. -/
def readU8 (r : Rd) : R (UInt8 × Rd) :=
  match r.rest with
  | b :: _ => .ok (b, { r with pos := r.pos + 1 })
  | [] => .error .eofError

/-- Little-endian signed value of a byte list of width `w` bytes. -/
def leSigned (w : Nat) (bs : List UInt8) : Int :=
  let u : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0
  if u < 2 ^ (8 * w - 1) then u else (u : Int) - 2 ^ (8 * w)

/-- `read(data, Int16)`, `read(data, UInt16)` (unsigned), with `EOFError` when
fewer than two bytes remain. -/
def readI16 (r : Rd) : R (Int × Rd) :=
  match r.rest with
  | a :: b :: _ => .ok (leSigned 2 [a, b], { r with pos := r.pos + 2 })
  | _ => .error .eofError
def readU16 (r : Rd) : R (Nat × Rd) :=
  match r.rest with
  | a :: b :: _ => .ok (a.toNat + 256 * b.toNat, { r with pos := r.pos + 2 })
  | _ => .error .eofError

/-- `reinterpret(NumInt, bytes)` for a `Vector{UInt8}`: chunks of `w` bytes; a
length that is not a multiple of `w` is an `ArgumentError`. -/
def reinterpretIntsF (w : Nat) : Nat → List UInt8 → R (List Int)
  | _, [] => .ok []
  | 0, _ :: _ => .error (.argumentError "cannot reinterpret")
  | fuel + 1, b :: bs =>
    if w = 0 then .error (.argumentError "cannot reinterpret")
    else if (b :: bs).length < w then .error (.argumentError "cannot reinterpret")
    else do
      let rest ← reinterpretIntsF w fuel ((b :: bs).drop w)
      pure (leSigned w ((b :: bs).take w) :: rest)

/-- Each chunk consumes at least one byte, so `length` rounds of fuel suffice. -/
def reinterpretInts (w : Nat) (bytes : List UInt8) : R (List Int) :=
  reinterpretIntsF w bytes.length bytes

/-- `split(s, '|')` on the bytes of a `String` (all pieces kept). -/
def splitBar : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: bs =>
    let rest := splitBar bs
    if b = 0x7C then [] :: rest
    else match rest with
      | p :: ps => (b :: p) :: ps
      | [] => [[b]]

/-- The bytes of `table` from 0-based offset `idx` up to (not including) the
first NUL, if there is one. -/
def cstringAt (table : List UInt8) (idx : Nat) : Option (List UInt8) :=
  let tail := table.drop idx
  if (0 : UInt8) ∈ tail then some (tail.takeWhile (· ≠ 0)) else none

/-- `_terminfo_read_strings(table, indices)`, `base/terminfo.jl:148-162`:
`none` is `nothing`. -/
def readString (table : List UInt8) (idx : Int) : R (Option (List UInt8)) :=
  if idx ≥ 0 then
    match cstringAt table idx.toNat with
    | some s => .ok (some s)
    | none => .error (.argumentError "Terminfo table entry does not terminate with a null byte")
  else if idx = -1 ∨ idx = -2 then .ok none
  else .error (.argumentError "Terminfo table index is invalid")

def readStrings (table : List UInt8) (indices : List Int) : R (List (Option (List UInt8))) :=
  indices.mapM (readString table)

/-- Extended capability names start after the furthest present value,
`base/terminfo.jl:142-148`. Indices paired with absent strings are ignored. -/
def extendedNamesOffset (indices : List Int) (strings : List (Option (List UInt8))) : Int :=
  (indices.zip strings).foldl (fun offset (idx, str) =>
    match str with
    | none => offset
    | some bytes => max offset (idx + bytes.length + 1)) 0


/-- Values of an extended capability. -/
inductive Val where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : List UInt8)
  | nothing
  deriving DecidableEq, Repr

/-- `TermInfoRaw`, `base/terminfo.jl:33-39`. -/
structure Raw where
  names : List (List UInt8)
  flags : List Bool
  numbers : List Int
  strings : List (Option (List UInt8))
  extended : Option (List (List UInt8 × Val))
  deriving DecidableEq, Repr

/-- If `position(data)` is odd, read the pad byte, which must be NUL. -/
def alignEven (r : Rd) (msg : String) : R Rd :=
  if r.pos % 2 ≠ 0 then do
    let (b, r) ← readU8 r
    if b = 0 then pure r else .error (.argumentError msg)
  else pure r

/-- `Dict(zip(labels, values))`: later duplicates overwrite earlier ones. -/
def dictOfPairs (ps : List (List UInt8 × Val)) : List (List UInt8 × Val) :=
  ps.foldl (fun d (k, v) => if d.any (·.1 == k) then d.map (fun e => if e.1 == k then (k, v) else e) else d ++ [(k, v)]) []
/-- Extended-section parser from the previous nightly, retained for its
historical counterexample. -/
def extendedterminfoHistorical (r : Rd) (w : Nat) : R (List (List UInt8 × Val) × Rd) := do
  let r ← (if r.pos % 2 ≠ 0 then do
      let (b, r) ← readU8 r
      if b = 0 then pure r else .error (.argumentError "Terminfo did not contain a null byte before the extended section")
    else pure r)
  let (flagBytes, r) ← readI16 r
  let (numbersCount, r) ← readI16 r
  let (stringCount, r) ← readI16 r
  let (tableCount, r) ← readI16 r
  let (tableBytes, r) ← readI16 r
  let (fb, r) ← readN r flagBytes
  let flags := fb.map (· == 1)
  let r ← (if flagBytes % 2 ≠ 0 then do
      let (b, r) ← readU8 r
      if b = 0 then pure r else .error (.argumentError "Terminfo did not contain a null byte after the extended flag section")
    else pure r)
  let (nb, r) ← readN r (numbersCount * (w : Int))
  let numbers ← reinterpretInts w nb
  let (ib, r) ← readN r (tableCount * 2)
  let tableIndices ← reinterpretInts 2 ib
  let (tableData, r) ← readN r tableBytes
  if stringCount < 0 ∨ tableIndices.length < stringCount.toNat then .error .boundsError else
  let strings ← readStrings tableData (tableIndices.take stringCount.toNat)
  let lastIdx : Int := if 1 ≤ stringCount then tableIndices.getD (stringCount.toNat - 1) 0 else 0
  let lastLen : Nat := match strings.getLast? with
    | some (some s) => s.length
    | _ => 0
  let labelIdx := (tableIndices.drop stringCount.toNat).map (· + (lastIdx + lastLen + 1))
  let labels ← readStrings tableData labelIdx
  let values : List Val := flags.map Val.bool ++ numbers.map Val.int ++
    strings.map (fun s => match s with | some s => Val.str s | none => Val.nothing)
  let labels ← labels.mapM (fun l => match l with | some l => .ok l | none => .error (.methodError "Symbol"))
  pure (dictOfPairs (labels.zip values), r)

/-- Raw parser from the previous nightly. -/
def readRawHistorical (data : List UInt8) : R Raw := do
  let r : Rd := ⟨data, 0⟩
  let (magic, r) ← readU16 r
  let w : Nat ← (if magic = 0o432 then pure 2 else if magic = 0o1036 then pure 4 else
    .error (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"))
  let (nameBytes, r) ← readI16 r
  let (flagBytes, r) ← readI16 r
  let (numbersCount, r) ← readI16 r
  let (stringCount, r) ← readI16 r
  let (tableBytes, r) ← readI16 r
  let (nm, r) ← readN r (nameBytes - 1)
  let termNames := splitBar nm
  let (z, r) ← readU8 r
  if z ≠ 0 then .error (.argumentError "Terminfo data did not contain a null byte after the terminal names section") else
  let (fb, r) ← readN r flagBytes
  let flags := fb.map (· == 1)
  let r ← alignEven r "Terminfo did not contain a null byte after the flag section"
  let (nb, r) ← readN r (numbersCount * (w : Int))
  let numbers ← reinterpretInts w nb
  let (sb, r) ← readN r (stringCount * 2)
  let stringIndices ← reinterpretInts 2 sb
  let (table, r) ← readN r tableBytes
  let strings ← readStrings table stringIndices
  let ext ← (if !r.eof then do let (e, _) ← extendedterminfoHistorical r w; pure (some e) else pure none)
  pure ⟨termNames, flags, numbers, strings, ext⟩


/-- `extendedterminfo(data, NumInt)`, `base/terminfo.jl:112-139`; `w` is
`sizeof(NumInt)`. -/
def extendedterminfo (r : Rd) (w : Nat) : R (List (List UInt8 × Val) × Rd) := do
  let r ← (if r.pos % 2 ≠ 0 then do
      let (b, r) ← readU8 r
      if b = 0 then pure r else .error (.argumentError "Terminfo did not contain a null byte before the extended section")
    else pure r)
  let (flagBytes, r) ← readI16 r
  let (numbersCount, r) ← readI16 r
  let (stringCount, r) ← readI16 r
  let (tableCount, r) ← readI16 r
  let (tableBytes, r) ← readI16 r
  if flagBytes < 0 ∨ numbersCount < 0 ∨ stringCount < 0 ∨ tableCount < 0 ∨
      tableBytes < 0 ∨ stringCount > tableCount then
    .error (.argumentError "Terminfo extended header contains an invalid section size") else
  let (fb, r) ← readExact r flagBytes.toNat
  let flags := fb.map (· == 1)
  let r ← (if flagBytes % 2 ≠ 0 then do
      let (b, r) ← readU8 r
      if b = 0 then pure r else .error (.argumentError "Terminfo did not contain a null byte after the extended flag section")
    else pure r)
  let (nb, r) ← readExact r (numbersCount.toNat * w)
  let numbers ← reinterpretInts w nb
  let (ib, r) ← readExact r (tableCount.toNat * 2)
  let tableIndices ← reinterpretInts 2 ib
  let (tableData, r) ← readExact r tableBytes.toNat
  let strings ← readStrings tableData (tableIndices.take stringCount.toNat)
  let namesOffset := extendedNamesOffset tableIndices strings
  let nameIndices := tableIndices.drop stringCount.toNat
  if nameIndices.any (fun idx => idx < 0 ∨ idx > 32767 - namesOffset) then
    .error (.argumentError "Terminfo extended capability name index is invalid") else
  let labelIdx := nameIndices.map (· + namesOffset)
  let labels ← readStrings tableData labelIdx
  let values : List Val := flags.map Val.bool ++ numbers.map Val.int ++
    strings.map (fun s => match s with | some s => Val.str s | none => Val.nothing)
  -- `map(Symbol, ...)` of a `nothing` label is a `MethodError`
  let labels ← labels.mapM (fun l => match l with | some l => .ok l | none => .error (.methodError "Symbol"))
  pure (dictOfPairs (labels.zip values), r)

/-- `read(data::IO, ::Type{TermInfoRaw})`, `base/terminfo.jl:74-106`,
starting at the stream's current position. -/
def readRawAt (r : Rd) : R Raw := do
  let (magic, r) ← readU16 r
  let w : Nat ← (if magic = 0o432 then pure 2 else if magic = 0o1036 then pure 4 else
    .error (.argumentError "Terminfo data did not start with the magic number 0o0432 or 0o01036"))
  let (nameBytes, r) ← readI16 r
  let (flagBytes, r) ← readI16 r
  let (numbersCount, r) ← readI16 r
  let (stringCount, r) ← readI16 r
  let (tableBytes, r) ← readI16 r
  if nameBytes < 1 ∨ flagBytes < 0 ∨ numbersCount < 0 ∨ stringCount < 0 ∨ tableBytes < 0 then
    .error (.argumentError "Terminfo header contains an invalid section size") else
  let (nm, r) ← readExact r (nameBytes - 1).toNat
  let termNames := splitBar nm
  let (z, r) ← readU8 r
  if z ≠ 0 then .error (.argumentError "Terminfo data did not contain a null byte after the terminal names section") else
  let (fb, r) ← readExact r flagBytes.toNat
  let flags := fb.map (· == 1)
  let r ← alignEven r "Terminfo did not contain a null byte after the flag section"
  let (nb, r) ← readExact r (numbersCount.toNat * w)
  let numbers ← reinterpretInts w nb
  let (sb, r) ← readExact r (stringCount.toNat * 2)
  let stringIndices ← reinterpretInts 2 sb
  let (table, r) ← readExact r tableBytes.toNat
  let strings ← readStrings table stringIndices
  let ext ← (if !r.eof then do let (e, _) ← extendedterminfo r w; pure (some e) else pure none)
  pure ⟨termNames, flags, numbers, strings, ext⟩

/-- Reader convenience for a stream positioned at the beginning. -/
def readRaw (data : List UInt8) : R Raw := readRawAt ⟨data, 0⟩

/-! ## `TermInfo` -/

/-- One `TermCapability`: long name and short capname. -/
structure Cap where
  name : String
  capname : String
  deriving DecidableEq, Repr

/-- `TermInfo`, `base/terminfo.jl:60-67`. Keys are capability names. -/
structure TI where
  names : List (List UInt8)
  flags : List (String × Bool)
  numbers : List (String × Int)
  strings : List (String × List UInt8)
  extensions : Option (List String)
  aliases : List (String × String)
  deriving DecidableEq, Repr

/-- `TermInfo()`, `base/terminfo.jl:69`. -/
def blank : TI := ⟨[], [], [], [], none, []⟩

/-- `d[k] = v`. -/
def setKey {β} (d : List (String × β)) (k : String) (v : β) : List (String × β) :=
  if d.any (·.1 == k) then d.map (fun e => if e.1 == k then (k, v) else e) else d ++ [(k, v)]

/-- `get(d, k, default)`. -/
def getKey {β} (d : List (String × β)) (k : String) (default : β) : β :=
  match d.find? (·.1 == k) with
  | some (_, v) => v
  | none => default

def hasKey {β} (d : List (String × β)) (k : String) : Bool := d.any (·.1 == k)

/-- `push!(s, k)` on a `Set`. -/
def pushSet (s : List String) (k : String) : List String := if k ∈ s then s else s ++ [k]

/-- The string form of a terminfo label (`Symbol(bytes)`); labels and keys are
compared as these strings. -/
def keyOf (bs : List UInt8) : String := String.ofList (bs.map (fun b => Char.ofNat b.toNat))

/-- `TermInfo(raw::TermInfoRaw)`, `base/terminfo.jl:170-212`, including
`longalias(key, value) = first(get(TERM_USER, (typeof(value), key), (nothing, "")))`
(`base/terminfo.jl:194`); `termUser kind short` is that lookup, with `kind`
`0`/`1`/`2`/`3` for `Bool`/`Int`/`String`/`Nothing`. -/
def ofRaw (termFlags termNumbers termStrings : List Cap)
    (termUser : Nat → String → Option String) (raw : Raw) : TI :=
  -- `for (flag, value) in zip(TERM_FLAGS, raw.flags)`
  let (flags, aliases) := (termFlags.zip raw.flags).foldl
    (fun (fl, al) (flag, value) => (setKey fl flag.name value, setKey al flag.capname flag.name))
    (([] : List (String × Bool)), ([] : List (String × String)))
  -- `for (num, value) in zip(TERM_NUMBERS, raw.numbers)`
  let (numbers, aliases) := (termNumbers.zip raw.numbers).foldl
    (fun (nu, al) (num, value) => (setKey nu num.name value, setKey al num.capname num.name))
    (([] : List (String × Int)), aliases)
  -- `for (str, value) in zip(TERM_STRINGS, raw.strings)`, skipping `nothing`
  let (strings, aliases) := (termStrings.zip raw.strings).foldl
    (fun (st, al) (str, value) => match value with
      | some v => (setKey st str.name v, setKey al str.capname str.name)
      | none => (st, al))
    (([] : List (String × List UInt8)), aliases)
  match raw.extended with
  | none => ⟨raw.names, flags, numbers, strings, none, aliases⟩
  | some ext =>
    -- `for (short, value) in raw.extended`
    let (fl, nu, st, al, exts) := ext.foldl
      (fun (fl, nu, st, al, exts) (shortB, value) =>
        let short := keyOf shortB
        let kind := match value with | .bool _ => 0 | .int _ => 1 | .str _ => 2 | .nothing => 3
        let long := termUser kind short
        let key := long.getD short
        let exts := pushSet exts key
        let (fl, nu, st) := match value with
          | .bool b => (setKey fl key b, nu, st)
          | .int n => (fl, setKey nu key n, st)
          | .str s => (fl, nu, setKey st key s)
          | .nothing => (fl, nu, st)
        let al := match long with
          | some l => setKey al short l
          | none => al
        (fl, nu, st, al, exts))
      (flags, numbers, strings, aliases, ([] : List String))
    ⟨raw.names, fl, nu, st, some exts, al⟩

/-- Capability values a lookup can return. -/
inductive CapVal where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : List UInt8)
  deriving DecidableEq, Repr

/-- `get(ti, key, default::Bool)`, `::Int`, `::String`, `base/terminfo.jl:214-216`. -/
def getBool (ti : TI) (key : String) (default : Bool) : Bool :=
  getKey ti.flags (getKey ti.aliases key key) default
def getInt (ti : TI) (key : String) (default : Int) : Int :=
  getKey ti.numbers (getKey ti.aliases key key) default
def getStr (ti : TI) (key : String) (default : List UInt8) : List UInt8 :=
  getKey ti.strings (getKey ti.aliases key key) default

/-- `haskey(ti::TermInfo, key)`, `base/terminfo.jl:218-219`. -/
def haskey (ti : TI) (key : String) : Bool :=
  hasKey ti.flags key || hasKey ti.numbers key || hasKey ti.strings key || hasKey ti.aliases key

/-- `getindex(ti::TermInfo, key)`, `base/terminfo.jl:221-227`, with fuel for the
alias recursion (Julia recurses without a bound; running out of fuel stands
for a stack overflow). -/
def getindex : Nat → TI → String → R CapVal
  | 0, _, _ => .error .boundsError
  | fuel + 1, ti, key =>
    if hasKey ti.flags key then .ok (.bool (getKey ti.flags key false))
    else if hasKey ti.numbers key then .ok (.int (getKey ti.numbers key 0))
    else if hasKey ti.strings key then .ok (.str (getKey ti.strings key []))
    else if hasKey ti.aliases key then getindex fuel ti (getKey ti.aliases key key)
    else .error (.keyError key)

/-- `keys(ti) = keys(ti.flags) ∪ keys(ti.numbers) ∪ keys(ti.strings) ∪ keys(ti.aliases)`,
`base/terminfo.jl:229`. -/
def keys (ti : TI) : List String :=
  (ti.flags.map (·.1) ++ ti.numbers.map (·.1) ++ ti.strings.map (·.1) ++ ti.aliases.map (·.1)).foldl pushSet []

/-- `show(io, ::MIME"text/plain", ti::TermInfo)`, `base/terminfo.jl:231-237`;
`namesRepr` is what `print(io, ti.names)` prints. -/
def showTI (namesRepr : String) (ti : TI) : Out :=
  ["TermInfo(", namesRepr, "; ", intStr ti.flags.length, " flags, ",
   intStr ti.numbers.length, " numbers, ", intStr ti.strings.length, " strings"] ++
  (match ti.extensions with
   | some e => [", ", intStr e.length, " extended capabilities"]
   | none => []) ++ [")"]

/-! ## Locating and loading -/

inductive StatError where
  | io
  | argument
  | eof
  | system
  | other
  deriving DecidableEq, Repr

/-- `_terminfo_stat_check` suppresses IO errors and propagates other exceptions. -/
def statCheck (check : String → Except StatError Bool) (path : String) : Except StatError Bool :=
  match check path with
  | .ok value => .ok value
  | .error .io => .ok false
  | .error err => .error err

/-- The environment and file system `find_terminfo_file` consults. -/
structure Env where
  env : String → Option String
  homedir : String
  isdir : String → Except StatError Bool
  isfile : String → Except StatError Bool
  /-- `normpath(Sys.BINDIR, DATAROOTDIR, "julia", "terminfo")`. -/
  bundled : String
  isunix : Bool

/-- `joinpath` of path components (`/`-separated). -/
def joinpath (parts : List String) : String := "/".intercalate parts

/-- `split(s, ':')` with empty entries replaced by `/usr/share/terminfo`. -/
def terminfoDirsList (s : String) : List String :=
  (s.splitOn ":").map (fun d => if d = "" then "/usr/share/terminfo" else d)

/-- The directories `find_terminfo_file` searches, in order, `base/terminfo.jl:251-264`. -/
def searchDirs (e : Env) : Except StatError (List String) := do
  let first ← match e.env "TERMINFO" with
    | some d => pure [d]
    | none => do
      let path := joinpath [e.homedir, ".terminfo"]
      if ← statCheck e.isdir path then pure [path] else pure []
  let fromDirs := match e.env "TERMINFO_DIRS" with
    | some s => terminfoDirsList s
    | none => []
  pure (first ++ fromDirs ++ [e.bundled] ++
    (if e.isunix then ["/etc/terminfo", "/lib/terminfo", "/usr/share/terminfo"] else []))

/-- The three candidates tried in one directory: first character, its hex
code, and the lowercased forms, `base/terminfo.jl:266-276`. -/
def candidates (dir chr chrcode lchr lterm term : String) : List String :=
  [joinpath [dir, chr, term], joinpath [dir, chrcode, term], joinpath [dir, lchr, lterm]]

/-- `find_terminfo_file(term)`, `base/terminfo.jl:248-279`. `chr`, `chrcode`,
`lower` are `string(first(term))`, `string(Int(first(term)), base=16)` and
`lowercase`. -/
def findTerminfoFile (e : Env) (lower : String → String) (term : String) : Except StatError (Option String) := do
  match term.toList with
  | [] => pure none
  | c :: _ =>
    if term.toList.any (fun ch => ch = '/' ∨ (!e.isunix ∧ ch = '\\')) then pure none else
    let chr := String.singleton c
    let byte := (term.toUTF8.toList.headD 0).toNat
    let digits := Nat.toDigits 16 byte
    let chrcode := String.ofList (if digits.length < 2 then '0' :: digits else digits)
    let rec go : List String → Except StatError (Option String)
      | [] => pure none
      | dir :: dirs => do
        let p1 := joinpath [dir, chr, term]
        let p2 := joinpath [dir, chrcode, term]
        let p3 := joinpath [dir, lower chr, lower term]
        if ← statCheck e.isfile p1 then pure (some p1)
        else if ← statCheck e.isfile p2 then pure (some p2)
        else if ← statCheck e.isfile p3 then pure (some p3)
        else go dirs
    go (← searchDirs e)

/-- How reading a terminfo file can end: parsed, or an exception of a kind. -/
inductive ReadResult where
  | ok (raw : Raw)
  | argumentError
  | ioError
  | eofError
  | systemError
  | otherError
  deriving DecidableEq, Repr

/-- Outcome of `load_terminfo`: a `TermInfo`, or a rethrown exception. -/
inductive Loaded where
  | info (ti : TI)
  | rethrown
  deriving DecidableEq, Repr

/-- `load_terminfo(term)`, `base/terminfo.jl:286-298`. `readFile path` is
`read(file, TermInfoRaw)`; `conv` is `TermInfo(raw)`. -/
def loadTerminfo (e : Env) (lower : String → String) (readFile : String → ReadResult)
    (conv : Raw → TI) (term : String) : Loaded :=
  match findTerminfoFile e lower term with
  | .error .io | .error .argument | .error .eof | .error .system => .info blank
  | .error .other => .rethrown
  | .ok none => .info blank
  | .ok (some file) =>
    match readFile file with
    | .ok raw => .info (conv raw)
    | .argumentError => .info blank
    | .ioError => .info blank
    | .eofError => .info blank
    | .systemError => .info blank
    | .otherError => .rethrown

/-! ## Colour detection -/

/-- `ttyhascolor()` on Unix: `haskey(current_terminfo(), :setaf)`; on Windows
`true`, `base/terminfo.jl:316-322`. -/
def ttyhascolor (windows : Bool) (ti : TI) : Bool :=
  if windows then true else haskey ti "setaf"

/-- The facts `ttyhastruecolor()` reads, `base/terminfo.jl:357-374`. -/
structure ColorEnv where
  env : String → Option String
  isunix : Bool
  /-- `Sys.iswindows() && Sys.windows_version() ≥ v"10.0.14931"`. -/
  windowsTrueColor : Bool
  /-- `tryparse(Int, get(ENV, "VTE_VERSION", ""))`. -/
  vteVersion : Option Int

/-- `ttyhastruecolor()`, `base/terminfo.jl:357-374`. -/
def ttyhastruecolor (c : ColorEnv) (ti : TI) : Bool :=
  (c.env "COLORTERM" = some "truecolor" || c.env "COLORTERM" = some "24bit") ||
  getBool ti "RGB" false || getBool ti "Tc" false ||
  (haskey ti "setrgbf" && haskey ti "setrgbb") ||
  (if c.isunix then decide (getInt ti "colors" 0 > 256) else false) ||
  c.windowsTrueColor ||
  decide ((c.vteVersion.getD 0) ≥ 3600) ||
  (c.env "XTERM_VERSION").isSome ||
  c.env "TERMINAL_PROGRAM" = some "iTerm.app" ||
  (c.env "KONSOLE_PROFILE_NAME").isSome ||
  (c.env "KONSOLE_DBUS_SESSION").isSome ||
  (let term := (c.env "TERM").getD ""
   term.startsWith "linux" || term.startsWith "rxvt" || term.startsWith "st")

/-- `get_have_color()` / `get_have_truecolor()`, `base/terminfo.jl:376-386`: the
global cache `have_color` (`none` is `nothing`) is filled on first use. Returns
the value and the new cache. -/
def getHaveCached (cache : Option Bool) (compute : Bool) : Bool × Option Bool :=
  match cache with
  | some v => (v, some v)
  | none => (compute, some compute)

/-- The `TTY` property methods, `base/terminfo.jl:388-391`; `haveColor` is
`get_have_color()`. `in` only has a method for `Pair{Symbol,Bool}`; other pairs
reach `in(::Pair, ::IO) = false`. -/
def inTTY (haveColor : Bool) (key : String) (value : Option Bool) : Bool :=
  match value with
  | some b => key == "color" && b == haveColor
  | none => false
def haskeyTTY (key : String) : Bool := key == "color"
def getindexTTY (haveColor : Bool) (key : String) : R Bool :=
  if key == "color" then .ok haveColor else .error (.keyError key)
def getTTY {α} (haveColor : α) (key : String) (default : α) : α :=
  if key == "color" then haveColor else default

end JuliaLean.ShowCov.TermInfo


namespace JuliaLean.ShowCov.Methods.TermInfoFile

open JuliaLean.ShowCov.TermInfo

def m69 (_args : Unit) := blank

def m71 (data : Rd) := readRawAt data

def m112 (data : Rd) (wordBytes : Nat) := extendedterminfo data wordBytes

def m148 (table : List UInt8) (indices : List Int) := readStrings table indices

def m170 (tf tn ts : List Cap) (termUser : Nat → String → Option String) (raw : Raw) :=
  ofRaw tf tn ts termUser raw

/-- Nested `longalias(key, value)` at `base/terminfo.jl:194`: the source gets
the first component of the TERM_USER lookup default, represented by
`termUser kind key`. -/
def m194 (termUser : Nat → String → Option String) (kind : Nat) (key : String) :=
  termUser kind key

def m214 (ti : TI) (key : String) (default : Bool) := getBool ti key default

def m215 (ti : TI) (key : String) (default : Int) := getInt ti key default

def m216 (ti : TI) (key : String) (default : List UInt8) := getStr ti key default

def m218 (ti : TI) (key : String) := haskey ti key

def m221 (fuel : Nat) (ti : TI) (key : String) := getindex fuel ti key

def m229 (ti : TI) := keys ti

def m231 (namesRepr : String) (ti : TI) := showTI namesRepr ti

def m248 (env : Env) (lower : String → String) (term : String) :=
  findTerminfoFile env lower term

def m286 (env : Env) (lower : String → String) (readFile : String → ReadResult)
    (convert : Raw → TI) (term : String) := loadTerminfo env lower readFile convert term

def m319 (ti : TI) := ttyhascolor false ti

def m357 (env : ColorEnv) (ti : TI) := ttyhastruecolor env ti

def m376 (cache : Option Bool) (computed : Bool) := getHaveCached cache computed

def m382 (cache : Option Bool) (computed : Bool) := getHaveCached cache computed

def m388 (haveColor : Bool) (key : String) (value : Bool) := inTTY haveColor key (some value)

def m389 (key : String) := haskeyTTY key

def m390 (haveColor : Bool) (key : String) := getindexTTY haveColor key

def m391 {α} (haveColor : α) (key : String) (default : α) := getTTY haveColor key default

end JuliaLean.ShowCov.Methods.TermInfoFile
