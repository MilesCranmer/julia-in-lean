import JuliaLean.base.strings.annotated
import JuliaLean.base.strings.io
import JuliaLean.base.strings.annotated_io

/-!
# Model of `base/strings/strings.jl`

The included Julia source files are retained in source order. Imports name the included files with
models already installed in JuliaLean.
-/

namespace JuliaLean.base.strings.strings

-- Source: base/strings/strings.jl:1-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- include("strings/annotated.jl")
-- include("strings/search.jl")
-- include("strings/unicode.jl")
-- 
-- import .Unicode: textwidth, islowercase, isuppercase, isletter, isdigit, isnumeric, iscntrl, ispunct,
--     isspace, isprint, isxdigit, lowercase, uppercase, titlecase, lowercasefirst, uppercasefirst
-- 
-- import .Iterators: PartitionIterator
-- 
-- include("strings/util.jl")
-- include("strings/io.jl")
-- include("strings/annotated_io.jl")
-- /Source
def includedFiles : List String := [
  "strings/annotated.jl",
  "strings/search.jl",
  "strings/unicode.jl",
  "strings/util.jl",
  "strings/io.jl",
  "strings/annotated_io.jl"
]

end JuliaLean.base.strings.strings
