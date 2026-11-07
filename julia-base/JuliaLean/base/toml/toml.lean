import JuliaLean.base.toml.parser

/-!
# Model of `base/toml/toml.jl`

`base/toml/toml.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027` defines the modules
`Base.TOML` and `Base.TOML.Printer` and includes `parser.jl` (modelled in
`JuliaLean.base.toml.parser`) and `printer.jl`. It defines no methods.
-/

namespace JuliaLean.base.toml.toml

-- UNTRANSLATED
-- module definitions and `include` statements of `Base.TOML`; no methods
-- Source: base/toml/toml.jl:1-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
-- `Base.TOML` is an undocumented internal part of Julia's TOML implementation.
-- Users should call the documented interface in the TOML.jl standard library
-- instead (by `import TOML` or `using TOML`).
-- """
-- module TOML
-- 
-- include("parser.jl")
-- 
-- # We put the printing functionality in a separate module since it
-- # defines a function `print` and we don't want that to collide with normal
-- # usage of `(Base.)print` in other files
-- module Printer
--     include("printer.jl")
-- end
-- 
-- end
-- /Source

end JuliaLean.base.toml.toml
