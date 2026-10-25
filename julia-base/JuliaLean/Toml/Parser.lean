import JuliaLean.Toml.Strings

/-!
# TOML keys, values, tables and the driver

`base/toml/parser.jl:593-961` at master `bbfa0ce4150`, without comment capture.
`tryparse` mirrors `Base.TOML.tryparse(::Parser)` (`base/toml/parser.jl:599-616`),
which `TOML.tryparse(str)` (`dates = true`, `Parser{Dates}`) and Base's code
loading (`dates = false`, `Parser{nothing}`) call.
-/

namespace JuliaLean.Toml

open JuliaLean

/-! ### Tables -/

/-- `x in s` for an `IdSet` of heap objects. -/
def memId (v : Val) (s : List Nat) : Bool :=
  match v with
  | .ref k => s.contains k
  | _ => false

/-- `v isa Dict`. -/
def isDict (v : Val) : M Bool := do
  match v with
  | .ref k => match ← getObj k with
    | .table _ => return true
    | _ => return false
  | _ => return false

/-- `check_allowed_add_key`, `base/toml/parser.jl:669-678`. -/
def check_allowed_add_key (d : Val) (checkDefined : Bool := true) : M Unit := do
  let l ← get
  if !(← isDict d) then perr .ErrKeyAlreadyHasValue
  else if memId d l.inline_tables then perr .ErrAddKeyToInlineTable
  else if checkDefined && memId d l.defined_tables then perr .ErrDuplicatedKey

/-- `d::TOMLDict`: the table index, or `TypeError`. -/
def asDict (d : Val) : M Nat := do
  match d with
  | .ref k => match ← getObj k with
    | .table _ => return k
    | _ => throw .typeError
  | _ => throw .typeError

/-- `get!(TOMLDict, d, key)`. -/
def getBangDict (t : Nat) (key : Str) : M Val := do
  match ← dictGet t key with
  | some v => return v
  | none =>
    let k ← alloc (.table [])
    dictSet t key (.ref k)
    return .ref k

/-- `recurse_dict!(l, d, dotted_keys, check, define_implicit)`,
`base/toml/parser.jl:644-667`. `n` is `length(dotted_keys)`. -/
def recurse_dict_loop (keys : List Str) (n : Nat) (check defineImplicit : Bool) :
    Nat → Val → M Val
  | i, d =>
    match keys with
    | [] => do return .ref (← asDict d)
    | key :: rest => do
      let t ← asDict d
      let mut d ← getBangDict t key
      match d with
      | .ref k =>
        match ← getObj k with
        | .array .any xs =>
          match xs.getLast? with
          | none => perr .ErrArrayTreatedAsDictionary
          | some last => d := last
        | .array _ _ => perr .ErrKeyAlreadyHasValue
        | .table _ => pure ()
      | _ => pure ()
      if check then
        let checkDef := if defineImplicit then true else i == n
        check_allowed_add_key d checkDef
      if defineImplicit && (← isDict d) then
        match d with
        | .ref k => modify fun l => { l with implicit_tables := l.implicit_tables ++ [k] }
        | _ => pure ()
      recurse_dict_loop rest n check defineImplicit (i + 1) d

def recurse_dict (d : Val) (keys : List Str) (check : Bool := true)
    (defineImplicit : Bool := false) : M Nat := do
  match ← recurse_dict_loop keys keys.length check defineImplicit 1 d with
  | .ref k => return k
  | _ => throw .typeError

/-! ### Keys, `base/toml/parser.jl:796-845` -/

/-- `isvalid_barekey_char`, `base/toml/parser.jl:800-804`. -/
def isvalid_barekey_char (c : Nat) : Bool :=
  (ch 'a' ≤ c && c ≤ ch 'z') || (ch 'A' ≤ c && c ≤ ch 'Z') || isdigit c ||
    c == ch '-' || c == ch '_'

/-- `_parse_key`, `base/toml/parser.jl:813-845`. -/
def _parse_key (fuel : Nat) : Nat → M (List Str)
  | 0 => throw .outOfFuel
  | k + 1 => do
    discard (skip_ws fuel)
    if (← get).dotted_keys.isEmpty then
      if (← acceptC '=') then perr .ErrEmptyBareKey
    let dq ← acceptC '"'
    let keyval ← if dq then parse_string_start fuel false (allowMultiline := false) else do
      let sq ← acceptC '\''
      if sq then parse_string_start fuel true (allowMultiline := false) else do
        set_marker
        if (← accept_batch isvalid_barekey_char fuel) then
          let p ← peek
          if !(p == ch '.' || iswhitespace p || p == ch ']' || p == ch '=') then
            discard eat_char
            perr .ErrInvalidBareKeyCharacter
          take_substring
        else
          discard eat_char
          perr .ErrInvalidBareKeyCharacter
    modify fun l => { l with dotted_keys := l.dotted_keys ++ [keyval] }
    discard (skip_ws fuel)
    if (← acceptC '.') then
      discard (skip_ws fuel)
      discard (_parse_key fuel k)
    return (← get).dotted_keys

/-- `parse_key`, `base/toml/parser.jl:807-810`. -/
def parse_key (fuel : Nat) : M (List Str) := do
  modify fun l => { l with dotted_keys := [] }
  _parse_key fuel fuel

/-! ### Values, arrays, inline tables and entries -/

/-- The element type `parse_array` gives a homogeneous array of `T`, or
`none` for its final `else error("unexpected type")`,
`base/toml/parser.jl:902-933`. -/
def arrayElTy (dates : Bool) : Option JTy → Option (ElTy × Bool)
  | none => some (.any, true)          -- `Union{}`: a fresh `Any[]`
  | some .string => some (.string, true)
  | some .bool => some (.bool, true)
  | some .i64 => some (.i64, true)
  | some .u64 => some (.u64, true)
  | some .f64 => some (.f64, true)
  | some .dict | some .big | some .u128 | some .i128 | some (.vec _) => some (.any, false)
  | some .date | some .time | some .datetime => if dates then some (.any, false) else none

/-- The type `T` of `parse_array`: `typeof(array[1])` if all elements share it,
`Any` (`none` inside `some`) otherwise, and `Union{}` (`none`) when empty. -/
def commonType (xs : List Val) : M (Option (Option JTy)) := do
  match xs with
  | [] => return none
  | x :: rest =>
    let t ← typeOf x
    let same ← rest.allM fun y => do return (← typeOf y) == t
    return some (if same then some t else none)

/-! The mutually recursive part. `lf` is the fuel of the non-recursive helpers'
loops (more than the input length); the explicit `Nat` argument is the fuel of
the mutual recursion, on which every function recurses structurally. -/

mutual

/-- `parse_value`, `base/toml/parser.jl:852-872`. -/
def parse_value (lf : Nat) (fuel : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    match ← parse_value_dispatch lf fuel with
    | some v => return v
    | none => perr .ErrGenericValueError
termination_by structural fuel

/-- The `if`/`elseif` chain of `parse_value`; `none` is Julia's `nothing`. -/
def parse_value_dispatch (lf : Nat) (fuel : Nat) : M (Option Val) :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    if (← acceptC '[') then return some (← parse_array lf fuel)
    if (← acceptC '{') then return some (← parse_inline_table lf fuel)
    if (← acceptC '"') then return some (.str (← parse_string_start lf false))
    if (← acceptC '\'') then return some (.str (← parse_string_start lf true))
    if (← acceptC 't') then return ← parse_bool true
    if (← acceptC 'f') then return ← parse_bool false
    parse_number_or_date_start lf
termination_by structural fuel

/-- `parse_array`, `base/toml/parser.jl:886-936`, after `[`. -/
def parse_array (lf : Nat) (fuel : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    discard (skip_ws_nl lf lf)
    let emptyArray ← acceptC ']'
    let xs ← if emptyArray then pure [] else parse_array_items lf fuel []
    let dates := (← get).dates
    match ← commonType xs with
    | none =>
      let k ← alloc (.array .any [])
      modify fun l => { l with static_arrays := l.static_arrays ++ [k] }
      return .ref k
    | some t =>
      let el ← match t with
        | none => pure ElTy.any
        | some t => match arrayElTy dates (some t) with
          | some (e, _) => pure e
          | none => throw (.errorException "unexpected type")
      let k ← alloc (.array el xs)
      modify fun l => { l with static_arrays := l.static_arrays ++ [k] }
      return .ref k
termination_by structural fuel

/-- The `while !empty_array` loop of `parse_array`. -/
def parse_array_items (lf : Nat) (fuel : Nat) (acc : List Val) : M (List Val) :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let v ← parse_value lf fuel
    let acc := acc ++ [v]
    discard (skip_ws_nl lf lf)
    let comma ← acceptC ','
    discard (skip_ws_nl lf lf)
    if (← acceptC ']') then return acc
    if !comma then perr .ErrExpectedCommaBetweenItemsArray
    parse_array_items lf fuel acc
termination_by structural fuel

/-- `parse_inline_table`, `base/toml/parser.jl:943-961`, after `{`. -/
def parse_inline_table (lf : Nat) (fuel : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let d ← alloc (.table [])
    modify fun l => { l with inline_tables := l.inline_tables ++ [d] }
    discard (skip_ws_nl lf lf)
    if (← acceptC '}') then return .ref d
    parse_inline_loop lf fuel d
termination_by structural fuel

/-- The `while true` loop of `parse_inline_table`. -/
def parse_inline_loop (lf : Nat) (fuel : Nat) (d : Nat) : M Val :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    parse_entry lf fuel (.ref d)
    discard (skip_ws_nl lf lf)
    if (← acceptC '}') then return .ref d
    if (← acceptC ',') then
      discard (skip_ws_nl lf lf)
      if (← acceptC '}') then return .ref d
      parse_inline_loop lf fuel d
    else perr .ErrExpectedCommaBetweenItemsInlineTable
termination_by structural fuel

/-- `parse_entry(l, d)`, `base/toml/parser.jl:748-789`, without comment capture. -/
def parse_entry (lf : Nat) (fuel : Nat) (d0 : Val) : M Unit :=
  match fuel with
  | 0 => throw .outOfFuel
  | fuel + 1 => do
    let key ← parse_key lf
    discard (skip_ws lf)
    if !(← acceptC '=') then perr .ErrExpectedEqualAfterKey
    let mut d := d0
    if key.length > 1 then
      d := .ref (← recurse_dict d key.dropLast true true)
    let lastKeyPart := (← get).dotted_keys.getLastD []
    let t ← asDict d
    match ← dictGet t lastKeyPart with
    | some v =>
      check_allowed_add_key v
      if (← isDict v) && memId v (← get).implicit_tables then perr .ErrDuplicatedKey
    | none => pure ()
    discard (skip_ws lf)
    let value ← parse_value lf fuel
    if (← isDict value) && (← dictGet t lastKeyPart).isSome then perr .ErrInlineTableRedefine
    dictSet t lastKeyPart value
termination_by structural fuel

end

/-- `parse_array_table`, `base/toml/parser.jl:711-746`, after `[[`. -/
def parse_array_table (lf : Nat) : M Unit := do
  let tableKey ← parse_key lf
  discard (skip_ws lf)
  let a1 ← acceptC ']'
  let ok ← if a1 then acceptC ']' else pure false
  if !ok then perr .ErrExpectedEndArrayOfTable
  let d ← recurse_dict (.ref 0) tableKey.dropLast false
  let k := tableKey.getLastD []
  let old ← match ← dictGet d k with
    | some v => pure v
    | none => do
      let a ← alloc (.array .any [])
      dictSet d k (.ref a)
      pure (.ref a)
  let l ← get
  let oldArr ← match old with
    | .ref a => match ← getObj a with
      | .array _ _ =>
        if l.static_arrays.contains a then perr .ErrAddArrayToStaticArray
        pure a
      | _ => perr .ErrArrayTreatedAsDictionary
    | _ => perr .ErrArrayTreatedAsDictionary
  let dNew ← alloc (.table [])
  match ← getObj oldArr with
  | .array .any xs => setObj oldArr (.array .any (xs ++ [.ref dNew]))
  | _ => throw .typeError
  modify fun l => { l with defined_tables := l.defined_tables ++ [dNew], active_table := dNew }

/-- `parse_table`, `base/toml/parser.jl:681-709`, after `[`. -/
def parse_table (lf : Nat) : M Unit := do
  if (← acceptC '[') then return ← parse_array_table lf
  let tableKey ← parse_key lf
  discard (skip_ws lf)
  if !(← acceptC ']') then perr .ErrExpectedEndOfTable
  let t ← recurse_dict (.ref 0) tableKey
  modify fun l => { l with active_table := t }
  if (← get).implicit_tables.contains t then perr .ErrDuplicatedKey
  modify fun l => { l with defined_tables := l.defined_tables ++ [t] }

/-- The end-of-line check of `parse_toplevel`, `base/toml/parser.jl:627-630,637-640`. -/
def expect_newline (lf : Nat) : M Unit := do
  discard (skip_ws_comment lf)
  let p ← peek
  if !(p == ch '\n' || p == ch '\r' || p == ch '#' || p == EOF) then
    discard eat_char
    perr .ErrExpectedNewLineKeyValue

/-- `parse_toplevel`, `base/toml/parser.jl:620-642`. -/
def parse_toplevel (lf fuel : Nat) : M Unit := do
  if (← acceptC '[') then
    modify fun l => { l with active_table := 0 }
    parse_table lf
    expect_newline lf
  else
    parse_entry lf fuel (.ref (← get).active_table)
    expect_newline lf

/-- The loop of `tryparse(l::Parser)`, `base/toml/parser.jl:599-616`. -/
def tryparse_loop (lf fuel : Nat) : Nat → M Unit
  | 0 => throw .outOfFuel
  | k + 1 => do
    discard (skip_ws_nl lf lf)
    if (← peek) == EOF then return
    parse_toplevel lf fuel
    tryparse_loop lf fuel k

/-- `Base.TOML.tryparse(Parser{D}(s))`: the final parser state (whose heap
object `0` is the returned table), or how parsing ended. A `ParserError` is
returned by `tryparse`; every other `Exc` is thrown. -/
def tryparseState (s : Str) (dates : Bool := true) : Except Exc Parser := do
  let l ← Parser.new s dates
  let lf := s.length + 2
  let fuel := 4 * s.length + 16
  ((tryparse_loop lf fuel lf).run l).map (·.2)

end JuliaLean.Toml
