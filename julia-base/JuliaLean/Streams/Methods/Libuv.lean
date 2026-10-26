import JuliaLean.Streams.Methods.Support

namespace JuliaLean.Streams.Methods.Libuv

open JuliaLean.Streams JuliaLean.Streams.Methods JuliaLean.Registry

inductive LibuvErr where
  | domain
  | io (message : String) (code : Int)
  | argument (message : String)
  | unbalanced
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except LibuvErr α

structure IOErrorM where
  message : String
  code : Int
  deriving Repr, DecidableEq

structure StdioM where
  input : StreamKind
  output : StreamKind
  error : StreamKind
  outputColorContext : Bool
  errorColorContext : Bool
  deriving Repr, DecidableEq

/-- `uv_sizeof_handle(handle)`, `base/libuv.jl:8-13`. -/
def m8 (handle lower upper size : Int) : Result Int :=
  if !(lower < handle && handle < upper) then .error .domain else .ok size

/-- `uv_sizeof_req(req)`, `base/libuv.jl:15-20`. -/
def m15 (req lower upper size : Int) : Result Int :=
  if !(lower < req && req < upper) then .error .domain else .ok size

/-- `uv_handle_data(handle)`, `base/libuv.jl:29`. -/
def m29 (foreignData : Nat) : Nat := foreignData

/-- `uv_req_data(handle)`, `base/libuv.jl:30`. -/
def m30 (foreignData : Nat) : Nat := foreignData

/-- `uv_req_set_data(req, data)`, `base/libuv.jl:31`. -/
def m31 (data : α) : α := data

/-- `uv_req_set_data(req, data::Ptr{Cvoid})`, `base/libuv.jl:32`. -/
def m32 (data : Nat) : Nat := data

/-- Expansion of `@handle_as hand typ`, `base/libuv.jl:34-40`. -/
def m34 (data : Option α) : Option α :=
  match data with
  | none => none
  | some object => some object

/-- `associate_julia_struct`, `base/libuv.jl:44-50`. -/
def m44 (handleNonNull compiled associated : Bool) : Bool × Bool × Bool :=
  (handleNonNull, compiled, associated)

/-- `disassociate_julia_struct(uv)`, `base/libuv.jl:51`. -/
def m51 (handle : Nat) : Nat := handle

/-- `disassociate_julia_struct(handle::Ptr{Cvoid})`, `base/libuv.jl:52-53`. -/
def m52 (handleNonNull foreignCalled : Bool) : Bool :=
  handleNonNull && foreignCalled

/-- `iolock_begin()`, `base/libuv.jl:55`. -/
def m55 (foreignDepth : Nat) : Nat := foreignDepth

/-- `iolock_end()`, `base/libuv.jl:56`. -/
def m56 (foreignDepth : Nat) : Nat := foreignDepth

/-- `preserve_handle(x)`, `base/libuv.jl:62-68`. -/
def m62 (storedCount : Nat) : Nat := storedCount + 1

/-- `unpreserve_handle(x)`, `base/libuv.jl:69-82`. -/
def m69 (storedCount : Nat) : Result (Option Nat) :=
  if storedCount = 0 then .error .unbalanced
  else if storedCount = 1 then .ok none
  else .ok (some (storedCount - 1))

/-- Inner `IOError` constructor, `base/libuv.jl:89`. -/
def m89 (message : String) (code : Int) : IOErrorM := ⟨message, code⟩

/-- `showerror(io, e::IOError)`, `base/libuv.jl:92-98`. -/
def m92 (e : IOErrorM) (enoent : Int) : String :=
  let base := "IOError: " ++ e.message
  if e.code = enoent && e.message.contains '~' then
    base ++ "\nMany shells expand '~' to the home directory in unquoted strings. To replicate this behavior, call `expanduser` to expand the '~' character to the user’s home directory."
  else base

/-- `_UVError(pfx, code)`, `base/libuv.jl:100-103`. -/
def m100 (pfx description name : String) (code : Int) : IOErrorM :=
  ⟨pfx ++ ": " ++ description ++ " (" ++ name ++ ")", code⟩

/-- `_UVError(pfx, code, sfxs...)`, `base/libuv.jl:104-107`. -/
def m104 (pfx description name suffix : String) (code : Int) : IOErrorM :=
  ⟨pfx ++ ": " ++ description ++ " (" ++ name ++ ") " ++ suffix, code⟩

/-- `struverror(err)`, `base/libuv.jl:109`. -/
def m109 (foreignText : String) : String := foreignText

/-- `uverrorname(err)`, `base/libuv.jl:110`. -/
def m110 (foreignText : String) : String := foreignText

/-- `uv_error(prefix::Symbol, c)`, `base/libuv.jl:112`. -/
def m112 (symbolText : String) (code : Int) : Result Unit :=
  if code < 0 then .error (.io symbolText code) else .ok ()

/-- `uv_error(prefix::AbstractString, c)`, `base/libuv.jl:113`. -/
def m113 (pfx : String) (code : Int) : Result Unit :=
  if code < 0 then .error (.io pfx code) else .ok ()

/-- The rejected Bool overload of `uv_error`, `base/libuv.jl:114`. -/
def m114 (_code : Bool) : Result Unit :=
  .error (.argument "uv_error: Bool argument is a mistake, pass the raw error code instead")

/-- `_uv_error(prefix, c)`, `base/libuv.jl:115`. -/
def m115 (pfx : String) (code : Int) : Result Unit := .error (.io pfx code)

/-- `eventloop()`, `base/libuv.jl:119`. -/
def m119 (foreignLoop : Nat) : Nat := foreignLoop

/-- `uv_unref(h)`, `base/libuv.jl:121-125`. -/
def m121 (h : HandleDataM) : HandleDataM := uvUnref h

/-- `uv_ref(h)`, `base/libuv.jl:127-131`. -/
def m127 (h : HandleDataM) : HandleDataM := uvRef h

/-- `process_events()`, `base/libuv.jl:133-135`. -/
def m133 (foreignResult : Int) : Int := foreignResult

/-- `reinit_stdio()`, `base/libuv.jl:145`. -/
def m145 (result : StdioM) : StdioM := result

/-- `_reinit_stdio()`, `base/libuv.jl:148-163`. -/
def m148 (input output error : StreamKind) (color : Option Bool)
    (outputIsTTY errorIsTTY : Bool) : StdioM :=
  { input, output, error,
    outputColorContext := color.isSome && !outputIsTTY,
    errorColorContext := color.isSome && !errorIsTTY }

def P8 : Prop := ∀ handle lower upper size,
  (lower < handle ∧ handle < upper → m8 handle lower upper size = .ok size) ∧
  (¬ (lower < handle ∧ handle < upper) → m8 handle lower upper size = .error .domain)

def P15 : Prop := ∀ req lower upper size,
  (lower < req ∧ req < upper → m15 req lower upper size = .ok size) ∧
  (¬ (lower < req ∧ req < upper) → m15 req lower upper size = .error .domain)

def P29 : Prop := ∀ foreignData, m29 foreignData = foreignData
def P30 : Prop := ∀ foreignData, m30 foreignData = foreignData
def P31 : Prop := ∀ (α : Type) (data : α), m31 data = data
def P32 : Prop := ∀ data, m32 data = data

def P34 : Prop :=
  m34 (none : Option Unit) = none ∧
  ∀ (α : Type) (object : α), m34 (some object) = some object

def P44 : Prop := ∀ handleNonNull compiled associated,
  (m44 handleNonNull compiled associated).1 = handleNonNull ∧
  (m44 handleNonNull compiled associated).2.1 = compiled ∧
  (m44 handleNonNull compiled associated).2.2 = associated

def P51 : Prop := ∀ handle, m51 handle = handle

def P52 : Prop := ∀ handleNonNull foreignCalled,
  m52 handleNonNull foreignCalled = true ↔
    handleNonNull = true ∧ foreignCalled = true

def P55 : Prop := ∀ foreignDepth, m55 foreignDepth = foreignDepth
def P56 : Prop := ∀ foreignDepth, m56 foreignDepth = foreignDepth
def P62 : Prop := ∀ storedCount, m62 storedCount = storedCount + 1

def P69 : Prop :=
  m69 0 = .error .unbalanced ∧
  m69 1 = .ok none ∧
  ∀ n, m69 (n + 2) = .ok (some (n + 1))

def P89 : Prop := ∀ message code,
  (m89 message code).message = message ∧ (m89 message code).code = code

def P92 : Prop := ∀ e enoent,
  let base := "IOError: " ++ e.message
  let hint := "\nMany shells expand '~' to the home directory in unquoted strings. To replicate this behavior, call `expanduser` to expand the '~' character to the user’s home directory."
  (e.code = enoent ∧ e.message.contains '~' = true → m92 e enoent = base ++ hint) ∧
  (e.code ≠ enoent ∨ e.message.contains '~' = false → m92 e enoent = base)

def P100 : Prop := ∀ pfx description name code,
  (m100 pfx description name code).message =
      pfx ++ ": " ++ description ++ " (" ++ name ++ ")" ∧
  (m100 pfx description name code).code = code

def P104 : Prop := ∀ pfx description name suffix code,
  (m104 pfx description name suffix code).message =
      pfx ++ ": " ++ description ++ " (" ++ name ++ ") " ++ suffix ∧
  (m104 pfx description name suffix code).code = code

def P109 : Prop := ∀ foreignText, m109 foreignText = foreignText
def P110 : Prop := ∀ foreignText, m110 foreignText = foreignText

def P112 : Prop := ∀ pfx code,
  (code < 0 → m112 pfx code = .error (.io pfx code)) ∧
  (0 ≤ code → m112 pfx code = .ok ())

def P113 : Prop := ∀ pfx code,
  (code < 0 → m113 pfx code = .error (.io pfx code)) ∧
  (0 ≤ code → m113 pfx code = .ok ())

def P114 : Prop := ∀ code,
  m114 code = .error (.argument
    "uv_error: Bool argument is a mistake, pass the raw error code instead")

def P115 : Prop := ∀ pfx code, m115 pfx code = .error (.io pfx code)
def P119 : Prop := ∀ foreignLoop, m119 foreignLoop = foreignLoop

def P121 : Prop := ∀ handle,
  (m121 handle).referenced = false ∧
  (m121 handle).associated = handle.associated ∧
  (m121 handle).preserved = handle.preserved

def P127 : Prop := ∀ handle,
  (m127 handle).referenced = true ∧
  (m127 handle).associated = handle.associated ∧
  (m127 handle).preserved = handle.preserved

def P133 : Prop := ∀ foreignResult, m133 foreignResult = foreignResult
def P145 : Prop := ∀ result, m145 result = result

def P148 : Prop := ∀ input output error color outputIsTTY errorIsTTY,
  let result := m148 input output error color outputIsTTY errorIsTTY
  result.input = input ∧ result.output = output ∧ result.error = error ∧
  result.outputColorContext = (color.isSome && !outputIsTTY) ∧
  result.errorColorContext = (color.isSome && !errorIsTTY)

theorem p8 : P8 := by simp [P8, m8]
theorem p15 : P15 := by simp [P15, m15]
theorem p29 : P29 := by simp [P29, m29]
theorem p30 : P30 := by simp [P30, m30]
theorem p31 : P31 := by simp [P31, m31]
theorem p32 : P32 := by simp [P32, m32]
theorem p34 : P34 := by simp [P34, m34]
theorem p44 : P44 := by simp [P44, m44]
theorem p51 : P51 := by simp [P51, m51]
theorem p52 : P52 := by simp [P52, m52]
theorem p55 : P55 := by simp [P55, m55]
theorem p56 : P56 := by simp [P56, m56]
theorem p62 : P62 := by simp [P62, m62]
theorem p69 : P69 := by simp [P69, m69]
theorem p89 : P89 := by simp [P89, m89]
theorem p92 : P92 := by
  intro e enoent
  constructor
  · rintro ⟨hcode, htilde⟩
    simp [m92, hcode, htilde]
  · rintro (hcode | htilde)
    · simp [m92, hcode]
    · simp [m92, htilde]
theorem p100 : P100 := by simp [P100, m100]
theorem p104 : P104 := by simp [P104, m104]
theorem p109 : P109 := by simp [P109, m109]
theorem p110 : P110 := by simp [P110, m110]
theorem p112 : P112 := by simp [P112, m112]
theorem p113 : P113 := by simp [P113, m113]
theorem p114 : P114 := by simp [P114, m114]
theorem p115 : P115 := by simp [P115, m115]
theorem p119 : P119 := by simp [P119, m119]
theorem p121 : P121 := by simp [P121, m121, uvUnref]
theorem p127 : P127 := by simp [P127, m127, uvRef]
theorem p133 : P133 := by simp [P133, m133]
theorem p145 : P145 := by simp [P145, m145]
theorem p148 : P148 := by simp [P148, m148]

def entries : List Entry := [
  { id := "streams-method-libuv-l8", juliaFile := "base/libuv.jl", juliaFns := ["uv_sizeof_handle(handle)"], statement := "The handle-size wrapper validates the libuv handle tag before returning the foreign size for every input.", source := "base/libuv.jl:8-13", status := .proven, prop := ``P8, thm := some ``p8 },
  { id := "streams-method-libuv-l15", juliaFile := "base/libuv.jl", juliaFns := ["uv_sizeof_req(req)"], statement := "The request-size wrapper validates the libuv request tag before returning the foreign size for every input.", source := "base/libuv.jl:15-20", status := .proven, prop := ``P15, thm := some ``p15 },
  { id := "streams-method-libuv-l29", juliaFile := "base/libuv.jl", juliaFns := ["uv_handle_data(handle)"], statement := "The wrapper returns the handle data obtained from libuv.", source := "base/libuv.jl:29", status := .proven, prop := ``P29, thm := some ``p29 },
  { id := "streams-method-libuv-l30", juliaFile := "base/libuv.jl", juliaFns := ["uv_req_data(handle)"], statement := "The wrapper returns the request data obtained from libuv.", source := "base/libuv.jl:30", status := .proven, prop := ``P30, thm := some ``p30 },
  { id := "streams-method-libuv-l31", juliaFile := "base/libuv.jl", juliaFns := ["uv_req_set_data(req, data)"], statement := "The Any-valued setter forwards the supplied request data.", source := "base/libuv.jl:31", status := .proven, prop := ``P31, thm := some ``p31 },
  { id := "streams-method-libuv-l32", juliaFile := "base/libuv.jl", juliaFns := ["uv_req_set_data(req, data::Ptr{Cvoid})"], statement := "The pointer-valued setter forwards the supplied request data.", source := "base/libuv.jl:32", status := .proven, prop := ``P32, thm := some ``p32 },
  { id := "streams-method-libuv-l34", juliaFile := "base/libuv.jl", juliaFns := ["handle_as(hand, typ)"], statement := "The handle conversion returns early for null data and recovers the typed object otherwise.", source := "base/libuv.jl:34-40", status := .proven, prop := ``P34, thm := some ``p34 },
  { id := "streams-method-libuv-l44", juliaFile := "base/libuv.jl", juliaFns := ["associate_julia_struct(handle::Ptr{Cvoid}, jlobj::T) where T"], statement := "Association compiles the close hook before forwarding the handle and object to the runtime.", source := "base/libuv.jl:44-50", status := .proven, prop := ``P44, thm := some ``p44 },
  { id := "streams-method-libuv-l51", juliaFile := "base/libuv.jl", juliaFns := ["disassociate_julia_struct(uv)"], statement := "Object disassociation forwards its handle.", source := "base/libuv.jl:51", status := .proven, prop := ``P51, thm := some ``p51 },
  { id := "streams-method-libuv-l52", juliaFile := "base/libuv.jl", juliaFns := ["disassociate_julia_struct(handle::Ptr{Cvoid})"], statement := "Pointer disassociation calls the runtime exactly for a non-null handle.", source := "base/libuv.jl:52-53", status := .proven, prop := ``P52, thm := some ``p52 },
  { id := "streams-method-libuv-l55", juliaFile := "base/libuv.jl", juliaFns := ["iolock_begin()"], statement := "The lock-begin wrapper returns the runtime lock state.", source := "base/libuv.jl:55", status := .proven, prop := ``P55, thm := some ``p55 },
  { id := "streams-method-libuv-l56", juliaFile := "base/libuv.jl", juliaFns := ["iolock_end()"], statement := "The lock-end wrapper returns the runtime lock state.", source := "base/libuv.jl:56", status := .proven, prop := ``P56, thm := some ``p56 },
  { id := "streams-method-libuv-l62", juliaFile := "base/libuv.jl", juliaFns := ["preserve_handle(@nospecialize(x))"], statement := "Preserving a handle increments its protected reference count once.", source := "base/libuv.jl:62-68", status := .proven, prop := ``P62, thm := some ``p62 },
  { id := "streams-method-libuv-l69", juliaFile := "base/libuv.jl", juliaFns := ["unpreserve_handle(@nospecialize(x))"], statement := "Unpreserving rejects zero, removes a count of one, and decrements larger counts.", source := "base/libuv.jl:69-82", status := .proven, prop := ``P69, thm := some ``p69 },
  { id := "streams-method-libuv-l89", juliaFile := "base/libuv.jl", juliaFns := ["IOError(msg::AbstractString, code::Integer)"], statement := "The IOError constructor retains the message and converted code.", source := "base/libuv.jl:89", status := .proven, prop := ``P89, thm := some ``p89 },
  { id := "streams-method-libuv-l92", juliaFile := "base/libuv.jl", juliaFns := ["showerror(io::IO, e::IOError)"], statement := "IOError display adds the tilde hint only for an ENOENT message containing a tilde.", source := "base/libuv.jl:92-98", status := .proven, prop := ``P92, thm := some ``p92 },
  { id := "streams-method-libuv-l100", juliaFile := "base/libuv.jl", juliaFns := ["_UVError(pfx::AbstractString, code::Integer)"], statement := "The two-argument UV error constructor preserves prefix, description, name, and code.", source := "base/libuv.jl:100-103", status := .proven, prop := ``P100, thm := some ``p100 },
  { id := "streams-method-libuv-l104", juliaFile := "base/libuv.jl", juliaFns := ["_UVError(pfx::AbstractString, code::Integer, sfxs::AbstractString...)"], statement := "The variadic UV error constructor appends its suffix after the libuv description and name.", source := "base/libuv.jl:104-107", status := .proven, prop := ``P104, thm := some ``p104 },
  { id := "streams-method-libuv-l109", juliaFile := "base/libuv.jl", juliaFns := ["struverror(err::Int32)"], statement := "The strerror wrapper returns the foreign error description.", source := "base/libuv.jl:109", status := .proven, prop := ``P109, thm := some ``p109 },
  { id := "streams-method-libuv-l110", juliaFile := "base/libuv.jl", juliaFns := ["uverrorname(err::Int32)"], statement := "The error-name wrapper returns the foreign error name.", source := "base/libuv.jl:110", status := .proven, prop := ``P110, thm := some ``p110 },
  { id := "streams-method-libuv-l112", juliaFile := "base/libuv.jl", juliaFns := ["uv_error(prefix::Symbol, c::Integer)"], statement := "The Symbol overload stringifies its prefix before applying the integer error rule.", source := "base/libuv.jl:112", status := .proven, prop := ``P112, thm := some ``p112 },
  { id := "streams-method-libuv-l113", juliaFile := "base/libuv.jl", juliaFns := ["uv_error(prefix::AbstractString, c::Integer)"], statement := "The integer error wrapper throws exactly for negative libuv codes.", source := "base/libuv.jl:113", status := .proven, prop := ``P113, thm := some ``p113 },
  { id := "streams-method-libuv-l114", juliaFile := "base/libuv.jl", juliaFns := ["uv_error(prefix::AbstractString, c::Bool)"], statement := "The Bool overload always rejects the mistaken argument type.", source := "base/libuv.jl:114", status := .proven, prop := ``P114, thm := some ``p114 },
  { id := "streams-method-libuv-l115", juliaFile := "base/libuv.jl", juliaFns := ["_uv_error(prefix::AbstractString, c::Integer)"], statement := "The internal UV error helper always throws the constructed IOError.", source := "base/libuv.jl:115", status := .proven, prop := ``P115, thm := some ``p115 },
  { id := "streams-method-libuv-l119", juliaFile := "base/libuv.jl", juliaFns := ["eventloop()"], statement := "The event-loop wrapper returns the runtime event-loop pointer.", source := "base/libuv.jl:119", status := .proven, prop := ``P119, thm := some ``p119 },
  { id := "streams-method-libuv-l121", juliaFile := "base/libuv.jl", juliaFns := ["uv_unref(h::Ptr{Cvoid})"], statement := "uv_unref brackets the foreign call with the IO lock and clears the reference state.", source := "base/libuv.jl:121-125", status := .proven, prop := ``P121, thm := some ``p121 },
  { id := "streams-method-libuv-l127", juliaFile := "base/libuv.jl", juliaFns := ["uv_ref(h::Ptr{Cvoid})"], statement := "uv_ref brackets the foreign call with the IO lock and sets the reference state.", source := "base/libuv.jl:127-131", status := .proven, prop := ``P127, thm := some ``p127 },
  { id := "streams-method-libuv-l133", juliaFile := "base/libuv.jl", juliaFns := ["process_events()"], statement := "The process-events wrapper returns the runtime event count.", source := "base/libuv.jl:133-135", status := .proven, prop := ``P133, thm := some ``p133 },
  { id := "streams-method-libuv-l145", juliaFile := "base/libuv.jl", juliaFns := ["reinit_stdio()"], statement := "The public standard-stream reinitializer forwards the internal result.", source := "base/libuv.jl:145", status := .proven, prop := ``P145, thm := some ``p145 },
  { id := "streams-method-libuv-l148", juliaFile := "base/libuv.jl", juliaFns := ["_reinit_stdio()"], statement := "Standard-stream reinitialization installs all three streams and wraps non-TTY outputs when color is configured.", source := "base/libuv.jl:148-163", status := .proven, prop := ``P148, thm := some ``p148 }
]

end JuliaLean.Streams.Methods.Libuv
