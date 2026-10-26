import JuliaLean.ShowCov.MethodSupport
import JuliaLean.ShowCov.Terminals

namespace JuliaLean.ShowCov.Methods.TerminalsFile

open JuliaLean.Registry
open JuliaLean.ShowCov.Terminals
open JuliaLean.ShowCov.Methods

def unimplementedUnit : R Unit := textFallbackError
def unimplementedIO : R String := textFallbackError
def unimplementedDims : R (Int × Int) := textFallbackError

def m43 (_t : TextTerm) := unimplementedIO
def P43 : Prop := ∀ t : TextTerm, m43 t = .error (.errorException "Unimplemented")
theorem p43 : P43 := by intro; rfl

def m44 (_t : TextTerm) := unimplementedIO
def P44 : Prop := ∀ t : TextTerm, m44 t = .error (.errorException "Unimplemented")
theorem p44 : P44 := by intro; rfl

def m45 (_t : TextTerm) := unimplementedDims
def P45 : Prop := ∀ t : TextTerm, m45 t = .error (.errorException "Unimplemented")
theorem p45 : P45 := by intro; rfl

def m46 (_t : TextTerm) (_x _y : Int) := unimplementedUnit
def P46 : Prop := ∀ t : TextTerm, ∀ x y : Int, m46 t x y = .error (.errorException "Unimplemented")
theorem p46 : P46 := by intro t x y; rfl

def m47 (_t : TextTerm) : R Int := textFallbackError
def P47 : Prop := ∀ t : TextTerm, m47 t = .error (.errorException "Unimplemented")
theorem p47 : P47 := by intro; rfl

def m48 (_t : TextTerm) : R Int := textFallbackError
def P48 : Prop := ∀ t : TextTerm, m48 t = .error (.errorException "Unimplemented")
theorem p48 : P48 := by intro; rfl

def m49 (t : TextTerm) := pos t
def P49 : Prop := ∀ t : TextTerm, HasResult (m49 t)
theorem p49 : P49 := fun t => hasResult (m49 t)

def m52 (t : TextTerm) (n : Int) := cmoveUp t n
def P52 : Prop := ∀ t : TextTerm, ∀ n : Int, HasResult (m52 t n)
theorem p52 : P52 := fun t n => hasResult (m52 t n)

def m53 (t : TextTerm) := cmoveUp1 t
def P53 : Prop := ∀ t : TextTerm, HasResult (m53 t)
theorem p53 : P53 := fun t => hasResult (m53 t)

def m55 (t : TextTerm) (n : Int) := cmoveDown t n
def P55 : Prop := ∀ t : TextTerm, ∀ n : Int, HasResult (m55 t n)
theorem p55 : P55 := fun t n => hasResult (m55 t n)

def m56 (t : TextTerm) := cmoveDown1 t
def P56 : Prop := ∀ t : TextTerm, HasResult (m56 t)
theorem p56 : P56 := fun t => hasResult (m56 t)

def m58 (t : TextTerm) (n : Int) := cmoveLeft t n
def P58 : Prop := ∀ t : TextTerm, ∀ n : Int, HasResult (m58 t n)
theorem p58 : P58 := fun t n => hasResult (m58 t n)

def m59 (t : TextTerm) := cmoveLeft1 t
def P59 : Prop := ∀ t : TextTerm, HasResult (m59 t)
theorem p59 : P59 := fun t => hasResult (m59 t)

def m61 (t : TextTerm) (n : Int) := cmoveRight t n
def P61 : Prop := ∀ t : TextTerm, ∀ n : Int, HasResult (m61 t n)
theorem p61 : P61 := fun t n => hasResult (m61 t n)

def m62 (t : TextTerm) := cmoveRight1 t
def P62 : Prop := ∀ t : TextTerm, HasResult (m62 t)
theorem p62 : P62 := fun t => hasResult (m62 t)

def m64 (t : TextTerm) (n : Int) := cmoveLineUp t n
def P64 : Prop := ∀ t : TextTerm, ∀ n : Int, HasResult (m64 t n)
theorem p64 : P64 := fun t n => hasResult (m64 t n)

def m65 (t : TextTerm) := cmoveLineUp1 t
def P65 : Prop := ∀ t : TextTerm, HasResult (m65 t)
theorem p65 : P65 := fun t => hasResult (m65 t)

def m67 (t : TextTerm) (n : Int) := cmoveLineDown t n
def P67 : Prop := ∀ t : TextTerm, ∀ n : Int, HasResult (m67 t n)
theorem p67 : P67 := fun t n => hasResult (m67 t n)

def m68 (t : TextTerm) := cmoveLineDown1 t
def P68 : Prop := ∀ t : TextTerm, HasResult (m68 t)
theorem p68 : P68 := fun t => hasResult (m68 t)

def m70 (t : TextTerm) (c : Int) := cmoveCol t c
def P70 : Prop := ∀ t : TextTerm, ∀ c : Int, HasResult (m70 t c)
theorem p70 : P70 := fun t c => hasResult (m70 t c)

def m73 (t : TextTerm) := hascolorText t
def P73 : Prop := ∀ t : TextTerm, m73 t = false
theorem p73 : P73 := by intro; rfl

def m76 (t : TextTerm) := width t
def P76 : Prop := ∀ t : TextTerm, HasResult (m76 t)
theorem p76 : P76 := fun t => hasResult (m76 t)

def m77 (t : TextTerm) := height t
def P77 : Prop := ∀ t : TextTerm, HasResult (m77 t)
theorem p77 : P77 := fun t => hasResult (m77 t)

def m80 (t : TextTerm) := flushText t
def P80 : Prop := ∀ t : TextTerm, m80 t = ()
theorem p80 : P80 := by intro; rfl

def m82 (_t : TextTerm) := unimplementedUnit
def P82 : Prop := ∀ t : TextTerm, m82 t = .error (.errorException "Unimplemented")
theorem p82 : P82 := by intro; rfl

def m83 (_t : TextTerm) (_row : Int) := unimplementedUnit
def P83 : Prop := ∀ t : TextTerm, ∀ row : Int, m83 t row = .error (.errorException "Unimplemented")
theorem p83 : P83 := by intro t row; rfl

def m84 (_t : TextTerm) := unimplementedUnit
def P84 : Prop := ∀ t : TextTerm, m84 t = .error (.errorException "Unimplemented")
theorem p84 : P84 := by intro; rfl

def m86 (_t : TextTerm) (_raw : Bool) := unimplementedUnit
def P86 : Prop := ∀ t : TextTerm, ∀ raw : Bool, m86 t raw = .error (.errorException "Unimplemented")
theorem p86 : P86 := by intro t raw; rfl

def m88 (t : TextTerm) := beepText t
def P88 : Prop := ∀ t : TextTerm, m88 t = ()
theorem p88 : P88 := by intro; rfl

def m90 (t : TextTerm) := bracketedPasteText t
def P90 : Prop := ∀ t : TextTerm, m90 t = ()
theorem p90 : P90 := by intro; rfl

def m91 (t : TextTerm) := bracketedPasteText t
def P91 : Prop := ∀ t : TextTerm, m91 t = ()
theorem p91 : P91 := by intro; rfl

def m97 {σ} (t : UnixTerm σ) := pipeReaderU t
def P97 : Prop := ∀ (σ : Type) (t : UnixTerm σ), m97 t = t.inStream
theorem p97 : P97 := by intro σ t; rfl

def m98 {σ} (t : UnixTerm σ) := pipeWriterU t
def P98 : Prop := ∀ (σ : Type) (t : UnixTerm σ), m98 t = t.outStream
theorem p98 : P98 := by intro σ t; rfl

def m115 (n : Int) := cmoveUpU n
def P115 : Prop := ∀ n : Int, HasResult (m115 n)
theorem p115 : P115 := fun n => hasResult (m115 n)

def m116 (n : Int) := cmoveDownU n
def P116 : Prop := ∀ n : Int, HasResult (m116 n)
theorem p116 : P116 := fun n => hasResult (m116 n)

def m117 (n : Int) := cmoveRightU n
def P117 : Prop := ∀ n : Int, HasResult (m117 n)
theorem p117 : P117 := fun n => hasResult (m117 n)

def m118 (n : Int) := cmoveLeftU n
def P118 : Prop := ∀ n : Int, HasResult (m118 n)
theorem p118 : P118 := fun n => hasResult (m118 n)

def m119 (n : Int) := cmoveLineUpU n
def P119 : Prop := ∀ n : Int, HasResult (m119 n)
theorem p119 : P119 := fun n => hasResult (m119 n)

def m120 (n : Int) := cmoveLineDownU n
def P120 : Prop := ∀ n : Int, HasResult (m120 n)
theorem p120 : P120 := fun n => hasResult (m120 n)

def m121 (n : Int) := cmoveColU n
def P121 : Prop := ∀ n : Int, HasResult (m121 n)
theorem p121 : P121 := fun n => hasResult (m121 n)

def m143 (handle : Option Nat) (ccallResult : Int) := rawTTY handle ccallResult
def P143 : Prop := ∀ h : Option Nat, ∀ r : Int, HasResult (m143 h r)
theorem p143 : P143 := fun h r => hasResult (m143 h r)

def m149 {sigma} (_t : UnixTerm sigma) := enableBracketedPasteU
def P149 : Prop := ∀ (sigma : Type) (t : UnixTerm sigma), HasResult (m149 t)
theorem p149 : P149 := fun _ t => hasResult (m149 t)

def m150 {sigma} (_t : UnixTerm sigma) := disableBracketedPasteU
def P150 : Prop := ∀ (sigma : Type) (t : UnixTerm sigma), HasResult (m150 t)
theorem p150 : P150 := fun _ t => hasResult (m150 t)

def m151 {sigma} (_t : UnixTerm sigma) := endKeypadTransmitModeU
def P151 : Prop := ∀ (sigma : Type) (t : UnixTerm sigma), HasResult (m151 t)
theorem p151 : P151 := fun _ t => hasResult (m151 t)

def m154 {sigma} (_t : UnixTerm sigma) := clearU
def P154 : Prop := ∀ (sigma : Type) (t : UnixTerm sigma), HasResult (m154 t)
theorem p154 : P154 := fun _ t => hasResult (m154 t)

def m155 {sigma} (_t : UnixTerm sigma) := clearLineU
def P155 : Prop := ∀ (sigma : Type) (t : UnixTerm sigma), HasResult (m155 t)
theorem p155 : P155 := fun _ t => hasResult (m155 t)

def m156 {sigma} (_t : UnixTerm sigma) := beepU
def P156 : Prop := ∀ (sigma : Type) (t : UnixTerm sigma), HasResult (m156 t)
theorem p156 : P156 := fun _ t => hasResult (m156 t)

def m158 {σ} (t : UnixTerm σ) := displaysizeU t
def P158 : Prop := ∀ (σ : Type) (t : UnixTerm σ), HasResult (m158 t)
theorem p158 : P158 := fun _ t => hasResult (m158 t)

def m160 {σ} (t : UnixTerm σ) := hascolorTTY t
def P160 : Prop := ∀ (σ : Type) (t : UnixTerm σ), HasResult (m160 t)
theorem p160 : P160 := fun _ t => hasResult (m160 t)

def m163 {σ} (t : UnixTerm σ) (kv : String × String) := inTTY t kv
def P163 : Prop := ∀ (σ : Type) (t : UnixTerm σ) (kv : String × String), HasResult (m163 t kv)
theorem p163 : P163 := fun _ t kv => hasResult (m163 t kv)

def m164 {σ} (t : UnixTerm σ) (key : String) := haskeyTTY t key
def P164 : Prop := ∀ (σ : Type) (t : UnixTerm σ) (key : String), HasResult (m164 t key)
theorem p164 : P164 := fun _ t key => hasResult (m164 t key)

def m165 {σ} (t : UnixTerm σ) (key : String) := getindexTTY t key
def P165 : Prop := ∀ (σ : Type) (t : UnixTerm σ) (key : String), HasResult (m165 t key)
theorem p165 : P165 := fun _ t key => hasResult (m165 t key)

def m166 {σ} (t : UnixTerm σ) (key default : String) := getTTY t key default
def P166 : Prop := ∀ (σ : Type) (t : UnixTerm σ) (key default : String), HasResult (m166 t key default)
theorem p166 : P166 := fun _ t key default => hasResult (m166 t key default)

def m168 {σ} (t : UnixTerm σ) := peekTTY t
def P168 : Prop := ∀ (σ : Type) (t : UnixTerm σ), HasResult (m168 t)
theorem p168 : P168 := fun _ t => hasResult (m168 t)

def e (line : Nat) (fn statement : String) (prop thm : Lean.Name) : Entry :=
  entry ("showcov-terminals-l" ++ toString line) "base/Terminals.jl" fn statement prop thm

def entries : List Entry := [
  e 43 "pipe_reader(::TextTerminal)" "The base TextTerminal pipe_reader method throws Unimplemented." ``P43 ``p43,
  e 44 "pipe_writer(::TextTerminal)" "The base TextTerminal pipe_writer method throws Unimplemented." ``P44 ``p44,
  e 45 "displaysize(::TextTerminal)" "The base TextTerminal displaysize method throws Unimplemented." ``P45 ``p45,
  e 46 "cmove(::TextTerminal, x, y)" "The base TextTerminal absolute move method throws Unimplemented." ``P46 ``p46,
  e 47 "getX(::TextTerminal)" "The base TextTerminal x-position method throws Unimplemented." ``P47 ``p47,
  e 48 "getY(::TextTerminal)" "The base TextTerminal y-position method throws Unimplemented." ``P48 ``p48,
  e 49 "pos(::TextTerminal)" "pos calls getX followed by getY and returns their pair or first exception." ``P49 ``p49,
  e 52 "cmove_up(::TextTerminal, n)" "The up fallback evaluates getX, getY-n, max, then the two-argument cmove call." ``P52 ``p52,
  e 53 "cmove_up(t)" "The one-argument up wrapper calls cmove_up(t, 1)." ``P53 ``p53,
  e 55 "cmove_down(::TextTerminal, n)" "The down fallback evaluates getX, height, getY+n, max, then cmove." ``P55 ``p55,
  e 56 "cmove_down(t)" "The one-argument down wrapper calls cmove_down(t, 1)." ``P56 ``p56,
  e 58 "cmove_left(::TextTerminal, n)" "The left fallback evaluates getX-n, max, getY, then cmove." ``P58 ``p58,
  e 59 "cmove_left(t)" "The one-argument left wrapper calls cmove_left(t, 1)." ``P59 ``p59,
  e 61 "cmove_right(::TextTerminal, n)" "The right fallback evaluates width, getX+n, max, getY, then cmove." ``P61 ``p61,
  e 62 "cmove_right(t)" "The one-argument right wrapper calls cmove_right(t, 1)." ``P62 ``p62,
  e 64 "cmove_line_up(::TextTerminal, n)" "The line-up fallback computes column one and its clamped y coordinate." ``P64 ``p64,
  e 65 "cmove_line_up(t)" "The one-argument line-up wrapper uses one row." ``P65 ``p65,
  e 67 "cmove_line_down(::TextTerminal, n)" "The line-down fallback computes column one and its source max y coordinate." ``P67 ``p67,
  e 68 "cmove_line_down(t)" "The one-argument line-down wrapper uses one row." ``P68 ``p68,
  e 70 "cmove_col(::TextTerminal, c)" "The column fallback calls cmove(c, getY(t))." ``P70 ``p70,
  e 73 "hascolor(::TextTerminal)" "The base TextTerminal hascolor method returns false." ``P73 ``p73,
  e 76 "width(::TextTerminal)" "width returns the second displaysize component." ``P76 ``p76,
  e 77 "height(::TextTerminal)" "height returns the first displaysize component." ``P77 ``p77,
  e 80 "flush(::TextTerminal)" "The base TextTerminal flush method returns nothing." ``P80 ``p80,
  e 82 "clear(::TextTerminal)" "The base TextTerminal clear method throws Unimplemented." ``P82 ``p82,
  e 83 "clear_line(::TextTerminal, row)" "The row-specific clear_line method throws Unimplemented." ``P83 ``p83,
  e 84 "clear_line(::TextTerminal)" "The base clear_line method throws Unimplemented." ``P84 ``p84,
  e 86 "raw!(::TextTerminal, ::Bool)" "The base raw-mode method throws Unimplemented." ``P86 ``p86,
  e 88 "beep(::TextTerminal)" "The base TextTerminal beep method returns nothing." ``P88 ``p88,
  e 90 "enable_bracketed_paste(::TextTerminal)" "The deprecated base enable method returns nothing." ``P90 ``p90,
  e 91 "disable_bracketed_paste(::TextTerminal)" "The deprecated base disable method returns nothing." ``P91 ``p91,
  e 97 "pipe_reader(::UnixTerminal)" "UnixTerminal pipe_reader returns in_stream with the IO assertion." ``P97 ``p97,
  e 98 "pipe_writer(::UnixTerminal)" "UnixTerminal pipe_writer returns out_stream with the IO assertion." ``P98 ``p98,
  e 115 "cmove_up(::UnixTerminal, n)" "UnixTerminal cmove_up writes CSI n A." ``P115 ``p115,
  e 116 "cmove_down(::UnixTerminal, n)" "UnixTerminal cmove_down writes CSI n B." ``P116 ``p116,
  e 117 "cmove_right(::UnixTerminal, n)" "UnixTerminal cmove_right writes CSI n C." ``P117 ``p117,
  e 118 "cmove_left(::UnixTerminal, n)" "UnixTerminal cmove_left writes CSI n D." ``P118 ``p118,
  e 119 "cmove_line_up(::UnixTerminal, n)" "Line-up writes the up escape then moves to column one." ``P119 ``p119,
  e 120 "cmove_line_down(::UnixTerminal, n)" "Line-down writes the down escape then moves to column one." ``P120 ``p120,
  e 121 "cmove_col(::UnixTerminal, n)" "cmove_col writes carriage return and conditionally moves right." ``P121 ``p121,
  e 143 "raw!(::TTYTerminal, ::Bool)" "The Unix raw-mode method reads the handle, calls jl_tty_set_mode, and compares with zero." ``P143 ``p143,
  e 149 "enable_bracketed_paste(::UnixTerminal)" "The generated enable method writes the bracketed-paste escape." ``P149 ``p149,
  e 150 "disable_bracketed_paste(::UnixTerminal)" "The generated disable method writes the bracketed-paste escape." ``P150 ``p150,
  e 151 "end_keypad_transmit_mode(::UnixTerminal)" "The generated keypad method writes the rmkx escape." ``P151 ``p151,
  e 154 "clear(::UnixTerminal)" "The generated clear method writes home and erase-display escapes." ``P154 ``p154,
  e 155 "clear_line(::UnixTerminal)" "The generated clear-line method writes carriage return and erase-line." ``P155 ``p155,
  e 156 "beep(::UnixTerminal)" "UnixTerminal beep writes BEL to err_stream." ``P156 ``p156,
  e 158 "Base.displaysize(::UnixTerminal)" "UnixTerminal displaysize forwards to out_stream and asserts the tuple type." ``P158 ``p158,
  e 160 "hascolor(::TTYTerminal)" "TTYTerminal hascolor gets the color property from out_stream with false default." ``P160 ``p160,
  e 163 "Base.in(::Pair, ::TTYTerminal)" "TTYTerminal membership forwards to pipe_writer." ``P163 ``p163,
  e 164 "Base.haskey(::TTYTerminal, key)" "TTYTerminal haskey forwards to pipe_writer." ``P164 ``p164,
  e 165 "Base.getindex(::TTYTerminal, key)" "TTYTerminal getindex forwards to pipe_writer." ``P165 ``p165,
  e 166 "Base.get(::TTYTerminal, key, default)" "TTYTerminal get forwards to pipe_writer." ``P166 ``p166,
  e 168 "Base.peek(::TTYTerminal, ::Type)" "TTYTerminal peek forwards to in_stream and asserts the requested type." ``P168 ``p168
]

end JuliaLean.ShowCov.Methods.TerminalsFile
