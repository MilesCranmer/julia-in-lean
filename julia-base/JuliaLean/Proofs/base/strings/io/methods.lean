import JuliaLean.Proofs.base.show.methodSupport
import JuliaLean.base.strings.io

namespace JuliaLean.ShowCov.Methods.StringsIOFile

open JuliaLean.Registry
open JuliaLean.ShowCov.StringsIO
open JuliaLean.ShowCov.Methods
open JuliaLean.Show JuliaLean.Strings

def P32 : Prop := ∀ shown, HasResult (m32 shown)
theorem p32 : P32 := fun shown => hasResult (m32 shown)

def P42 : Prop := ∀ shown, HasResult (m42 shown)
theorem p42 : P42 := fun shown => hasResult (m42 shown)

def P77 : Prop := ∀ shown, HasResult (m77 shown)
theorem p77 : P77 := fun shown => hasResult (m77 shown)

def P104 : Prop := ∀ f context sizehint, HasResult (m104 f context sizehint)
theorem p104 : P104 := fun f context sizehint => hasResult (m104 f context sizehint)

def P116 : Prop := ∀ x, HasResult (m116 x)
theorem p116 : P116 := fun x => hasResult (m116 x)

def P134 : Prop := ∀ xs, HasResult (m134 xs)
theorem p134 : P134 := fun xs => hasResult (m134 xs)

def P150 : Prop := ∀ env xs, HasResult (m150 env xs)
theorem p150 : P150 := fun env xs => hasResult (m150 env xs)

def P186 : Prop := ∀ xs, HasResult (m186 xs)
theorem p186 : P186 := fun xs => hasResult (m186 xs)

def P188 : Prop := ∀ name, m188 name = name
theorem p188 : P188 := by intro; rfl

def P192 : Prop := ∀ chars, HasResult (m192 chars)
theorem p192 : P192 := fun chars => hasResult (m192 chars)

def P193 : Prop := ∀ chars, HasResult (m193 chars)
theorem p193 : P193 := fun chars => hasResult (m193 chars)

def P194 : Prop := ∀ data s, HasResult (m194 data s)
theorem p194 : P194 := fun data s => hasResult (m194 data s)

def P197 : Prop := ∀ input limit, HasResult (m197 input limit)
theorem p197 : P197 := fun input limit => hasResult (m197 input limit)

def P217 : Prop := ∀ units skip, HasResult (m217 units skip)
theorem p217 : P217 := fun units skip => hasResult (m217 units skip)

def P242 : Prop := ∀ s, HasResult (m242 s)
theorem p242 : P242 := fun s => hasResult (m242 s)

def P246 : Prop := ∀ s, HasResult (m246 s)
theorem p246 : P246 := fun s => hasResult (m246 s)

def P284 : Prop := ∀ f context, HasResult (m284 f context)
theorem p284 : P284 := fun f context => hasResult (m284 f context)

def P286 : Prop := ∀ f, HasResult (m286 f)
theorem p286 : P286 := fun f => hasResult (m286 f)

def P306 : Prop := ∀ bytes, m306 bytes = ⟨bytes, 1, bytes⟩
theorem p306 : P306 := by intro; rfl

def P307 : Prop := ∀ parent offset bytes, offset + bytes ≤ parent →
  m307 parent offset bytes = ⟨parent, offset + 1, bytes⟩
theorem p307 : P307 := by intro parent offset bytes _; rfl

def P330 : Prop := ∀ items delim last, HasResult (m330 items delim last)
theorem p330 : P330 := fun items delim last => hasResult (m330 items delim last)

def P346 : Prop := ∀ items delim, HasResult (m346 items delim)
theorem p346 : P346 := fun items delim => hasResult (m346 items delim)

def P356 : Prop := ∀ info items delim last, HasResult (m356 info items delim last)
theorem p356 : P356 := fun info items delim last => hasResult (m356 info items delim last)

def P378 : Prop := ∀ info items delim last, HasResult (m378 info items delim last)
theorem p378 : P378 := fun info items delim last => hasResult (m378 info items delim last)

def P389 : Prop := ∀ info items, HasResult (m389 info items)
theorem p389 : P389 := fun info items => hasResult (m389 info items)

def P390 : Prop := ∀ info items delim, HasResult (m390 info items delim)
theorem p390 : P390 := fun info items delim => hasResult (m390 info items delim)

def P391 : Prop := ∀ info items delim last, HasResult (m391 info items delim last)
theorem p391 : P391 := fun info items delim last => hasResult (m391 info items delim last)

def P395 : Prop := ∀ c, HasResult (m395 c)
theorem p395 : P395 := fun c => hasResult (m395 c)

def P396 : Prop := ∀ c, HasResult (m396 c)
theorem p396 : P396 := fun c => hasResult (m396 c)

def P459 : Prop := ∀ d s esc keep ascii fullhex, HasResult (m459 d s esc keep ascii fullhex)
theorem p459 : P459 := fun d s esc keep ascii fullhex => hasResult (m459 d s esc keep ascii fullhex)

def P488 : Prop := ∀ d s esc keep ascii fullhex, HasResult (m488 d s esc keep ascii fullhex)
theorem p488 : P488 := fun d s esc keep ascii fullhex => hasResult (m488 d s esc keep ascii fullhex)

def P491 : Prop := ∀ d s, HasResult (m491 d s)
theorem p491 : P491 := fun d s => hasResult (m491 d s)

def P535 : Prop := ∀ s keep, HasResult (m535 s keep)
theorem p535 : P535 := fun s keep => hasResult (m535 s keep)

def P592 : Prop := ∀ s keep, HasResult (m592 s keep)
theorem p592 : P592 := fun s keep => hasResult (m592 s keep)

def P613 : Prop := ∀ s, HasResult (m613 s)
theorem p613 : P613 := fun s => hasResult (m613 s)

def P643 : Prop := ∀ s, m643 s = s
theorem p643 : P643 := by intro; rfl

def P663 : Prop := ∀ s delim, HasResult (m663 s delim)
theorem p663 : P663 := fun s delim => hasResult (m663 s delim)

def P694 : Prop := ∀ s delim, HasResult (m694 s delim)
theorem p694 : P694 := fun s delim => hasResult (m694 s delim)

def P719 : Prop := ∀ s tabwidth, HasResult (m719 s tabwidth)
theorem p719 : P719 := fun s tabwidth => hasResult (m719 s tabwidth)

def P749 : Prop := ∀ s indent tabwidth, HasResult (m749 s indent tabwidth)
theorem p749 : P749 := fun s indent tabwidth => hasResult (m749 s indent tabwidth)

def P805 : Prop := ∀ chars, HasResult (m805 chars)
theorem p805 : P805 := fun chars => hasResult (m805 chars)

def P818 : Prop := ∀ (C : Type) (printChar : C → List Char) (chars : List C), HasResult (m818 printChar chars)
theorem p818 : P818 := fun _ printChar chars => hasResult (m818 printChar chars)

def P826 : Prop := ∀ chars, HasResult (m826 chars)
theorem p826 : P826 := fun chars => hasResult (m826 chars)

def e (line : Nat) (fn statement : String) (prop thm : Lean.Name) : Entry :=
  entry ("showcov-strings-io-l" ++ toString line) "base/strings/io.jl" fn statement prop thm

def entries : List Entry := []

end JuliaLean.ShowCov.Methods.StringsIOFile
