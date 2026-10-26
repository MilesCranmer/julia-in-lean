import JuliaLean.RuntimeCov.Common

/-!
`base/osinfo.jl` (evaluated into `Base.Sys`): operating-system predicates on a
kernel symbol, the WSL runtime test, and the zero-argument predicates generated
for the build's `KERNEL`.
-/

namespace JuliaLean.RuntimeCov.OsInfo

open JuliaLean.RuntimeCov

/-- `islinux(os)`, base/osinfo.jl:51. -/
def islinux (os : Sym) : Bool := os == "Linux"
/-- `isfreebsd(os)`, base/osinfo.jl:78. -/
def isfreebsd (os : Sym) : Bool := os == "FreeBSD"
/-- `isopenbsd(os)`, base/osinfo.jl:92. -/
def isopenbsd (os : Sym) : Bool := os == "OpenBSD"
/-- `isnetbsd(os)`, base/osinfo.jl:106. -/
def isnetbsd (os : Sym) : Bool := os == "NetBSD"
/-- `isdragonfly(os)`, base/osinfo.jl:120. -/
def isdragonfly (os : Sym) : Bool := os == "DragonFly"
/-- `iswindows(os)`, base/osinfo.jl:128. -/
def iswindows (os : Sym) : Bool := os == "Windows" || os == "NT"
/-- `isapple(os)`, base/osinfo.jl:136. -/
def isapple (os : Sym) : Bool := os == "Apple" || os == "Darwin"
/-- `isjsvm(os)`, base/osinfo.jl:147. -/
def isjsvm (os : Sym) : Bool := os == "Emscripten"
/-- `isbsd(os)`, base/osinfo.jl:64. -/
def isbsd (os : Sym) : Bool :=
  isfreebsd os || isopenbsd os || isnetbsd os || isdragonfly os || isapple os

/-- `isunix(os)`, base/osinfo.jl:29-43. -/
def isunix (os : Sym) : Rt Bool :=
  if iswindows os then .ok false
  else if islinux os || isbsd os then .ok true
  else if os == "Emscripten" then .ok true
  else .error (.argumentError ("unknown operating system \"" ++ os ++ "\""))

/-- `detectwsl()`, base/osinfo.jl:162-168, with the host predicate and the two
file-system probes (`isfile(".../WSLInterop")`, `isdir("/run/WSL")`) as inputs. -/
def detectwsl (hostLinux interopFile runWslDir : Bool) : Bool :=
  hostLinux && (interopFile || runWslDir)

/-- The zero-argument predicates generated at base/osinfo.jl:170-172:
`$f() = $(f(KERNEL))`, evaluated once for the build kernel. -/
def hostPredicate {α : Type} (f : Sym → α) (kernel : Sym) : α := f kernel

/-- The documented kernel predicates classify every symbol: `isunix` is
defined exactly for Windows, Linux, BSD (including Apple) and Emscripten
kernels; Windows is never Unix; every BSD, Linux and Apple kernel is Unix;
`isbsd` holds for Apple kernels (the docstring note); WSL detection implies
Linux; the generated host predicates evaluate the predicate at `KERNEL`. -/
def OsPredicates : Prop :=
  (∀ os : Sym, (∃ b, isunix os = .ok b) ↔
      (iswindows os ∨ islinux os ∨ isbsd os ∨ isjsvm os)) ∧
  (∀ os : Sym, iswindows os = true → isunix os = .ok false) ∧
  (∀ os : Sym, (islinux os ∨ isbsd os ∨ isjsvm os) → iswindows os = false →
      isunix os = .ok true) ∧
  (∀ os : Sym, isapple os = true → isbsd os = true) ∧
  (∀ os : Sym, isbsd os = true → iswindows os = false ∧ islinux os = false) ∧
  (∀ h i r : Bool, detectwsl h i r = true → h = true) ∧
  (∀ (α : Type) (f : Sym → α) (k : Sym), hostPredicate f k = f k)
theorem isunix_cases (os : Sym) : isunix os =
    (if iswindows os then .ok false
     else if islinux os || isbsd os then .ok true
     else if isjsvm os then .ok true
     else .error (.argumentError ("unknown operating system \"" ++ os ++ "\""))) := rfl

theorem osPredicates_proven : OsPredicates := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro os
    rw [isunix_cases]
    cases iswindows os <;> cases islinux os <;> cases isbsd os <;> cases isjsvm os <;> simp
  · intro os h; rw [isunix_cases]; simp [h]
  · intro os h hw
    rw [isunix_cases]
    revert h hw
    cases iswindows os <;> cases islinux os <;> cases isbsd os <;> cases isjsvm os <;> simp
  · intro os h; simp [isbsd, h]
  · intro os h
    simp only [isbsd, isfreebsd, isopenbsd, isnetbsd, isdragonfly, isapple,
      Bool.or_eq_true, beq_iff_eq] at h
    rcases h with ((((h | h) | h) | h) | h | h) <;> subst h <;> first | decide | simp [iswindows, islinux]
  · intro h i r hd; simp [detectwsl] at hd; exact hd.1
  · intro α f k; rfl
end JuliaLean.RuntimeCov.OsInfo
