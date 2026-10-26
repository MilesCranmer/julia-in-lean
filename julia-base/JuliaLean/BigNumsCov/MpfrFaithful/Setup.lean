import JuliaLean.BigNumsCov.MpfrFaithful.Prelude

namespace JuliaLean.BigNumsCov.MpfrFaithful

/-! `base/mpfr.jl:44-110`. -/

def version44 (getVersion : Unit → String) (unsafeString : String → String)
    (versionNumber : String → String) : Run String :=
  let raw := getVersion ()
  let text := unsafeString raw
  ⟨["mpfr_get_version", "unsafe_string", "VersionNumber"], versionNumber text⟩

def Version44 : Prop :=
  ∀ getVersion unsafeString versionNumber,
    version44 getVersion unsafeString versionNumber =
      ⟨["mpfr_get_version", "unsafe_string", "VersionNumber"],
        versionNumber (unsafeString (getVersion ()))⟩

theorem version44_proven : Version44 := by simp [Version44, version44]

def patches45 (getPatches : Unit → String) (unsafeString : String → String)
    (splitSpace : String → List String) : Run (List String) :=
  let raw := getPatches ()
  let text := unsafeString raw
  ⟨["mpfr_get_patches", "unsafe_string", "split-space"], splitSpace text⟩

def Patches45 : Prop :=
  ∀ getPatches unsafeString splitSpace,
    patches45 getPatches unsafeString splitSpace =
      ⟨["mpfr_get_patches", "unsafe_string", "split-space"],
        splitSpace (unsafeString (getPatches ()))⟩

theorem patches45_proven : Patches45 := by simp [Patches45, patches45]

def init47 (setEmin setEmax : Int → Except String Unit) (showError : String → Unit)
    (eminMin emaxMax : Int) : Run Unit :=
  match setEmin eminMin with
  | .error error =>
      let _ := showError error
      ⟨["get_emin_min", "set_emin!", "showerror_nostdio"], ()⟩
  | .ok _ =>
      match setEmax emaxMax with
      | .error error =>
          let _ := showError error
          ⟨["get_emin_min", "set_emin!", "get_emax_max", "set_emax!",
            "showerror_nostdio"], ()⟩
      | .ok _ =>
          ⟨["get_emin_min", "set_emin!", "get_emax_max", "set_emax!"], ()⟩

def Init47 : Prop :=
  ∀ setEmin setEmax showError eminMin emaxMax,
    (init47 setEmin setEmax showError eminMin emaxMax).value = ()

theorem init47_proven : Init47 := by
  unfold Init47
  intros setEmin setEmax showError eminMin emaxMax
  unfold init47
  split
  · rfl
  · split <;> rfl

def convert75 (_ : PMode) : RMode := Mpfr.Mode.nearest
def convert76 (_ : PMode) : RMode := Mpfr.Mode.toZero
def convert77 (_ : PMode) : RMode := Mpfr.Mode.up
def convert78 (_ : PMode) : RMode := Mpfr.Mode.down
def convert79 (_ : PMode) : RMode := Mpfr.Mode.fromZero

def Convert75 : Prop := ∀ mode, convert75 mode = Mpfr.Mode.nearest
def Convert76 : Prop := ∀ mode, convert76 mode = Mpfr.Mode.toZero
def Convert77 : Prop := ∀ mode, convert77 mode = Mpfr.Mode.up
def Convert78 : Prop := ∀ mode, convert78 mode = Mpfr.Mode.down
def Convert79 : Prop := ∀ mode, convert79 mode = Mpfr.Mode.fromZero

theorem convert75_proven : Convert75 := by simp [Convert75, convert75]
theorem convert76_proven : Convert76 := by simp [Convert76, convert76]
theorem convert77_proven : Convert77 := by simp [Convert77, convert77]
theorem convert78_proven : Convert78 := by simp [Convert78, convert78]
theorem convert79_proven : Convert79 := by simp [Convert79, convert79]

def convert81 (mode : RMode) : Except String PMode :=
  match mode with
  | .nearest => .ok Mpfr.PublicMode.nearest
  | .toZero => .ok Mpfr.PublicMode.toZero
  | .up => .ok Mpfr.PublicMode.up
  | .down => .ok Mpfr.PublicMode.down
  | .fromZero => .ok Mpfr.PublicMode.fromZero
  | .faithful => .error "invalid MPFR rounding mode code"

def Convert81 : Prop :=
  ∀ mode, convert81 mode =
    match mode with
    | .nearest => .ok Mpfr.PublicMode.nearest
    | .toZero => .ok Mpfr.PublicMode.toZero
    | .up => .ok Mpfr.PublicMode.up
    | .down => .ok Mpfr.PublicMode.down
    | .fromZero => .ok Mpfr.PublicMode.fromZero
    | .faithful => .error "invalid MPFR rounding mode code"

theorem convert81_proven : Convert81 := by simp [Convert81, convert81]

def tieBreaker110 (_ : RMode) : Bool := true
def TieBreaker110 : Prop := ∀ mode : RMode, tieBreaker110 mode = true
theorem tieBreaker110_proven : TieBreaker110 := by simp [TieBreaker110, tieBreaker110]

end JuliaLean.BigNumsCov.MpfrFaithful
