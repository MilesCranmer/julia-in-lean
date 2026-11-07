import JuliaLean.base.regex

namespace JuliaLean.RegexUnicode.Core

open JuliaLean JuliaLean.Strings

/-- Complete runs of the iterator from a state: the matches produced until
`iterate` returns `nothing`, or the exception it throws. `collect(eachmatch(re,
s; overlap))` is the run from `startState`. -/
inductive EachTrace (re : Regex) (s : JStr) (ov : Bool) : State → RJl (List RegexMatch) → Prop where
  | done {st} : iterate re s ov st = .ok none → EachTrace re s ov st (.ok [])
  | err {st e} : iterate re s ov st = .error e → EachTrace re s ov st (.error e)
  | step {st m st' r} : iterate re s ov st = .ok (some (m, st')) → EachTrace re s ov st' r →
      EachTrace re s ov st ((m :: ·) <$> r)

/-- The iterator run for at most `k` steps (`none` if not finished). -/
def eachmatchFuel (re : Regex) (s : JStr) (ov : Bool) : Nat → State → Option (RJl (List RegexMatch))
  | 0, _ => none
  | k + 1, st =>
    match iterate re s ov st with
    | .error e => some (.error e)
    | .ok none => some (.ok [])
    | .ok (some (m, st')) => (fun r => (m :: ·) <$> r) <$> eachmatchFuel re s ov k st'

theorem eachmatchFuel_sound (re : Regex) (s : JStr) (ov : Bool) :
    ∀ (k : Nat) (st : State) (r : RJl (List RegexMatch)),
      eachmatchFuel re s ov k st = some r → EachTrace re s ov st r := by
  intro k
  induction k with
  | zero => intro st r h; simp [eachmatchFuel] at h
  | succ k ih =>
    intro st r h
    simp only [eachmatchFuel] at h
    split at h
    · rename_i e he; cases h; exact .err he
    · rename_i he; cases h; exact .done he
    · rename_i m st' he
      cases h' : eachmatchFuel re s ov k st' with
      | none => rw [h'] at h; cases h
      | some r' =>
        rw [h'] at h; cases h
        exact .step he (ih st' r' h')
end JuliaLean.RegexUnicode.Core
