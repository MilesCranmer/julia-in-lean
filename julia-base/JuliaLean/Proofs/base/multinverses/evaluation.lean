import JuliaLean.base.multinverses

namespace JuliaLean.ReinterpretArrays

open JuliaLean

/-- Bounded evaluator of the constructor; `smiNewEval_sound` shows every result it returns is the
constructor's. -/
def smiLoopEval {t : IntTy} (anc ad : JInt t.toUnsigned) : Nat → SmiState t → Option (SmiState t)
  | 0, _ => none
  | fuel + 1, s =>
    let s' := smiStep anc ad s
    if smiContinue ad s' then smiLoopEval anc ad fuel s' else some s'

def smiNewEval {t : IntTy} (d : JInt t) (fuel : Nat := 400) : Option (Jl (SignedMI t)) :=
  match smiPre d with
  | .error e => some (.error e)
  | .ok (anc, ad, s0) => (smiLoopEval anc ad fuel s0).map (smiFinish d)

theorem smiLoopEval_sound {t : IntTy} (anc ad : JInt t.toUnsigned) :
    ∀ (fuel : Nat) (s r : SmiState t), smiLoopEval anc ad fuel s = some r → SmiLoop anc ad s r
  | 0, _, _, h => by simp [smiLoopEval] at h
  | fuel + 1, s, r, h => by
    simp only [smiLoopEval] at h
    split at h
    · exact .next _ _ (by assumption) (smiLoopEval_sound anc ad fuel _ _ h)
    · cases h; exact .stop _ (by assumption)

theorem smiNewEval_sound {t : IntTy} (d : JInt t) (fuel : Nat) (mi : SignedMI t)
    (h : smiNewEval d fuel = some (.ok mi)) : SmiNew d mi := by
  unfold smiNewEval at h
  split at h
  · simp at h
  · rename_i anc ad s0 hpre
    cases hl : smiLoopEval anc ad fuel s0 with
    | none => simp [hl] at h
    | some s =>
      simp [hl] at h
      exact ⟨anc, ad, s0, s, hpre, smiLoopEval_sound anc ad fuel s0 s hl, h⟩

end JuliaLean.ReinterpretArrays
