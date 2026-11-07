import JuliaLean.base.multimedia


namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

def MultimediaRepresentationExact : Prop :=
  (∀ mime, isTextMime mime = (mime.startsWith "text/" || textualMimes.contains mime)) ∧
  (∀ mime value shown decoded,
    representation mime value shown decoded =
      if isTextMime mime then
        match value with
        | .text text => if mime == "text/plain" then .text decoded else .text text
        | _ => .text decoded
      else .bytes (binaryRepresentation value shown))

theorem multimediaRepresentationExact : MultimediaRepresentationExact := by
  constructor <;> intros <;> rfl

def MultimediaDisplayExact : Prop :=
  (∀ attempts, displayAny attempts = runDisplayLoop "display" ["display", "show"] attempts) ∧
  (∀ attempts, displayMime attempts = runDisplayLoop "display" ["display"] attempts) ∧
  (∀ attempts, redisplayAny attempts =
    runDisplayLoop "redisplay" ["redisplay", "display", "show"] attempts) ∧
  (∀ attempts, redisplayMime attempts =
    runDisplayLoop "redisplay" ["redisplay", "display"] attempts)

theorem multimediaDisplayExact : MultimediaDisplayExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def MultimediaStackExact : Prop :=
  (∀ stack backend, pushDisplay stack backend = stack ++ [backend]) ∧
  (popDisplay [] = .error "ArgumentError: array must be non-empty") ∧
  (∀ stack backend, popNamedDisplay stack backend =
    if stack.contains backend then .ok (removeLast backend stack) else .error "KeyError") ∧
  (∀ stdout, reinitDisplays stdout = [stdout]) ∧
  (∀ result, delegateDisplayIO result = result)

theorem multimediaStackExact : MultimediaStackExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.ErrorShow.Coverage
