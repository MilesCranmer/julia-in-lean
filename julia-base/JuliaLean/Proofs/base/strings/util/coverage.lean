import JuliaLean.base.strings.util
import JuliaLean.Proofs.base.strings.util.utility_entries

/-! Coverage models for `base/strings/util.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Util

open JuliaLean JuliaLean.Strings

def PrefixSuffix : Prop :=
  (∀ a b, startswith a b = b.isPrefixOf a) ∧
  (∀ cs s, startswithChars cs s = match s with | [] => false | c :: _ => cs.contains c) ∧
  (∀ a b, endswith a b = b.reverse.isPrefixOf a.reverse) ∧
  (∀ cs s, endswithChars cs s = match s.getLast? with | none => false | some c => cs.contains c) ∧
  (∀ a b, startswithDense a b = b.isPrefixOf a) ∧
  (∀ a b, startswithFast a b = startswithDense a b) ∧
  (∀ u p, startswithIO u p = p.isPrefixOf u) ∧
  (∀ a b, endswithDense a b = b.reverse.isPrefixOf a.reverse) ∧
  (∀ a b, endswithFast a b = endswithDense a b) ∧
  (∀ (α : Type) (occurs : α → α → Bool) (h n : α), contains occurs h n = occurs n h) ∧
  (∀ suf s, endswithFix suf s = endswith s suf) ∧
  (∀ pre s, startswithFix pre s = startswith s pre) ∧
  (∀ n h, containsFix n h = n.isSublist h)

set_option maxRecDepth 100000 in
theorem prefixSuffix : PrefixSuffix := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ChopAffixes : Prop :=
  (∀ s p, chopprefix s p = if p.isPrefixOf s then s.drop p.length else s) ∧
  (∀ s p, chopprefixFast s p = chopprefix s p) ∧
  (∀ s c, chopprefixChar s c = match s with | x :: xs => if x == c then xs else x :: xs | [] => []) ∧
  (∀ s p, chopsuffix s p = if p.reverse.isPrefixOf s.reverse then
    s.take (s.length - p.length) else s) ∧
  (∀ s p, chopsuffixFast s p = chopsuffix s p) ∧
  (∀ s c, chopsuffixChar s c = if s.getLast? == some c then s.dropLast else s)

set_option maxRecDepth 100000 in
theorem chopAffixes : ChopAffixes := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def StripWrappers : Prop :=
  (∀ s, lstripDefault s = Strings.lstrip (fun _ => false) s) ∧
  (∀ cs s, lstripChars cs s = Strings.lstrip (cs.contains ·) s) ∧
  lstripStringError = .error (.jl (.argumentError "second argument must be Chars")) ∧
  (∀ s, rstripDefault s = Strings.rstrip (fun _ => false) s) ∧
  (∀ cs s, rstripChars cs s = Strings.rstrip (cs.contains ·) s) ∧
  rstripStringError = .error (.jl (.argumentError "second argument must be Chars")) ∧
  (∀ s, stripDefault s = Strings.rstrip (fun _ => false) s >>= Strings.lstrip (fun _ => false) ∘ JSub.view) ∧
  (∀ cs s, stripChars cs s = Strings.rstrip (cs.contains ·) s >>= Strings.lstrip (cs.contains ·) ∘ JSub.view) ∧
  stripStringError = .error (.jl (.argumentError "second argument must be Chars")) ∧
  (∀ f s, stripPredicate f s = Strings.rstrip f s >>= Strings.lstrip f ∘ JSub.view)

theorem stripWrappers : StripWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def PadTruncateWrappers : Prop :=
  (∀ (α : Type) toString (s p : α) n tw, lpadGeneric toString s p n tw = Strings.lpad (toString s) tw n) ∧
  (∀ c r, padRemainderChar c r = c) ∧
  (∀ (α β : Type) impl (s p : α) n, rpadGeneric (β := β) impl s p n = impl s n p) ∧
  (∀ cw s r maxw mode prefer, truncateBoundaries cw s r maxw mode prefer =
    JuliaLean.StringUtil.truncBoundaries cw s r maxw mode prefer)

theorem padTruncateWrappers : PadTruncateWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def SplitWrappers : Prop :=
  (∀ s f l k, eachsplitCtor s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  splitEltype = "SubString" ∧ splitIteratorSize = "SizeUnknown" ∧
  (∀ s f l k st, splitIterate s f l k st = JuliaLean.StringUtil.splitIterate s f l k st) ∧
  partitionEltype = "SubString" ∧
  (∀ s n st, partitionIterate s n st = Strings.partitionIterate s n st) ∧
  (∀ s f l k, eachsplitChars s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, eachsplitChar s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, eachsplitWhitespace s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, eachrsplitCtor s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  rsplitEltype = "SubString" ∧ rsplitIteratorSize = "SizeUnknown" ∧
  (∀ s f l k, eachrsplitChars s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, eachrsplitChar s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, eachrsplitWhitespace s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f k to rem, rsplitIterate s f k to rem = JuliaLean.StringUtil.rsplitIterate s f k to rem) ∧
  (∀ s f l k, splitCollect s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, splitWhitespace s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, rsplitCollect s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, rsplitWhitespace s f l k = JuliaLean.StringUtil.rsplitGen s f l k)

theorem splitWrappers : SplitWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ReplaceWrappers : Prop :=
  (∀ r, replaceLiteral r = r) ∧
  (∀ (α : Type) showFn (r : α), replaceShown showFn r = showFn r) ∧
  (∀ f s, replaceFunction f s = f s) ∧
  (∀ f c, replaceCharFunction f c = f c) ∧
  (∀ (α : Type) (x : α), patReplacer x = x) ∧
  (∀ (α : Type) (x : α), freePatReplacer x = ()) ∧
  (∀ c x, patReplacerChar c x = (x == c)) ∧
  (∀ cs x, patReplacerChars cs x = cs.contains x) ∧
  (∀ s ps c, replaceIO s ps c = JuliaLean.StringUtil.replaceN s ps c) ∧
  (∀ s ps c, replaceString s ps c = JuliaLean.StringUtil.replace s ps c)

theorem replaceWrappers : ReplaceWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def EncodingRest : Prop :=
  (∀ s, hex2bytes s = JuliaLean.StringUtil.hex2bytes s) ∧
  (∀ (α σ : Type) d l (st : SJl (Option (α × σ))) it conv,
    hex2bytesBang d l st it conv = JuliaLean.StringUtil.hex2bytesBang d l st it conv) ∧
  (∀ c, numberFromHexChar c = JuliaLean.StringUtil.numberFromHexChar c) ∧
  (∀ b, bytes2hex b = JuliaLean.StringUtil.bytes2hex b) ∧
  (∀ b, bytes2hexIO b = JuliaLean.StringUtil.bytes2hexFill b) ∧
  (∀ s, ascii s = if Strings.isascii s then .ok s else .error (.jl (.argumentError "invalid ASCII"))) ∧
  throwInvalidAscii = .error (.jl (.argumentError "invalid ASCII")) ∧
  (∀ (α : Type) toString (s : α), asciiAbstract toString s = ascii (toString s)) ∧
  (∀ s i, restFast s i = Strings.substring s i (Strings.lastindex s)) ∧
  (∀ (α : Type) collect (s : α), restGeneric collect s = collect s)

theorem encodingRest : EncodingRest := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.Util
