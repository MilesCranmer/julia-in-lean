import JuliaLean.StringsCovA.Util

namespace JuliaLean.StringsCovA.UtilFaithful

open JuliaLean JuliaLean.Strings

def StartswithProperty : Prop :=
  (∀ a b, Util.startswith a b = b.isPrefixOf a) ∧
  (∀ cs s, Util.startswithChars cs s = match s with | [] => false | c :: _ => cs.contains c) ∧
  (∀ a b, Util.startswithDense a b = b.isPrefixOf a) ∧
  (∀ a b, Util.startswithFast a b = Util.startswithDense a b) ∧
  (∀ u p, Util.startswithIO u p = p.isPrefixOf u) ∧
  (∀ pre s, Util.startswithFix pre s = Util.startswith s pre)
theorem startswith_proven : StartswithProperty := by
  unfold StartswithProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def EndswithProperty : Prop :=
  (∀ a b, Util.endswith a b = b.reverse.isPrefixOf a.reverse) ∧
  (∀ cs s, Util.endswithChars cs s = match s.getLast? with | none => false | some c => cs.contains c) ∧
  (∀ a b, Util.endswithDense a b = b.reverse.isPrefixOf a.reverse) ∧
  (∀ a b, Util.endswithFast a b = Util.endswithDense a b) ∧
  (∀ suf s, Util.endswithFix suf s = Util.endswith s suf)
theorem endswith_proven : EndswithProperty := by
  unfold EndswithProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def ContainsProperty : Prop :=
  (∀ (α : Type) (occurs : α → α → Bool) (h n : α), Util.contains occurs h n = occurs n h) ∧
  (∀ n h, Util.containsFix n h = n.isSublist h)
theorem contains_proven : ContainsProperty := by constructor <;> intros <;> rfl

def ChopprefixProperty : Prop :=
  (∀ s p, Util.chopprefix s p = if p.isPrefixOf s then s.drop p.length else s) ∧
  (∀ s p, Util.chopprefixFast s p = Util.chopprefix s p) ∧
  (∀ s c, Util.chopprefixChar s c = match s with | x :: xs => if x == c then xs else x :: xs | [] => [])
theorem chopprefix_proven : ChopprefixProperty := by
  unfold ChopprefixProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def ChopsuffixProperty : Prop :=
  (∀ s p, Util.chopsuffix s p = if p.reverse.isPrefixOf s.reverse then s.take (s.length - p.length) else s) ∧
  (∀ s p, Util.chopsuffixFast s p = Util.chopsuffix s p) ∧
  (∀ s c, Util.chopsuffixChar s c = if s.getLast? == some c then s.dropLast else s)
theorem chopsuffix_proven : ChopsuffixProperty := by
  unfold ChopsuffixProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def LstripProperty : Prop :=
  (∀ s, Util.lstripDefault s = Strings.lstrip (fun _ => false) s) ∧
  (∀ cs s, Util.lstripChars cs s = Strings.lstrip (cs.contains ·) s) ∧
  ∀ _u : Unit, Util.lstripStringError = .error (.jl (.argumentError "second argument must be Chars"))
theorem lstrip_proven : LstripProperty := by
  unfold LstripProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def RstripProperty : Prop :=
  (∀ s, Util.rstripDefault s = Strings.rstrip (fun _ => false) s) ∧
  (∀ cs s, Util.rstripChars cs s = Strings.rstrip (cs.contains ·) s) ∧
  ∀ _u : Unit, Util.rstripStringError = .error (.jl (.argumentError "second argument must be Chars"))
theorem rstrip_proven : RstripProperty := by
  unfold RstripProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def StripProperty : Prop :=
  (∀ s, Util.stripDefault s = Strings.rstrip (fun _ => false) s >>= Strings.lstrip (fun _ => false) ∘ JSub.view) ∧
  (∀ cs s, Util.stripChars cs s = Strings.rstrip (cs.contains ·) s >>= Strings.lstrip (cs.contains ·) ∘ JSub.view) ∧
  ∀ _u : Unit, Util.stripStringError = .error (.jl (.argumentError "second argument must be Chars"))
theorem strip_proven : StripProperty := by
  unfold StripProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def LpadProperty : Prop := ∀ (α : Type) toString (s p : α) n tw,
  Util.lpadGeneric toString s p n tw = Strings.lpad (toString s) tw n
theorem lpad_proven : LpadProperty := by unfold LpadProperty; intros; rfl
def PadRemainderProperty : Prop := ∀ c r, Util.padRemainderChar c r = c
theorem padRemainder_proven : PadRemainderProperty := by unfold PadRemainderProperty; intros; rfl
def RpadProperty : Prop := ∀ (α β : Type) impl (s p : α) n,
  Util.rpadGeneric (β := β) impl s p n = impl s n p
theorem rpad_proven : RpadProperty := by unfold RpadProperty; intros; rfl
def TruncateProperty : Prop := ∀ cw s r maxw mode prefer,
  Util.truncateBoundaries cw s r maxw mode prefer = JuliaLean.StringUtil.truncBoundaries cw s r maxw mode prefer
theorem truncate_proven : TruncateProperty := by unfold TruncateProperty; intros; rfl

def SplitTraitsProperty : Prop :=
  (∀ _u : Unit, Util.splitEltype = "SubString") ∧ (∀ _u : Unit, Util.splitEltype = "SubString") ∧
  ∀ _u : Unit, Util.splitIteratorSize = "SizeUnknown"
theorem splitTraits_proven : SplitTraitsProperty := by
  unfold SplitTraitsProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def PartitionTraitsProperty : Prop :=
  (∀ _u : Unit, Util.partitionEltype = "SubString") ∧ ∀ _u : Unit, Util.partitionEltype = "SubString"
theorem partitionTraits_proven : PartitionTraitsProperty := by constructor <;> intros <;> rfl
def EachsplitProperty : Prop :=
  (∀ s f l k, Util.eachsplitCtor s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, Util.eachsplitChars s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, Util.eachsplitChar s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, Util.eachsplitWhitespace s f l k = JuliaLean.StringUtil.splitGen s f l k)
theorem eachsplit_proven : EachsplitProperty := by
  unfold EachsplitProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def RsplitTraitsProperty : Prop :=
  (∀ _u : Unit, Util.rsplitEltype = "SubString") ∧ (∀ _u : Unit, Util.rsplitEltype = "SubString") ∧
  ∀ _u : Unit, Util.rsplitIteratorSize = "SizeUnknown"
theorem rsplitTraits_proven : RsplitTraitsProperty := by
  unfold RsplitTraitsProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def EachrsplitProperty : Prop :=
  (∀ s f l k, Util.eachrsplitCtor s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, Util.eachrsplitChars s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, Util.eachrsplitChar s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, Util.eachrsplitWhitespace s f l k = JuliaLean.StringUtil.rsplitGen s f l k)
theorem eachrsplit_proven : EachrsplitProperty := by
  unfold EachrsplitProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def SplitCollectProperty : Prop :=
  (∀ s f l k, Util.splitCollect s f l k = JuliaLean.StringUtil.splitGen s f l k) ∧
  (∀ s f l k, Util.splitWhitespace s f l k = JuliaLean.StringUtil.splitGen s f l k)
theorem splitCollect_proven : SplitCollectProperty := by constructor <;> intros <;> rfl
def RsplitCollectProperty : Prop :=
  (∀ s f l k, Util.rsplitCollect s f l k = JuliaLean.StringUtil.rsplitGen s f l k) ∧
  (∀ s f l k, Util.rsplitWhitespace s f l k = JuliaLean.StringUtil.rsplitGen s f l k)
theorem rsplitCollect_proven : RsplitCollectProperty := by constructor <;> intros <;> rfl

def ReplaceDispatchProperty : Prop :=
  (∀ r, Util.replaceLiteral r = r) ∧
  (∀ (α : Type) showFn (r : α), Util.replaceShown showFn r = showFn r) ∧
  (∀ f s, Util.replaceFunction f s = f s) ∧
  (∀ f c, Util.replaceCharFunction f c = f c)
theorem replaceDispatch_proven : ReplaceDispatchProperty := by
  unfold ReplaceDispatchProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def PatReplacerProperty : Prop :=
  (∀ (α : Type) (x : α), Util.patReplacer x = x) ∧
  (∀ (α : Type) (x : α), Util.freePatReplacer x = ()) ∧
  (∀ c x, Util.patReplacerChar c x = (x == c)) ∧
  (∀ cs x, Util.patReplacerChars cs x = cs.contains x)
theorem patReplacer_proven : PatReplacerProperty := by
  unfold PatReplacerProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def ReplaceEngineProperty : Prop :=
  (∀ s ps c, Util.replaceIO s ps c = JuliaLean.StringUtil.replaceN s ps c) ∧
  (∀ s ps c, Util.replaceString s ps c = JuliaLean.StringUtil.replace s ps c)
theorem replaceEngine_proven : ReplaceEngineProperty := by constructor <;> intros <;> rfl

def HexProperty : Prop :=
  (∀ s, Util.hex2bytes s = JuliaLean.StringUtil.hex2bytes s) ∧
  (∀ (α σ : Type) d l (st : SJl (Option (α × σ))) it conv,
    Util.hex2bytesBang d l st it conv = JuliaLean.StringUtil.hex2bytesBang d l st it conv) ∧
  (∀ c, Util.numberFromHexChar c = JuliaLean.StringUtil.numberFromHexChar c) ∧
  (∀ b, Util.bytes2hex b = JuliaLean.StringUtil.bytes2hex b) ∧
  (∀ b, Util.bytes2hexIO b = JuliaLean.StringUtil.bytes2hexFill b)
theorem hex_proven : HexProperty := by
  unfold HexProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def AsciiProperty : Prop :=
  (∀ s, Util.ascii s = if Strings.isascii s then .ok s else .error (.jl (.argumentError "invalid ASCII"))) ∧
  (∀ _u : Unit, Util.throwInvalidAscii = .error (.jl (.argumentError "invalid ASCII"))) ∧
  (∀ (α : Type) toString (s : α), Util.asciiAbstract toString s = Util.ascii (toString s))
theorem ascii_proven : AsciiProperty := by
  unfold AsciiProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def RestProperty : Prop :=
  (∀ s i, Util.restFast s i = Strings.substring s i (Strings.lastindex s)) ∧
  (∀ (α : Type) collect (s : α), Util.restGeneric collect s = collect s)
theorem rest_proven : RestProperty := by constructor <;> intros <;> rfl

end JuliaLean.StringsCovA.UtilFaithful
