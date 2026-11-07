import JuliaLean.base.channels
import JuliaLean.Proofs.base.locks_mt.common

/-! Source-body models and properties for uncovered methods in `base/channels.jl`. -/

namespace JuliaLean.ConcurrencyCov.ChannelsCov

open JuliaLean.ConcurrencyCov
























/-- Constructor wrappers, task binding, state queries, and display traits preserve
the branch and mutation order in `base/channels.jl:10-387,408,535,648-794`. -/
def ChannelBodies : Prop :=
  (∀ p v, pushWrapper p v = (p, v)) ∧
  (∀ v, popfirstWrapper v = v) ∧
  (∀ n, channelDefault (.integer n) = channelInteger n) ∧
  (∀ n, channelDefault (.float n) = channelFloat n) ∧
  (∀ size spawn pool ref, channelFunctionAny size spawn pool ref =
    channelFunction size spawn pool ref) ∧
  (∀ c e, (close c e).isOpen = false ∧ (close c e).exception = some e) ∧
  (∀ c, isopen c = c.isOpen ∧ isbuffered c = (c.size != 0)) ∧
  (∀ c, (bind c).hooks = c.hooks + 1) ∧
  (∀ n funcs, channeledTasks n funcs n n = .ok (n, funcs)) ∧
  (∀ msg, showInvalidState msg = "InvalidStateException: " ++ msg) ∧
  (∀ c inc, (incrementAvailable c inc).available = c.available + inc) ∧
  fetchUnbuffered = .error (.errorException "`fetch` is not supported on an unbuffered Channel.") ∧
  (∀ c, isempty c = decide (c.available = 0) ∧ isfull c = decide (c.size ≤ c.available)) ∧
  (∀ c, (channelLock c).locked = true ∧ (channelUnlock c).locked = false) ∧
  (∀ t, channelEltype t = t) ∧
  channelIteratorSize = .sizeUnknown

theorem channelBodies_proven : ChannelBodies := by
  refine ⟨fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun _ => rfl, ?_,
    fun _ => rfl, fun _ _ => rfl, rfl, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl, rfl⟩
  intro n funcs
  simp [channeledTasks]

/-- Every size not listed by the constructor documentation should reach its
`ArgumentError` (`base/channels.jl:13-27,43-57`). -/
def FloatSizeArgumentError : Prop :=
  ∀ s, s ∈ [FloatSize.negativeInf, .nan, .fractional] →
    channelFloat s = .error (.argumentError sizeError)

theorem floatSizeArgumentError_refuted : ¬ FloatSizeArgumentError := by
  intro h
  have bad := h .negativeInf (by simp)
  cases bad

/-- The function constructor defaults the pool before setting stickiness, the
deprecated constructor rejects mixed keyword families, task termination closes
once, and lock/display wrappers delegate to the channel state
(`base/channels.jl:139-176,329-381,698-767`). -/
def ChannelWrapperSpec : Prop :=
  (∀ size spawn pool ref plan, channelFunction size spawn pool ref = .ok plan →
    plan.pool = pool.getD "default" ∧ plan.sticky = !(spawn || pool.isSome) ∧
    plan.scheduled = (spawn || pool.isSome) ∧ plan.taskrefWritten = ref) ∧
  (∀ size, channelDeprecated true false true false size =
    .error (.argumentError "Cannot combine deprecated and scheduling keywords")) ∧
  (∀ t c, c.isOpen = true → (closeOnTaskDone (.failed t) c).exception = some (Exn.taskFailed t)) ∧
  (∀ c, channelTrylock c = if c.locked then (false, c) else (true, channelLock c)) ∧
  (∀ body c, channelWithLock body c = (body, channelUnlock (channelLock c))) ∧
  (∀ compact name c, channelShowPlain compact name c =
    let head := channelShow name c
    if compact then head
    else if !c.isOpen then head ++ " (closed)"
    else if c.available = 0 then head ++ " (empty)"
    else head ++ " (" ++ toString c.available ++ " item" ++
      (if c.available = 1 then "" else "s") ++ " available)")

theorem channelWrapperSpec_proven : ChannelWrapperSpec := by
  refine ⟨?_, fun _ => rfl, ?_, fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · intro size spawn pool ref plan h
    unfold channelFunction at h
    obtain ⟨ch, -, h⟩ := bind_ok h
    cases h
    simp
  · intro t c h
    simp [closeOnTaskDone, h, close]

end JuliaLean.ConcurrencyCov.ChannelsCov
