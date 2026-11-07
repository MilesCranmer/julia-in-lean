import JuliaLean.base.channels
import JuliaLean.Proofs.base.channels.channel_entries
import JuliaLean.Proofs.base.channels.concurrency

/-! Per-method source-body models for `base/channels.jl`. -/

namespace JuliaLean.ConcurrencyCov.FaithfulChannels

open JuliaLean.ConcurrencyCov

def PushAbstractProp : Prop := ∀ put channel value, pushAbstract put channel value = channel
theorem pushAbstract_proven : PushAbstractProp := by
  unfold PushAbstractProp
  intros
  rfl

def PopfirstAbstractProp : Prop := ∀ take channel, popfirstAbstract take channel = take channel
theorem popfirstAbstract_proven : PopfirstAbstractProp := by
  unfold PopfirstAbstractProp
  intros
  rfl

def ChannelIntegerProp : Prop := ∀ size, channelIntegerM size = ChannelsCov.channelInteger size
theorem channelInteger_proven : ChannelIntegerProp := by
  unfold ChannelIntegerProp
  intros
  rfl

def ChannelFloatProp : Prop := ∀ size, channelFloatM size = ChannelsCov.channelFloat size
theorem channelFloat_proven : ChannelFloatProp := by
  unfold ChannelFloatProp
  intros
  rfl

def ChannelDefaultProp : Prop := ∀ size, channelDefaultM size = ChannelsCov.channelDefault size
theorem channelDefault_proven : ChannelDefaultProp := by
  unfold ChannelDefaultProp
  intros
  rfl

def ChannelFunctionProp : Prop := ∀ size spawn pool taskref,
  channelFunctionM size spawn pool taskref = ChannelsCov.channelFunction size spawn pool taskref
theorem channelFunction_proven : ChannelFunctionProp := by
  unfold ChannelFunctionProp
  intros
  rfl

def ChannelFunctionAnyProp : Prop := ∀ size spawn pool taskref,
  channelFunctionAnyM size spawn pool taskref = ChannelsCov.channelFunction size spawn pool taskref
theorem channelFunctionAny_proven : ChannelFunctionAnyProp := by
  unfold ChannelFunctionAnyProp
  intros
  rfl

def ClosedExceptionProp : Prop := ∀ _u : Unit, closedExceptionM = .invalidState "Channel is closed." "closed"
theorem closedException_proven : ClosedExceptionProp := by
  unfold ClosedExceptionProp
  intros
  rfl

def IsbufferedProp : Prop := ∀ c, isbufferedM c = (c.size != 0)
theorem isbuffered_proven : IsbufferedProp := by
  unfold IsbufferedProp
  intros
  rfl

def CheckChannelStateProp : Prop := ∀ c, checkChannelState c =
  if !c.isOpen then match c.exception with | some e => .error e | none => .error ChannelsCov.closedException
  else .ok ()
theorem checkChannelState_proven : CheckChannelStateProp := by
  unfold CheckChannelStateProp
  intros
  rfl

def CloseDefaultProp : Prop := ∀ c, closeDefaultM c = ChannelsCov.close c ChannelsCov.closedException
theorem closeDefault_proven : CloseDefaultProp := by
  unfold CloseDefaultProp
  intros
  rfl

def CloseProp : Prop := ∀ c e, closeM c e = { c with isOpen := false, exception := some e }
theorem close_proven : CloseProp := by
  unfold CloseProp
  intros
  rfl

def IsopenProp : Prop := ∀ c, isopenM c = c.isOpen
theorem isopen_proven : IsopenProp := by
  unfold IsopenProp
  intros
  rfl

def EmptyProp : Prop := ∀ s task, emptyM s task = JuliaLean.Channels.emptyBody s task
theorem empty_proven : EmptyProp := by
  unfold EmptyProp
  intros
  rfl

def BindProp : Prop := ∀ c, (bindM c).hooks = c.hooks + 1
theorem bind_proven : BindProp := by
  unfold BindProp
  intros
  rfl

def ChanneledTasksProp : Prop := ∀ n funcs types sizes,
  channeledTasksM n funcs types sizes = ChannelsCov.channeledTasks n funcs types sizes
theorem channeledTasks_proven : ChanneledTasksProp := by
  unfold ChanneledTasksProp
  intros
  rfl

def CloseOnTaskDoneProp : Prop := ∀ status c,
  closeOnTaskDoneM status c = ChannelsCov.closeOnTaskDone status c
theorem closeOnTaskDone_proven : CloseOnTaskDoneProp := by
  unfold CloseOnTaskDoneProp
  intros
  rfl

def ShowInvalidStateProp : Prop := ∀ msg, showInvalidStateM msg = "InvalidStateException: " ++ msg
theorem showInvalidState_proven : ShowInvalidStateProp := by
  unfold ShowInvalidStateProp
  intros
  rfl

def PutProp : Prop := ∀ s task value, putM s task value =
  if s.ch.sz = 0 then JuliaLean.Channels.putUnbBody s task value
  else JuliaLean.Channels.putBufBody s task value
theorem put_proven : PutProp := by
  unfold PutProp
  intros
  rfl

def IncrementAvailableProp : Prop := ∀ s inc,
  (incrementAvailableM s inc).ch.nAvail = s.ch.nAvail + inc
theorem incrementAvailable_proven : IncrementAvailableProp := by
  unfold IncrementAvailableProp
  intros
  rfl

def PutBufferedProp : Prop := ∀ s task value,
  putBufferedM s task value = JuliaLean.Channels.putBufBody s task value
theorem putBuffered_proven : PutBufferedProp := by
  unfold PutBufferedProp
  intros
  rfl

def PutUnbufferedProp : Prop := ∀ s task value,
  putUnbufferedM s task value = JuliaLean.Channels.putUnbBody s task value
theorem putUnbuffered_proven : PutUnbufferedProp := by
  unfold PutUnbufferedProp
  intros
  rfl

def FetchProp : Prop := ∀ s task, fetchM s task =
  if s.ch.sz = 0 then s.finish task (.err .fetchUnbuffered) else JuliaLean.Channels.fetchBody s task
theorem fetch_proven : FetchProp := by
  unfold FetchProp
  intros
  rfl

def FetchBufferedProp : Prop := ∀ s task,
  fetchBufferedM s task = JuliaLean.Channels.fetchBody s task
theorem fetchBuffered_proven : FetchBufferedProp := by
  unfold FetchBufferedProp
  intros
  rfl

def FetchUnbufferedProp : Prop := ∀ _c : Nat,
  fetchUnbufferedM = .error (.errorException "`fetch` is not supported on an unbuffered Channel.")
theorem fetchUnbuffered_proven : FetchUnbufferedProp := by
  unfold FetchUnbufferedProp
  intros
  rfl

def TakeProp : Prop := ∀ s task,
  takeM s task false = JuliaLean.Channels.takeBody s task false
theorem take_proven : TakeProp := by
  unfold TakeProp
  intros
  rfl

def TakeBufferedProp : Prop := ∀ s task,
  takeBufferedM s task false = JuliaLean.Channels.takeBufBody s task false
theorem takeBuffered_proven : TakeBufferedProp := by
  unfold TakeBufferedProp
  intros
  rfl

def TakeUnbufferedProp : Prop := ∀ s task,
  takeUnbufferedM s task false = JuliaLean.Channels.takeUnbStart s task false
theorem takeUnbuffered_proven : TakeUnbufferedProp := by
  unfold TakeUnbufferedProp
  intros
  rfl

def IsreadyProp : Prop := ∀ s, isreadyM s = decide (s.ch.nAvail > 0)
theorem isready_proven : IsreadyProp := by
  unfold IsreadyProp
  intros
  rfl

def IsemptyProp : Prop := ∀ s, isemptyM s = decide (s.ch.nAvail = 0)
theorem isempty_proven : IsemptyProp := by
  unfold IsemptyProp
  intros
  rfl

def NAvailProp : Prop := ∀ s, nAvailM s = s.ch.nAvail
theorem nAvail_proven : NAvailProp := by
  unfold NAvailProp
  intros
  rfl

def IsfullProp : Prop := ∀ s, isfullM s = decide ((s.ch.sz : Int) ≤ s.ch.nAvail)
theorem isfull_proven : IsfullProp := by
  unfold IsfullProp
  intros
  rfl

def LockProp : Prop := ∀ c, (lockM c).locked = true
theorem lock_proven : LockProp := by
  unfold LockProp
  intros
  rfl

def LockDoProp : Prop := ∀ body c, lockDoM body c = (body, ChannelsCov.channelUnlock (ChannelsCov.channelLock c))
theorem lockDo_proven : LockDoProp := by
  unfold LockDoProp
  intros
  rfl

def UnlockProp : Prop := ∀ c, (unlockM c).locked = false
theorem unlock_proven : UnlockProp := by
  unfold UnlockProp
  intros
  rfl

def TrylockProp : Prop := ∀ c, trylockM c = if c.locked then (false, c) else (true, ChannelsCov.channelLock c)
theorem trylock_proven : TrylockProp := by
  unfold TrylockProp
  intros
  rfl

def WaitProp : Prop := ∀ s task, waitM s task = JuliaLean.Channels.waitBody s task
theorem wait_proven : WaitProp := by
  unfold WaitProp
  intros
  rfl

def EltypeProp : Prop := ∀ typeName, eltypeM typeName = typeName
theorem eltype_proven : EltypeProp := by
  unfold EltypeProp
  intros
  rfl

def ShowShortProp : Prop := ∀ typeName c,
  showShortM typeName c = typeName ++ "(" ++ toString c.size ++ ")"
theorem showShort_proven : ShowShortProp := by
  unfold ShowShortProp
  intros
  rfl

def ShowPlainProp : Prop := ∀ compact typeName c,
  showPlainM compact typeName c = ChannelsCov.channelShowPlain compact typeName c
theorem showPlain_proven : ShowPlainProp := by
  unfold ShowPlainProp
  intros
  rfl

def IterateProp : Prop := ∀ s task, iterateM s task = JuliaLean.Channels.takeBody s task true
theorem iterate_proven : IterateProp := by
  unfold IterateProp
  intros
  rfl

def IteratorSizeProp : Prop := ∀ _type : Nat, iteratorSizeM = .sizeUnknown
theorem iteratorSize_proven : IteratorSizeProp := by
  unfold IteratorSizeProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulChannels
