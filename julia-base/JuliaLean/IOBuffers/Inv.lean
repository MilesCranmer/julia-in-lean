import JuliaLean.IOBuffers.Props

/-!
Well-formedness of a reachable `IOBuffer` (the comments at `base/iobuffer.jl:55-93`),
with the size bounds that keep every `Int` computation of the modelled methods free of
wrapping. `reachable_inv` (in `InvProofs.lean`) shows that every reachable buffer
satisfies it.
-/

namespace JuliaLean.IOBuffers

open JuliaLean

structure Inv (io : IOBuf) : Prop where
  maxsize_nonneg : 0 ≤ io.maxsize.val
  len_le : io.data.length ≤ 2 ^ 62
  oc_ge : -2 ^ 61 ≤ io.oc.val
  oc_seekable : io.seekable = true → 0 ≤ io.oc.val
  off_le_size : (getOffset io).val ≤ io.size.val
  size_le_len : io.size.val ≤ io.data.length
  ptr_ge : (getOffset io).val + 1 ≤ io.ptr.val
  ptr_le : io.ptr.val ≤ io.size.val + 1
  stored_le : io.size.val - (getOffset io).val ≤ io.maxsize.val
  mark_ge : -1 ≤ io.mark.val
  mark_le : io.mark.val ≤ 2 ^ 62
  mark_pipe : io.seekable = false → 0 ≤ io.mark.val →
    io.mark.val ≤ (position io).val ∧ (getOffset io).val ≤ io.mark.val + io.oc.val
  reinit_state : io.reinit = true → io.ptr.val = 1 ∧ io.size.val = 0 ∧ io.oc.val = 0

end JuliaLean.IOBuffers
