import JuliaLean.base.libuv

namespace JuliaLean.Streams

open JuliaLean

def LibuvHandleCoverage : Prop := ∀ (α : Type) (x : α) h size depth,
  associateHandle x = ⟨true, false, true⟩ ∧
  (disassociateHandle h).associated = false ∧
  (preserveHandle h).preserved = true ∧
  (unpreserveHandle h).preserved = false ∧
  (uvRef h).referenced = true ∧ (uvUnref h).referenced = false ∧
  uvSizeResult none = .error .argumentError ∧ uvSizeResult (some size) = .ok size ∧
  iolockDepth depth true = depth + 1 ∧ iolockDepth depth false = depth - 1

def LibuvErrorCoverage : Prop := ∀ code pfx name description kind,
  uvErrorResult code = (if code < 0 then .error .ioError else .ok ()) ∧
  uvErrorText pfx name description code =
    pfx ++ ": " ++ name ++ " (" ++ description ++ ")" ++ " [" ++ toString code ++ "]" ∧
  reinitStdioKind kind = (match kind with
    | .file => .ok .ioStream | .tty | .tcp | .pipe => .ok .libuvStream
    | .invalid => .error .argumentError)

theorem libuvHandleCoverage_proven : LibuvHandleCoverage := by
  simp [LibuvHandleCoverage, associateHandle, disassociateHandle, preserveHandle,
    unpreserveHandle, uvRef, uvUnref, uvSizeResult, iolockDepth]
theorem libuvErrorCoverage_proven : LibuvErrorCoverage := by
  intro code pfx name description kind
  cases kind <;> simp [uvErrorResult, uvErrorText, reinitStdioKind]

end JuliaLean.Streams
