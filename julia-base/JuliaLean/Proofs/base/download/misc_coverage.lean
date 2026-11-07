import JuliaLean.base.download

namespace JuliaLean.MiscCov.BaseJl

/-- The UUID is that of the `Downloads` stdlib (`f43a241f-c20a-4ad4-852c-f6b1247861c6`
in its `Project.toml`); both methods warn once, then call `Downloads.download` with the
given path, or `nothing` (a temporary file) when none is given. -/
def DownloadContract : Prop :=
  downloadsUuid = 0xf43a241fc20a4ad4852cf6b1247861c6 ∧
  (∀ url path, download2 url path = [.depwarn "Base.download is deprecated; use Downloads.download instead" "download",
      .require downloadsUuid "Downloads", .download url (some path)]) ∧
  (∀ url, (download1 url).getLast? = some (.download url none) ∧
      (download1 url).countP (fun e => match e with | .depwarn .. => true | _ => false) = 1)

theorem downloadContract_proven : DownloadContract := by
  refine ⟨by decide, fun _ _ => rfl, fun url => ⟨rfl, rfl⟩⟩

end JuliaLean.MiscCov.BaseJl
