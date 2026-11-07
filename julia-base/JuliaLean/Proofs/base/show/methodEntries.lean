import JuliaLean.Proofs.base.coreio.showMethods
import JuliaLean.Proofs.base.Terminals.methods
import JuliaLean.Proofs.base.terminfo.methods
import JuliaLean.Proofs.base.strings.io.methods

namespace JuliaLean.ShowCov.Methods

def entries := CoreIO.entries ++ TerminalsFile.entries ++ TermInfoFile.entries ++
  StringsIOFile.entries

end JuliaLean.ShowCov.Methods
