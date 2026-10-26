import JuliaLean.ShowCov.MethodsCoreIO
import JuliaLean.ShowCov.MethodsTerminals
import JuliaLean.ShowCov.MethodsTermInfo
import JuliaLean.ShowCov.MethodsStringsIO
import JuliaLean.ShowCov.MethodsShow

namespace JuliaLean.ShowCov.Methods

def entries := CoreIO.entries ++ TerminalsFile.entries ++ TermInfoFile.entries ++
  StringsIOFile.entries ++ ShowFile.entries

end JuliaLean.ShowCov.Methods
