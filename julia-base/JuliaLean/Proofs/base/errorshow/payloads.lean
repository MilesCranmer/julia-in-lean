import JuliaLean.base.errorshow


namespace JuliaLean.ErrorShow


def emittedPayloads : List Piece → List String
  | [] => []
  | .literal _ :: rest => emittedPayloads rest
  | .payload text :: rest => text :: emittedPayloads rest

def errorPayloads : ErrorView → List String
  | .fallback shown => [shown]
  | .parse messageRepr none => [messageRepr]
  | .parse _ (some detail) => [detail]
  | .typeName _ => []
  | .bareBounds => []
  | .bounds summary indices => summary :: indices
  | .typeErrorBoolean gotType => [gotType]
  | .typeErrorDictKey gotRepr expected => [gotRepr, expected]
  | .typeError context expected got => [context, expected, got]
  | .load inner file line => [inner, file, line]
  | .init inner moduleName => [inner, moduleName]
  | .domain value none => [value]
  | .domain value (some message) => [value, message]
  | .system sysPrefix errorText none => [sysPrefix, errorText]
  | .system sysPrefix errorText (some extra) => [extra, sysPrefix, errorText]
  | .fixed _ => []
  | .message _ message => [message]
  | .key keyRepr => [keyRepr]
  | .undefKeyword name => [name]
  | .undefVar name none => [name]
  | .undefVar name (some (.moduleName scope)) => [name, scope]
  | .undefVar name (some .staticParameter) => [name]
  | .undefVar name (some (.localKind scope)) => [name, scope]
  | .inexact functionName typeName typeRepr firstArgument moreArguments =>
      functionName :: (if typeName == functionName then [] else [typeRepr]) ++
        firstArgument :: moreArguments
  | .canonicalIndex functionName typeRepr => [functionName, typeRepr]
  | .method signature hints candidates => signature :: hints ++ candidates
  | .field typeRepr fieldName hint => [typeRepr, fieldName] ++ hint.toList

end JuliaLean.ErrorShow
