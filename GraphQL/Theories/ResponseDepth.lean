import GraphQL.Operation

/-! Response-depth metrics shared by recursive execution theories. -/

namespace GraphQL

-- Response-field boundaries along one selection path. Inline fragments do not consume
-- execution or query-inclusion fuel by themselves.
mutual
  def selectionResponseDepth : Selection -> Nat
    | .field _responseName _fieldName _arguments _directives selectionSet =>
        selectionSetResponseDepth selectionSet + 1
    | .inlineFragment _typeCondition _directives selectionSet =>
        selectionSetResponseDepth selectionSet

  def selectionSetResponseDepth : List Selection -> Nat
    | [] => 0
    | selection :: rest =>
        max (selectionResponseDepth selection) (selectionSetResponseDepth rest)
end

end GraphQL
