import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL

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
