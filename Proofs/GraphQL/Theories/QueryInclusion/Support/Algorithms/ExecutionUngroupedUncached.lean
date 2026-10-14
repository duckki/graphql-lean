import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Algorithms.ExecutionUngroupedUncached

open GraphQL.Execution

def executableField (fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    : ExecutableField :=
  {
    fieldName := fieldName
    arguments := arguments
    selectionSet := selectionSet
  }

end GraphQL.Algorithms.ExecutionUngroupedUncached
