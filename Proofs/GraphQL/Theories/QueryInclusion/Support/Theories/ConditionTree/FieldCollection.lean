import GraphQL.Theories.QueryInclusion

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.ConditionTree

open GraphQL.Execution

mutual
  def collectFlatFields (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : List Selection -> List (Name × ExecutableField)
    | [] => []
    | selection :: rest =>
        collectFlatSelection schema variableValues executionParentType source selection
        ++ collectFlatFields schema variableValues executionParentType source rest

  def collectFlatSelection (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : Selection -> List (Name × ExecutableField)
    | .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [(
            responseName,
            {
              fieldName
              arguments
              selectionSet
            }
          )]
        else
          []
    | .inlineFragment none directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          collectFlatFields schema variableValues executionParentType source selectionSet
        else
          []
    | .inlineFragment (some typeCondition) directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives
            && doesFragmentTypeApplyBool schema executionParentType source
                typeCondition then
          collectFlatFields schema variableValues executionParentType source selectionSet
        else
          []
end

def flattenExecutableFieldGroups
    : List (Name × List ExecutableField) -> List (Name × ExecutableField)
  | [] => []
  | (responseName, fields) :: rest =>
      fields.map (fun field => (responseName, field)) ++ flattenExecutableFieldGroups rest

end GraphQL.ConditionTree
