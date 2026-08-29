import GraphQL.Execution

/-! Occurrence-preserving runtime field collection and response-name grouping. -/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution

-- Ungrouped runtime field collection for one selection-set scope.
mutual
  def collectFlatFields (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : List Selection -> List ExecutableField
    | [] => []
    | selection :: rest =>
        collectFlatSelection schema variableValues executionParentType source selection
        ++ collectFlatFields schema variableValues executionParentType source rest

  def collectFlatSelection (schema : Schema) (variableValues : VariableValues)
      (executionParentType : Name) (source : ResolverValue ObjectRef)
      : Selection -> List ExecutableField
    | .field responseName fieldName arguments directives selectionSet =>
        if selectionDirectivesAllowBool variableValues directives then
          [{
            parentType := executionParentType
            responseName
            fieldName
            arguments
            selectionSet
          }]
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

-- For coverage and exactness statements, forget response-name grouping while retaining
-- every executable field occurrence.
def flattenCollectedFields (groups : List (Name × List ExecutableField))
    : List ExecutableField :=
  groups.flatMap Prod.snd

-- Groups a flat field stream by response name. The first occurrence fixes group order;
-- later occurrences append their selections to that group.
def groupExecutableFields (fields : List ExecutableField)
    : List (Name × List ExecutableField) :=
  fields.foldl
    (fun groups field => addExecutableGroup (field.responseName, [field]) groups) []

def RuntimeFieldGroupsExact (fields : List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  (groups.map Prod.fst).Nodup ∧ (flattenCollectedFields groups).Perm fields

end ConditionTree
end GraphQL
