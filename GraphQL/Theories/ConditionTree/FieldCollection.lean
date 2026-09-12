import GraphQL.Execution

/-! Occurrence-preserving runtime field collection and response-name grouping. -/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution

-- Ungrouped runtime field collection for one selection-set scope.
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

-- Groups a flat field stream by response name. The first occurrence fixes group order;
-- later occurrences append their selections to that group.
def groupExecutableFields (fields : List (Name × ExecutableField))
    : List (Name × List ExecutableField) :=
  fields.foldl (fun groups entry => addExecutableGroup (entry.1, [entry.2]) groups) []

-- Lossless occurrence stream for a response-name-grouped field map.
def flattenExecutableFieldGroups
    : List (Name × List ExecutableField) -> List (Name × ExecutableField)
  | [] => []
  | (responseName, fields) :: rest =>
      fields.map (fun field => (responseName, field)) ++ flattenExecutableFieldGroups rest

def RuntimeFieldGroupsExact (fields : List (Name × ExecutableField))
    (groups : List (Name × List ExecutableField))
    : Prop :=
  (groups.map Prod.fst).Nodup ∧ (flattenExecutableFieldGroups groups).Perm fields

end ConditionTree
end GraphQL
