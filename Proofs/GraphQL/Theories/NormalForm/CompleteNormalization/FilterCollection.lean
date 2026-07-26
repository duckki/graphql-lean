import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterReadiness
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.InlineDirectiveExecution

/-!
Field-collection facts for Boolean case filtering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

def filterExecutableFieldBoolCase
    (boolCase : BoolCase) (field : Execution.ExecutableField)
    : Execution.ExecutableField :=
  {
    field with
      selectionSet :=
        filterSelectionSetBoolCase boolCase field.selectionSet
  }

def filterExecutableGroupBoolCase
    (boolCase : BoolCase)
    (group : Name × List Execution.ExecutableField)
    : Name × List Execution.ExecutableField :=
  (group.fst, group.snd.map (filterExecutableFieldBoolCase boolCase))

def filterExecutableGroupsBoolCase
    (boolCase : BoolCase)
    (groups : List (Name × List Execution.ExecutableField))
    : List (Name × List Execution.ExecutableField) :=
  groups.map (filterExecutableGroupBoolCase boolCase)

theorem filterExecutableGroupsBoolCase_nil (boolCase : BoolCase)
    : filterExecutableGroupsBoolCase boolCase [] = [] := by
  rfl

theorem filterExecutableGroupsBoolCase_cons
    (boolCase : BoolCase)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : filterExecutableGroupsBoolCase boolCase (group :: groups)
      = filterExecutableGroupBoolCase boolCase group
        :: filterExecutableGroupsBoolCase boolCase groups := by
  rfl

theorem filterExecutableGroupsBoolCase_addExecutableGroup
    (boolCase : BoolCase)
    (group : Name × List Execution.ExecutableField)
    : ∀ groups,
        filterExecutableGroupsBoolCase boolCase
          (Execution.addExecutableGroup group groups)
        = Execution.addExecutableGroup
            (filterExecutableGroupBoolCase boolCase group)
            (filterExecutableGroupsBoolCase boolCase groups)
  | [] => by
      cases group
      rfl
  | candidate :: rest => by
      cases group with
      | mk responseName fields =>
      cases candidate with
      | mk candidateName candidateFields =>
      cases hresponse : candidateName == responseName <;>
        simp [Execution.addExecutableGroup,
          filterExecutableGroupsBoolCase,
          filterExecutableGroupBoolCase, hresponse, List.map_append]
      exact filterExecutableGroupsBoolCase_addExecutableGroup boolCase
        (responseName, fields) rest

theorem filterExecutableGroupsBoolCase_mergeExecutableGroups
    (boolCase : BoolCase)
    (left right : List (Name × List Execution.ExecutableField))
    : filterExecutableGroupsBoolCase boolCase (Execution.mergeExecutableGroups left right)
      = Execution.mergeExecutableGroups
          (filterExecutableGroupsBoolCase boolCase left)
          (filterExecutableGroupsBoolCase boolCase right) := by
  unfold Execution.mergeExecutableGroups
  induction right generalizing left with
  | nil =>
      simp [filterExecutableGroupsBoolCase]
  | cons group rest ih =>
      rw [List.foldl_cons]
      rw [ih (Execution.addExecutableGroup group left)]
      rw [filterExecutableGroupsBoolCase_addExecutableGroup]
      rfl

mutual
  theorem collectSelection_filterSelectionSetBoolCase
      (schema : Schema) (variableValues : Execution.VariableValues)
      (operation : Operation) (boolCase : BoolCase)
      (hagrees
        : variableValuesAgreeWithCase variableValues boolCase
            (operationBoolVars operation))
      : ∀ parentType (source : Execution.ResolverValue ObjectRef) selection,
          (∀ varName,
            varName ∈ selectionBooleanVariables selection
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
          -> Execution.collectFields schema variableValues parentType source
                (filterSelectionSetBoolCase boolCase [selection])
              = filterExecutableGroupsBoolCase boolCase
                  (Execution.collectSelection schema variableValues parentType
                    source selection)
    | parentType, source,
      .field responseName fieldName arguments directives selectionSet,
      hsourceVars => by
        have hdirectiveEq :
            directivesAllowIn boolCase directives =
              Execution.selectionDirectivesAllowBool variableValues
                directives :=
          directivesAllowInCase_eq_execution_of_operationVariables
            variableValues boolCase operation directives hagrees
            (by
              intro varName hmem
              exact hsourceVars varName
                (by
                  simp [selectionBooleanVariables, hmem]))
        cases hallow : directivesAllowIn boolCase directives
        · have hexec :
              Execution.selectionDirectivesAllowBool variableValues
                directives = false := by
            simpa [hallow] using hdirectiveEq.symm
          simp [filterSelectionSetBoolCase, hallow,
            Execution.collectFields, Execution.collectSelection, hexec,
            filterExecutableGroupsBoolCase]
        · have hexec :
              Execution.selectionDirectivesAllowBool variableValues
                directives = true := by
            simpa [hallow] using hdirectiveEq.symm
          cases selectionSet with
          | nil =>
              have hempty :
                  Execution.selectionDirectivesAllowBool variableValues [] =
                    true := by
                simp [Execution.selectionDirectivesAllowBool]
              simp [filterSelectionSetBoolCase, hallow,
                Execution.collectFields, Execution.collectSelection, hexec,
                hempty,
                Execution.mergeExecutableGroups,
                filterExecutableGroupsBoolCase,
                filterExecutableGroupBoolCase,
                filterExecutableFieldBoolCase]
          | cons child children =>
              cases hchild :
                  filterSelectionSetBoolCase boolCase
                    (child :: children) with
              | nil =>
                  have hempty :
                      Execution.selectionDirectivesAllowBool variableValues [] =
                        true := by
                    simp [Execution.selectionDirectivesAllowBool]
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    Execution.collectFields, Execution.collectSelection,
                    hexec, hempty,
                    Execution.mergeExecutableGroups,
                    filterExecutableGroupsBoolCase,
                    filterExecutableGroupBoolCase,
                    filterExecutableFieldBoolCase]
              | cons filteredChild filteredChildren =>
                  have hempty :
                      Execution.selectionDirectivesAllowBool variableValues [] =
                        true := by
                    simp [Execution.selectionDirectivesAllowBool]
                  simp [filterSelectionSetBoolCase, hallow, hchild,
                    Execution.collectFields, Execution.collectSelection,
                    hexec, hempty,
                    Execution.mergeExecutableGroups,
                    filterExecutableGroupsBoolCase,
                    filterExecutableGroupBoolCase,
                    filterExecutableFieldBoolCase]
    | parentType, source,
      .inlineFragment none directives selectionSet, hsourceVars => by
        have hdirectiveEq :
            directivesAllowIn boolCase directives =
              Execution.selectionDirectivesAllowBool variableValues
                directives :=
          directivesAllowInCase_eq_execution_of_operationVariables
            variableValues boolCase operation directives hagrees
            (by
              intro varName hmem
              exact hsourceVars varName
                (by
                  simp [selectionBooleanVariables, hmem]))
        cases hallow : directivesAllowIn boolCase directives
        · have hexec :
              Execution.selectionDirectivesAllowBool variableValues
                directives = false := by
            simpa [hallow] using hdirectiveEq.symm
          simp [filterSelectionSetBoolCase, hallow,
            Execution.collectFields, Execution.collectSelection, hexec,
            filterExecutableGroupsBoolCase]
        · have hexec :
              Execution.selectionDirectivesAllowBool variableValues
                directives = true := by
            simpa [hallow] using hdirectiveEq.symm
          have hchildVars :
              ∀ varName,
                varName ∈ selectionSetBooleanVariables selectionSet ->
                  varName ∈
                    selectionSetBooleanVariables operation.selectionSet := by
            intro varName hmem
            exact hsourceVars varName
              (by simp [selectionBooleanVariables, hmem])
          have hchildCollect :=
            collectFields_filterSelectionSetBoolCase schema variableValues
              operation boolCase hagrees parentType source selectionSet
              hchildVars
          cases hchild :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              simpa [filterSelectionSetBoolCase, hallow, hchild,
                Execution.collectFields, Execution.collectSelection, hexec,
                filterExecutableGroupsBoolCase] using hchildCollect
          | cons filteredChild filteredChildren =>
              have hempty :
                  Execution.selectionDirectivesAllowBool variableValues [] =
                    true := by
                simp [Execution.selectionDirectivesAllowBool]
              simpa [filterSelectionSetBoolCase, hallow, hchild,
                Execution.collectFields, Execution.collectSelection,
                Execution.mergeExecutableGroups, hexec, hempty]
                using hchildCollect
    | parentType, source,
      .inlineFragment (some typeCondition) directives selectionSet,
      hsourceVars => by
        have hdirectiveEq :
            directivesAllowIn boolCase directives =
              Execution.selectionDirectivesAllowBool variableValues
                directives :=
          directivesAllowInCase_eq_execution_of_operationVariables
            variableValues boolCase operation directives hagrees
            (by
              intro varName hmem
              exact hsourceVars varName
                (by
                  simp [selectionBooleanVariables, hmem]))
        cases hallow : directivesAllowIn boolCase directives
        · have hexec :
              Execution.selectionDirectivesAllowBool variableValues
                directives = false := by
            simpa [hallow] using hdirectiveEq.symm
          simp [filterSelectionSetBoolCase, hallow,
            Execution.collectFields, Execution.collectSelection, hexec,
            filterExecutableGroupsBoolCase]
        · have hexec :
              Execution.selectionDirectivesAllowBool variableValues
                directives = true := by
            simpa [hallow] using hdirectiveEq.symm
          have hchildVars :
              ∀ varName,
                varName ∈ selectionSetBooleanVariables selectionSet ->
                  varName ∈
                    selectionSetBooleanVariables operation.selectionSet := by
            intro varName hmem
            exact hsourceVars varName
              (by simp [selectionBooleanVariables, hmem])
          have hchildCollect :=
            collectFields_filterSelectionSetBoolCase schema variableValues
              operation boolCase hagrees parentType source selectionSet
              hchildVars
          cases happly :
              Execution.doesFragmentTypeApplyBool schema parentType source
                typeCondition
          · cases hchild :
                filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                simp [filterSelectionSetBoolCase, hallow, hchild,
                  Execution.collectFields, Execution.collectSelection, hexec,
                  happly, filterExecutableGroupsBoolCase]
            | cons filteredChild filteredChildren =>
                simp [filterSelectionSetBoolCase, hallow, hchild,
                  Execution.collectFields, Execution.collectSelection, hexec,
                  happly, filterExecutableGroupsBoolCase,
                  Execution.mergeExecutableGroups]
          · cases hchild :
                filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                simpa [filterSelectionSetBoolCase, hallow, hchild,
                  Execution.collectFields, Execution.collectSelection, hexec,
                  happly, filterExecutableGroupsBoolCase] using hchildCollect
            | cons filteredChild filteredChildren =>
                have hempty :
                    Execution.selectionDirectivesAllowBool variableValues [] =
                      true := by
                  simp [Execution.selectionDirectivesAllowBool]
                simpa [filterSelectionSetBoolCase, hallow, hchild,
                  Execution.collectFields, Execution.collectSelection, hexec,
                  Execution.mergeExecutableGroups, happly, hempty]
                  using hchildCollect

  theorem collectFields_filterSelectionSetBoolCase
      (schema : Schema) (variableValues : Execution.VariableValues)
      (operation : Operation) (boolCase : BoolCase)
      (hagrees
        : variableValuesAgreeWithCase variableValues boolCase
            (operationBoolVars operation))
      : ∀ parentType (source : Execution.ResolverValue ObjectRef) selectionSet,
          (∀ varName,
            varName ∈ selectionSetBooleanVariables selectionSet
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
          -> Execution.collectFields schema variableValues parentType source
                (filterSelectionSetBoolCase boolCase selectionSet)
              = filterExecutableGroupsBoolCase boolCase
                  (Execution.collectFields schema variableValues parentType source
                    selectionSet)
    | _parentType, _source, [], _hsourceVars => by
        simp [filterSelectionSetBoolCase, Execution.collectFields,
          filterExecutableGroupsBoolCase]
    | parentType, source, selection :: rest, hsourceVars => by
        have hheadVars :
            ∀ varName,
              varName ∈ selectionBooleanVariables selection ->
                varName ∈
                  selectionSetBooleanVariables operation.selectionSet := by
          intro varName hmem
          exact hsourceVars varName
            (by simp [selectionSetBooleanVariables, hmem])
        have htailVars :
            ∀ varName,
              varName ∈ selectionSetBooleanVariables rest ->
                varName ∈
                  selectionSetBooleanVariables operation.selectionSet := by
          intro varName hmem
          exact hsourceVars varName
            (by simp [selectionSetBooleanVariables, hmem])
        have hhead :=
          collectSelection_filterSelectionSetBoolCase schema variableValues
            operation boolCase hagrees parentType source selection hheadVars
        have htail :=
          collectFields_filterSelectionSetBoolCase schema variableValues
            operation boolCase hagrees parentType source rest htailVars
        rw [filterSelectionSetBoolCase_cons]
        rw [collectFields_append]
        rw [hhead, htail]
        simp [Execution.collectFields,
          filterExecutableGroupsBoolCase_mergeExecutableGroups]
end

end CompleteNormalization

end NormalForm

end GraphQL
