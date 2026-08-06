import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterCollection

/-!
Execution facts for Boolean case filtering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

def executableFieldSelectionVarsInOperation
    (operation : Operation) (field : Execution.ExecutableField)
    : Prop :=
  ∀ varName,
    varName ∈ selectionSetBooleanVariables field.selectionSet
    -> varName ∈ selectionSetBooleanVariables operation.selectionSet

def executableFieldsSelectionVarsInOperation
    (operation : Operation) (fields : List Execution.ExecutableField)
    : Prop :=
  ∀ field, field ∈ fields -> executableFieldSelectionVarsInOperation operation field

def executableGroupsSelectionVarsInOperation
    (operation : Operation)
    (groups : List (Name × List Execution.ExecutableField))
    : Prop :=
  ∀ group, group ∈ groups -> executableFieldsSelectionVarsInOperation operation group.snd

theorem filterExecutableFieldBoolCase_parentType
    (boolCase : BoolCase) (field : Execution.ExecutableField)
    : (filterExecutableFieldBoolCase boolCase field).parentType = field.parentType := by
  rfl

theorem filterExecutableFieldBoolCase_fieldName
    (boolCase : BoolCase) (field : Execution.ExecutableField)
    : (filterExecutableFieldBoolCase boolCase field).fieldName = field.fieldName := by
  rfl

theorem filterExecutableFieldBoolCase_arguments
    (boolCase : BoolCase) (field : Execution.ExecutableField)
    : (filterExecutableFieldBoolCase boolCase field).arguments = field.arguments := by
  rfl

theorem mergedFieldSelectionSet_map_filterExecutableFieldBoolCase (boolCase : BoolCase)
    : ∀ fields,
        Execution.mergedFieldSelectionSet
          (fields.map (filterExecutableFieldBoolCase boolCase))
        = filterSelectionSetBoolCase boolCase (Execution.mergedFieldSelectionSet fields)
  | [] => by
      simp [Execution.mergedFieldSelectionSet, filterSelectionSetBoolCase]
  | field :: rest => by
      simp [Execution.mergedFieldSelectionSet,
        filterExecutableFieldBoolCase,
        mergedFieldSelectionSet_map_filterExecutableFieldBoolCase boolCase
          rest,
        filterSelectionSetBoolCase_append]

theorem selectionSetBooleanVariables_append_iff (varName : BoolVar)
    : ∀ left right,
        varName ∈ selectionSetBooleanVariables (left ++ right)
        ↔ varName ∈ selectionSetBooleanVariables left
          ∨ varName ∈ selectionSetBooleanVariables right
  | [], right => by
      simp [selectionSetBooleanVariables]
  | selection :: rest, right => by
      simp [selectionSetBooleanVariables,
        selectionSetBooleanVariables_append_iff varName rest right]
      constructor
      · intro h
        cases h with
        | inl hselection => exact Or.inl (Or.inl hselection)
        | inr htail =>
            cases htail with
            | inl hrest => exact Or.inl (Or.inr hrest)
            | inr hright => exact Or.inr hright
      · intro h
        cases h with
        | inl hleft =>
            cases hleft with
            | inl hselection => exact Or.inl hselection
            | inr hrest => exact Or.inr (Or.inl hrest)
        | inr hright => exact Or.inr (Or.inr hright)

theorem executableFieldsSelectionVarsInOperation_merged (operation : Operation)
    : ∀ fields,
        executableFieldsSelectionVarsInOperation operation fields
        -> ∀ varName,
            varName
              ∈ selectionSetBooleanVariables (Execution.mergedFieldSelectionSet fields)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet
  | [], _hfields, varName, hmem => by
      simp [Execution.mergedFieldSelectionSet,
        selectionSetBooleanVariables] at hmem
  | field :: rest, hfields, varName, hmem => by
      rw [Execution.mergedFieldSelectionSet] at hmem
      have hcases :=
        (selectionSetBooleanVariables_append_iff varName
          field.selectionSet
          (Execution.mergedFieldSelectionSet rest)).mp hmem
      cases hcases with
      | inl hfield =>
          exact hfields field (by simp) varName hfield
      | inr hrest =>
          exact executableFieldsSelectionVarsInOperation_merged operation
            rest
            (by
              intro candidate hcandidate
              exact hfields candidate (by simp [hcandidate]))
                    varName hrest

theorem executableGroupsSelectionVarsInOperation_addExecutableGroup
    (operation : Operation)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : executableFieldsSelectionVarsInOperation operation group.snd
      -> executableGroupsSelectionVarsInOperation operation groups
      -> executableGroupsSelectionVarsInOperation operation
          (Execution.addExecutableGroup group groups) := by
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro candidate hcandidate
      simp [Execution.addExecutableGroup] at hcandidate
      subst candidate
      exact hgroup
  | cons current rest ih =>
      intro candidate hcandidate
      cases group with
      | mk responseName fields =>
          cases current with
          | mk currentName currentFields =>
              cases hresponse : currentName == responseName
              · simp [Execution.addExecutableGroup, hresponse] at hcandidate
                rcases hcandidate with hhead | htail
                ·
                    subst candidate
                    exact hgroups (currentName, currentFields) (by simp)
                ·
                    exact ih
                      (by
                        intro restGroup hmem
                        exact hgroups restGroup (by simp [hmem]))
                      candidate htail
              · simp [Execution.addExecutableGroup, hresponse] at hcandidate
                rcases hcandidate with hhead | htail
                ·
                    subst candidate
                    intro field hfield
                    rw [List.mem_append] at hfield
                    rcases hfield with hcurrent | hnew
                    · exact hgroups (currentName, currentFields) (by simp)
                        field hcurrent
                    · exact hgroup field hnew
                · exact hgroups candidate (by simp [htail])

theorem executableGroupsSelectionVarsInOperation_mergeExecutableGroups
    (operation : Operation)
    (left right : List (Name × List Execution.ExecutableField))
    : executableGroupsSelectionVarsInOperation operation left
      -> executableGroupsSelectionVarsInOperation operation right
      -> executableGroupsSelectionVarsInOperation operation
          (Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  unfold Execution.mergeExecutableGroups
  induction right generalizing left with
  | nil =>
      simpa using hleft
  | cons group rest ih =>
      rw [List.foldl_cons]
      apply ih
      · exact executableGroupsSelectionVarsInOperation_addExecutableGroup
          operation group left (hright group (by simp)) hleft
      · intro candidate hcandidate
        exact hright candidate (by simp [hcandidate])

mutual
  theorem collectSelection_executableGroupsSelectionVarsInOperation
      (schema : Schema) (variableValues : Execution.VariableValues)
      (operation : Operation)
      : ∀ parentType (source : Execution.ResolverValue ObjectRef) selection,
          (∀ varName,
            varName ∈ selectionBooleanVariables selection
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
          -> executableGroupsSelectionVarsInOperation operation
              (Execution.collectSelection schema variableValues parentType
                source selection)
    | parentType, source,
      .field responseName fieldName arguments directives selectionSet,
      hvars => by
        cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
        · simp [Execution.collectSelection, hallow,
            executableGroupsSelectionVarsInOperation]
        · intro group hgroup
          simp [Execution.collectSelection, hallow] at hgroup
          subst group
          intro field hfield
          simp at hfield
          subst field
          intro varName hmem
          exact hvars varName (by
            simp [selectionBooleanVariables, hmem])
    | parentType, source,
      .inlineFragment none directives selectionSet, hvars => by
        cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
        · simp [Execution.collectSelection, hallow,
            executableGroupsSelectionVarsInOperation]
        · have hchildVars :
              ∀ varName,
                varName ∈ selectionSetBooleanVariables selectionSet ->
                  varName ∈
                    selectionSetBooleanVariables operation.selectionSet := by
            intro varName hmem
            exact hvars varName (by
              simp [selectionBooleanVariables, hmem])
          simpa [Execution.collectSelection, hallow] using
            collectFields_executableGroupsSelectionVarsInOperation schema
              variableValues operation parentType source selectionSet
              hchildVars
    | parentType, source,
      .inlineFragment (some typeCondition) directives selectionSet,
      hvars => by
        cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
        · simp [Execution.collectSelection, hallow,
            executableGroupsSelectionVarsInOperation]
        · cases happly :
            Execution.doesFragmentTypeApplyBool schema parentType source
              typeCondition
          · simp [Execution.collectSelection, hallow, happly,
              executableGroupsSelectionVarsInOperation]
          · have hchildVars :
                ∀ varName,
                  varName ∈ selectionSetBooleanVariables selectionSet ->
                    varName ∈
                      selectionSetBooleanVariables operation.selectionSet := by
              intro varName hmem
              exact hvars varName (by
                simp [selectionBooleanVariables, hmem])
            simpa [Execution.collectSelection, hallow, happly] using
              collectFields_executableGroupsSelectionVarsInOperation schema
                variableValues operation parentType source selectionSet
                hchildVars

  theorem collectFields_executableGroupsSelectionVarsInOperation
      (schema : Schema) (variableValues : Execution.VariableValues)
      (operation : Operation)
      : ∀ parentType (source : Execution.ResolverValue ObjectRef) selectionSet,
          (∀ varName,
            varName ∈ selectionSetBooleanVariables selectionSet
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
          -> executableGroupsSelectionVarsInOperation operation
              (Execution.collectFields schema variableValues parentType source
                selectionSet)
    | _parentType, _source, [], _hvars => by
        simp [Execution.collectFields,
          executableGroupsSelectionVarsInOperation]
    | parentType, source, selection :: rest, hvars => by
        have hheadVars :
            ∀ varName,
              varName ∈ selectionBooleanVariables selection ->
                varName ∈
                  selectionSetBooleanVariables operation.selectionSet := by
          intro varName hmem
          exact hvars varName (by
            simp [selectionSetBooleanVariables, hmem])
        have htailVars :
            ∀ varName,
              varName ∈ selectionSetBooleanVariables rest ->
                varName ∈
                  selectionSetBooleanVariables operation.selectionSet := by
          intro varName hmem
          exact hvars varName (by
            simp [selectionSetBooleanVariables, hmem])
        simp [Execution.collectFields]
        exact executableGroupsSelectionVarsInOperation_mergeExecutableGroups
          operation
          (Execution.collectSelection schema variableValues parentType source
            selection)
          (Execution.collectFields schema variableValues parentType source
            rest)
          (collectSelection_executableGroupsSelectionVarsInOperation schema
            variableValues operation parentType source selection hheadVars)
          (collectFields_executableGroupsSelectionVarsInOperation schema
            variableValues operation parentType source rest htailVars)
end

theorem executeCollectedFields_filterExecutableGroupsBoolCase_of_rec
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (boolCase : BoolCase)
    (depth : Nat) (source : Execution.ResolverValue ObjectRef)
    (groups : List (Name × List Execution.ExecutableField))
    : (∀ childDepth,
        childDepth < depth
        -> ∀ parentType (childSource : Execution.ResolverValue ObjectRef) selectionSet,
            (∀ varName,
              varName ∈ selectionSetBooleanVariables selectionSet
              -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
            -> Execution.executeSelectionSet schema resolvers variableValues
                  childDepth parentType childSource
                  (filterSelectionSetBoolCase boolCase selectionSet)
                = Execution.executeSelectionSet schema resolvers variableValues
                    childDepth parentType childSource selectionSet)
      -> executableGroupsSelectionVarsInOperation operation groups
      -> Execution.executeCollectedFields schema resolvers variableValues depth
            source (filterExecutableGroupsBoolCase boolCase groups)
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source groups := by
  intro hrec hgroups
  induction groups with
  | nil =>
      simp [filterExecutableGroupsBoolCase, Execution.executeCollectedFields]
  | cons group rest ih =>
      cases group with
      | mk responseName fields =>
          have hrestVars :
              executableGroupsSelectionVarsInOperation operation rest := by
            intro candidate hcandidate
            exact hgroups candidate (by simp [hcandidate])
          have htail :
              Execution.executeCollectedFields schema resolvers variableValues depth
                  source (filterExecutableGroupsBoolCase boolCase rest)
                =
              Execution.executeCollectedFields schema resolvers variableValues depth
                  source rest :=
            ih hrestVars
          cases fields with
          | nil =>
              simpa [filterExecutableGroupsBoolCase,
                filterExecutableGroupBoolCase] using
                GroundTypeNormalization.executeCollectedFields_cons_eq_of_parts
                  schema resolvers variableValues depth source
                  (responseName, []) (responseName, [])
                  (filterExecutableGroupsBoolCase boolCase rest)
                  rest
                  (by simp [Execution.executeField])
                  htail
          | cons field fields =>
              have hfieldsVars :
                  executableFieldsSelectionVarsInOperation operation
                    (field :: fields) := by
                exact hgroups (responseName, field :: fields) (by simp)
              have hhead :
                  Execution.executeField schema resolvers variableValues depth
                      source responseName
                      (filterExecutableFieldBoolCase boolCase field
                        :: fields.map
                          (filterExecutableFieldBoolCase boolCase))
                    =
                  Execution.executeField schema resolvers variableValues depth
                      source responseName (field :: fields) := by
                apply executeField_cons_eq_cons_of_completeValue
                  schema resolvers variableValues depth source responseName
                  field (filterExecutableFieldBoolCase boolCase field)
                  fields (fields.map (filterExecutableFieldBoolCase boolCase))
                · exact filterExecutableFieldBoolCase_parentType boolCase field
                · exact filterExecutableFieldBoolCase_fieldName boolCase field
                · exact filterExecutableFieldBoolCase_arguments boolCase field
                · cases hlookup :
                      schema.lookupField field.parentType field.fieldName with
                  | none =>
                      simp []
                  | some fieldDefinition =>
                      cases hresolved :
                          resolvers.resolve field.parentType field.fieldName
                            field.arguments source with
                      | none =>
                          simp []
                      | some value =>
                          simp []
                          apply completeValue_eq_of_child_object_lt
                          intro childDepth runtimeType ref hlt
                          have hltDepth : childDepth < depth :=
                            Nat.lt_of_lt_of_le hlt (Nat.sub_le depth 1)
                          simpa [
                            Execution.mergedFieldSelectionSet,
                            filterExecutableFieldBoolCase,
                            filterSelectionSetBoolCase_append,
                            mergedFieldSelectionSet_map_filterExecutableFieldBoolCase]
                            using
                              hrec childDepth hltDepth runtimeType
                                (Execution.ResolverValue.object runtimeType ref)
                                (Execution.mergedFieldSelectionSet (field :: fields))
                                (executableFieldsSelectionVarsInOperation_merged
                                  operation (field :: fields) hfieldsVars)
              simpa [filterExecutableGroupsBoolCase,
                filterExecutableGroupBoolCase,
                Execution.executeCollectedFields] using
                GroundTypeNormalization.executeCollectedFields_cons_eq_of_parts
                  schema resolvers variableValues depth source
                  (responseName,
                    filterExecutableFieldBoolCase boolCase field
                      :: fields.map
                        (filterExecutableFieldBoolCase boolCase))
                  (responseName, field :: fields)
                  (filterExecutableGroupsBoolCase boolCase rest)
                  rest hhead htail

theorem executeSelectionSet_filterSelectionSetBoolCase
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (boolCase : BoolCase)
    (hagrees
      : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation))
    : ∀ depth parentType (source : Execution.ResolverValue ObjectRef) selectionSet,
        (∀ varName,
          varName ∈ selectionSetBooleanVariables selectionSet
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
        -> Execution.executeSelectionSet schema resolvers variableValues depth
              parentType source
              (filterSelectionSetBoolCase boolCase selectionSet)
            = Execution.executeSelectionSet schema resolvers variableValues depth
                parentType source selectionSet := by
  intro depth
  induction depth using Nat.strongRecOn with
  | ind depth ih =>
      intro parentType source selectionSet hvars
      have hcollect :=
        collectFields_filterSelectionSetBoolCase schema variableValues
          operation boolCase hagrees parentType source selectionSet hvars
      have hgroups :
          executableGroupsSelectionVarsInOperation operation
            (Execution.collectFields schema variableValues parentType source
              selectionSet) :=
        collectFields_executableGroupsSelectionVarsInOperation schema
          variableValues operation parentType source selectionSet hvars
      have hcollected :
          Execution.executeCollectedFields schema resolvers variableValues
              depth source
              (filterExecutableGroupsBoolCase boolCase
                (Execution.collectFields schema variableValues parentType
                  source selectionSet))
            =
          Execution.executeCollectedFields schema resolvers variableValues
              depth source
              (Execution.collectFields schema variableValues parentType
                source selectionSet) :=
        executeCollectedFields_filterExecutableGroupsBoolCase_of_rec
          schema resolvers variableValues operation boolCase depth source
          (Execution.collectFields schema variableValues parentType source
            selectionSet)
          (by
            intro childDepth hlt childParent childSource childSelectionSet
              hchildVars
            exact ih childDepth hlt childParent childSource
              childSelectionSet hchildVars)
          hgroups
      simp [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
        hcollect]
      exact hcollected

end CompleteNormalization

end NormalForm

end GraphQL
