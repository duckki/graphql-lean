import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection

/-!
Collected-group argument, resolver, and execution-state invariants.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

def CollectedGroupsArgumentsNodup (groups : List (Name × List ExecutableField)) : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups -> ExecutableFieldsArgumentsNodup fields

theorem ExecutableFieldsArgumentsNodup_singleton (field : ExecutableField)
    : (field.arguments.map Argument.name).Nodup
      -> ExecutableFieldsArgumentsNodup [field] := by
  intro hnodup candidate hmem
  have hcandidate : candidate = field := by
    simpa using hmem
  subst candidate
  exact hnodup

theorem ExecutableFieldsArgumentsNodup_append (left right : List ExecutableField)
    : ExecutableFieldsArgumentsNodup left
      -> ExecutableFieldsArgumentsNodup right
      -> ExecutableFieldsArgumentsNodup (left ++ right) := by
  intro hleft hright field hmem
  rcases List.mem_append.mp hmem with hfield | hfield
  · exact hleft field hfield
  · exact hright field hfield

theorem CollectedGroupsArgumentsNodup_nil : CollectedGroupsArgumentsNodup [] := by
  intro _responseName _fields hmem
  simp at hmem

theorem CollectedGroupsArgumentsNodup_singleton
    (responseName : Name) (fields : List ExecutableField)
    : ExecutableFieldsArgumentsNodup fields
      -> CollectedGroupsArgumentsNodup [(responseName, fields)] := by
  intro hfields groupResponseName groupFields hmem
  have hpair :
      (groupResponseName, groupFields) = (responseName, fields) := by
    simpa using hmem
  cases hpair
  exact hfields

theorem CollectedGroupsArgumentsNodup_tail
    {group : Name × List ExecutableField}
    {groups : List (Name × List ExecutableField)}
    : CollectedGroupsArgumentsNodup (group :: groups)
      -> CollectedGroupsArgumentsNodup groups := by
  intro hgroups responseName fields hmem
  exact hgroups responseName fields (by simp [hmem])

theorem CollectedGroupsArgumentsNodup_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : ExecutableFieldsArgumentsNodup group.snd
      -> CollectedGroupsArgumentsNodup groups
      -> CollectedGroupsArgumentsNodup
          (GraphQL.Execution.addExecutableGroup group groups) := by
  rcases group with ⟨groupName, groupFields⟩
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro responseName fields hmem
      simp [GraphQL.Execution.addExecutableGroup] at hmem
      rcases hmem with ⟨_hresponseName, hfields⟩
      cases hfields
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hname] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact ExecutableFieldsArgumentsNodup_append currentFields
            groupFields
            (hgroups currentName currentFields (by simp))
            hgroup
        · exact hgroups responseName fields (by simp [htail])
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        intro responseName fields hmem
        simp [GraphQL.Execution.addExecutableGroup, hfalse] at hmem
        rcases hmem with hhead | htail
        · rcases hhead with ⟨_hresponseName, hfields⟩
          cases hfields
          exact hgroups currentName currentFields (by simp)
        · exact ih (CollectedGroupsArgumentsNodup_tail hgroups)
            responseName fields htail

theorem CollectedGroupsArgumentsNodup_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    : CollectedGroupsArgumentsNodup left
      -> CollectedGroupsArgumentsNodup right
      -> CollectedGroupsArgumentsNodup
          (GraphQL.Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [GraphQL.Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [GraphQL.Execution.mergeExecutableGroups]
      exact ih (GraphQL.Execution.addExecutableGroup (responseName, fields) left)
        (CollectedGroupsArgumentsNodup_addExecutableGroup
          (responseName, fields) left (hright responseName fields (by simp))
          hleft)
        (CollectedGroupsArgumentsNodup_tail hright)

theorem argumentsValid_argumentsNodup
    {schema : Schema} {definitions : List InputValueDefinition}
    {variableDefinitions : List VariableDefinition}
    {arguments : List Argument}
    : Validation.argumentsValid schema definitions variableDefinitions arguments
      -> (arguments.map Argument.name).Nodup := by
  intro hvalid
  exact hvalid.1

theorem ValidOperationPrefixSelectionState.field_argumentsNodup
    {schema : Schema} {operation : Operation}
    {prefixSelections suffix : List Selection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication} {selectionSet : List Selection}
    : ValidOperationPrefixSelectionState schema operation prefixSelections
        (.field responseName fieldName arguments directives selectionSet)
        suffix
      -> (arguments.map Argument.name).Nodup := by
  intro hstate
  rcases ValidOperationPrefixSelectionState.field_lookup hstate with
    ⟨_fieldDefinition, _hlookup, harguments, _hselectionSet⟩
  exact argumentsValid_argumentsNodup harguments

mutual
  theorem collectSelection_argumentsNodup_of_selectionValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : ResolverValue ObjectIdentity)
      (selection : Selection)
      : Validation.selectionValid schema variableDefinitions validParent selection
        -> CollectedGroupsArgumentsNodup
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent source selection) := by
    intro hvalid
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨_fieldDefinition, _hlookup, harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsArgumentsNodup_singleton responseName
            [{
              parentType := collectParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsArgumentsNodup_singleton
              {
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              (argumentsValid_argumentsNodup harguments))
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsArgumentsNodup_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  validParent selectionSet :=
              Validation.selectionValid_inlineFragment_none_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact collectFields_argumentsNodup_of_selectionSetValid schema
                variableDefinitions variableValues collectParent validParent
                source selectionSet hselectionSet
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]
        | some typeCondition =>
            have hselectionSet :
                Validation.selectionSetValid schema variableDefinitions
                  typeCondition selectionSet :=
              Validation.selectionValid_inlineFragment_some_selectionSetValid
                hvalid
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent source
                    typeCondition = true
              · simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact collectFields_argumentsNodup_of_selectionSetValid schema
                  variableDefinitions variableValues collectParent typeCondition
                  source selectionSet hselectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent source
                      typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent source
                        typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsArgumentsNodup_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]

  theorem collectFields_argumentsNodup_of_selectionSetValid
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent : Name)
      (source : ResolverValue ObjectIdentity)
      (selectionSet : List Selection)
      : Validation.selectionSetValid schema variableDefinitions validParent selectionSet
        -> CollectedGroupsArgumentsNodup
            (GraphQL.Execution.collectFields schema variableValues collectParent
              source selectionSet) := by
    intro hvalid
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsArgumentsNodup_nil]
    | cons selection rest =>
        have htail :
            Validation.selectionSetValid schema variableDefinitions validParent
              rest :=
          Validation.selectionSetValid_tail hvalid
        have hhead :
            Validation.selectionValid schema variableDefinitions validParent
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsArgumentsNodup_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent source selection)
          (GraphQL.Execution.collectFields schema variableValues collectParent
            source rest)
          (collectSelection_argumentsNodup_of_selectionValid schema
            variableDefinitions variableValues collectParent validParent source
            selection hhead)
          (collectFields_argumentsNodup_of_selectionSetValid schema
            variableDefinitions variableValues collectParent validParent source
            rest htail)
end

mutual
  theorem collectSelection_argumentsNodup_of_selectionValidInPossibleTypes_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : SchemaWellFormedness.schemaWellFormed schema
        -> ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionValidInPossibleTypes schema variableDefinitions
            validParent selection
        -> CollectedGroupsArgumentsNodup
            (GraphQL.Execution.collectSelection schema variableValues
              collectParent (.object runtimeType identity) selection) := by
    intro hschema hparentRuntime hvalid
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hselectionValid :
            Validation.selectionValid schema variableDefinitions validParent
              (Selection.field responseName fieldName arguments directives
                selectionSet) := by
          simpa [Validation.selectionValidInPossibleTypes] using hvalid.1
        rcases Validation.selectionValid_field_lookup hselectionValid with
          ⟨_fieldDefinition, _hlookup, harguments, _hselectionSet⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, hallows]
          exact CollectedGroupsArgumentsNodup_singleton responseName
            [{
              parentType := collectParent,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
            (ExecutableFieldsArgumentsNodup_singleton
              {
                parentType := collectParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              (argumentsValid_argumentsNodup harguments))
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            CollectedGroupsArgumentsNodup_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hbody :
                Validation.selectionSetValidInPossibleTypes schema
                  variableDefinitions runtimeType selectionSet := by
              have hchildren :
                  ∀ objectType,
                    objectType ∈ schema.getPossibleTypes validParent ->
                      Validation.selectionSetValidInPossibleTypes schema
                        variableDefinitions objectType selectionSet := by
                simpa [Validation.selectionValidInPossibleTypes] using hvalid
              exact hchildren runtimeType (List.contains_iff_mem.mp hparentRuntime)
            have hruntimeSelf :
                ScopedParentRuntimeApplies schema runtimeType runtimeType :=
              ScopedParentRuntimeApplies.of_typeIncludesObjectBool schema
                runtimeType runtimeType
                (ScopedParentRuntimeApplies.runtimeSelf schema hschema
                  hparentRuntime)
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows]
              exact
                collectFields_argumentsNodup_of_selectionSetValidInPossibleTypes_object
                  schema variableDefinitions variableValues collectParent
                  runtimeType runtimeType identity selectionSet hschema
                  hruntimeSelf hbody
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have hcondition :
                    schema.typeIncludesObjectBool typeCondition runtimeType =
                      true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using
                    happly
                have hoverlap :
                    schema.typesOverlapBool validParent typeCondition =
                      true := by
                  unfold Schema.typesOverlapBool
                  exact List.any_eq_true.mpr
                    ⟨runtimeType, List.contains_iff_mem.mp hparentRuntime,
                      hcondition⟩
                have hbody :
                    Validation.selectionSetValidInPossibleTypes schema
                      variableDefinitions runtimeType selectionSet := by
                  have hchildren :
                      ∀ objectType,
                        objectType ∈ schema.getPossibleTypes typeCondition ->
                          Validation.selectionSetValidInPossibleTypes schema
                            variableDefinitions objectType selectionSet := by
                    simpa [Validation.selectionValidInPossibleTypes] using
                      hvalid hoverlap
                  exact hchildren runtimeType
                    (List.contains_iff_mem.mp hcondition)
                have hruntimeSelf :
                    ScopedParentRuntimeApplies schema runtimeType runtimeType :=
                  ScopedParentRuntimeApplies.of_typeIncludesObjectBool schema
                    runtimeType runtimeType
                    (ScopedParentRuntimeApplies.runtimeSelf schema hschema
                      hparentRuntime)
                simp [GraphQL.Execution.collectSelection, hallows, happly]
                exact
                  collectFields_argumentsNodup_of_selectionSetValidInPossibleTypes_object
                    schema variableDefinitions variableValues collectParent
                    runtimeType runtimeType identity selectionSet hschema
                    hruntimeSelf
                    hbody
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  CollectedGroupsArgumentsNodup_nil]
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                CollectedGroupsArgumentsNodup_nil]

  theorem collectFields_argumentsNodup_of_selectionSetValidInPossibleTypes_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : SchemaWellFormedness.schemaWellFormed schema
        -> ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions validParent selectionSet
        -> CollectedGroupsArgumentsNodup
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet) := by
    intro hschema hparentRuntime himplementation
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, CollectedGroupsArgumentsNodup_nil]
    | cons selection rest =>
        have hhead :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              validParent selection := by
          simpa [Validation.selectionSetValidInPossibleTypes] using
            himplementation.1
        have htail :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions validParent rest := by
          simpa [Validation.selectionSetValidInPossibleTypes] using
            himplementation.2
        simp [GraphQL.Execution.collectFields]
        exact CollectedGroupsArgumentsNodup_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues
            collectParent (.object runtimeType identity) selection)
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) rest)
          (collectSelection_argumentsNodup_of_selectionValidInPossibleTypes_object
            schema variableDefinitions variableValues collectParent validParent
            runtimeType identity selection hschema hparentRuntime hhead)
          (collectFields_argumentsNodup_of_selectionSetValidInPossibleTypes_object
            schema variableDefinitions variableValues collectParent validParent
            runtimeType identity rest hschema hparentRuntime htail)
end

def CollectedGroupsResolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName fields,
    (responseName, fields) ∈ groups
    -> ExecutableFieldsResolveStable resolvers source fields

theorem CollectedGroupsResolveStable.group
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField)
    : CollectedGroupsResolveStable resolvers source groups
      -> (responseName, fields) ∈ groups
      -> ExecutableFieldsResolveStable resolvers source fields := by
  intro hstable hmem
  exact hstable responseName fields hmem

theorem CollectedGroupsResolveStable.tail
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity)
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : CollectedGroupsResolveStable resolvers source (group :: groups)
      -> CollectedGroupsResolveStable resolvers source groups := by
  intro hstable responseName fields hmem
  exact hstable responseName fields (by simp [hmem])

structure ExecutionStateInvariant (state : ExecutionEquivalenceState ObjectIdentity)
    : Prop where
  groupedResponseKeysUnique
    : PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsCompatible
    : ∀ responseName fields,
        (responseName, fields)
          ∈ GraphQL.Execution.collectFields state.window.schema
              state.window.variableValues state.window.parentType state.window.source
              state.window.selectionSet
        -> ExecutableFieldsMergeCompatible fields
  groupedFieldsResolveStable
    : ∀ responseName fields,
        (responseName, fields)
          ∈ GraphQL.Execution.collectFields state.window.schema
              state.window.variableValues state.window.parentType state.window.source
              state.window.selectionSet
        -> ExecutableFieldsResolveStable state.window.resolvers state.window.source fields

structure ExecutionSemanticStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity)
    : Prop where
  groupedResponseKeysUnique
    : PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsSameParent
    : CollectedGroupsSameResponseParent
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsValidationCompatible
    : CollectedGroupsValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  resolversRespectArgumentEquivalence
    : ResolversRespectArgumentEquivalence state.window.resolvers state.window.source

structure ExecutionFieldSemanticStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity)
    : Prop where
  groupedResponseKeysUnique
    : PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsFieldCompatible
    : CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  resolversRespectFieldAndArgumentEquivalence
    : ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
        state.window.source

structure ExecutionValidFieldSemanticStateInvariant
    (state : ExecutionEquivalenceState ObjectIdentity)
    : Prop where
  groupedResponseKeysUnique
    : PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsFieldCompatible
    : CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsArgumentsNodup
    : CollectedGroupsArgumentsNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  resolversRespectValidFieldAndArgumentEquivalence
    : ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
        state.window.source

structure ExecutionCollectedFieldInvariant
    (state : ExecutionEquivalenceState ObjectIdentity)
    : Prop where
  groupedResponseKeysUnique
    : PairKeysNodup
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)
  groupedFieldsResolveStable
    : CollectedGroupsResolveStable state.window.resolvers state.window.source
        (GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet)

def CollectedGroupsFieldLookupValid
    (schema : Schema) (parentType : Name)
    (groups : List (Name × List ExecutableField))
    : Prop :=
  ∀ responseName field fields,
    (responseName, field :: fields) ∈ groups
    -> ∃ fieldDefinition,
        schema.lookupField parentType field.fieldName = some fieldDefinition

mutual
  theorem inputValue_structuralEquivalent_refl
      : ∀ value : InputValue, InputValue.structuralEquivalent value value
    | .null => by simp [InputValue.structuralEquivalent]
    | .int value => by simp [InputValue.structuralEquivalent]
    | .float value => by simp [InputValue.structuralEquivalent]
    | .string value => by simp [InputValue.structuralEquivalent]
    | .boolean value => by simp [InputValue.structuralEquivalent]
    | .enum value => by simp [InputValue.structuralEquivalent]
    | .variable name => by simp [InputValue.structuralEquivalent]
    | .list values => by
        simp [InputValue.structuralEquivalent,
          inputValue_structuralValuesEquivalent_refl values]
    | .object fields => by
        simp [InputValue.structuralEquivalent,
          inputValue_structuralObjectFieldsEquivalent_refl fields]

  theorem inputValue_structuralValuesEquivalent_refl
      : ∀ values : List InputValue, InputValue.structuralValuesEquivalent values values
    | [] => by simp [InputValue.structuralValuesEquivalent]
    | value :: rest => by
        simp [InputValue.structuralValuesEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValue_structuralValuesEquivalent_refl rest]

  theorem inputValue_structuralObjectFieldsEquivalent_refl
      : ∀ fields : List (Name × InputValue),
          InputValue.structuralObjectFieldsEquivalent fields fields
    | [] => by simp [InputValue.structuralObjectFieldsEquivalent]
    | (name, value) :: rest => by
        simp [InputValue.structuralObjectFieldsEquivalent,
          inputValue_structuralEquivalent_refl value,
          inputValue_structuralObjectFieldsEquivalent_refl rest]
end

theorem inputValue_equivalent_refl (value : InputValue) : value.equivalent value := by
  exact inputValue_structuralEquivalent_refl value.canonical

theorem fieldsForNameCanMerge_executable_identity
    (schema : Schema) (first later : ExecutableField)
    (firstOutputType laterOutputType : TypeRef)
    : FieldMerge.fieldsForNameCanMerge schema
        {
          parentType := first.parentType
          responseName := first.responseName
          fieldName := first.fieldName
          arguments := first.arguments
          outputType := firstOutputType
          selectionSet := first.selectionSet
        }
        {
          parentType := later.parentType
          responseName := later.responseName
          fieldName := later.fieldName
          arguments := later.arguments
          outputType := laterOutputType
          selectionSet := later.selectionSet
        }
      -> first.parentType = later.parentType
      -> first.fieldName = later.fieldName
          ∧ Argument.argumentsEquivalent first.arguments later.arguments := by
  intro hmerge hparent
  exact FieldMerge.fieldsForNameCanMerge_same_parent_identity hmerge hparent

theorem fieldsInSetCanMerge_scoped_collectFields_compatible
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ScopedFieldsValidationMergeCompatible
          (FieldMerge.collectFields schema parentType selectionSet) := by
  intro hmerge first later hfirst hlater hresponse hparent
  exact FieldMerge.fieldsForNameCanMerge_same_parent_identity
    (FieldMerge.fieldsInSetCanMerge_pair hmerge hfirst hlater hresponse)
    hparent

theorem ScopedFieldsValidationMergeCompatible.fieldCompatible
    (fields : List FieldMerge.ScopedField)
    : ScopedFieldsSameResponseParent fields
      -> ScopedFieldsValidationMergeCompatible fields
      -> ScopedFieldsFieldValidationMergeCompatible fields := by
  intro hsameParent hcompatible first later hfirst hlater hresponse
  exact hcompatible first later hfirst hlater hresponse
    (hsameParent first later hfirst hlater hresponse)

theorem fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
    (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ScopedFieldsSameResponseParent
          (FieldMerge.collectFields schema parentType selectionSet)
      -> ScopedFieldsFieldValidationMergeCompatible
          (FieldMerge.collectFields schema parentType selectionSet) := by
  intro hmerge hsameParent
  exact ScopedFieldsValidationMergeCompatible.fieldCompatible
    (FieldMerge.collectFields schema parentType selectionSet)
    hsameParent
      (fieldsInSetCanMerge_scoped_collectFields_compatible schema parentType
        selectionSet hmerge)

theorem fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_runtimeApplies
    (schema : Schema) (parentType runtimeType : Name) (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> (∀ scopedField,
            scopedField ∈ FieldMerge.collectFields schema parentType selectionSet
            -> ScopedFieldRuntimeApplies schema runtimeType scopedField)
      -> ScopedFieldsFieldValidationMergeCompatible
          (FieldMerge.collectFields schema parentType selectionSet) := by
  intro hmerge happlies first later hfirst hlater hresponse
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema first later :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hfirst hlater hresponse
  exact FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
    (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      first later (happlies first hfirst) (happlies later hlater))

theorem ScopedFieldsValidationMergeCompatible.executable_sameParent
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : ScopedFieldsValidationMergeCompatible scopedFields
      -> ExecutableFieldsScopedBy scopedFields fields
      -> ExecutableFieldsSameParentValidationMergeCompatible fields := by
  intro hcompatible hscoped first later hfirst hlater hresponse hparent
  rcases hscoped first hfirst with ⟨firstScoped, hfirstScopedMem,
    hfirstScopedMatch⟩
  rcases hscoped later hlater with ⟨laterScoped, hlaterScopedMem,
    hlaterScopedMatch⟩
  rcases hfirstScopedMatch with
    ⟨hfirstParent, hfirstResponse, hfirstField, hfirstArguments,
      _hfirstSelection⟩
  rcases hlaterScopedMatch with
    ⟨hlaterParent, hlaterResponse, hlaterField, hlaterArguments,
      _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  have hscopedParent :
      firstScoped.parentType = laterScoped.parentType := by
    rw [hfirstParent, hlaterParent]
    exact hparent
  rcases hcompatible firstScoped laterScoped hfirstScopedMem hlaterScopedMem
      hscopedResponse hscopedParent with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem ScopedFieldsFieldValidationMergeCompatible.executable
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : ScopedFieldsFieldValidationMergeCompatible scopedFields
      -> ExecutableFieldsScopedBy scopedFields fields
      -> ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hcompatible hscoped first later hfirst hlater hresponse
  rcases hscoped first hfirst with ⟨firstScoped, hfirstScopedMem,
    hfirstScopedMatch⟩
  rcases hscoped later hlater with ⟨laterScoped, hlaterScopedMem,
    hlaterScopedMatch⟩
  rcases hfirstScopedMatch with
    ⟨_hfirstParent, hfirstResponse, hfirstField, hfirstArguments,
      _hfirstSelection⟩
  rcases hlaterScopedMatch with
    ⟨_hlaterParent, hlaterResponse, hlaterField, hlaterArguments,
      _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  rcases hcompatible firstScoped laterScoped hfirstScopedMem hlaterScopedMem
      hscopedResponse with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem ScopedFieldsFieldValidationMergeCompatible.executable_identity
    (scopedFields : List FieldMerge.ScopedField)
    (fields : List ExecutableField)
    : ScopedFieldsFieldValidationMergeCompatible scopedFields
      -> ExecutableFieldsIdentityScopedBy scopedFields fields
      -> ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hcompatible hscoped first later hfirst hlater hresponse
  rcases hscoped first hfirst with ⟨firstScoped, hfirstScopedMem,
    hfirstScopedMatch⟩
  rcases hscoped later hlater with ⟨laterScoped, hlaterScopedMem,
    hlaterScopedMatch⟩
  rcases hfirstScopedMatch with
    ⟨hfirstResponse, hfirstField, hfirstArguments, _hfirstSelection⟩
  rcases hlaterScopedMatch with
    ⟨hlaterResponse, hlaterField, hlaterArguments, _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  rcases hcompatible firstScoped laterScoped hfirstScopedMem hlaterScopedMem
      hscopedResponse with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem fieldsInSetCanMerge_executable_runtimeScoped
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (fields : List ExecutableField)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema parentType selectionSet) fields
      -> ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hmerge hscoped first later hfirst hlater hresponse
  rcases hscoped first hfirst with
    ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
  rcases hscoped later hlater with
    ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstResponse, hfirstField, hfirstArguments, _hfirstSelection⟩
  rcases hlaterMatch with
    ⟨hlaterResponse, hlaterField, hlaterArguments, _hlaterSelection⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema firstScoped laterScoped :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse
  rcases
      FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
        (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
          firstScoped laterScoped hfirstRuntime hlaterRuntime) with
    ⟨hfield, hargumentsEquivalent⟩
  constructor
  · rw [← hfirstField, ← hlaterField]
    exact hfield
  · rw [← hfirstArguments, ← hlaterArguments]
    exact hargumentsEquivalent

theorem fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (responseName : Name)
    (fields : List ExecutableField)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> (∀ field, field ∈ fields -> field.responseName = responseName)
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema parentType selectionSet) fields
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hmerge hresponses hscoped objectType
  apply FieldMerge.fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise
  intro first hfirst later hlater
  rcases hscoped first hfirst with
    ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
  rcases hscoped later hlater with
    ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstResponse, _hfirstField, _hfirstArguments, hfirstSelectionSet⟩
  rcases hlaterMatch with
    ⟨hlaterResponse, _hlaterField, _hlaterArguments, hlaterSelectionSet⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse, hresponses first hfirst,
      hresponses later hlater]
  have hparents :
      firstScoped.parentType = laterScoped.parentType
        ∨ ¬schema.objectType firstScoped.parentType
        ∨ ¬schema.objectType laterScoped.parentType :=
    ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      firstScoped laterScoped hfirstRuntime hlaterRuntime
  simpa [hfirstSelectionSet, hlaterSelectionSet] using
    FieldMerge.fieldsInSetCanMerge_pair_subfields schema parentType
      selectionSet firstScoped laterScoped hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse hparents objectType

theorem collectFields_group_mergedFieldSelectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField)
    : Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet
          = groups
      -> (responseName, fields) ∈ groups
      -> CollectedGroupsResponseName groups
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hvalid hmerge hparentRuntime hcollect hgroup hresponses
  apply fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped
    schema validParent runtimeType selectionSet responseName fields hmerge
  · intro field hfield
    exact hresponses responseName fields hgroup field hfield
  · have hscopedAll :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields groups) := by
      rw [← hcollect]
      exact collectFields_runtimeScopedBy_of_selectionSetValid schema
        variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet hparentRuntime hvalid
    intro field hfield
    exact hscopedAll field
      (collectedExecutableFields_mem_of_group_mem hgroup hfield)

theorem collectFields_group_mergedFieldSelectionSet_canMerge_of_valid_root_operation
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (operation : Operation)
    (runtimeType : Name) (identity : ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField)
    : rootSourceAppliesBool schema operation (.object runtimeType identity) = true
      -> Validation.operationDefinitionValid schema operation
      -> GraphQL.Execution.collectFields schema variableValues (operation.rootType schema)
            (.object runtimeType identity) operation.selectionSet
          = groups
      -> (responseName, fields) ∈ groups
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hroot hvalid hcollect hgroup
  apply collectFields_group_mergedFieldSelectionSet_canMerge_runtimeScoped
    schema operation.variableDefinitions variableValues (operation.rootType schema)
    (operation.rootType schema) runtimeType identity operation.selectionSet groups
    responseName fields
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  · exact ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      runtimeType identity hroot
  · exact hcollect
  · exact hgroup
  · rw [← hcollect]
    exact collectFields_responseName schema variableValues (operation.rootType schema)
      (.object runtimeType identity) operation.selectionSet

theorem collectFields_fieldCompatible_of_selectionSetValid_scopedCompatible
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent : Name)
    (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> ScopedFieldsFieldValidationMergeCompatible
          (FieldMerge.collectFields schema validParent selectionSet)
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues collectParent
            source selectionSet) := by
  intro hvalid hscopedCompatible
  apply CollectedGroupsFieldValidationMergeCompatible.of_collectedExecutableFields
  exact ScopedFieldsFieldValidationMergeCompatible.executable_identity
    (FieldMerge.collectFields schema validParent selectionSet)
    (collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues collectParent source
        selectionSet))
    hscopedCompatible
    (collectFields_identityScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent source
      selectionSet hvalid)

theorem collectFields_fieldCompatible_of_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (source : ResolverValue ObjectIdentity)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              source selectionSet))
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues collectParent
            source selectionSet) := by
  intro hmerge hscoped
  apply CollectedGroupsFieldValidationMergeCompatible.of_collectedExecutableFields
  exact fieldsInSetCanMerge_executable_runtimeScoped schema validParent
    runtimeType selectionSet
    (collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues collectParent
        source selectionSet))
    hmerge hscoped

theorem collectFields_fieldCompatible_of_canMerge_lookupValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
  intro hmerge hparentRuntime hlookupValid
  apply collectFields_fieldCompatible_of_canMerge_runtimeScoped
    schema variableValues collectParent validParent runtimeType
    (.object runtimeType identity) selectionSet hmerge
  exact collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
    variableValues collectParent validParent runtimeType identity selectionSet
    hparentRuntime hlookupValid

theorem collectFields_fieldCompatible_of_canMerge_lookupValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
  intro hmerge hparentRuntime hlookupValid
  apply collectFields_fieldCompatible_of_canMerge_runtimeScoped
    schema variableValues collectParent validParent runtimeType
    (.object runtimeType identity) selectionSet hmerge
  exact collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
    variableValues collectParent validParent runtimeType identity selectionSet
    hparentRuntime hlookupValid

theorem ExecutableFieldsMergeCompatible.to_validation (fields : List ExecutableField)
    : ExecutableFieldsMergeCompatible fields
      -> ExecutableFieldsValidationMergeCompatible fields := by
  intro hcompatible first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hparent, hfield, harguments⟩
  constructor
  · exact hparent
  constructor
  · exact hfield
  · rw [harguments]
    constructor
    · intro argument hmem
      exact ⟨argument, hmem, by exact ⟨rfl, inputValue_equivalent_refl argument.value⟩⟩
    · intro argument hmem
      exact ⟨argument, hmem, by exact ⟨rfl, inputValue_equivalent_refl argument.value⟩⟩

theorem ExecutableFieldsSameParentValidationMergeCompatible.fieldCompatible
    (fields : List ExecutableField)
    : ExecutableFieldsSameResponseParent fields
      -> ExecutableFieldsSameParentValidationMergeCompatible fields
      -> ExecutableFieldsFieldValidationMergeCompatible fields := by
  intro hsameParent hcompatible first later hfirst hlater hresponse
  exact hcompatible first later hfirst hlater hresponse
    (hsameParent first later hfirst hlater hresponse)

theorem CollectedGroupsValidationMergeCompatible.fieldCompatible
    (groups : List (Name × List ExecutableField))
    : CollectedGroupsSameResponseParent groups
      -> CollectedGroupsValidationMergeCompatible groups
      -> CollectedGroupsFieldValidationMergeCompatible groups := by
  intro hsameParent hcompatible responseName fields hmem
  exact ExecutableFieldsSameParentValidationMergeCompatible.fieldCompatible
    fields
    (hsameParent responseName fields hmem)
    (hcompatible responseName fields hmem)

theorem ExecutableFieldsMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    : ExecutableFieldsMergeCompatible fields
      -> ExecutableFieldsResolveStable resolvers source fields := by
  intro hcompatible first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hparent, hfield, harguments⟩
  simp [hparent, hfield, harguments]

theorem ExecutableFieldsSameParentValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    : ResolversRespectArgumentEquivalence resolvers source
      -> ExecutableFieldsSameResponseParent fields
      -> ExecutableFieldsSameParentValidationMergeCompatible fields
      -> ExecutableFieldsResolveStable resolvers source fields := by
  intro hresolvers hsameParent hcompatible first later hfirst hlater hresponse
  have hparent := hsameParent first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse hparent with
    ⟨hfield, harguments⟩
  rw [hparent, hfield]
  exact hresolvers later.parentType later.fieldName first.arguments
    later.arguments harguments

theorem ExecutableFieldsFieldValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    : ResolversRespectFieldAndArgumentEquivalence resolvers source
      -> ExecutableFieldsFieldValidationMergeCompatible fields
      -> ExecutableFieldsResolveStable resolvers source fields := by
  intro hresolvers hcompatible first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hfield, harguments⟩
  rw [hfield]
  exact hresolvers first.parentType later.parentType later.fieldName
    first.arguments later.arguments harguments

theorem ExecutableFieldsFieldValidationMergeCompatible.resolveStableValid
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity) (fields : List ExecutableField)
    : ResolversRespectValidFieldAndArgumentEquivalence resolvers source
      -> ExecutableFieldsFieldValidationMergeCompatible fields
      -> ExecutableFieldsArgumentsNodup fields
      -> ExecutableFieldsResolveStable resolvers source fields := by
  intro hresolvers hcompatible hnodup first later hfirst hlater hresponse
  rcases hcompatible first later hfirst hlater hresponse with
    ⟨hfield, harguments⟩
  rw [hfield]
  exact hresolvers first.parentType later.parentType later.fieldName
    first.arguments later.arguments (hnodup first hfirst)
    (hnodup later hlater) harguments

theorem CollectedGroupsValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : ResolversRespectArgumentEquivalence resolvers source
      -> CollectedGroupsSameResponseParent groups
      -> CollectedGroupsValidationMergeCompatible groups
      -> CollectedGroupsResolveStable resolvers source groups := by
  intro hresolvers hsameParent hcompatible responseName fields hmem
  exact
    ExecutableFieldsSameParentValidationMergeCompatible.resolveStable
      resolvers source fields hresolvers
      (hsameParent responseName fields hmem)
      (hcompatible responseName fields hmem)

theorem CollectedGroupsFieldValidationMergeCompatible.resolveStable
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : ResolversRespectFieldAndArgumentEquivalence resolvers source
      -> CollectedGroupsFieldValidationMergeCompatible groups
      -> CollectedGroupsResolveStable resolvers source groups := by
  intro hresolvers hcompatible responseName fields hmem
  exact
    ExecutableFieldsFieldValidationMergeCompatible.resolveStable resolvers
      source fields hresolvers (hcompatible responseName fields hmem)

theorem CollectedGroupsFieldValidationMergeCompatible.resolveStableValid
    {ObjectIdentity : Type} (resolvers : Resolvers ObjectIdentity)
    (source : ResolverValue ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    : ResolversRespectValidFieldAndArgumentEquivalence resolvers source
      -> CollectedGroupsFieldValidationMergeCompatible groups
      -> CollectedGroupsArgumentsNodup groups
      -> CollectedGroupsResolveStable resolvers source groups := by
  intro hresolvers hcompatible hnodup responseName fields hmem
  exact
    ExecutableFieldsFieldValidationMergeCompatible.resolveStableValid resolvers
      source fields hresolvers (hcompatible responseName fields hmem)
      (hnodup responseName fields hmem)

theorem ExecutionSemanticStateInvariant.groupedFieldsResolveStable
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionSemanticStateInvariant state
      -> ∀ responseName fields,
          (responseName, fields)
            ∈ GraphQL.Execution.collectFields state.window.schema
                state.window.variableValues state.window.parentType
                state.window.source state.window.selectionSet
          -> ExecutableFieldsResolveStable state.window.resolvers
              state.window.source fields := by
  intro hinvariant responseName fields hmem
  exact
    CollectedGroupsValidationMergeCompatible.resolveStable
      state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.resolversRespectArgumentEquivalence
      hinvariant.groupedFieldsSameParent
      hinvariant.groupedFieldsValidationCompatible
      responseName fields hmem

theorem ExecutionFieldSemanticStateInvariant.groupedFieldsResolveStable
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionFieldSemanticStateInvariant state
      -> ∀ responseName fields,
          (responseName, fields)
            ∈ GraphQL.Execution.collectFields state.window.schema
                state.window.variableValues state.window.parentType
                state.window.source state.window.selectionSet
          -> ExecutableFieldsResolveStable state.window.resolvers
              state.window.source fields := by
  intro hinvariant responseName fields hmem
  exact
    CollectedGroupsFieldValidationMergeCompatible.resolveStable
      state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.resolversRespectFieldAndArgumentEquivalence
      hinvariant.groupedFieldsFieldCompatible
      responseName fields hmem

theorem ExecutionValidFieldSemanticStateInvariant.groupedFieldsResolveStable
    {ObjectIdentity : Type} (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionValidFieldSemanticStateInvariant state
      -> ∀ responseName fields,
          (responseName, fields)
            ∈ GraphQL.Execution.collectFields state.window.schema
                state.window.variableValues state.window.parentType
                state.window.source state.window.selectionSet
          -> ExecutableFieldsResolveStable state.window.resolvers
              state.window.source fields := by
  intro hinvariant responseName fields hmem
  exact
    CollectedGroupsFieldValidationMergeCompatible.resolveStableValid
      state.window.resolvers state.window.source
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.resolversRespectValidFieldAndArgumentEquivalence
      hinvariant.groupedFieldsFieldCompatible
      hinvariant.groupedFieldsArgumentsNodup
      responseName fields hmem

theorem ExecutionCollectedFieldInvariant.of_stateInvariant
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionStateInvariant state -> ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact hinvariant.groupedFieldsResolveStable

theorem ExecutionCollectedFieldInvariant.of_semantic
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionSemanticStateInvariant state
      -> ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact ExecutionSemanticStateInvariant.groupedFieldsResolveStable state
      hinvariant

theorem ExecutionCollectedFieldInvariant.of_fieldSemantic
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionFieldSemanticStateInvariant state
      -> ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact ExecutionFieldSemanticStateInvariant.groupedFieldsResolveStable state
      hinvariant

theorem ExecutionCollectedFieldInvariant.of_validFieldSemantic
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionValidFieldSemanticStateInvariant state
      -> ExecutionCollectedFieldInvariant state := by
  intro hinvariant
  constructor
  · exact hinvariant.groupedResponseKeysUnique
  · exact ExecutionValidFieldSemanticStateInvariant.groupedFieldsResolveStable
      state hinvariant

theorem ExecutionCollectedFieldInvariant.responseName_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hcollect
      : GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet
        = groups)
    : CollectedGroupsResponseName groups := by
  rw [← hcollect]
  exact collectFields_responseName state.window.schema
    state.window.variableValues state.window.parentType state.window.source
    state.window.selectionSet

theorem ExecutionCollectedFieldInvariant.parent_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hcollect
      : GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet
        = groups)
    : CollectedGroupsParent state.window.parentType groups := by
  rw [← hcollect]
  exact collectFields_parent state.window.schema state.window.variableValues
    state.window.parentType state.window.source state.window.selectionSet

theorem ExecutionCollectedFieldInvariant.pairKeysNodup_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hinvariant : ExecutionCollectedFieldInvariant state)
    (hcollect
      : GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet
        = groups)
    : PairKeysNodup groups := by
  rw [← hcollect]
  exact hinvariant.groupedResponseKeysUnique

theorem ExecutionCollectedFieldInvariant.resolveStable_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hinvariant : ExecutionCollectedFieldInvariant state)
    (hcollect
      : GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet
        = groups)
    : CollectedGroupsResolveStable state.window.resolvers state.window.source groups := by
  rw [← hcollect]
  exact hinvariant.groupedFieldsResolveStable

theorem ExecutionCollectedFieldInvariant.groupResolveStable_of_collect_eq
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (responseName : Name) (fields : List ExecutableField)
    (hinvariant : ExecutionCollectedFieldInvariant state)
    (hcollect
      : GraphQL.Execution.collectFields state.window.schema
          state.window.variableValues state.window.parentType state.window.source
          state.window.selectionSet
        = groups)
    (hgroup : (responseName, fields) ∈ groups)
    : ExecutableFieldsResolveStable state.window.resolvers state.window.source fields :=
  (hinvariant.resolveStable_of_collect_eq state groups hcollect)
    responseName fields hgroup

theorem ExecutionSemanticStateInvariant.of_grouped_validation
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique
      : PairKeysNodup
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hsameParent
      : CollectedGroupsSameResponseParent
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hcompatible
      : CollectedGroupsValidationMergeCompatible
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hresolvers
      : ResolversRespectArgumentEquivalence state.window.resolvers state.window.source)
    : ExecutionSemanticStateInvariant state := by
  constructor
  · exact hunique
  · exact hsameParent
  · exact hcompatible
  · exact hresolvers

theorem ExecutionFieldSemanticStateInvariant.of_grouped_validation
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique
      : PairKeysNodup
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hcompatible
      : CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hresolvers
      : ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
          state.window.source)
    : ExecutionFieldSemanticStateInvariant state := by
  constructor
  · exact hunique
  · exact hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_grouped_validation
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique
      : PairKeysNodup
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hcompatible
      : CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hargumentsNodup
      : CollectedGroupsArgumentsNodup
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
          state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  constructor
  · exact hunique
  · exact hcompatible
  · exact hargumentsNodup
  · exact hresolvers

theorem ExecutionFieldSemanticStateInvariant.of_semantic_same_parent
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    : ExecutionSemanticStateInvariant state
      -> ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
          state.window.source
      -> ExecutionFieldSemanticStateInvariant state := by
  intro hinvariant hresolvers
  apply ExecutionFieldSemanticStateInvariant.of_grouped_validation state
  · exact hinvariant.groupedResponseKeysUnique
  · exact CollectedGroupsValidationMergeCompatible.fieldCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hinvariant.groupedFieldsSameParent
      hinvariant.groupedFieldsValidationCompatible
  · exact hresolvers

theorem ExecutionSemanticStateInvariant.of_collected_groups
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hgroups
      : groups
        = GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)
    (hunique : PairKeysNodup groups)
    (hsameParent : CollectedGroupsSameResponseParent groups)
    (hcompatible : CollectedGroupsValidationMergeCompatible groups)
    (hresolvers
      : ResolversRespectArgumentEquivalence state.window.resolvers state.window.source)
    : ExecutionSemanticStateInvariant state := by
  apply ExecutionSemanticStateInvariant.of_grouped_validation state
  · simpa [← hgroups] using hunique
  · simpa [← hgroups] using hsameParent
  · simpa [← hgroups] using hcompatible
  · exact hresolvers

theorem ExecutionFieldSemanticStateInvariant.of_collected_groups
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hgroups
      : groups
        = GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)
    (hunique : PairKeysNodup groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hresolvers
      : ResolversRespectFieldAndArgumentEquivalence state.window.resolvers
          state.window.source)
    : ExecutionFieldSemanticStateInvariant state := by
  apply ExecutionFieldSemanticStateInvariant.of_grouped_validation state
  · simpa [← hgroups] using hunique
  · simpa [← hgroups] using hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_collected_groups
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (groups : List (Name × List ExecutableField))
    (hgroups
      : groups
        = GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet)
    (hunique : PairKeysNodup groups)
    (hcompatible : CollectedGroupsFieldValidationMergeCompatible groups)
    (hargumentsNodup : CollectedGroupsArgumentsNodup groups)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.resolvers
          state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · simpa [← hgroups] using hunique
  · simpa [← hgroups] using hcompatible
  · simpa [← hgroups] using hargumentsNodup
  · exact hresolvers

theorem ExecutionStateInvariant.of_grouped_compatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (hunique
      : PairKeysNodup
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hcompatible
      : ∀ responseName fields,
          (responseName, fields)
            ∈ GraphQL.Execution.collectFields state.window.schema
                state.window.variableValues state.window.parentType
                state.window.source state.window.selectionSet
          -> ExecutableFieldsMergeCompatible fields)
    : ExecutionStateInvariant state := by
  constructor
  · exact hunique
  · exact hcompatible
  · intro responseName fields hmem
    exact ExecutableFieldsMergeCompatible.resolveStable state.window.resolvers
      state.window.source fields (hcompatible responseName fields hmem)

end ExecutionUngrouped
end Algorithms

end GraphQL
