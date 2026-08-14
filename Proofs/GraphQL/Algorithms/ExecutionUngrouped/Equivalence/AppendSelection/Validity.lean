import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.AppendSelection

/-!
Validation-derived execution-state invariants for append-selection equivalence.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          state.window.parentType state.window.selectionSet)
    (hcompatible
      : CollectedGroupsFieldValidationMergeCompatible
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · exact collectFields_pairKeysNodup state.window.schema
      state.window.variableValues state.window.parentType state.window.source
      state.window.selectionSet
  · exact hcompatible
  · exact collectFields_argumentsNodup_of_selectionSetValid state.window.schema
      variableDefinitions state.window.variableValues state.window.parentType
      state.window.parentType state.window.source state.window.selectionSet
      hselectionSet
  · exact hresolvers

theorem
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_validationCompatible
    {ObjectIdentity : Type} (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          state.window.parentType state.window.selectionSet)
    (hcompatible
      : CollectedGroupsValidationMergeCompatible
          (GraphQL.Execution.collectFields state.window.schema
            state.window.variableValues state.window.parentType
            state.window.source state.window.selectionSet))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact CollectedGroupsValidationMergeCompatible.fieldCompatible
      (GraphQL.Execution.collectFields state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      (collectFields_sameResponseParent state.window.schema
        state.window.variableValues state.window.parentType
        state.window.source state.window.selectionSet)
      hcompatible
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    {ObjectIdentity : Type}
    (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          state.window.parentType state.window.selectionSet)
    (hscopedCompatible
      : ScopedFieldsFieldValidationMergeCompatible
          (FieldMerge.collectFields state.window.schema state.window.parentType
            state.window.selectionSet))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact collectFields_fieldCompatible_of_selectionSetValid_scopedCompatible
      state.window.schema variableDefinitions state.window.variableValues
      state.window.parentType state.window.parentType state.window.source
      state.window.selectionSet hselectionSet hscopedCompatible
  · exact hresolvers

theorem
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_sameScopedParent
    {ObjectIdentity : Type} (state : ExecutionEquivalenceState ObjectIdentity)
    (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          state.window.parentType state.window.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
          state.window.selectionSet)
    (hsameParent
      : ScopedFieldsSameResponseParent
          (FieldMerge.collectFields state.window.schema state.window.parentType
            state.window.selectionSet))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    state variableDefinitions hselectionSet
  · exact fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
      state.window.schema state.window.parentType state.window.selectionSet
      hmerge hsameParent
  · exact hresolvers

theorem
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeApplies
    {ObjectIdentity : Type} (state : ExecutionEquivalenceState ObjectIdentity)
    (runtimeType : Name) (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          state.window.parentType state.window.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
          state.window.selectionSet)
    (hruntimeApplies
      : ∀ scopedField,
          scopedField
            ∈ FieldMerge.collectFields state.window.schema state.window.parentType
                state.window.selectionSet
          -> ScopedFieldRuntimeApplies state.window.schema runtimeType scopedField)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    state variableDefinitions hselectionSet
  · exact
      fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_runtimeApplies
        state.window.schema state.window.parentType runtimeType
        state.window.selectionSet hmerge hruntimeApplies
  · exact hresolvers

theorem
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type} (state : ExecutionEquivalenceState ObjectIdentity)
    (runtimeType : Name) (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          state.window.parentType state.window.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge state.window.schema state.window.parentType
          state.window.selectionSet)
    (hruntimeScoped
      : ExecutableFieldsRuntimeScopedBy state.window.schema runtimeType
          (FieldMerge.collectFields state.window.schema state.window.parentType
            state.window.selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields state.window.schema
              state.window.variableValues state.window.parentType
              state.window.source state.window.selectionSet)))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet state
    variableDefinitions hselectionSet
  · exact collectFields_fieldCompatible_of_canMerge_runtimeScoped
      state.window.schema state.window.variableValues state.window.parentType
      state.window.parentType runtimeType state.window.source
      state.window.selectionSet hmerge hruntimeScoped
  · exact hresolvers

theorem
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScopedBy
    {ObjectIdentity : Type} (state : ExecutionEquivalenceState ObjectIdentity)
    (validParent runtimeType : Name) (variableDefinitions : List VariableDefinition)
    (hselectionSet
      : Validation.selectionSetValid state.window.schema variableDefinitions
          validParent state.window.selectionSet)
    (hmerge
      : FieldMerge.fieldsInSetCanMerge state.window.schema validParent
          state.window.selectionSet)
    (hruntimeScoped
      : ExecutableFieldsRuntimeScopedBy state.window.schema runtimeType
          (FieldMerge.collectFields state.window.schema validParent
            state.window.selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields state.window.schema
              state.window.variableValues state.window.parentType
              state.window.source state.window.selectionSet)))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence state.window.schema
          state.window.resolvers state.window.variableValues state.window.source)
    : ExecutionValidFieldSemanticStateInvariant state := by
  apply ExecutionValidFieldSemanticStateInvariant.of_grouped_validation state
  · exact collectFields_pairKeysNodup state.window.schema
      state.window.variableValues state.window.parentType state.window.source
      state.window.selectionSet
  · exact collectFields_fieldCompatible_of_canMerge_runtimeScoped
      state.window.schema state.window.variableValues state.window.parentType
      validParent runtimeType state.window.source state.window.selectionSet
      hmerge hruntimeScoped
  · exact collectFields_argumentsNodup_of_selectionSetValid state.window.schema
      variableDefinitions state.window.variableValues state.window.parentType
      validParent state.window.source state.window.selectionSet hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (initial : ResponseValue)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime : ScopedParentRuntimeApplies schema runtimeType parentType)
    (hselectionSet
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          (.object runtimeType identity))
    : ExecutionValidFieldSemanticStateInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := .object runtimeType identity
              selectionSet := selectionSet
            }
          initial := initial
        } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial }
      runtimeType variableDefinitions hselectionSet hmerge
  · exact collectFields_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues parentType parentType runtimeType
      identity selectionSet hparentRuntime hselectionSet
  · exact hresolvers

theorem
    ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge_optional
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (parentType runtimeType : Name)
    (identity : ObjectIdentity) (selectionSet : List Selection) (initial : ResponseValue)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime : ScopedParentRuntimeApplies schema runtimeType parentType)
    (hselectionSet
      : Validation.selectionSetValid schema variableDefinitions parentType selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          (.object runtimeType identity))
    : ExecutionValidFieldSemanticStateInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := .object runtimeType identity
              selectionSet := selectionSet
            }
          initial := initial
        } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_canMerge_runtimeScoped
      { window :=
        { schema := schema
          resolvers := resolvers
          variableValues := variableValues
          depth := depth
          parentType := parentType
          source := .object runtimeType identity
          selectionSet := selectionSet }
        initial := initial }
      runtimeType variableDefinitions hselectionSet hmerge
  · exact collectFields_runtimeScopedBy_of_selectionSetValid_object schema
      variableDefinitions variableValues parentType parentType runtimeType
      identity selectionSet hparentRuntime hselectionSet
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_object_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : ResponseValue)
    (hparentRuntime
      : ScopedParentRuntimeApplies schema runtimeType (operation.rootType schema))
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          (.object runtimeType identity))
    : ExecutionValidFieldSemanticStateInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := (operation.rootType schema)
              source := .object runtimeType identity
              selectionSet := operation.selectionSet
            }
          initial := initial
        } := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_object_selectionSet_canMerge
    schema resolvers variableValues depth (operation.rootType schema) runtimeType
    identity operation.selectionSet initial operation.variableDefinitions
    hparentRuntime
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : ResponseValue)
    (hroot : rootSourceAppliesBool schema operation (.object runtimeType identity) = true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          (.object runtimeType identity))
    : ExecutionValidFieldSemanticStateInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := (operation.rootType schema)
              source := .object runtimeType identity
              selectionSet := operation.selectionSet
            }
          initial := initial
        } := by
  exact ExecutionValidFieldSemanticStateInvariant.of_valid_object_operation_canMerge
    schema resolvers variableValues depth operation runtimeType identity initial
    (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
      runtimeType identity hroot)
    hvalid hresolvers

theorem ExecutionCollectedFieldInvariant.of_valid_root_operation_canMerge
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (runtimeType : Name)
    (identity : ObjectIdentity) (initial : ResponseValue)
    (hroot : rootSourceAppliesBool schema operation (.object runtimeType identity) = true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          (.object runtimeType identity))
    : ExecutionCollectedFieldInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := (operation.rootType schema)
              source := .object runtimeType identity
              selectionSet := operation.selectionSet
            }
          initial := initial
        } := by
  apply ExecutionCollectedFieldInvariant.of_validFieldSemantic
  exact ExecutionValidFieldSemanticStateInvariant.of_valid_root_operation_canMerge
    schema resolvers variableValues depth operation runtimeType identity
    initial hroot hvalid hresolvers

theorem
    ExecutionCollectedFieldInvariant.of_valid_object_selectionSet_canMerge_argumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (collectParent validParent runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (initial : ResponseValue)
    (variableDefinitions : List VariableDefinition)
    (hparentRuntime : ScopedParentRuntimeApplies schema runtimeType validParent)
    (hselectionSet
      : Validation.selectionSetValid schema variableDefinitions validParent selectionSet)
    (hmerge : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet)
    : ExecutionCollectedFieldInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := collectParent
              source := .object runtimeType identity
              selectionSet := selectionSet
            }
          initial := initial
        } := by
  let groups :=
    GraphQL.Execution.collectFields schema variableValues collectParent
      (.object runtimeType identity) selectionSet
  have hfieldCompatible :
      CollectedGroupsFieldValidationMergeCompatible groups := by
    dsimp [groups]
    apply collectFields_fieldCompatible_of_canMerge_runtimeScoped
      schema variableValues collectParent validParent runtimeType
      (.object runtimeType identity) selectionSet hmerge
    exact collectFields_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet hparentRuntime hselectionSet
  have hvalidationCompatible :
      CollectedGroupsValidationMergeCompatible groups := by
    intro responseName fields hmem first later hfirst hlater hresponse
      _hparent
    exact hfieldCompatible responseName fields hmem first later hfirst hlater
      hresponse
  have hargumentsNodup : CollectedGroupsArgumentsNodup groups := by
    dsimp [groups]
    exact collectFields_argumentsNodup_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent
      (.object runtimeType identity) selectionSet hselectionSet
  constructor
  · dsimp [groups]
    exact collectFields_pairKeysNodup schema variableValues collectParent
      (.object runtimeType identity) selectionSet
  · dsimp [groups]
    exact
      CollectedGroupsValidationMergeCompatible.resolveStableValid schema resolvers
        variableValues (.object runtimeType identity)
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet)
        (Resolvers.respectValidArgumentEquivalence schema resolvers variableValues
          (.object runtimeType identity))
        (collectFields_sameResponseParent schema variableValues collectParent
          (.object runtimeType identity) selectionSet)
        hvalidationCompatible hargumentsNodup

theorem
    ExecutionCollectedFieldInvariant.of_valid_root_operation_canMerge_argumentEquivalence
    {ObjectIdentity : Type} (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat) (operation : Operation)
    (runtimeType : Name) (identity : ObjectIdentity) (initial : ResponseValue)
    (hroot : rootSourceAppliesBool schema operation (.object runtimeType identity) = true)
    (hvalid : Validation.operationDefinitionValid schema operation)
    : ExecutionCollectedFieldInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := (operation.rootType schema)
              source := .object runtimeType identity
              selectionSet := operation.selectionSet
            }
          initial := initial
        } := by
  apply
    ExecutionCollectedFieldInvariant.of_valid_object_selectionSet_canMerge_argumentEquivalence
      schema resolvers variableValues depth (operation.rootType schema)
      (operation.rootType schema) runtimeType identity operation.selectionSet initial
      operation.variableDefinitions
      (ScopedParentRuntimeApplies.of_rootSourceAppliesBool schema operation
        runtimeType identity hroot)
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid

theorem OperationNoAliasCollision.of_valid_sameScopedParent
    (schema : Schema) (operation : Operation)
    : Validation.operationDefinitionValid schema operation
      -> ScopedFieldsSameResponseParent
          (FieldMerge.collectFields schema (operation.rootType schema)
            operation.selectionSet)
      -> OperationNoAliasCollision schema operation := by
  intro hvalid hsameParent
  unfold OperationNoAliasCollision ScopedFieldsNoAliasCollision
  exact fieldsInSetCanMerge_scoped_collectFields_fieldCompatible_of_sameParent
    schema (operation.rootType schema) operation.selectionSet
    (Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid)
    hsameParent

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_operation_noAliasCollision
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (source : ResolverValue ObjectIdentity)
    (initial : ResponseValue)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnoAlias : OperationNoAliasCollision schema operation)
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          source)
    : ExecutionValidFieldSemanticStateInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := (operation.rootType schema)
              source := source
              selectionSet := operation.selectionSet
            }
          initial := initial
        } := by
  apply ExecutionValidFieldSemanticStateInvariant.of_valid_selectionSet_scopedCompatible
    { window :=
      { schema := schema
        resolvers := resolvers
        variableValues := variableValues
        depth := depth
        parentType := (operation.rootType schema)
        source := source
        selectionSet := operation.selectionSet }
      initial := initial }
    operation.variableDefinitions
  · exact Validation.operationDefinitionValid_selectionSetValid hvalid
  · exact ScopedFieldsNoAliasCollision.fieldCompatible
      (FieldMerge.collectFields schema (operation.rootType schema) operation.selectionSet)
      hnoAlias
  · exact hresolvers

theorem ExecutionValidFieldSemanticStateInvariant.of_valid_operation_sameScopedParent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (operation : Operation) (source : ResolverValue ObjectIdentity)
    (initial : ResponseValue)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hsameParent
      : ScopedFieldsSameResponseParent
          (FieldMerge.collectFields schema (operation.rootType schema)
            operation.selectionSet))
    (hresolvers
      : ResolversRespectValidFieldAndArgumentEquivalence schema resolvers variableValues
          source)
    : ExecutionValidFieldSemanticStateInvariant
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := (operation.rootType schema)
              source := source
              selectionSet := operation.selectionSet
            }
          initial := initial
        } := by
  apply
    ExecutionValidFieldSemanticStateInvariant.of_valid_operation_noAliasCollision
      schema resolvers variableValues depth operation source initial hvalid
  · exact OperationNoAliasCollision.of_valid_sameScopedParent schema operation
      hvalid hsameParent
  · exact hresolvers

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
