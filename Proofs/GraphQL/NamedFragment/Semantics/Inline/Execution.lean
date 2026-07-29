import Proofs.GraphQL.NamedFragment.Semantics.Inline.Translate
import Proofs.GraphQL.NamedFragment.Semantics.Inline.Operation

/-! Direct-execution proof witnesses for fragment-free named-fragment operations. -/

namespace GraphQL
namespace NamedFragment
namespace Semantics

variable {ObjectRef : Type}

mutual
  theorem executeCollectedFields_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (source : Execution.ResolverValue ObjectRef)
            (groups : List (Name × List Execution.ExecutableField)),
          Execution.executeCollectedFields schema resolvers variableValues fuel
            source groups
          = GraphQL.Execution.executeCollectedFields schema resolvers variableValues
              fuel source (executableGroupsToSpec groups)
    | schema, resolvers, variableValues, fuel, source, [] => by
        simp [Execution.executeCollectedFields,
          GraphQL.Execution.executeCollectedFields, executableGroupsToSpec]
    | schema, resolvers, variableValues, fuel, source,
        (responseName, fields) :: rest => by
        simp [Execution.executeCollectedFields,
          GraphQL.Execution.executeCollectedFields, executableGroupsToSpec,
          executableGroupToSpec,
          executeField_toSpec schema resolvers variableValues fuel source
            responseName fields,
          executeCollectedFields_toSpec schema resolvers variableValues fuel
            source rest]
  termination_by _schema _resolvers _variableValues fuel _source groups =>
    (fuel, 4, 0, sizeOf groups)

  theorem executeField_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (source : Execution.ResolverValue ObjectRef)
            (responseName : Name) (fields : List Execution.ExecutableField),
          Execution.executeField schema resolvers variableValues fuel source
            responseName fields
          = GraphQL.Execution.executeField schema resolvers variableValues fuel
              source responseName (fields.map executableFieldToSpec)
    | schema, resolvers, variableValues, fuel, source,
        responseName, [] => by
        simp [Execution.executeField, GraphQL.Execution.executeField]
    | schema, resolvers, variableValues, 0, source,
        responseName, field :: fields => by
        simp [Execution.executeField, GraphQL.Execution.executeField,
          executableFieldToSpec]
    | schema, resolvers, variableValues, fuel + 1, source,
        responseName, field :: fields => by
        cases hfield : schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, GraphQL.Execution.executeField,
              executableFieldToSpec, hfield]
        | some fieldDefinition =>
            cases hresolved :
                resolvers.resolve field.parentType field.fieldName
                  field.arguments source with
            | none =>
                simp [Execution.executeField, GraphQL.Execution.executeField,
                  executableFieldToSpec, hfield, hresolved]
            | some resolved =>
                simp [Execution.executeField, GraphQL.Execution.executeField,
                  executableFieldToSpec, hfield, hresolved,
                  completeValue_toSpec schema resolvers variableValues fuel
                    fieldDefinition.outputType (field :: fields) resolved]
  termination_by _schema _resolvers _variableValues fuel _source _responseName fields =>
    (fuel, 3, 0, sizeOf fields)

  theorem completeValue_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (fieldType : TypeRef) (fields : List Execution.ExecutableField)
            (value : Execution.ResolverValue ObjectRef),
          Execution.completeValue schema resolvers variableValues fuel
            fieldType fields value
          = GraphQL.Execution.completeValue schema resolvers variableValues fuel
              fieldType (fields.map executableFieldToSpec) value
    | schema, resolvers, variableValues, 0, fieldType, fields,
        value => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .nonNull inner,
        fields, value => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue,
          completeValue_toSpec schema resolvers variableValues (fuel + 1)
            inner fields value]
    | schema, resolvers, variableValues, fuel + 1, .named typeName,
        fields, .null => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .named typeName,
        fields, .scalar value => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .named parentType,
        fields, source@(.object runtimeType ref) => by
        by_cases hinclude :
            schema.typeIncludesObjectBool parentType runtimeType = true
        · simp [Execution.completeValue, GraphQL.Execution.completeValue,
            hinclude]
          rw [executeCollectedFields_toSpec schema resolvers variableValues fuel
            (Execution.ResolverValue.object runtimeType ref)
            (Execution.collectSubfields schema variableValues
              runtimeType (Execution.ResolverValue.object runtimeType ref)
              fields)]
          rw [collectSubfields_toSpec schema variableValues
            runtimeType (Execution.ResolverValue.object runtimeType ref) fields]
        · simp [Execution.completeValue, GraphQL.Execution.completeValue,
            hinclude]
    | schema, resolvers, variableValues, fuel + 1, .named typeName,
        fields, .list values => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .list values => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue,
          completeValueList_toSpec schema resolvers variableValues fuel
            inner fields values]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .null => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .scalar value => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .object runtimeType ref => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
  termination_by _schema _resolvers _variableValues fuel fieldType fields _value =>
    (fuel, 1, sizeOf fieldType, sizeOf fields)

  theorem completeValueList_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (itemType : TypeRef) (fields : List Execution.ExecutableField)
            (values : List (Execution.ResolverValue ObjectRef)),
          Execution.completeValueList schema resolvers variableValues fuel
            itemType fields values
          = GraphQL.Execution.completeValueList schema resolvers variableValues fuel
              itemType (fields.map executableFieldToSpec) values
    | schema, resolvers, variableValues, fuel, itemType, fields,
        [] => by
        simp [Execution.completeValueList, GraphQL.Execution.completeValueList]
    | schema, resolvers, variableValues, fuel, itemType, fields,
        value :: values => by
        simp [Execution.completeValueList, GraphQL.Execution.completeValueList,
          completeValue_toSpec schema resolvers variableValues fuel
            itemType fields value,
          completeValueList_toSpec schema resolvers variableValues fuel
            itemType fields values]
  termination_by _schema _resolvers _variableValues fuel itemType _fields values =>
    (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

theorem executeRootSelectionSet_toSpec
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (fragments : List FragmentDefinition) (selectionSet : List Selection)
    : Execution.executeRootSelectionSet schema resolvers variableValues fuel
        parentType source fragments selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues fuel
          parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet fragments selectionSet)) := by
  simp [Execution.executeRootSelectionSet,
    GraphQL.Execution.executeRootSelectionSet]
  rw [executeCollectedFields_toSpec schema resolvers variableValues fuel
    source
    (Execution.collectFields schema variableValues fragments parentType source
      selectionSet)]
  rw [collectFields_toSpec schema variableValues fragments parentType source
    selectionSet]

theorem executeQueryWithFuel_toSpec_inlineOperation
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    : Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          (Translate.reduceOperation (Inline.inlineOperation operation))
          fuel source := by
  cases operation with
  | mk name operationType variableDefinitions fragmentDefinitions selectionSet =>
      cases operationType
      cases source with
      | null =>
          simp [Execution.executeQueryWithFuel,
            Execution.rootSourceAppliesBool,
            GraphQL.Execution.executeQueryWithFuel,
            GraphQL.Execution.rootSourceAppliesBool,
            GraphQL.Execution.runtimeObjectType?]
      | scalar value =>
          simp [Execution.executeQueryWithFuel,
            Execution.rootSourceAppliesBool,
            GraphQL.Execution.executeQueryWithFuel,
            GraphQL.Execution.rootSourceAppliesBool,
            GraphQL.Execution.runtimeObjectType?]
      | list values =>
          simp [Execution.executeQueryWithFuel,
            Execution.rootSourceAppliesBool,
            GraphQL.Execution.executeQueryWithFuel,
            GraphQL.Execution.rootSourceAppliesBool,
            GraphQL.Execution.runtimeObjectType?]
      | object objectName ref =>
          by_cases hroot :
              schema.typeIncludesObjectBool schema.queryType objectName = true
          · simp [Execution.executeQueryWithFuel,
              Execution.rootSourceAppliesBool,
              GraphQL.Execution.executeQueryWithFuel,
              GraphQL.Execution.rootSourceAppliesBool,
              GraphQL.Execution.runtimeObjectType?,
              Operation.rootType, OperationType.rootType,
              GraphQL.Operation.rootType, GraphQL.OperationType.rootType,
              hroot]
            rw [executeRootSelectionSet_toSpec schema resolvers
              (Execution.coerceVariableValues
                {
                  name := name
                  variableDefinitions := variableDefinitions
                  fragmentDefinitions := fragmentDefinitions
                  selectionSet := selectionSet
                }
                variableValues)
              fuel schema.queryType (Execution.ResolverValue.object objectName ref)
              fragmentDefinitions selectionSet]
            simp [Execution.coerceVariableValues,
              GraphQL.Execution.coerceVariableValues]
            rfl
          · simp [Execution.executeQueryWithFuel,
              Execution.rootSourceAppliesBool,
              GraphQL.Execution.executeQueryWithFuel,
              GraphQL.Execution.rootSourceAppliesBool,
              GraphQL.Execution.runtimeObjectType?,
              Operation.rootType, OperationType.rootType,
              GraphQL.Operation.rootType, GraphQL.OperationType.rootType,
              hroot]

theorem executeQueryWithFuel_eq_spec_of_inlined
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (hinlined : operationInlined operation)
    : Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          (Translate.reduceOperation operation) fuel source := by
  rw [executeQueryWithFuel_toSpec_inlineOperation]
  rw [inlineOperation_eq_of_inlined operation hinlined]

-- The public predicate carries schema-well-formedness and named-fragment validity
-- premises because it is a conformance statement, but this execution witness only
-- needs the explicit `operationInlined` hypothesis: once there are no fragment
-- spreads left, fragment-aware execution is definitionally bridged to spec execution.
theorem fragmentAwareInlinedExecutionEquivalentToSpecExecution_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareInlinedExecutionEquivalentToSpecExecution schema operation := by
  intro _hschema _hvalid hinlined
  intro ObjectRef resolvers variableValues fuel source
  exact executeQueryWithFuel_eq_spec_of_inlined schema resolvers
    variableValues operation fuel source hinlined

theorem fragmentAwareInlineExecutionEquivalentToSpecExecution_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareInlineExecutionEquivalentToSpecExecution schema operation := by
  intro _hschema _hvalid
  intro ObjectRef resolvers variableValues fuel source
  exact executeQueryWithFuel_toSpec_inlineOperation schema resolvers
    variableValues operation fuel source

theorem fragmentAwareExecutionEquivalentToInline_of_inlined
    (schema : Schema) (operation : Operation)
    (hinlined : operationInlined operation)
    : fragmentAwareExecutionEquivalentToInline schema operation := by
  intro _hschema _hvalid
  intro ObjectRef resolvers variableValues fuel source
  rw [executeQueryWithFuel_eq_spec_of_inlined schema resolvers
    variableValues operation fuel source hinlined]
  rw [executeQueryWithFuel_eq_spec_of_inlined schema resolvers
    variableValues (Inline.inlineOperation operation) fuel source
    (inlineOperation_inlined operation)]
  rw [inlineOperation_eq_of_inlined operation hinlined]

-- This witness is unconditional over valid operations because direct fragment-aware
-- execution is proved by translating both sides through the spec execution of
-- `Inline.inlineOperation operation`. The validity premise is part of the public
-- theorem shape, not a dependency of the executable equality proof.
theorem fragmentAwareExecutionEquivalentToInline_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareExecutionEquivalentToInline schema operation := by
  intro _hschema _hvalid
  intro ObjectRef resolvers variableValues fuel source
  calc
    Execution.executeQueryWithFuel schema resolvers variableValues operation
        fuel source
        =
      GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
        (Translate.reduceOperation (Inline.inlineOperation operation))
        fuel source := by
          exact executeQueryWithFuel_toSpec_inlineOperation schema resolvers
            variableValues operation fuel source
    _ =
      Execution.executeQueryWithFuel schema resolvers variableValues
        (Inline.inlineOperation operation) fuel source := by
          symm
          rw [executeQueryWithFuel_toSpec_inlineOperation schema resolvers
            variableValues (Inline.inlineOperation operation) fuel source]
          rw [inlineOperation_idem operation]

end Semantics
end NamedFragment
end GraphQL
