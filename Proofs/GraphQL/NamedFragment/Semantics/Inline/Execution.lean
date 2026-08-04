import Proofs.GraphQL.NamedFragment.Semantics.Inline.Translate
import Proofs.GraphQL.NamedFragment.Semantics.Inline.Operation
import Proofs.GraphQL.NamedFragment.Semantics.Inline.VisitedFragments

/-! Direct-execution proof for fragment-aware operations and their inlined forms. -/

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
          executableGroupsInlined groups
          -> Execution.executeCollectedFields schema resolvers variableValues fuel
                source groups
              = GraphQL.Execution.executeCollectedFields schema resolvers variableValues
                  fuel source (executableGroupsToSpec groups)
    | schema, resolvers, variableValues, fuel, source, [], _hinlined => by
        simp [Execution.executeCollectedFields,
          GraphQL.Execution.executeCollectedFields, executableGroupsToSpec]
    | schema, resolvers, variableValues, fuel, source,
        (responseName, fields) :: rest, hinlined => by
        have hfields : executableFieldsInlined fields :=
          hinlined (responseName, fields) (by simp)
        have hrest : executableGroupsInlined rest := by
          intro group hgroup
          exact hinlined group (by simp [hgroup])
        simp [Execution.executeCollectedFields,
          GraphQL.Execution.executeCollectedFields, executableGroupsToSpec,
          executableGroupToSpec,
          executeField_toSpec schema resolvers variableValues fuel source
            responseName fields hfields,
          executeCollectedFields_toSpec schema resolvers variableValues fuel
            source rest hrest]
  termination_by _schema _resolvers _variableValues fuel _source groups _hinlined =>
    (fuel, 4, 0, sizeOf groups)

  theorem executeField_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (source : Execution.ResolverValue ObjectRef)
            (responseName : Name) (fields : List Execution.ExecutableField),
          executableFieldsInlined fields
          -> Execution.executeField schema resolvers variableValues fuel source
                responseName fields
              = GraphQL.Execution.executeField schema resolvers variableValues fuel
                  source responseName (fields.map executableFieldToSpec)
    | schema, resolvers, variableValues, fuel, source,
        responseName, [], _hinlined => by
        simp [Execution.executeField, GraphQL.Execution.executeField]
    | schema, resolvers, variableValues, 0, source,
        responseName, field :: fields, _hinlined => by
        simp [Execution.executeField, GraphQL.Execution.executeField,
          executableFieldToSpec]
    | schema, resolvers, variableValues, fuel + 1, source,
        responseName, field :: fields, hinlined => by
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
                    fieldDefinition.outputType (field :: fields) resolved hinlined]
  termination_by _schema _resolvers _variableValues fuel _source _responseName fields
      _hinlined =>
    (fuel, 3, 0, sizeOf fields)

  theorem completeValue_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (fieldType : TypeRef) (fields : List Execution.ExecutableField)
            (value : Execution.ResolverValue ObjectRef),
          executableFieldsInlined fields
          -> Execution.completeValue schema resolvers variableValues fuel
                fieldType fields value
              = GraphQL.Execution.completeValue schema resolvers variableValues fuel
                  fieldType (fields.map executableFieldToSpec) value
    | schema, resolvers, variableValues, 0, fieldType, fields,
        value, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .nonNull inner,
        fields, value, hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue,
          completeValue_toSpec schema resolvers variableValues (fuel + 1)
            inner fields value hinlined]
    | schema, resolvers, variableValues, fuel + 1, .named typeName,
        fields, .null, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .named typeName,
        fields, .scalar value, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .named parentType,
        fields, source@(.object runtimeType ref), hinlined => by
        by_cases hinclude :
            schema.typeIncludesObjectBool parentType runtimeType = true
        · simp [Execution.completeValue, GraphQL.Execution.completeValue,
            hinclude]
          rw [executeCollectedFields_toSpec schema resolvers variableValues fuel
            (Execution.ResolverValue.object runtimeType ref)
            (Execution.collectSubfields schema variableValues
              runtimeType (Execution.ResolverValue.object runtimeType ref)
              fields)
            (by
              intro group hgroup
              exact collectSubfields_inlined schema variableValues runtimeType
                (Execution.ResolverValue.object runtimeType ref) fields hinlined
                group hgroup)]
          rw [collectSubfields_toSpec schema variableValues
            runtimeType (Execution.ResolverValue.object runtimeType ref) fields
            hinlined]
          rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
        · simp [Execution.completeValue, GraphQL.Execution.completeValue,
            hinclude]
    | schema, resolvers, variableValues, fuel + 1, .named typeName,
        fields, .list values, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .list values, hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue,
          completeValueList_toSpec schema resolvers variableValues fuel
            inner fields values hinlined]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .null, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .scalar value, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        fields, .object runtimeType ref, _hinlined => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
  termination_by _schema _resolvers _variableValues fuel fieldType fields _value
      _hinlined =>
    (fuel, 1, sizeOf fieldType, sizeOf fields)

  theorem completeValueList_toSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (itemType : TypeRef) (fields : List Execution.ExecutableField)
            (values : List (Execution.ResolverValue ObjectRef)),
          executableFieldsInlined fields
          -> Execution.completeValueList schema resolvers variableValues fuel
                itemType fields values
              = GraphQL.Execution.completeValueList schema resolvers variableValues fuel
                  itemType (fields.map executableFieldToSpec) values
    | schema, resolvers, variableValues, fuel, itemType, fields,
        [], _hinlined => by
        simp [Execution.completeValueList, GraphQL.Execution.completeValueList]
    | schema, resolvers, variableValues, fuel, itemType, fields,
        value :: values, hinlined => by
        simp [Execution.completeValueList, GraphQL.Execution.completeValueList,
          completeValue_toSpec schema resolvers variableValues fuel
            itemType fields value hinlined,
          completeValueList_toSpec schema resolvers variableValues fuel
            itemType fields values hinlined]
  termination_by _schema _resolvers _variableValues fuel itemType _fields values
      _hinlined =>
    (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

mutual
  theorem executeCollectedFields_toExpandedSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues)
            (variableDefinitions : List VariableDefinition)
            (original : List FragmentDefinition),
          GraphQL.NamedFragment.Validation.fragmentNamesUnique original
          -> GraphQL.NamedFragment.Validation.fragmentsAcyclic original
          -> GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
              variableDefinitions original
          -> ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
                (groups : List (Name × List Execution.ExecutableField)),
              VisitedFragments.ExecutableGroupsValidContext schema variableDefinitions
                original groups
              -> Execution.executeCollectedFields schema resolvers variableValues fuel
                    source groups
                  = GraphQL.Execution.executeCollectedFields schema resolvers
                      variableValues fuel source
                      (VisitedFragments.expandedExecutableGroupsToSpec groups)
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel, source, [], _hgroups => by
        simp [Execution.executeCollectedFields,
          GraphQL.Execution.executeCollectedFields,
          VisitedFragments.expandedExecutableGroupsToSpec]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel, source,
        (responseName, fields) :: rest, hgroups => by
        have hfields :
            VisitedFragments.ExecutableFieldsValidContext schema variableDefinitions
              original fields :=
          hgroups (responseName, fields) (by simp)
        have hrest :
            VisitedFragments.ExecutableGroupsValidContext schema variableDefinitions
              original rest := by
          intro group hgroup
          exact hgroups group (by simp [hgroup])
        simp [Execution.executeCollectedFields,
          GraphQL.Execution.executeCollectedFields,
          VisitedFragments.expandedExecutableGroupsToSpec,
          VisitedFragments.expandedExecutableGroupToSpec,
          executeField_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall fuel source responseName
            fields hfields,
          executeCollectedFields_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall fuel source rest hrest]
  termination_by _schema _resolvers _variableValues _variableDefinitions _original
      _hunique _hacyclic _hall fuel _source groups _hgroups =>
    (fuel, 4, 0, sizeOf groups)

  theorem executeField_toExpandedSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues)
            (variableDefinitions : List VariableDefinition)
            (original : List FragmentDefinition),
          GraphQL.NamedFragment.Validation.fragmentNamesUnique original
          -> GraphQL.NamedFragment.Validation.fragmentsAcyclic original
          -> GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
              variableDefinitions original
          -> ∀ (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
                (responseName : Name) (fields : List Execution.ExecutableField),
              VisitedFragments.ExecutableFieldsValidContext schema variableDefinitions
                original fields
              -> Execution.executeField schema resolvers variableValues fuel source
                    responseName fields
                  = GraphQL.Execution.executeField schema resolvers variableValues fuel
                      source responseName
                      (fields.map VisitedFragments.expandedExecutableFieldToSpec)
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel, source, responseName, [], _hfields => by
        simp [Execution.executeField, GraphQL.Execution.executeField]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, 0, source, responseName, field :: fields,
        _hfields => by
        simp [Execution.executeField, GraphQL.Execution.executeField,
          VisitedFragments.expandedExecutableFieldToSpec]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, source, responseName, field :: fields,
        hfields => by
        cases hfield : schema.lookupField field.parentType field.fieldName with
        | none =>
            simp [Execution.executeField, GraphQL.Execution.executeField,
              VisitedFragments.expandedExecutableFieldToSpec, hfield]
        | some fieldDefinition =>
            cases hresolved :
                resolvers.resolve field.parentType field.fieldName field.arguments
                  source with
            | none =>
                simp [Execution.executeField, GraphQL.Execution.executeField,
                  VisitedFragments.expandedExecutableFieldToSpec, hfield, hresolved]
            | some resolved =>
                simp [Execution.executeField, GraphQL.Execution.executeField,
                  VisitedFragments.expandedExecutableFieldToSpec, hfield, hresolved,
                  completeValue_toExpandedSpec schema resolvers variableValues
                    variableDefinitions original hunique hacyclic hall fuel
                    fieldDefinition.outputType (field :: fields) resolved hfields]
  termination_by _schema _resolvers _variableValues _variableDefinitions _original
      _hunique _hacyclic _hall fuel _source _responseName fields _hfields =>
    (fuel, 3, 0, sizeOf fields)

  theorem completeValue_toExpandedSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues)
            (variableDefinitions : List VariableDefinition)
            (original : List FragmentDefinition),
          GraphQL.NamedFragment.Validation.fragmentNamesUnique original
          -> GraphQL.NamedFragment.Validation.fragmentsAcyclic original
          -> GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
              variableDefinitions original
          -> ∀ (fuel : Nat) (fieldType : TypeRef)
                (fields : List Execution.ExecutableField)
                (value : Execution.ResolverValue ObjectRef),
              VisitedFragments.ExecutableFieldsValidContext schema variableDefinitions
                original fields
              -> Execution.completeValue schema resolvers variableValues fuel fieldType
                    fields value
                  = GraphQL.Execution.completeValue schema resolvers variableValues fuel
                      fieldType
                      (fields.map VisitedFragments.expandedExecutableFieldToSpec) value
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, 0, fieldType, fields, value, _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .nonNull inner, fields, value,
        hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue,
          completeValue_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall (fuel + 1) inner fields
            value hfields]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .named typeName, fields, .null,
        _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .named typeName, fields, .scalar value,
        _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .named parentType, fields,
        source@(.object runtimeType ref), hfields => by
        by_cases hinclude :
            schema.typeIncludesObjectBool parentType runtimeType = true
        · simp [Execution.completeValue, GraphQL.Execution.completeValue, hinclude]
          rw [executeCollectedFields_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall fuel
            (Execution.ResolverValue.object runtimeType ref)
            (Execution.collectSubfields schema variableValues runtimeType
              (Execution.ResolverValue.object runtimeType ref) fields)
            (VisitedFragments.collectSubfields_validContext hunique hacyclic hall
              variableValues runtimeType
              (Execution.ResolverValue.object runtimeType ref) fields hfields)]
          rw [GraphQL.Execution.DuplicateFields.executeCollectedFields_firstOccurrences
            schema resolvers variableValues fuel
            (Execution.ResolverValue.object runtimeType ref)
            (VisitedFragments.expandedExecutableGroupsToSpec
              (Execution.collectSubfields schema variableValues runtimeType
                (Execution.ResolverValue.object runtimeType ref) fields))
            (GraphQL.Execution.collectSubfields schema variableValues runtimeType
              (Execution.ResolverValue.object runtimeType ref)
              (fields.map VisitedFragments.expandedExecutableFieldToSpec))
            (VisitedFragments.collectSubfields_firstOccurrences variableValues hunique
              hacyclic hall runtimeType
              (Execution.ResolverValue.object runtimeType ref) fields hfields)]
          rw [GraphQL.NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet]
        · simp [Execution.completeValue, GraphQL.Execution.completeValue, hinclude]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .named typeName, fields, .list values,
        _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .list inner, fields, .list values,
        hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue,
          completeValueList_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall fuel inner fields values
            hfields]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .list inner, fields, .null,
        _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .list inner, fields, .scalar value,
        _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel + 1, .list inner, fields,
        .object runtimeType ref, _hfields => by
        simp [Execution.completeValue, GraphQL.Execution.completeValue]
  termination_by _schema _resolvers _variableValues _variableDefinitions _original
      _hunique _hacyclic _hall fuel fieldType fields _value _hfields =>
    (fuel, 1, sizeOf fieldType, sizeOf fields)

  theorem completeValueList_toExpandedSpec
      : ∀ (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues)
            (variableDefinitions : List VariableDefinition)
            (original : List FragmentDefinition),
          GraphQL.NamedFragment.Validation.fragmentNamesUnique original
          -> GraphQL.NamedFragment.Validation.fragmentsAcyclic original
          -> GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
              variableDefinitions original
          -> ∀ (fuel : Nat) (itemType : TypeRef)
                (fields : List Execution.ExecutableField)
                (values : List (Execution.ResolverValue ObjectRef)),
              VisitedFragments.ExecutableFieldsValidContext schema variableDefinitions
                original fields
              -> Execution.completeValueList schema resolvers variableValues fuel itemType
                    fields values
                  = GraphQL.Execution.completeValueList schema resolvers variableValues
                      fuel itemType
                      (fields.map VisitedFragments.expandedExecutableFieldToSpec) values
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel, itemType, fields, [], _hfields => by
        simp [Execution.completeValueList, GraphQL.Execution.completeValueList]
    | schema, resolvers, variableValues, variableDefinitions, original,
        hunique, hacyclic, hall, fuel, itemType, fields, value :: values,
        hfields => by
        simp [Execution.completeValueList, GraphQL.Execution.completeValueList,
          completeValue_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall fuel itemType fields value
            hfields,
          completeValueList_toExpandedSpec schema resolvers variableValues
            variableDefinitions original hunique hacyclic hall fuel itemType fields values
            hfields]
  termination_by _schema _resolvers _variableValues _variableDefinitions _original
      _hunique _hacyclic _hall fuel itemType _fields values _hfields =>
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
    (hinlined : selectionSetInlined selectionSet)
    : Execution.executeRootSelectionSet schema resolvers variableValues fuel
        parentType source fragments selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues fuel
          parentType source
          (Translate.reduceSelectionSet selectionSet) := by
  simp [Execution.executeRootSelectionSet,
    GraphQL.Execution.executeRootSelectionSet]
  rw [executeCollectedFields_toSpec schema resolvers variableValues fuel
    source
    (Execution.collectFields schema variableValues fragments [] parentType source
      selectionSet).groupedFields
    (collectFields_inlined schema variableValues fragments [] parentType source
      selectionSet hinlined)]
  rw [(collectFields_toSpec_of_inlined schema variableValues fragments [] parentType
    source selectionSet hinlined).1]

theorem executeRootSelectionSet_toExpandedSpec
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variableDefinitions : List VariableDefinition) (fuel : Nat)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (fragments : List FragmentDefinition) (selectionSet : List Selection)
    (hunique : GraphQL.NamedFragment.Validation.fragmentNamesUnique fragments)
    (hacyclic : GraphQL.NamedFragment.Validation.fragmentsAcyclic fragments)
    (hall
      : GraphQL.NamedFragment.Validation.allFragmentDefinitionsValid schema
          variableDefinitions fragments)
    (hvalid
      : GraphQL.NamedFragment.Validation.selectionSetValid schema variableDefinitions
          fragments parentType selectionSet)
    : Execution.executeRootSelectionSet schema resolvers variableValues fuel parentType
        source fragments selectionSet
      = GraphQL.Execution.executeRootSelectionSet schema resolvers variableValues fuel
          parentType source
          (Translate.reduceSelectionSet
            (Inline.inlineSelectionSet fragments selectionSet)) := by
  simp [Execution.executeRootSelectionSet,
    GraphQL.Execution.executeRootSelectionSet]
  rw [executeCollectedFields_toExpandedSpec schema resolvers variableValues
    variableDefinitions fragments hunique hacyclic hall fuel source
    (Execution.collectFields schema variableValues fragments [] parentType source
      selectionSet).groupedFields
    (VisitedFragments.collectFields_validContext hunique hacyclic hall variableValues
      fragments [] parentType parentType source selectionSet hunique hvalid
      (VisitedFragments.SpreadContext.root fragments selectionSet))]
  rw [GraphQL.Execution.DuplicateFields.executeCollectedFields_firstOccurrences
    schema resolvers variableValues fuel source
    (VisitedFragments.expandedExecutableGroupsToSpec
      (Execution.collectFields schema variableValues fragments [] parentType source
        selectionSet).groupedFields)
    (GraphQL.Execution.collectFields schema variableValues parentType source
      (Translate.reduceSelectionSet
        (Inline.inlineSelectionSet fragments selectionSet)))
    (VisitedFragments.collectFields_firstOccurrences variableValues hunique hacyclic hall
      parentType source selectionSet hvalid)]

theorem executeQueryWithFuel_eq_spec_of_inlined
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (hinlined : operationInlined operation)
    : Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          (Translate.reduceOperation operation) fuel source := by
  cases operation with
  | mk name operationType variableDefinitions fragmentDefinitions selectionSet =>
      simp [operationInlined] at hinlined
      rcases hinlined with ⟨hfragments, hselectionSet⟩
      subst fragmentDefinitions
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
                  fragmentDefinitions := []
                  selectionSet := selectionSet
                }
                variableValues)
              fuel schema.queryType (Execution.ResolverValue.object objectName ref)
              [] selectionSet hselectionSet]
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

theorem executeQueryWithFuel_toSpec_inlineOperation
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (fuel : Nat) (source : Execution.ResolverValue ObjectRef)
    (hvalid : GraphQL.NamedFragment.Validation.operationDefinitionValid schema operation)
    : Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
      = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
          (Translate.reduceOperation (Inline.inlineOperation operation)) fuel source := by
  cases operation with
  | mk name operationType variableDefinitions fragmentDefinitions selectionSet =>
      rcases hvalid with
        ⟨_hoperationType, _hrootComposite, _hvariables, hunique, hacyclic,
          _hfragmentsUsed, hall, _hselectionNonempty, hselectionValid,
          _hfieldsMerge, _hvariablesUsed⟩
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
            rw [executeRootSelectionSet_toExpandedSpec schema resolvers
              (Execution.coerceVariableValues
                {
                  name := name
                  variableDefinitions := variableDefinitions
                  fragmentDefinitions := fragmentDefinitions
                  selectionSet := selectionSet
                }
                variableValues)
              variableDefinitions fuel schema.queryType
              (Execution.ResolverValue.object objectName ref) fragmentDefinitions
              selectionSet hunique hacyclic hall hselectionValid]
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
  intro _hschema hvalid
  intro ObjectRef resolvers variableValues fuel source
  exact executeQueryWithFuel_toSpec_inlineOperation schema resolvers variableValues
    operation fuel source hvalid

theorem fragmentAwareExecutionEquivalentToInline_of_inlined
    (schema : Schema) (operation : Operation)
    (hinlined : operationInlined operation)
    : fragmentAwareExecutionEquivalentToInline schema operation := by
  intro _hschema _hvalid
  intro ObjectRef resolvers variableValues fuel source
  rw [inlineOperation_eq_of_inlined operation hinlined]

theorem fragmentAwareExecutionEquivalentToInline_holds
    (schema : Schema) (operation : Operation)
    : fragmentAwareExecutionEquivalentToInline schema operation := by
  intro _hschema hvalid
  intro ObjectRef resolvers variableValues fuel source
  calc
    Execution.executeQueryWithFuel schema resolvers variableValues operation fuel source
        = GraphQL.Execution.executeQueryWithFuel schema resolvers variableValues
            (Translate.reduceOperation (Inline.inlineOperation operation)) fuel source :=
      executeQueryWithFuel_toSpec_inlineOperation schema resolvers variableValues
        operation fuel source hvalid
    _ = Execution.executeQueryWithFuel schema resolvers variableValues
          (Inline.inlineOperation operation) fuel source :=
      (executeQueryWithFuel_eq_spec_of_inlined schema resolvers variableValues
        (Inline.inlineOperation operation) fuel source
        (inlineOperation_inlined operation)).symm

end Semantics
end NamedFragment
end GraphQL
