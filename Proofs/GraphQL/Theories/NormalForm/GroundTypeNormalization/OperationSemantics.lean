import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.SelectionSetSemantics
import Proofs.GraphQL.Theories.NormalForm.Shared.Execution

/-!
Operation-level semantic bridge facts for ground-type normalization.

This module lifts the selection-set semantic preservation theorem to operation-level
resolver-parametric equivalence.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectRef : Type}

theorem normalizeOperation_name (schema : Schema) (operation : Operation)
    : (normalizeOperation schema operation).name = operation.name := by
  rfl

theorem normalizeOperation_rootType (schema : Schema) (operation : Operation)
    : ((normalizeOperation schema operation).rootType schema)
      = (operation.rootType schema) := by
  rfl

theorem normalizeOperation_variableDefinitions (schema : Schema) (operation : Operation)
    : (normalizeOperation schema operation).variableDefinitions
      = operation.variableDefinitions := by
  rfl

theorem normalizeOperation_selectionSet (schema : Schema) (operation : Operation)
    : (normalizeOperation schema operation).selectionSet
      = normalizeSelectionSet schema (operation.rootType schema)
          operation.selectionSet := by
  rfl

theorem rootSourceAppliesBool_normalizeOperation (schema : Schema)
    (operation : Operation) (source : Execution.ResolverValue ObjectRef)
    : Execution.rootSourceAppliesBool schema (normalizeOperation schema operation) source
      = Execution.rootSourceAppliesBool schema operation source := by
  rw [Execution.rootSourceAppliesBool]
  rw [Execution.rootSourceAppliesBool]
  rw [normalizeOperation_rootType schema operation]

theorem executeQuery_normalizedOperation_of_rootSource_not_apply
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (operation : Operation) (depth : Nat)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.rootSourceAppliesBool schema operation source = false
      -> Execution.executeQueryWithFuel schema resolvers variableValues operation
            depth source
          = Execution.executeQueryWithFuel schema resolvers variableValues
              (normalizeOperation schema operation) depth source := by
  intro hroot
  have hnormalizedRoot :
      Execution.rootSourceAppliesBool schema (normalizeOperation schema operation)
          source =
        false := by
    rw [rootSourceAppliesBool_normalizeOperation schema operation source]
    exact hroot
  simp [Execution.executeQueryWithFuel, hroot, hnormalizedRoot]

theorem groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet
    (schema : Schema) (operation : Operation)
    : (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
          variableValues depth (source : Execution.ResolverValue ObjectRef),
        Execution.rootSourceAppliesBool schema operation source = true
        -> Execution.executeSelectionSet schema resolvers variableValues
              depth (operation.rootType schema) source operation.selectionSet
            = Execution.executeSelectionSet schema resolvers variableValues
                depth ((normalizeOperation schema operation).rootType schema) source
                (normalizeOperation schema operation).selectionSet)
      -> operationsEquivalent schema operation (normalizeOperation schema operation) := by
  intro hselection
  unfold operationsEquivalent
  intro ObjectRef resolvers variableValues depth source
  by_cases hroot :
      Execution.rootSourceAppliesBool schema operation source = true
  · have hnormalizedRoot :
        Execution.rootSourceAppliesBool schema (normalizeOperation schema operation)
            source =
          true := by
      rw [rootSourceAppliesBool_normalizeOperation schema operation source]
      exact hroot
    simp [Execution.executeQueryWithFuel, hroot, hnormalizedRoot]
    exact congrArg
      (fun (completed : Execution.Result (List (Name × Execution.ResponseValue))) =>
        match completed with
        | Except.error errors =>
            ({ data := Execution.ResponseValue.null, errors := errors } :
              Execution.Response)
        | Except.ok (fields, errors) =>
            ({ data := Execution.ResponseValue.object fields, errors := errors } :
              Execution.Response))
      (by
        simpa [Execution.executeSelectionSet, Execution.coerceVariableValues,
          normalizeOperation_variableDefinitions] using
          hselection resolvers
            (Execution.coerceVariableValues operation variableValues)
            depth source hroot)
  · have hrootFalse :
        Execution.rootSourceAppliesBool schema operation source = false := by
      cases hmatch : Execution.rootSourceAppliesBool schema operation source
      · rfl
      · contradiction
    exact executeQuery_normalizedOperation_of_rootSource_not_apply schema
      resolvers variableValues operation depth source hrootFalse

theorem normalizeOperation_executeQuery (schema : Schema) (operation : Operation)
    : (∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
          variableValues depth (source : Execution.ResolverValue ObjectRef),
        Execution.rootSourceAppliesBool schema operation source = true
        -> Execution.executeSelectionSet schema resolvers variableValues
              depth (operation.rootType schema) source operation.selectionSet
            = Execution.executeSelectionSet schema resolvers variableValues
                depth ((normalizeOperation schema operation).rootType schema) source
                (normalizeOperation schema operation).selectionSet)
      -> operationsEquivalent schema operation (normalizeOperation schema operation) := by
  exact groundTypeNormalFormSemanticsPreserved_of_executeSelectionSet schema
    operation

theorem groundTypeNormalFormSemanticsPreservation_of_selectionSet
    (schema : Schema) (operation : Operation)
    : (SchemaWellFormedness.schemaWellFormed schema
        -> Validation.operationDefinitionValid schema operation
        -> operationDirectiveFree operation
        -> ∀ {ObjectRef : Type} (resolvers : Execution.Resolvers ObjectRef)
              variableValues depth
              (source : Execution.ResolverValue ObjectRef),
            Execution.rootSourceAppliesBool schema operation source = true
            -> Execution.executeSelectionSet schema resolvers variableValues
                  depth (operation.rootType schema) source operation.selectionSet
                = Execution.executeSelectionSet schema resolvers variableValues
                    depth ((normalizeOperation schema operation).rootType schema) source
                    (normalizeOperation schema operation).selectionSet)
      -> NormalForm.groundTypeNormalFormSemanticsPreservation schema operation := by
  intro hselection hschema hvalid hfree
  exact normalizeOperation_executeQuery schema operation
    (hselection hschema hvalid hfree)

theorem groundTypeNormalFormSemanticsPreservation
    (schema : Schema) (operation : Operation)
    : NormalForm.groundTypeNormalFormSemanticsPreservation schema operation := by
  intro hschema hvalid hfree
  apply normalizeOperation_executeQuery schema operation
  intro ObjectRef resolvers variableValues depth source hroot
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema (operation.rootType schema) = true :=
    objectTypeNameBool_eq_true_of_objectType schema hrootObject
  have hsource :
      ∃ runtimeType ref,
        source = Execution.ResolverValue.object runtimeType ref
          ∧ schema.typeIncludesObjectBool (operation.rootType schema) runtimeType =
            true :=
    rootSourceAppliesBool_true_object schema operation source hroot
  have hselectionValid :
      Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema) operation.selectionSet :=
    Validation.operationDefinitionValid_selectionSetValid hvalid
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema hrootObject
      operation.selectionSet hselectionValid
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hpreserved :=
    normalizeSelectionSet_executeSelectionSet schema resolvers variableValues
      hschema depth (operation.rootType schema) source operation.selectionSet hobject
      hsource hfree hready hmerge
  simpa [normalizeOperation, Operation.rootType, OperationType.rootType] using
    hpreserved.symm

end GroundTypeNormalization

end NormalForm

end GraphQL
