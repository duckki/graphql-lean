import Proofs.GraphQL.Theories.ConditionTree.Reduce.Semantics

/-! Public soundness witnesses for condition-tree reduction. -/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution
open NormalForm.GroundTypeNormalization
open NormalForm.GroundTypeNormalization.ReorderingSoundness
open ExecutionEquivalence

@[simp]
theorem reduceOperation_rootType (schema : Schema) (operation : Operation)
    : (reduceOperation schema operation).rootType schema = operation.rootType schema :=
  rfl

@[simp]
theorem reduceOperation_coerceVariableValues
    (schema : Schema) (operation : Operation) (variableValues : VariableValues)
    : coerceVariableValues (reduceOperation schema operation) variableValues
      = coerceVariableValues operation variableValues :=
  rfl

@[simp]
theorem reduceOperation_rootSourceAppliesBool
    {ObjectRef : Type} (schema : Schema) (operation : Operation)
    (source : ResolverValue ObjectRef)
    : rootSourceAppliesBool schema (reduceOperation schema operation) source
      = rootSourceAppliesBool schema operation source := by
  simp [rootSourceAppliesBool]

theorem reduction_sound (schema : Schema) (parentType : Name)
    (selectionSet : List Selection)
    : ReductionSound schema parentType selectionSet := by
  intro variableDefinitions hschema hvalid hmerge ObjectRef resolvers
    variableValues fuel runtimeType ref hinclude
  have hpossible : runtimeType ∈ schema.getPossibleTypes parentType :=
    List.contains_iff_mem.mp hinclude
  have hobject : schema.objectType runtimeType :=
    SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects hschema
      parentType runtimeType hpossible
  let units : List ReductionUnit := [.reduce parentType [] selectionSet]
  have hready : NormalForm.selectionSetSemanticsReady schema runtimeType
      selectionSet :=
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_possibleObject schema
      variableDefinitions parentType runtimeType hschema hpossible selectionSet hvalid
  have happlicable : ReductionUnit.AllRuntimeApplicable schema variableValues
      runtimeType units := by
    intro unit hunit
    have hunitEq : unit = .reduce parentType [] selectionSet :=
      List.mem_singleton.mp hunit
    subst unit
    simp only [ReductionUnit.RuntimeApplicable]
    constructor
    · rfl
    · exact hinclude
  have hparentRuntime :
      Algorithms.ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
        runtimeType parentType := by
    exact hinclude
  have hscoped :=
    Algorithms.ExecutionUngroupedUncached.Eager.collectFields_runtimeScopedBy_of_selectionSetValid
      schema variableDefinitions variableValues runtimeType parentType runtimeType ref
      selectionSet hparentRuntime hvalid
  have hcompatible :=
    Algorithms.ExecutionUngroupedUncached.Eager.collectFields_fieldCompatible_of_canMerge_runtimeScoped
      schema variableValues runtimeType parentType runtimeType
      (.object runtimeType ref) selectionSet hmerge hscoped
  have hargumentsAndChildrenNodup :=
    Algorithms.ExecutionUngroupedUncached.Eager.collectFields_argumentsAndChildrenNodup
      schema variableValues runtimeType (.object runtimeType ref) selectionSet
      (Algorithms.ExecutionUngroupedUncached.Eager.selectionSetArgumentsNodup_of_selectionSetValid
        hvalid)
  have hgroupScoped : ∀ {responseName fields},
      (responseName, fields) ∈ collectFields schema variableValues runtimeType
          (.object runtimeType ref) selectionSet
      -> Algorithms.ExecutionUngroupedUncached.Eager.ExecutableFieldsRuntimeScopedBy schema
          runtimeType (FieldMerge.collectFields schema parentType selectionSet)
          fields := by
    intro responseName fields hgroup field hfield
    exact hscoped field
      (Algorithms.ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_of_group_mem
        hgroup hfield)
  have hresult := reductionUnits_execute_equivalent schema resolvers variableValues
    hschema fuel parentType runtimeType ref units (reduce schema parentType selectionSet)
    selectionSet hobject hinclude hready hcompatible hargumentsAndChildrenNodup.1
    hargumentsAndChildrenNodup.2 hgroupScoped hmerge happlicable
    (by simp [units, ReductionUnit.outputSelectionSet, reduce])
    (by simp [units, ReductionUnit.inputSelectionSet, ReductionUnit.selectionSet])
  exact responseEquivalent_of_selectionSetResultEquivalent
    (selectionSetResultEquivalent_symm hresult)

theorem reduceOperation_sound (schema : Schema) (operation : Operation)
    : ReduceOperationSound schema operation := by
  intro ObjectRef resolvers variableValues fuel source hschema hoperation
  let reduced := reduceOperation schema operation
  have hrootType : reduced.rootType schema = operation.rootType schema := by
    simp [reduced]
  have hcoerce : coerceVariableValues reduced variableValues
      = coerceVariableValues operation variableValues := by
    simp [reduced]
  have hrootReduced : rootSourceAppliesBool schema reduced source
      = rootSourceAppliesBool schema operation source := by
    simp [reduced]
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simp only [executeQueryWithFuel]
      rw [hroot, hrootReduced, hroot]
      exact Response.semanticEquivalent_refl _
  | true =>
      obtain ⟨runtimeType, ref, rfl, hinclude⟩ :=
        NormalForm.GroundTypeNormalization.rootSourceAppliesBool_true_object
          schema operation source hroot
      have hrootObject : schema.objectType (operation.rootType schema) :=
        NormalForm.CompleteNormalization.operation_root_object_of_valid
          hschema hoperation
      have hruntime : runtimeType = operation.rootType schema :=
        object_typeIncludesObjectBool_eq_self schema hrootObject hinclude
      subst runtimeType
      let coercedVariableValues := coerceVariableValues operation variableValues
      have hselection := reduction_sound schema (operation.rootType schema)
        operation.selectionSet operation.variableDefinitions hschema
        (Validation.operationDefinitionValid_selectionSetValid hoperation)
        (Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation)
        resolvers coercedVariableValues fuel (operation.rootType schema) ref hinclude
      simp only [executeQueryWithFuel]
      rw [hroot, hrootReduced, hroot]
      simp only [if_true]
      rw [hcoerce, hrootType]
      simpa [reduced, reduceOperation, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet, coercedVariableValues] using hselection

end ConditionTree
end GraphQL
