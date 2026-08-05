import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Variables

/-! Operation-level validity preservation for complete normalization. -/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem selectionSetValidInPossibleTypes_of_rootObjectPossible
    (schema : Schema) (variableDefinitions : List VariableDefinition)
    {rootType objectType : Name} {selectionSet : List Selection}
    : schema.objectType rootType
      -> objectType ∈ schema.getPossibleTypes rootType
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions rootType selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions objectType selectionSet := by
  intro hrootObject hpossible himplementation
  have hinclude :
      schema.typeIncludesObjectBool rootType objectType = true :=
    List.contains_iff_mem.mpr hpossible
  have hobjectEq : objectType = rootType :=
    object_typeIncludesObjectBool_eq_self schema hrootObject hinclude
  simpa [hobjectEq] using himplementation

theorem completeNormalizeRootSelectionSet_eq_flatten
    (schema : Schema) (variables : List BoolVar)
    (parentType : Name) (selectionSet : List Selection)
    : completeNormalizeRootSelectionSet schema variables parentType selectionSet
      = List.flatten
          ((allBoolCases variables).map
            (fun boolCase =>
              match normalizeSelectionSet schema parentType
                      (filterSelectionSetBoolCase boolCase selectionSet) with
              | [] => []
              | selection :: rest =>
                  wrapWithBoolCase boolCase (selection :: rest))) := by
  rfl

theorem flatten_map_ne_nil_of_mem_ne_nil
    {α β : Type} {items : List α} {f : α -> List β} {item : α}
    : item ∈ items -> f item ≠ [] -> List.flatten (items.map f) ≠ [] := by
  intro hmem hitem
  intro hflatten
  cases hbranch : f item with
  | nil =>
      exact hitem hbranch
  | cons selection rest =>
      have hselection :
          selection ∈ List.flatten (items.map f) := by
        rw [List.mem_flatten]
        exact ⟨f item, List.mem_map.mpr ⟨item, hmem, rfl⟩,
          by simp [hbranch]⟩
      rw [hflatten] at hselection
      cases hselection

theorem completeNormalizeRootSelectionSet_selectionSetValid
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hboolFeasibleCases
      : ∀ boolCase,
          boolCase ∈ allBoolCases (operationBoolVars operation)
          -> selectionSetBoolTypeConditionFeasibleInCase schema
              (operation.rootType schema) [(operation.rootType schema)] boolCase
              operation.selectionSet)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hfields : operationFieldsValidInPossibleTypes schema operation)
    : Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema)
        (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          (operation.rootType schema) operation.selectionSet) := by
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have himplementation :
      Validation.selectionSetValidInPossibleTypes schema
        operation.variableDefinitions (operation.rootType schema) operation.selectionSet :=
    by simpa [operationFieldsValidInPossibleTypes] using hfields
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  rw [completeNormalizeRootSelectionSet_eq_flatten schema
    (operationBoolVars operation) (operation.rootType schema) operation.selectionSet]
  exact completeNormalizeBranches_selectionSetValid schema operation hschema
    hoperation hrootObject hready himplementation hmerge
    (allBoolCases (operationBoolVars operation))
    (by intro boolCase hcase; exact hcase)
    hboolFeasibleCases

theorem completeNormalizeRootSelectionSet_selectionSetValid_of_boolTypeFeasible
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hboolFeasible : operationBoolTypeConditionFeasible schema operation)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (hfields : operationFieldsValidInPossibleTypes schema operation)
    : Validation.selectionSetValid schema operation.variableDefinitions
        (operation.rootType schema)
        (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          (operation.rootType schema) operation.selectionSet) := by
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have himplementation :
      Validation.selectionSetValidInPossibleTypes schema
        operation.variableDefinitions (operation.rootType schema) operation.selectionSet :=
    by simpa [operationFieldsValidInPossibleTypes] using hfields
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  rw [completeNormalizeRootSelectionSet_eq_flatten schema
    (operationBoolVars operation) (operation.rootType schema) operation.selectionSet]
  exact completeNormalizeBranches_selectionSetValid schema operation hschema
    hoperation hrootObject hready himplementation hmerge
    (allBoolCases (operationBoolVars operation))
    (by intro boolCase hcase; exact hcase)
    (fun _boolCase hcase =>
      operationBoolTypeConditionFeasible_inCase hboolFeasible hcase)

theorem completeNormalizeRootSelectionSet_ne_nil_of_boolTypeFeasible
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationBoolTypeConditionFeasible schema operation
      -> completeNormalizeRootSelectionSet schema
            (operationBoolVars operation) (operation.rootType schema)
            operation.selectionSet
          ≠ [] := by
  intro hschema hoperation hboolFeasible
  have hselectionSetNonempty : operation.selectionSet ≠ [] :=
    Validation.operationDefinitionValid_selectionSet_nonempty hoperation
  have hselectionSetCons :
      ∃ selection rest, operation.selectionSet = selection :: rest := by
    cases hselectionSet : operation.selectionSet with
    | nil =>
        exact False.elim (hselectionSetNonempty hselectionSet)
    | cons selection rest =>
        exact ⟨selection, rest, rfl⟩
  rcases hselectionSetCons with ⟨selection, rest, hselectionSet⟩
  have hselectionFeasible :
      selectionBoolTypeConditionFeasible schema (operation.rootType schema)
        [(operation.rootType schema)]
        (allBoolCases (operationBoolVars operation)) selection :=
    hboolFeasible selection (by rw [hselectionSet]; simp)
  rcases selectionBoolTypeConditionFeasible_exists_allowed
      hselectionFeasible with
    ⟨boolCase, hcase, hallow⟩
  have hselectionContains :
      selectionBoolTypeConditionHasFieldInCase schema (operation.rootType schema)
        [(operation.rootType schema)] boolCase selection :=
    selectionBoolTypeConditionHasFieldInCase_of_feasible schema
      (operation.rootType schema) [(operation.rootType schema)]
      (allBoolCases (operationBoolVars operation)) boolCase selection
      hselectionFeasible hcase hallow
  have hcontainsBool :
      selectionSetBoolTypeConditionHasFieldInCase schema (operation.rootType schema)
        [(operation.rootType schema)] boolCase operation.selectionSet :=
    selectionSetBoolTypeConditionHasFieldInCase_of_mem
      operation.selectionSet (by rw [hselectionSet]; simp) hselectionContains
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have hfilteredReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
      (operation.rootType schema) operation.selectionSet hready
  have hfilteredContains :
      GroundTypeNormalization.selectionSetContainsTypeConditionFeasibleField schema
        [(operation.rootType schema)]
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    selectionSetContainsTypeConditionFeasibleField_filterSelectionSetBoolCase
      schema boolCase (operation.rootType schema) [(operation.rootType schema)]
      operation.selectionSet hcontainsBool
  have hnormalizedNonempty :
      normalizeSelectionSet schema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) ≠ [] :=
    GroundTypeNormalization.normalizeSelectionSet_ne_nil_of_contains schema
      (operation.rootType schema)
      (filterSelectionSetBoolCase boolCase operation.selectionSet)
      hrootObject hfilteredReady hfilteredContains
  rw [completeNormalizeRootSelectionSet_eq_flatten schema
    (operationBoolVars operation) (operation.rootType schema) operation.selectionSet]
  apply flatten_map_ne_nil_of_mem_ne_nil hcase
  cases hnormalized
        : normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase boolCase operation.selectionSet) with
  | nil =>
      exact False.elim (hnormalizedNonempty hnormalized)
  | cons selection rest =>
      exact wrapWithBoolCase_ne_nil boolCase (selection :: rest) (by simp)

theorem completeFilteredBoolCasesFieldsCanMerge (schema : Schema) (operation : Operation)
    : Validation.operationDefinitionValid schema operation
      -> ∀ leftCase,
          leftCase ∈ allBoolCases (operationBoolVars operation)
          -> ∀ rightCase,
              rightCase ∈ allBoolCases (operationBoolVars operation)
              -> FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
                  (filterSelectionSetBoolCase leftCase operation.selectionSet
                    ++ filterSelectionSetBoolCase rightCase operation.selectionSet) := by
  intro hoperation leftCase _hleftCase rightCase _hrightCase
  have hsourceMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  exact fieldsInSetCanMerge_filterSelectionSetBoolCase_pair schema
    leftCase rightCase
    (GroundTypeNormalization.fieldsInSetCanMerge_self schema
      (operation.rootType schema) operation.selectionSet hsourceMerge)

/-
Operation-level branch-merge bridge used by `completeNormalizeOperation_valid`.
The public BoolCase/type-condition feasibility assumption supplies both the
branch-specific feasible children and the root nonemptiness witness; no separate
complete-BoolCase survival predicate is needed.
-/
theorem completeNormalizedBoolCaseBranchesFieldsCanMerge_of_boolTypeFeasible
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationFieldsValidInPossibleTypes schema operation
      -> operationBoolTypeConditionFeasible schema operation
      -> ∀ leftCase,
          leftCase ∈ allBoolCases (operationBoolVars operation)
          -> ∀ rightCase,
              rightCase ∈ allBoolCases (operationBoolVars operation)
              -> FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
                  (normalizeSelectionSet schema (operation.rootType schema)
                      (filterSelectionSetBoolCase leftCase operation.selectionSet)
                    ++ normalizeSelectionSet schema (operation.rootType schema)
                        (filterSelectionSetBoolCase rightCase
                          operation.selectionSet)) := by
  intro hschema hoperation hfields hboolFeasible leftCase hleftCase
    rightCase hrightCase
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have himplementation :
      Validation.selectionSetValidInPossibleTypes schema
        operation.variableDefinitions (operation.rootType schema) operation.selectionSet :=
    by simpa [operationFieldsValidInPossibleTypes] using hfields
  have hleftReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema leftCase
      (operation.rootType schema) operation.selectionSet hready
  have hrightReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    filterSelectionSetBoolCase_selectionSetSemanticsReady schema rightCase
      (operation.rootType schema) operation.selectionSet hready
  have hsourceMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  have hleftMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema leftCase
      hsourceMerge
  have hrightMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase schema rightCase
      hsourceMerge
  have hpairMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        (filterSelectionSetBoolCase leftCase operation.selectionSet
          ++ filterSelectionSetBoolCase rightCase
            operation.selectionSet) :=
    completeFilteredBoolCasesFieldsCanMerge schema operation hoperation
      leftCase hleftCase rightCase hrightCase
  have hleftBoolFeasible :
      selectionSetBoolTypeConditionFeasibleInCase schema (operation.rootType schema)
        [(operation.rootType schema)] leftCase operation.selectionSet :=
    operationBoolTypeConditionFeasible_inCase hboolFeasible hleftCase
  have hrightBoolFeasible :
      selectionSetBoolTypeConditionFeasibleInCase schema (operation.rootType schema)
        [(operation.rootType schema)] rightCase operation.selectionSet :=
    operationBoolTypeConditionFeasible_inCase hboolFeasible hrightCase
  have hleftSource :
      selectionSetFilteredCurrentSourceValid schema operation.variableDefinitions
        (operation.rootType schema)
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema leftCase (operation.rootType schema)
      hrootObject operation.selectionSet himplementation
  have hrightSource :
      selectionSetFilteredCurrentSourceValid schema operation.variableDefinitions
        (operation.rootType schema)
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    selectionSetFilteredCurrentSourceValid_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema rightCase (operation.rootType schema)
      hrootObject operation.selectionSet himplementation
  have hleftReturnLookup :
      selectionSetFilteredReturnLookupValid schema (operation.rootType schema)
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema leftCase (operation.rootType schema)
      hrootObject operation.selectionSet himplementation
  have hrightReturnLookup :
      selectionSetFilteredReturnLookupValid schema (operation.rootType schema)
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    selectionSetFilteredReturnLookupValid_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema rightCase (operation.rootType schema)
      hrootObject operation.selectionSet himplementation
  have hleftFeasible :
      selectionSetTypeConditionFeasible schema (operation.rootType schema)
        [(operation.rootType schema)]
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    selectionSetTypeConditionFeasible_filterSelectionSetBoolCase schema
      leftCase (operation.rootType schema) [(operation.rootType schema)] operation.selectionSet
      hleftBoolFeasible
  have hrightFeasible :
      selectionSetTypeConditionFeasible schema (operation.rootType schema)
        [(operation.rootType schema)]
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    selectionSetTypeConditionFeasible_filterSelectionSetBoolCase schema
      rightCase (operation.rootType schema) [(operation.rootType schema)] operation.selectionSet
      hrightBoolFeasible
  have hleftNonempty :
      selectionSetFilteredCompositeChildrenNonempty schema (operation.rootType schema)
        [(operation.rootType schema)]
        (filterSelectionSetBoolCase leftCase operation.selectionSet) :=
    selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema leftCase (operation.rootType schema)
      [(operation.rootType schema)] hrootObject operation.selectionSet himplementation
      hleftBoolFeasible
  have hrightNonempty :
      selectionSetFilteredCompositeChildrenNonempty schema (operation.rootType schema)
        [(operation.rootType schema)]
        (filterSelectionSetBoolCase rightCase operation.selectionSet) :=
    selectionSetFilteredCompositeChildrenNonempty_filterSelectionSetBoolCase
      schema operation.variableDefinitions hschema rightCase (operation.rootType schema)
      [(operation.rootType schema)] hrootObject operation.selectionSet himplementation
      hrightBoolFeasible
  exact
    normalizeSelectionSets_fieldsInSetCanMerge_filteredCurrentSource_anyParent schema
      operation.variableDefinitions hschema (operation.rootType schema)
      (filterSelectionSetBoolCase leftCase operation.selectionSet)
      (filterSelectionSetBoolCase rightCase operation.selectionSet)
      hrootObject hleftReady hrightReady hleftSource hrightSource
      hleftReturnLookup hrightReturnLookup hleftMerge hrightMerge hpairMerge
      (filterSelectionSetBoolCase_directiveFree schema leftCase
        operation.selectionSet)
      (filterSelectionSetBoolCase_directiveFree schema rightCase
        operation.selectionSet)
      hleftFeasible hrightFeasible hleftNonempty hrightNonempty
      (operation.rootType schema)

theorem completeNormalizeOperation_valid (schema : Schema) (operation : Operation)
    : NormalForm.completeNormalizeOperationValid schema operation := by
  intro hschema hoperation hfields hboolFeasible
  have hnormalizedNonempty :
      completeNormalizeRootSelectionSet schema
        (operationBoolVars operation) (operation.rootType schema)
        operation.selectionSet ≠ [] :=
    completeNormalizeRootSelectionSet_ne_nil_of_boolTypeFeasible schema
      operation hschema hoperation hboolFeasible
  have hbranchPairs :
      ∀ leftCase, leftCase ∈ allBoolCases (operationBoolVars operation) ->
        ∀ rightCase, rightCase ∈ allBoolCases (operationBoolVars operation) ->
          FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
            (normalizeSelectionSet schema (operation.rootType schema)
                (filterSelectionSetBoolCase leftCase operation.selectionSet)
              ++
              normalizeSelectionSet schema (operation.rootType schema)
                (filterSelectionSetBoolCase rightCase operation.selectionSet)) :=
    completeNormalizedBoolCaseBranchesFieldsCanMerge_of_boolTypeFeasible
      schema operation hschema hoperation hfields hboolFeasible
  have hnormalizedMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        (completeNormalizeRootSelectionSet schema
          (operationBoolVars operation) (operation.rootType schema)
          operation.selectionSet) :=
    completeNormalizeRootSelectionSet_fieldsInSetCanMerge_of_branchPairs
      schema (operationBoolVars operation) (operation.rootType schema)
      operation.selectionSet hbranchPairs
  have hvariablesUsed :
      Validation.operationVariablesUsed
        (completeNormalizeOperation schema operation) :=
    completeNormalizeOperation_operationVariablesUsed schema operation
      hschema hoperation hboolFeasible
  exact ⟨
    by simp [completeNormalizeOperation,
      Validation.operationDefinitionValid_rootType_eq hoperation],
    by
      simpa [completeNormalizeOperation, Operation.rootType,
        OperationType.rootType] using
        (Validation.operationDefinitionValid_rootTypeComposite
          (operation := operation) hoperation),
    by
      simpa [completeNormalizeOperation] using
        (Validation.operationDefinitionValid_variableDefinitionsValid
          (operation := operation) hoperation),
    by
      simpa [completeNormalizeOperation] using hnormalizedNonempty,
    by
      simpa [completeNormalizeOperation, Operation.rootType,
        OperationType.rootType] using
        completeNormalizeRootSelectionSet_selectionSetValid_of_boolTypeFeasible
          schema operation hschema hboolFeasible hoperation hfields,
    by
      simpa [completeNormalizeOperation, Operation.rootType,
        OperationType.rootType] using hnormalizedMerge,
    hvariablesUsed⟩

end CompleteNormalization

end NormalForm

end GraphQL
