import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Variables

/-! Variable-use preservation through Boolean filtering. -/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

mutual
  theorem inputValueBooleanVariables_eq_variables
      : ∀ value, inputValueBooleanVariables value = Validation.inputValueVariables value
    | .null
    | .int _
    | .float _
    | .string _
    | .boolean _
    | .enum _
    | .variable _ => rfl
    | .list values => inputValuesBooleanVariables_eq_variables values
    | .object fields => inputObjectFieldsBooleanVariables_eq_variables fields

  theorem inputValuesBooleanVariables_eq_variables
      : ∀ values,
          inputValuesBooleanVariables values = Validation.inputValuesVariables values
    | [] => rfl
    | value :: rest => by
        simp only [inputValuesBooleanVariables,
          Validation.inputValuesVariables,
          inputValueBooleanVariables_eq_variables value,
          inputValuesBooleanVariables_eq_variables rest]

  theorem inputObjectFieldsBooleanVariables_eq_variables
      : ∀ fields,
          inputObjectFieldsBooleanVariables fields
          = Validation.inputObjectFieldsVariables fields
    | [] => rfl
    | (name, value) :: rest => by
        simp only [inputObjectFieldsBooleanVariables,
          Validation.inputObjectFieldsVariables,
          inputValueBooleanVariables_eq_variables value,
          inputObjectFieldsBooleanVariables_eq_variables rest]
end

theorem directiveBooleanVariables_eq_variables (directive : DirectiveApplication)
    : directiveBooleanVariables directive = Validation.directiveVariables directive := by
  cases directive <;>
    simp [directiveBooleanVariables, Validation.directiveVariables,
      inputValueBooleanVariables_eq_variables]

theorem directivesBooleanVariables_eq_variables
    : ∀ directives,
        directivesBooleanVariables directives = Validation.directivesVariables directives
  | [] => rfl
  | directive :: rest => by
      simp [directivesBooleanVariables, Validation.directivesVariables,
        directiveBooleanVariables_eq_variables,
        directivesBooleanVariables_eq_variables rest]

theorem selectionSetVariables_exists_selection {variableName : Name}
    : ∀ selectionSet,
        variableName ∈ Validation.selectionSetVariables selectionSet
        -> ∃ selection,
            selection ∈ selectionSet
            ∧ variableName ∈ Validation.selectionVariables selection
  | [], hvariable => by
      cases hvariable
  | selection :: rest, hvariable => by
      simp only [Validation.selectionSetVariables, List.mem_append] at hvariable
      rcases hvariable with hhead | htail
      · exact ⟨selection, by simp, hhead⟩
      · rcases selectionSetVariables_exists_selection rest htail with
          ⟨candidate, hcandidate, hcandidateVariable⟩
        exact ⟨candidate, List.mem_cons_of_mem selection hcandidate,
          hcandidateVariable⟩

private theorem selection_size_pos_for_variableFiltering (selection : Selection)
    : 0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons_for_variableFiltering
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left
    (selection_size_pos_for_variableFiltering selection)

mutual
  theorem selectionVariables_filterSelectionSetBoolCase_of_feasible
      (schema : Schema) (variableName : Name)
      (parentType : Name) (typeConditions : List Name)
      (boolCases : List BoolCase)
      : ∀ selection,
          selectionBoolTypeConditionFeasible schema parentType typeConditions
            boolCases selection
          -> variableName ∈ Validation.selectionVariables selection
          -> variableName ∉ selectionBooleanVariables selection
          -> ∃ boolCase,
              boolCase ∈ boolCases
              ∧ variableName
                ∈ Validation.selectionSetVariables
                    (filterSelectionSetBoolCase boolCase [selection])
    | .field responseName fieldName arguments directives selectionSet,
      hfeasible, hvariable, hnotBoolean => by
        have hvariableParts :
            variableName ∈ Validation.argumentsVariables arguments
            ∨ variableName ∈ Validation.directivesVariables directives
            ∨ variableName
                ∈ Validation.selectionSetVariables selectionSet := by
          simpa [Validation.selectionVariables] using hvariable
        rcases hvariableParts with harguments | hdirectives | hchildren
        · rcases selectionBoolTypeConditionFeasible_exists_allowed hfeasible with
            ⟨boolCase, hcase, hallow⟩
          have hallowDirectives :
              directivesAllowIn boolCase directives = true := by
            simpa [selectionAllowsIn] using hallow
          refine ⟨boolCase, hcase, ?_⟩
          cases hsource : selectionSet with
          | nil =>
              subst selectionSet
              simp [filterSelectionSetBoolCase, hallowDirectives,
                Validation.selectionSetVariables, Validation.selectionVariables,
                Validation.directivesVariables, harguments]
          | cons sourceChild sourceChildren =>
              subst selectionSet
              cases hfiltered :
                  filterSelectionSetBoolCase boolCase
                    (sourceChild :: sourceChildren) <;>
                simp [filterSelectionSetBoolCase, hallowDirectives,
                  hfiltered, Validation.selectionSetVariables,
                  Validation.selectionVariables,
                  Validation.directivesVariables, harguments]
        · have hdirectiveBoolean :
              variableName ∈ directivesBooleanVariables directives := by
            rw [directivesBooleanVariables_eq_variables]
            exact hdirectives
          exact False.elim
            (hnotBoolean
              (by
                simp [selectionBooleanVariables, hdirectiveBoolean]))
        · have hchildrenNotBoolean :
              variableName ∉ selectionSetBooleanVariables selectionSet := by
            intro hchildBoolean
            exact hnotBoolean
              (by
                simp [selectionBooleanVariables, hchildBoolean])
          have hselectionSetNonempty : selectionSet ≠ [] := by
            intro hnil
            subst selectionSet
            cases hchildren
          have hselectionSetCons :
              ∃ child children, selectionSet = child :: children := by
            cases hsource : selectionSet with
            | nil =>
                exact False.elim (hselectionSetNonempty hsource)
            | cons child children =>
                exact ⟨child, children, rfl⟩
          rcases hselectionSetCons with
            ⟨sourceChild, sourceChildren, hsource⟩
          subst selectionSet
          simp only [selectionBoolTypeConditionFeasible] at hfeasible
          rcases hfeasible.2.2 with hnil | hchildFeasible
          · exact False.elim (hselectionSetNonempty hnil)
          · cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [hlookup] at hchildFeasible
            | some fieldDefinition =>
                simp only [hlookup] at hchildFeasible
                let allowedCases :=
                  boolCases.filter
                    (fun candidate =>
                      directivesAllowIn candidate directives)
                rcases List.exists_mem_of_ne_nil _ hchildFeasible.1 with
                  ⟨objectType, hobjectType⟩
                rcases
                    selectionSetVariables_filterSelectionSetBoolCase_of_feasible
                      schema variableName
                      objectType [objectType] allowedCases
                      (sourceChild :: sourceChildren)
                      (fun candidate hcandidate =>
                        selectionSetBoolTypeConditionFeasible_selection
                          (hchildFeasible.2 objectType hobjectType) hcandidate)
                      hchildren
                      hchildrenNotBoolean with
                  ⟨boolCase, hallowedCase, hfilteredVariable⟩
                have hallowedParts := List.mem_filter.mp hallowedCase
                have hfilteredNonempty :
                    filterSelectionSetBoolCase boolCase
                        (sourceChild :: sourceChildren) ≠ [] := by
                  intro hnil
                  rw [hnil] at hfilteredVariable
                  cases hfilteredVariable
                cases hfiltered :
                    filterSelectionSetBoolCase boolCase
                      (sourceChild :: sourceChildren) with
                | nil =>
                    exact False.elim (hfilteredNonempty hfiltered)
                | cons child children =>
                    refine ⟨boolCase, hallowedParts.1, ?_⟩
                    simp [filterSelectionSetBoolCase, hallowedParts.2,
                      hfiltered, Validation.selectionSetVariables,
                      Validation.selectionVariables]
                    exact Or.inr (Or.inr (by
                      simpa [hfiltered, Validation.selectionSetVariables] using
                        hfilteredVariable))
    | .inlineFragment none directives selectionSet,
      hfeasible, hvariable, hnotBoolean => by
        simp only [Validation.selectionVariables, List.mem_append] at hvariable
        rcases hvariable with hdirectives | hchildren
        · have hdirectiveBoolean :
              variableName ∈ directivesBooleanVariables directives := by
            rw [directivesBooleanVariables_eq_variables]
            exact hdirectives
          exact False.elim
            (hnotBoolean
              (by simp [selectionBooleanVariables, hdirectiveBoolean]))
        · have hchildrenNotBoolean :
              variableName ∉ selectionSetBooleanVariables selectionSet := by
            intro hchildBoolean
            exact hnotBoolean
              (by simp [selectionBooleanVariables, hchildBoolean])
          simp only [selectionBoolTypeConditionFeasible] at hfeasible
          let allowedCases :=
            boolCases.filter
              (fun candidate => directivesAllowIn candidate directives)
          rcases
              selectionSetVariables_filterSelectionSetBoolCase_of_feasible
                schema variableName parentType typeConditions allowedCases
                selectionSet
                (fun candidate hcandidate =>
                  selectionSetBoolTypeConditionFeasible_selection
                    hfeasible.2 hcandidate)
                hchildren hchildrenNotBoolean with
            ⟨boolCase, hallowedCase, hfilteredVariable⟩
          have hallowedParts := List.mem_filter.mp hallowedCase
          have hfilteredNonempty :
              filterSelectionSetBoolCase boolCase selectionSet ≠ [] := by
            intro hnil
            rw [hnil] at hfilteredVariable
            cases hfilteredVariable
          cases hfiltered :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              exact False.elim (hfilteredNonempty hfiltered)
          | cons child children =>
              refine ⟨boolCase, hallowedParts.1, ?_⟩
              simp [filterSelectionSetBoolCase, hallowedParts.2, hfiltered,
                Validation.selectionSetVariables,
                Validation.selectionVariables,
                Validation.directivesVariables]
              simpa [hfiltered, Validation.selectionSetVariables] using
                hfilteredVariable
    | .inlineFragment (some typeCondition) directives selectionSet,
      hfeasible, hvariable, hnotBoolean => by
        simp only [Validation.selectionVariables, List.mem_append] at hvariable
        rcases hvariable with hdirectives | hchildren
        · have hdirectiveBoolean :
              variableName ∈ directivesBooleanVariables directives := by
            rw [directivesBooleanVariables_eq_variables]
            exact hdirectives
          exact False.elim
            (hnotBoolean
              (by simp [selectionBooleanVariables, hdirectiveBoolean]))
        · have hchildrenNotBoolean :
              variableName ∉ selectionSetBooleanVariables selectionSet := by
            intro hchildBoolean
            exact hnotBoolean
              (by simp [selectionBooleanVariables, hchildBoolean])
          simp only [selectionBoolTypeConditionFeasible] at hfeasible
          let allowedCases :=
            boolCases.filter
              (fun candidate => directivesAllowIn candidate directives)
          rcases
              selectionSetVariables_filterSelectionSetBoolCase_of_feasible
                schema variableName parentType
                (typeCondition :: typeConditions) allowedCases
                selectionSet
                (fun candidate hcandidate =>
                  selectionSetBoolTypeConditionFeasible_selection
                    hfeasible.2 hcandidate)
                hchildren hchildrenNotBoolean with
            ⟨boolCase, hallowedCase, hfilteredVariable⟩
          have hallowedParts := List.mem_filter.mp hallowedCase
          have hfilteredNonempty :
              filterSelectionSetBoolCase boolCase selectionSet ≠ [] := by
            intro hnil
            rw [hnil] at hfilteredVariable
            cases hfilteredVariable
          cases hfiltered :
              filterSelectionSetBoolCase boolCase selectionSet with
          | nil =>
              exact False.elim (hfilteredNonempty hfiltered)
          | cons child children =>
              refine ⟨boolCase, hallowedParts.1, ?_⟩
              simp [filterSelectionSetBoolCase, hallowedParts.2, hfiltered,
                Validation.selectionSetVariables,
                Validation.selectionVariables,
                Validation.directivesVariables]
              simpa [hfiltered, Validation.selectionSetVariables] using
                hfilteredVariable
  termination_by selection => 2 * selection.size
  decreasing_by
    all_goals
      simp_all [Selection.size, SelectionSet.size]
      omega

  theorem selectionSetVariables_filterSelectionSetBoolCase_of_feasible
      (schema : Schema) (variableName : Name)
      (parentType : Name) (typeConditions : List Name)
      (boolCases : List BoolCase)
      : ∀ selectionSet,
          (∀ selection,
            selection ∈ selectionSet
            -> selectionBoolTypeConditionFeasible schema parentType
                typeConditions boolCases selection)
          -> variableName ∈ Validation.selectionSetVariables selectionSet
          -> variableName ∉ selectionSetBooleanVariables selectionSet
          -> ∃ boolCase,
              boolCase ∈ boolCases
              ∧ variableName
                ∈ Validation.selectionSetVariables
                    (filterSelectionSetBoolCase boolCase selectionSet)
    | [], _hall, hvariable, _hnotBoolean => by
        cases hvariable
    | selection :: rest, hall, hvariable, hnotBoolean => by
        simp only [Validation.selectionSetVariables, List.mem_append] at hvariable
        simp only [selectionSetBooleanVariables, List.mem_append] at hnotBoolean
        rcases hvariable with hheadVariable | htailVariable
        · have hheadNotBoolean :
              variableName ∉ selectionBooleanVariables selection := by
            intro hheadBoolean
            exact hnotBoolean (Or.inl hheadBoolean)
          rcases
              selectionVariables_filterSelectionSetBoolCase_of_feasible
                schema variableName parentType typeConditions boolCases selection
                (hall selection (by simp)) hheadVariable hheadNotBoolean with
            ⟨boolCase, hcase, hfilteredVariable⟩
          refine ⟨boolCase, hcase, ?_⟩
          rw [filterSelectionSetBoolCase_cons]
          rw [GroundTypeNormalization.selectionSetVariables_append]
          exact List.mem_append_left _ hfilteredVariable
        · have htailNotBoolean :
              variableName ∉ selectionSetBooleanVariables rest := by
            intro htailBoolean
            exact hnotBoolean (Or.inr htailBoolean)
          rcases
              selectionSetVariables_filterSelectionSetBoolCase_of_feasible
                schema variableName parentType typeConditions boolCases rest
                (fun candidate hcandidate =>
                  hall candidate
                    (List.mem_cons_of_mem selection hcandidate))
                htailVariable htailNotBoolean with
            ⟨boolCase, hcase, hfilteredVariable⟩
          refine ⟨boolCase, hcase, ?_⟩
          rw [filterSelectionSetBoolCase_cons]
          rw [GroundTypeNormalization.selectionSetVariables_append]
          exact List.mem_append_right _ hfilteredVariable
  termination_by selectionSet => 2 * SelectionSet.size selectionSet + 1
  decreasing_by
    all_goals
      have htail :=
        selectionSet_size_tail_lt_cons_for_variableFiltering selection rest
      simp [SelectionSet.size] at htail ⊢
      omega
end

theorem selectionSetVariables_wrapWithBoolCase_of_body (variableName : Name)
    : ∀ boolCase selectionSet,
        variableName ∈ Validation.selectionSetVariables selectionSet
        -> variableName
            ∈ Validation.selectionSetVariables (wrapWithBoolCase boolCase selectionSet)
  | [], selectionSet, hvariable => by
      simpa [wrapWithBoolCase] using hvariable
  | (caseVariable, value) :: rest, selectionSet, hvariable => by
      simp only [wrapWithBoolCase, Validation.selectionSetVariables,
        Validation.selectionVariables, Validation.directivesVariables,
        List.mem_append]
      exact Or.inl (Or.inr
        (selectionSetVariables_wrapWithBoolCase_of_body variableName rest
          selectionSet hvariable))

theorem selectionSetVariables_wrapWithBoolCase_of_case (variableName : Name)
    : ∀ boolCase selectionSet,
        variableName ∈ boolCase.map Prod.fst
        -> variableName
            ∈ Validation.selectionSetVariables (wrapWithBoolCase boolCase selectionSet)
  | [], selectionSet, hvariable => by
      cases hvariable
  | (caseVariable, value) :: rest, selectionSet, hvariable => by
      simp only [List.map_cons, List.mem_cons] at hvariable
      rcases hvariable with rfl | hrest
      · cases value <;>
          simp [wrapWithBoolCase, Validation.selectionSetVariables,
            Validation.selectionVariables, Validation.directivesVariables,
            directiveForBit, Validation.directiveVariables,
            Validation.inputValueVariables]
      · simp only [wrapWithBoolCase, Validation.selectionSetVariables,
          Validation.selectionVariables, Validation.directivesVariables,
          List.mem_append]
        exact Or.inl (Or.inr
          (selectionSetVariables_wrapWithBoolCase_of_case variableName rest
            selectionSet hrest))

theorem selectionSetVariables_flatten_of_mem
    {variableName : Name} {selectionSets : List (List Selection)}
    {selectionSet : List Selection}
    : selectionSet ∈ selectionSets
      -> variableName ∈ Validation.selectionSetVariables selectionSet
      -> variableName
          ∈ Validation.selectionSetVariables (List.flatten selectionSets) := by
  intro hselectionSet hvariable
  induction selectionSets with
  | nil =>
      cases hselectionSet
  | cons head rest ih =>
      rw [List.flatten_cons,
        GroundTypeNormalization.selectionSetVariables_append]
      rcases List.mem_cons.mp hselectionSet with rfl | htail
      · exact List.mem_append_left _ hvariable
      · exact List.mem_append_right _ (ih htail)

theorem operation_root_object_of_valid {schema : Schema} {operation : Operation}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> schema.objectType (operation.rootType schema) := by
  intro hschema hoperation
  have hqueryObject := hschema.2.1
  have hrootEq :=
    Validation.operationDefinitionValid_rootType_eq hoperation
  rw [hrootEq]
  exact hqueryObject

theorem operation_selectionSetSemanticsReady_of_valid
    {schema : Schema} {operation : Operation}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> selectionSetSemanticsReady schema (operation.rootType schema)
          operation.selectionSet := by
  intro hschema hoperation
  exact selectionSetSemanticsReady_of_selectionSetValid_object schema
    operation.variableDefinitions (operation.rootType schema) hschema
    (operation_root_object_of_valid hschema hoperation)
    operation.selectionSet
    (Validation.operationDefinitionValid_selectionSetValid hoperation)

theorem operationBoolTypeConditionFeasible_inCase
    {schema : Schema} {operation : Operation}
    (hfeasible : operationBoolTypeConditionFeasible schema operation)
    {boolCase : BoolCase}
    (hcase : boolCase ∈ allBoolCases (operationBoolVars operation))
    : selectionSetBoolTypeConditionFeasibleInCase schema (operation.rootType schema)
        [(operation.rootType schema)] boolCase operation.selectionSet :=
  selectionSetBoolTypeConditionFeasibleInCase_of_all schema
    (operation.rootType schema) [(operation.rootType schema)]
    (allBoolCases (operationBoolVars operation)) boolCase
    operation.selectionSet hfeasible hcase

theorem completeNormalizeRootSelectionSet_variables_of_normalized_case
    {schema : Schema} {variables : List BoolVar} {parentType : Name}
    {selectionSet : List Selection} {boolCase : BoolCase}
    {normalized : List Selection} {variableName : Name}
    : boolCase ∈ allBoolCases variables
      -> normalizeSelectionSet schema parentType
            (filterSelectionSetBoolCase boolCase selectionSet)
          = normalized
      -> normalized ≠ []
      -> variableName
          ∈ Validation.selectionSetVariables (wrapWithBoolCase boolCase normalized)
      -> variableName
          ∈ Validation.selectionSetVariables
              (completeNormalizeRootSelectionSet schema variables parentType
                selectionSet) := by
  intro hcase hnormalized hnonempty hvariable
  cases normalized with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons selection rest =>
      unfold completeNormalizeRootSelectionSet
      refine selectionSetVariables_flatten_of_mem
        (selectionSet := wrapWithBoolCase boolCase (selection :: rest)) ?_
        hvariable
      · apply List.mem_map.mpr
        exact ⟨boolCase, hcase, by simp [hnormalized]⟩

theorem completeNormalizeOperation_operationVariablesUsed
    (schema : Schema) (operation : Operation)
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.operationDefinitionValid schema operation
      -> operationBoolTypeConditionFeasible schema operation
      -> Validation.operationVariablesUsed
          (completeNormalizeOperation schema operation) := by
  intro hschema hoperation hboolFeasible
  have hrootObject : schema.objectType (operation.rootType schema) :=
    operation_root_object_of_valid hschema hoperation
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    operation_selectionSetSemanticsReady_of_valid hschema hoperation
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation
  have hrootStack :
      GroundTypeNormalization.objectSatisfiesTypeConditionStack schema
        (operation.rootType schema)
        [(operation.rootType schema)] :=
    GroundTypeNormalization.objectSatisfiesTypeConditionStack_singleton_of_object_forValidity
      schema hrootObject
  have hsourceVariablesUsed :
      Validation.operationVariablesUsed operation :=
    Validation.operationDefinitionValid_operationVariablesUsed hoperation
  intro variableDefinition hvariableDefinition
  have hsourceDefinition :
      variableDefinition ∈ operation.variableDefinitions := by
    simpa [completeNormalizeOperation] using hvariableDefinition
  have hsourceVariable :
      variableDefinition.name
        ∈ Validation.selectionSetVariables operation.selectionSet :=
    hsourceVariablesUsed variableDefinition hsourceDefinition
  change variableDefinition.name
    ∈ Validation.selectionSetVariables
        (completeNormalizeRootSelectionSet schema (operationBoolVars operation)
          (operation.rootType schema) operation.selectionSet)
  by_cases hboolean :
      variableDefinition.name ∈ operationBoolVars operation
  · have hselectionSetNonempty : operation.selectionSet ≠ [] :=
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
        operation.selectionSet (by rw [hselectionSet]; simp)
        hselectionContains
    have hfilteredReady :
        selectionSetSemanticsReady schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
      filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
        (operation.rootType schema) operation.selectionSet hready
    have hfilteredContains :
        GroundTypeNormalization.selectionSetContainsTypeConditionFeasibleField
          schema [(operation.rootType schema)]
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
    have hcaseVariable :
        variableDefinition.name ∈ boolCase.map Prod.fst := by
      rw [boolCase_map_fst_of_mem_allBoolCases hcase]
      exact hboolean
    exact completeNormalizeRootSelectionSet_variables_of_normalized_case
      hcase rfl hnormalizedNonempty
      (selectionSetVariables_wrapWithBoolCase_of_case
        variableDefinition.name boolCase
        (normalizeSelectionSet schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet))
        hcaseVariable)
  · have hsourceNotBoolean :
        variableDefinition.name
          ∉ selectionSetBooleanVariables operation.selectionSet := by
      intro hsourceBoolean
      exact hboolean
        ((mem_dedupBoolVars_iff variableDefinition.name
          (selectionSetBooleanVariables operation.selectionSet)).2
            hsourceBoolean)
    rcases
        selectionSetVariables_filterSelectionSetBoolCase_of_feasible
          schema variableDefinition.name (operation.rootType schema)
          [(operation.rootType schema)]
          (allBoolCases (operationBoolVars operation))
          operation.selectionSet hboolFeasible hsourceVariable
          hsourceNotBoolean with
      ⟨boolCase, hcase, hfilteredVariable⟩
    have hfilteredReady :
        selectionSetSemanticsReady schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
      filterSelectionSetBoolCase_selectionSetSemanticsReady schema boolCase
        (operation.rootType schema) operation.selectionSet hready
    have hfilteredMerge :
        FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
      fieldsInSetCanMerge_filterSelectionSetBoolCase schema boolCase hmerge
    have hfilteredFree :
        selectionSetDirectiveFree
          (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
      filterSelectionSetBoolCase_directiveFree schema boolCase
        operation.selectionSet
    have hfilteredBoolFeasible :
        selectionSetBoolTypeConditionFeasibleInCase schema (operation.rootType schema)
          [(operation.rootType schema)] boolCase operation.selectionSet :=
      operationBoolTypeConditionFeasible_inCase hboolFeasible hcase
    have hfilteredFeasible :
        selectionSetTypeConditionFeasible schema (operation.rootType schema)
          [(operation.rootType schema)]
          (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
      selectionSetTypeConditionFeasible_filterSelectionSetBoolCase schema
        boolCase (operation.rootType schema) [(operation.rootType schema)]
        operation.selectionSet hfilteredBoolFeasible
    have hnormalizedVariable :
        variableDefinition.name
          ∈ Validation.selectionSetVariables
              (normalizeSelectionSet schema (operation.rootType schema)
                (filterSelectionSetBoolCase boolCase
                  operation.selectionSet)) :=
      GroundTypeNormalization.normalizeSelectionSet_variables_mem schema
        variableDefinition.name hschema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet)
        [(operation.rootType schema)] hrootObject (by simp) hrootStack
        hfilteredReady hfilteredMerge hfilteredFree hfilteredFeasible
        hfilteredVariable
    have hnormalizedNonempty :
        normalizeSelectionSet schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet) ≠ [] := by
      intro hnil
      rw [hnil] at hnormalizedVariable
      cases hnormalizedVariable
    exact completeNormalizeRootSelectionSet_variables_of_normalized_case
      hcase rfl hnormalizedNonempty
      (selectionSetVariables_wrapWithBoolCase_of_body
        variableDefinition.name boolCase
        (normalizeSelectionSet schema (operation.rootType schema)
          (filterSelectionSetBoolCase boolCase operation.selectionSet))
        hnormalizedVariable)

end CompleteNormalization

end NormalForm

end GraphQL
