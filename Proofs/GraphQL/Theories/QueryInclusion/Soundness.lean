import Proofs.GraphQL.Theories.QueryInclusion.GuardedFieldGroup

/-! Soundness of the executable query-inclusion checker. -/

namespace GraphQL
namespace QueryInclusion

open Execution AnnotatedExecution

private theorem validDirectivesBooleanVariable_isModeled
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    : ∀ directives variableName,
        Validation.directivesValid schema variableDefinitions directives
        -> variableName ∈ NormalForm.directivesBooleanVariables directives
        -> variableName
            ∈ directives.filterMap SelectionConditions.directiveBooleanVariable?
  | [], _variableName, _hvalid, hvariable => by cases hvariable
  | directive :: rest, variableName, hvalid, hvariable => by
      simp only [NormalForm.directivesBooleanVariables, List.mem_append] at hvariable
      rcases hvariable with hdirective | hrest
      · have hdirectiveValid := hvalid.2 directive (by simp)
        cases directive <;> rename_i ifArgument <;> cases ifArgument <;>
          simp [NormalForm.directiveBooleanVariables,
            NormalForm.inputValueBooleanVariables, Validation.directiveValid,
            Validation.directiveIfArgumentValid] at hdirective hdirectiveValid
        all_goals
          subst variableName
          simp [SelectionConditions.directiveBooleanVariable?]
      · simp only [List.filterMap_cons]
        cases SelectionConditions.directiveBooleanVariable? directive <;>
          simp only [List.mem_cons]
        · exact validDirectivesBooleanVariable_isModeled rest variableName (by
              constructor
              · exact (List.nodup_cons.mp hvalid.1).2
              · intro candidate hcandidate
                exact hvalid.2 candidate (by simp [hcandidate])) hrest
        · exact Or.inr
            (validDirectivesBooleanVariable_isModeled rest variableName (by
              constructor
              · exact (List.nodup_cons.mp hvalid.1).2
              · intro candidate hcandidate
                exact hvalid.2 candidate (by simp [hcandidate])) hrest)

mutual
  private theorem validSelectionBooleanVariable_isModeled
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name} {selection : Selection}
      (hvalid : Validation.selectionValid schema variableDefinitions parentType selection)
      {variableName : Name}
      (hvariable : variableName ∈ NormalForm.selectionBooleanVariables selection)
      : variableName ∈ SelectionConditions.selectionBooleanVariables selection := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp only [NormalForm.selectionBooleanVariables, List.mem_append] at hvariable
        simp only [SelectionConditions.selectionBooleanVariables, List.mem_append]
        rcases hvariable with hdirectives | hchildren
        · exact Or.inl (validDirectivesBooleanVariable_isModeled directives
            variableName (Validation.selectionValid_field_directivesValid hvalid)
            hdirectives)
        · rcases Validation.selectionValid_field_lookup hvalid with
            ⟨fieldDefinition, _hlookup, _harguments, hselectionSet⟩
          simp [Validation.fieldSelectionSetValid] at hselectionSet
          rcases hselectionSet.2 with hleaf | hcomposite
          · rw [hleaf.2] at hchildren
            cases hchildren
          · exact Or.inr
              (validSelectionSetBooleanVariable_isModeled hcomposite.2.2 hchildren)
    | inlineFragment typeCondition directives selectionSet =>
        simp only [NormalForm.selectionBooleanVariables, List.mem_append] at hvariable
        simp only [SelectionConditions.selectionBooleanVariables, List.mem_append]
        cases typeCondition with
        | none =>
            simp only [Validation.selectionValid] at hvalid
            rcases hvariable with hdirectives | hchildren
            · exact Or.inl (validDirectivesBooleanVariable_isModeled directives
                variableName hvalid.1 hdirectives)
            · exact Or.inr
                (validSelectionSetBooleanVariable_isModeled hvalid.2.2 hchildren)
        | some typeCondition =>
            simp only [Validation.selectionValid] at hvalid
            rcases hvariable with hdirectives | hchildren
            · exact Or.inl (validDirectivesBooleanVariable_isModeled directives
                variableName hvalid.1 hdirectives)
            · exact Or.inr
                (validSelectionSetBooleanVariable_isModeled hvalid.2.2.2.2 hchildren)

  private theorem validSelectionSetBooleanVariable_isModeled
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name}
      : ∀ {selectionSet},
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> ∀ {variableName},
              variableName ∈ NormalForm.selectionSetBooleanVariables selectionSet
              -> variableName
                  ∈ SelectionConditions.selectionSetBooleanVariables selectionSet
    | [], _hvalid, _variableName, hvariable => by cases hvariable
    | selection :: rest, hvalid, variableName, hvariable => by
        unfold Validation.selectionSetValid at hvalid
        simp only [NormalForm.selectionSetBooleanVariables, List.mem_append] at hvariable
        simp only [SelectionConditions.selectionSetBooleanVariables, List.mem_append]
        rcases hvariable with hselection | hrest
        · exact Or.inl (validSelectionBooleanVariable_isModeled
            (hvalid selection (by simp)) hselection)
        · exact Or.inr (validSelectionSetBooleanVariable_isModeled (by
              unfold Validation.selectionSetValid
              intro candidate hcandidate
              exact hvalid candidate (by simp [hcandidate])) hrest)
end

theorem executeQueryAnnotated_zero_error_decompose
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (suppliedValues : VariableValues) (operation : Operation)
    (source : ResolverValue ObjectRef)
    (herrors
      : (executeQueryAnnotated schema resolvers suppliedValues operation source).errors
        = 0)
    : ∃ runtimeType ref fields,
        source = .object runtimeType ref
        ∧ runtimeType ∈ schema.getPossibleTypes (operation.rootType schema)
        ∧ (executeQueryAnnotated schema resolvers suppliedValues operation source).data
          = .object runtimeType fields
        ∧ executeQueryAnnotatedCollectedFields schema resolvers
            (coerceVariableValues operation suppliedValues)
            (executeQueryFuelBound schema operation) (.object runtimeType ref)
            (collectFields schema (coerceVariableValues operation suppliedValues)
              (operation.rootType schema) (.object runtimeType ref)
              operation.selectionSet)
          = .ok (fields, 0) := by
  unfold executeQueryAnnotated executeQueryAnnotatedWithFuel at herrors ⊢
  split at herrors
  · rename_i hroot
    rcases NormalForm.GroundTypeNormalization.rootSourceAppliesBool_true_object schema
        operation source hroot with ⟨runtimeType, ref, rfl, hincludes⟩
    cases hresult
          : executeQueryAnnotatedCollectedFields schema resolvers
              (coerceVariableValues operation suppliedValues)
              (executeQueryFuelBound schema operation) (.object runtimeType ref)
              (collectFields schema (coerceVariableValues operation suppliedValues)
                (operation.rootType schema) (.object runtimeType ref)
                operation.selectionSet) with
    | error errors =>
        simp only [hresult] at herrors
        have hpositive := executeQueryAnnotatedCollectedFields_error_positive schema
          resolvers (coerceVariableValues operation suppliedValues)
          (executeQueryFuelBound schema operation) (.object runtimeType ref)
          (collectFields schema (coerceVariableValues operation suppliedValues)
            (operation.rootType schema) (.object runtimeType ref)
            operation.selectionSet) errors hresult
        omega
    | ok result =>
        rcases result with ⟨fields, errors⟩
        simp only [hresult] at herrors
        subst errors
        refine ⟨runtimeType, ref, fields, rfl, ?_, ?_, hresult⟩
        · simpa [Schema.typeIncludesObjectBool] using List.contains_iff_mem.mp hincludes
        · simp [hroot, hresult, runtimeObjectType?]
  · simp at herrors

-- The semantic continuation shared by the checker-facing and path-facing soundness
-- proofs: root-type agreement, shared-definition compatibility, and reference-checker
-- acceptance under every complete Boolean environment together imply semantic query
-- inclusion.
theorem includes_of_selectionSetChecks {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (_hleftValid : Validation.operationDefinitionValid schema left)
    (_hrightValid : Validation.operationDefinitionValid schema right)
    (hroot : left.rootType schema = right.rootType schema)
    (hdefinitions'
      : sharedVariableDefinitionsSyntacticallyCompatible left.variableDefinitions
          right.variableDefinitions)
    (hselectionChecks
      : ∀ conditionValues,
          boolVarsComplete
            (comparisonConditionVariables left.selectionSet right.selectionSet)
            conditionValues
          -> selectionSetIncludesBoolWithFuel schema (right.size + 1)
                (right.rootType schema) conditionValues
                left.selectionSet right.selectionSet
              = true)
    : includes schema left right := by
  refine ⟨hdefinitions', ?_⟩
  intro ObjectRef resolvers suppliedValues source
  dsimp only
  intro hleftErrors hrightErrors
  rcases executeQueryAnnotated_zero_error_decompose schema resolvers suppliedValues left
      source hleftErrors with
    ⟨runtimeType, ref, leftFields, hsource, hleftRuntime, hleftData, hleftResult⟩
  subst source
  rcases executeQueryAnnotated_zero_error_decompose schema resolvers suppliedValues right
      (.object runtimeType ref) hrightErrors with
    ⟨rightRuntimeType, rightRef, rightFields, hsource, hrightRuntime, hrightData,
      hrightResult⟩
  injection hsource with hruntimeType href
  subst rightRuntimeType
  subst rightRef
  have hleftVariableDefinitionsValid :=
    Validation.operationDefinitionValid_variableDefinitionsValid _hleftValid
  have hrightVariableDefinitionsValid :=
    Validation.operationDefinitionValid_variableDefinitionsValid _hrightValid
  have hleftSelectionValid :=
    Validation.operationDefinitionValid_selectionSetValid _hleftValid
  have hrightSelectionValid :=
    Validation.operationDefinitionValid_selectionSetValid _hrightValid
  have hleftDefinitionOfSelectionVariable : ∀ variableName,
      variableName ∈ Validation.selectionSetVariables left.selectionSet
      -> ∃ definition,
          definition ∈ left.variableDefinitions
          ∧ definition.name = variableName := by
    intro variableName hvariable
    rcases Validation.selectionSetValid_variable_defined left.selectionSet
        hleftSelectionValid hvariable with
      ⟨definition, hlookup⟩
    unfold Validation.getVariableDefinition? at hlookup
    have hname : (definition.name == variableName) = true :=
      List.find?_some
        (p := fun candidate : VariableDefinition => candidate.name == variableName)
        hlookup
    exact ⟨definition, List.mem_of_find?_eq_some hlookup,
      beq_iff_eq.mp hname⟩
  have hrightDefinitionOfSelectionVariable : ∀ variableName,
      variableName ∈ Validation.selectionSetVariables right.selectionSet
      -> ∃ definition,
          definition ∈ right.variableDefinitions
          ∧ definition.name = variableName := by
    intro variableName hvariable
    rcases Validation.selectionSetValid_variable_defined right.selectionSet
        hrightSelectionValid hvariable with
      ⟨definition, hlookup⟩
    unfold Validation.getVariableDefinition? at hlookup
    have hname : (definition.name == variableName) = true :=
      List.find?_some
        (p := fun candidate : VariableDefinition => candidate.name == variableName)
        hlookup
    exact ⟨definition, List.mem_of_find?_eq_some hlookup,
      beq_iff_eq.mp hname⟩
  have hcommonLookups : ∀ variableName,
      variableName ∈ Validation.selectionSetVariables left.selectionSet
      -> variableName ∈ Validation.selectionSetVariables right.selectionSet
      -> Option.Rel
          (fun leftValue rightValue =>
            InputValue.equivalent leftValue.toInputValue rightValue.toInputValue)
          (lookupVariableValue? (coerceVariableValues left suppliedValues) variableName)
          (lookupVariableValue? (coerceVariableValues right suppliedValues)
            variableName) := by
    intro variableName hleftVariable hrightVariable
    rcases hleftDefinitionOfSelectionVariable variableName hleftVariable with
      ⟨leftDefinition, hleftDefinition, hleftName⟩
    rcases hrightDefinitionOfSelectionVariable variableName hrightVariable with
      ⟨rightDefinition, hrightDefinition, hrightName⟩
    simpa [hleftName, hrightName] using
      coerceVariableValues_shared_lookup_equivalent hdefinitions'
      hleftVariableDefinitionsValid.1 hrightVariableDefinitionsValid.1
      hleftDefinition hrightDefinition (hleftName.trans hrightName.symm)
      suppliedValues
  let conditionValues :=
    coerceVariableValues right suppliedValues
      ++ coerceVariableValues left suppliedValues
  have hconditionLeft : ∀ variableName,
      variableName ∈ Validation.selectionSetVariables left.selectionSet
      -> inputValueBoolean? conditionValues (.variable variableName)
          = inputValueBoolean? (coerceVariableValues left suppliedValues)
              (.variable variableName) := by
    intro variableName hleftVariable
    by_cases hrightVariable :
        variableName ∈ Validation.selectionSetVariables right.selectionSet
    · have hequivalent := hcommonLookups variableName hleftVariable hrightVariable
      have hboolean := inputValueBoolean?_eq_of_lookup_equivalent hequivalent
      dsimp only [conditionValues]
      simp only [inputValueBoolean?, lookupVariableValue?_append]
      cases hrightLookup : lookupVariableValue?
          (coerceVariableValues right suppliedValues) variableName
      · rfl
      · simpa [inputValueBoolean?, hrightLookup] using hboolean.symm
    · rcases hleftDefinitionOfSelectionVariable variableName hleftVariable with
        ⟨leftDefinition, hleftDefinition, hleftName⟩
      have hrightNameNotDefined :
          variableName ∉ right.variableDefinitions.map VariableDefinition.name := by
        intro hname
        rcases List.mem_map.mp hname with
          ⟨definition, hdefinition, hdefinitionName⟩
        apply hrightVariable
        have hused :=
          Validation.operationDefinitionValid_operationVariablesUsed _hrightValid
            definition hdefinition
        simpa [hdefinitionName] using hused
      have hrightLookup :=
        lookupVariableValue?_coerceVariableValues_of_name_not_defined right
          suppliedValues variableName hrightNameNotDefined
      have hleftLookup := lookupVariableValue?_coerceVariableValues_at_definition
        hleftVariableDefinitionsValid.1 hleftDefinition suppliedValues
      dsimp only [conditionValues]
      simp only [inputValueBoolean?, lookupVariableValue?_append, hrightLookup]
      rw [hleftName] at hleftLookup
      rw [hleftLookup]
      cases lookupVariableValue? suppliedValues variableName <;>
        cases leftDefinition.defaultValue <;> rfl
  have hactualCheck :
      selectionSetIncludesBoolWithFuel schema (right.size + 1)
        (right.rootType schema) conditionValues
        left.selectionSet right.selectionSet = true :=
    selectionSetIncludesBoolWithFuel_of_complete_checks schema (right.size + 1)
      (right.rootType schema) left.selectionSet right.selectionSet
      hselectionChecks conditionValues
  let leftFuel := executeQueryFuelBound schema left
  let rightFuel := executeQueryFuelBound schema right
  let commonFuel := max leftFuel rightFuel
  have hleftCommon :
      executeQueryAnnotatedCollectedFields schema resolvers
        (coerceVariableValues left suppliedValues) commonFuel
        (.object runtimeType ref)
        (collectFields schema (coerceVariableValues left suppliedValues)
          (right.rootType schema) (.object runtimeType ref) left.selectionSet)
        = .ok (leftFields, 0) := by
    rw [← hroot]
    change executeQueryAnnotatedCollectedFields schema resolvers
        (coerceVariableValues left suppliedValues) commonFuel
        (.object runtimeType ref)
        (collectFields schema (coerceVariableValues left suppliedValues)
          (left.rootType schema) (.object runtimeType ref) left.selectionSet)
        = .ok (leftFields, 0)
    rw [show commonFuel = leftFuel + (commonFuel - leftFuel) by
      exact (Nat.add_sub_of_le (Nat.le_max_left _ _)).symm]
    exact executeQueryAnnotatedCollectedFields_success_mono schema resolvers
      (coerceVariableValues left suppliedValues) leftFuel (.object runtimeType ref)
      (collectFields schema (coerceVariableValues left suppliedValues)
        (left.rootType schema) (.object runtimeType ref) left.selectionSet)
      leftFields hleftResult (commonFuel - leftFuel)
  have hrightCommon :
      executeQueryAnnotatedCollectedFields schema resolvers
        (coerceVariableValues right suppliedValues) commonFuel
        (.object runtimeType ref)
        (collectFields schema (coerceVariableValues right suppliedValues)
          (right.rootType schema) (.object runtimeType ref) right.selectionSet)
        = .ok (rightFields, 0) := by
    rw [show commonFuel = rightFuel + (commonFuel - rightFuel) by
      exact (Nat.add_sub_of_le (Nat.le_max_right _ _)).symm]
    exact executeQueryAnnotatedCollectedFields_success_mono schema resolvers
      (coerceVariableValues right suppliedValues) rightFuel (.object runtimeType ref)
      (collectFields schema (coerceVariableValues right suppliedValues)
        (right.rootType schema) (.object runtimeType ref) right.selectionSet)
      rightFields hrightResult (commonFuel - rightFuel)
  have hleftNodup : selectionSetArgumentsNodup left.selectionSet :=
    Execution.selectionSetArgumentsNodup_of_selectionSetValid
      (Validation.operationDefinitionValid_selectionSetValid _hleftValid)
  have hrightNodup : selectionSetArgumentsNodup right.selectionSet :=
    Execution.selectionSetArgumentsNodup_of_selectionSetValid
      (Validation.operationDefinitionValid_selectionSetValid _hrightValid)
  rw [hleftData, hrightData]
  apply selectionSetIncludesBoolWithFuel_annotated_execution schema resolvers hschema
    (right.size + 1) conditionValues (coerceVariableValues left suppliedValues)
    (coerceVariableValues right suppliedValues) (right.rootType schema)
    runtimeType ref left.selectionSet right.selectionSet commonFuel leftFields rightFields
  · exact hrightRuntime
  · exact hactualCheck
  · intro variableName hvariable
    exact hconditionLeft variableName
      (selectionBooleanVariable_mem_selectionVariables left.selectionSet variableName
        hvariable)
  · intro variableName hvariable
    have hrightVariable :
        variableName ∈ Validation.selectionSetVariables right.selectionSet :=
      selectionBooleanVariable_mem_selectionVariables right.selectionSet variableName
        hvariable
    rcases hrightDefinitionOfSelectionVariable variableName hrightVariable with
      ⟨rightDefinition, hrightDefinition, hrightName⟩
    dsimp only [conditionValues]
    simp only [inputValueBoolean?, lookupVariableValue?_append]
    cases hrightLookup
          : lookupVariableValue? (coerceVariableValues right suppliedValues)
              variableName with
    | some resolved => rfl
    | none =>
        have hleftLookup :
            lookupVariableValue? (coerceVariableValues left suppliedValues) variableName
              = none := by
          have hrightAt := lookupVariableValue?_coerceVariableValues_at_definition
            hrightVariableDefinitionsValid.1 hrightDefinition suppliedValues
          rw [hrightName, hrightLookup] at hrightAt
          cases hsupplied : lookupVariableValue? suppliedValues variableName with
          | some suppliedValue =>
              rw [hsupplied] at hrightAt
              simp at hrightAt
          | none =>
              by_cases hleftDeclared :
                  variableName ∈ left.variableDefinitions.map VariableDefinition.name
              · rcases List.mem_map.mp hleftDeclared with
                  ⟨leftDefinition, hleftDefinition, hleftName⟩
                have hrel := coerceVariableValues_shared_lookup_equivalent hdefinitions'
                  hleftVariableDefinitionsValid.1 hrightVariableDefinitionsValid.1
                  hleftDefinition hrightDefinition
                  (hleftName.trans hrightName.symm) suppliedValues
                rw [hleftName, hrightName, hrightLookup] at hrel
                cases hcandidate
                      : lookupVariableValue?
                          (coerceVariableValues left suppliedValues) variableName with
                | none => rfl
                | some leftValue =>
                    rw [hcandidate] at hrel
                    cases hrel
              · rw [lookupVariableValue?_coerceVariableValues_of_name_not_defined left
                  suppliedValues variableName hleftDeclared]
                exact hsupplied
        rw [hleftLookup]
  · exact hcommonLookups
  · exact hleftNodup
  · exact hrightNodup
  · exact hleftCommon
  · exact hrightCommon

theorem includesBool_sound {schema : Schema} {left right : Operation}
    : IncludesBoolSound schema left right := by
  intro hschema hleftValid hrightValid hcheck
  rcases includesBool_to_selectionSetChecks hschema hleftValid hrightValid hcheck with
    ⟨hroot, hdefinitions, hselectionChecks⟩
  exact includes_of_selectionSetChecks hschema hleftValid hrightValid hroot
    ((sharedVariableDefinitionsSyntacticallyCompatibleBool_iff _ _).mp hdefinitions)
    hselectionChecks

end QueryInclusion
end GraphQL
