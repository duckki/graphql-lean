import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.CaseBodies
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.ReorderingVariables
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.StemExecution
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Semantics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness

/-!
Semantic soundness of complete-normal equality up to branch, stem, and sibling
reordering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

private theorem operationBoolVars_eq_nil_of_equivalent_left_nil
    {left right : Operation}
    (hvariables : operationBoolVarsEquivalent left right)
    (hleft : operationBoolVars left = [])
    : operationBoolVars right = [] := by
  cases hright : operationBoolVars right with
  | nil => rfl
  | cons head tail =>
      have hheadRight : head ∈ operationBoolVars right := by
        simp [hright]
      have hheadLeft : head ∈ operationBoolVars left :=
        (hvariables head).2 hheadRight
      simp [hleft] at hheadLeft

private theorem completeNormalSelection_body_normal_free
    {schema : Schema} {leftVar : BoolVar} {variables : List BoolVar}
    {parentType : Name} {selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (leftVar :: variables) parentType selectionSet)
    {selection : Selection} {boolCase : BoolCase}
    {body : List Selection}
    (hmem : selection ∈ selectionSet)
    (hcase : completeNormalBoolCase (leftVar :: variables) boolCase)
    (hstem : completeNormalBooleanStem boolCase selection body)
    : selectionSetNormal schema parentType body ∧ selectionSetDirectiveFree body := by
  rcases hnormal with ⟨_hvariablesNodup, _hselectionSetNodup,
    hbranches, _hunique⟩
  rcases hbranches selection hmem with
    ⟨normalCase, normalBody, hnormalCase, hnormalStem,
      hbodyNormal, hbodyFree⟩
  have heq := completeNormalBooleanStem_case_body_eq hcase hnormalCase
    (by simp) hstem hnormalStem
  cases heq.1
  cases heq.2
  exact ⟨hbodyNormal, hbodyFree⟩

private theorem completeNormalSelectionSets_semanticallyEquivalent_of_equal
    {schema : Schema} {parentType : Name}
    {leftVar rightVar : BoolVar}
    {leftVariables rightVariables : List BoolVar}
    {left right : List Selection}
    (hleftNormal
      : completeNormalSelectionSet schema (leftVar :: leftVariables) parentType left)
    (hrightNormal
      : completeNormalSelectionSet schema (rightVar :: rightVariables) parentType right)
    (hvariables
      : ∀ varName,
          varName ∈ leftVar :: leftVariables ↔ varName ∈ rightVar :: rightVariables)
    (hequal
      : CompleteNormalSelectionSetEqualUpToReordering
          (leftVar :: leftVariables) (rightVar :: rightVariables) left right)
    : selectionSetsSemanticallyEquivalent schema parentType left right := by
  classical
  rcases hequal with ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩
  intro ObjectRef resolvers variableValues fuel source hsource
  by_cases hcomplete : boolVarsComplete (leftVar :: leftVariables)
      variableValues
  · rcases allBoolCases_complete_for_variableValues variableValues
        (leftVar :: leftVariables) hcomplete with
      ⟨runtimeCase, hruntimeMem, hagreesLeft⟩
    have hruntimeLeft :
        completeNormalBoolCase (leftVar :: leftVariables) runtimeCase :=
      completeNormalBoolCase_of_mem_allBoolCases hleftNormal.1 hruntimeMem
    have hruntimeRight :
        completeNormalBoolCase (rightVar :: rightVariables) runtimeCase :=
      completeNormalBoolCase_of_variable_mem_iff hruntimeLeft hrightNormal.1
        (fun varName => (hruntimeLeft.2.2 varName).trans (hvariables varName))
    have hagreesRight : variableValuesAgreeWithCase variableValues runtimeCase
        (rightVar :: rightVariables) := by
      intro varName hmem
      exact hagreesLeft varName ((hvariables varName).2 hmem)
    by_cases hmatch : ∃ pair leftCase rightCase leftBody rightBody,
        pair ∈ pairs
          ∧ completeNormalBoolCase (leftVar :: leftVariables) leftCase
          ∧ completeNormalBoolCase (rightVar :: rightVariables) rightCase
          ∧ completeNormalBooleanStem leftCase pair.1 leftBody
          ∧ completeNormalBooleanStem rightCase pair.2 rightBody
          ∧ completeNormalBoolCasesEquivalent leftCase rightCase
          ∧ SelectionSetEqualUpToReordering leftBody rightBody
          ∧ completeNormalBoolCasesEquivalent runtimeCase leftCase
    · rcases hmatch with
        ⟨pair, leftCase, rightCase, leftBody, rightBody, hpair,
          hleftCase, hrightCase, hleftStem, hrightStem, hcasesEqual,
          hbodiesEqual, hruntimeEqual⟩
      have hleftPairMem : pair.1 ∈ pairs.map Prod.fst :=
        List.mem_map.mpr ⟨pair, hpair, rfl⟩
      have hrightPairMem : pair.2 ∈ pairs.map Prod.snd :=
        List.mem_map.mpr ⟨pair, hpair, rfl⟩
      have hleftMem : pair.1 ∈ left := hpairsLeft.mem_iff.mp hleftPairMem
      have hrightMem : pair.2 ∈ right :=
        hpairsRight.mem_iff.mp hrightPairMem
      have hleftBody := completeNormalSelection_body_normal_free hleftNormal
        hleftMem hleftCase hleftStem
      have hrightBody := completeNormalSelection_body_normal_free hrightNormal
        hrightMem hrightCase hrightStem
      have hrightRuntimeEqual :
          completeNormalBoolCasesEquivalent runtimeCase rightCase :=
        completeNormalBoolCasesEquivalent_trans hruntimeEqual hcasesEqual
      have hleftCollect :=
        collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
          schema variableValues parentType source hleftNormal hleftMem
          hruntimeLeft hleftCase hagreesLeft hruntimeEqual hleftStem
          hleftBody.2
      have hrightCollect :=
        collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
          schema variableValues parentType source hrightNormal hrightMem
          hruntimeRight hrightCase hagreesRight hrightRuntimeEqual hrightStem
          hrightBody.2
      have hleftExecute := executeSelectionSet_eq_of_collectFields_eq schema
        resolvers variableValues fuel parentType source left leftBody
        hleftCollect
      have hrightExecute := executeSelectionSet_eq_of_collectFields_eq schema
        resolvers variableValues fuel parentType source right rightBody
        hrightCollect
      have hbodySem : selectionSetsSemanticallyEquivalent schema parentType
          leftBody rightBody :=
        GroundTypeNormalization.selectionSetsSemanticallyEquivalent_of_equalUpToReordering
          hleftBody.2 hrightBody.2 hleftBody.1 hrightBody.1 hbodiesEqual
      unfold Execution.executeSelectionSetAsResponse
      rw [hleftExecute, hrightExecute]
      simpa [Execution.executeSelectionSetAsResponse] using
        hbodySem resolvers variableValues fuel source hsource
    · have hnoneLeft : ¬ ∃ selection candidate body,
          selection ∈ left
            ∧ completeNormalBoolCase (leftVar :: leftVariables) candidate
            ∧ completeNormalBooleanStem candidate selection body
            ∧ completeNormalBoolCasesEquivalent runtimeCase candidate := by
        rintro ⟨selection, candidate, body, hselection, hcandidate,
          hstem, hequivalent⟩
        have hselectionPair : selection ∈ pairs.map Prod.fst :=
          hpairsLeft.mem_iff.mpr hselection
        rcases List.mem_map.mp hselectionPair with
          ⟨pair, hpair, hpairLeft⟩
        rcases hpairsEqual pair hpair with
          ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
            hrightCase, hleftStem, hrightStem, hcasesEqual,
            hbodiesEqual⟩
        have hcandidateStemAtPair :
            completeNormalBooleanStem candidate pair.1 body := by
          simpa [hpairLeft] using hstem
        have hcaseBodyEq := completeNormalBooleanStem_case_body_eq
          hcandidate hleftCase (by simp) hcandidateStemAtPair hleftStem
        have hcandidateCasesEqual :
            completeNormalBoolCasesEquivalent candidate rightCase := by
          simpa [hcaseBodyEq.1] using hcasesEqual
        have hcandidateBodiesEqual :
            SelectionSetEqualUpToReordering body rightBody := by
          simpa [hcaseBodyEq.2] using hbodiesEqual
        exact hmatch ⟨pair, candidate, rightCase, body, rightBody,
          hpair, hcandidate, hrightCase, hcandidateStemAtPair, hrightStem,
          hcandidateCasesEqual, hcandidateBodiesEqual, hequivalent⟩
      have hnoneRight : ¬ ∃ selection candidate body,
          selection ∈ right
            ∧ completeNormalBoolCase (rightVar :: rightVariables) candidate
            ∧ completeNormalBooleanStem candidate selection body
            ∧ completeNormalBoolCasesEquivalent runtimeCase candidate := by
        rintro ⟨selection, candidate, body, hselection, hcandidate,
          hstem, hequivalent⟩
        have hselectionPair : selection ∈ pairs.map Prod.snd :=
          hpairsRight.mem_iff.mpr hselection
        rcases List.mem_map.mp hselectionPair with
          ⟨pair, hpair, hpairRight⟩
        rcases hpairsEqual pair hpair with
          ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
            hrightCase, hleftStem, hrightStem, hcasesEqual,
            hbodiesEqual⟩
        have hcandidateStemAtPair :
            completeNormalBooleanStem candidate pair.2 body := by
          simpa [hpairRight] using hstem
        have hcaseBodyEq := completeNormalBooleanStem_case_body_eq
          hcandidate hrightCase (by simp) hcandidateStemAtPair hrightStem
        have hleftCandidateCasesEqual :
            completeNormalBoolCasesEquivalent leftCase candidate := by
          simpa [hcaseBodyEq.1] using hcasesEqual
        have hleftCandidateBodiesEqual :
            SelectionSetEqualUpToReordering leftBody body := by
          simpa [hcaseBodyEq.2] using hbodiesEqual
        have hruntimeLeftCase := completeNormalBoolCasesEquivalent_trans
          hequivalent
          (completeNormalBoolCasesEquivalent_symm hleftCandidateCasesEqual)
        exact hmatch ⟨pair, leftCase, candidate, leftBody, body,
          hpair, hleftCase, hcandidate, hleftStem, hcandidateStemAtPair,
          hleftCandidateCasesEqual, hleftCandidateBodiesEqual,
          hruntimeLeftCase⟩
      have hleftCollect :=
        collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent_of_agrees
          schema variableValues parentType source hleftNormal hruntimeLeft
          hagreesLeft hnoneLeft
      have hrightCollect :=
        collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent_of_agrees
          schema variableValues parentType source hrightNormal hruntimeRight
          hagreesRight hnoneRight
      have hcollect :
          Execution.collectFields schema variableValues parentType source left =
            Execution.collectFields schema variableValues parentType source
              right :=
        hleftCollect.trans hrightCollect.symm
      have hexecute := executeSelectionSet_eq_of_collectFields_eq schema
        resolvers variableValues fuel parentType source left right hcollect
      unfold Execution.executeSelectionSetAsResponse
      rw [hexecute]
      exact ⟨rfl, rfl⟩
  · have hmissingExists : ∃ missingVar,
        missingVar ∈ leftVar :: leftVariables
          ∧ ∀ value, Execution.inputValueBoolean? variableValues
            (.variable missingVar) ≠ some value := by
      exact Classical.byContradiction (fun hnone => by
        apply hcomplete
        intro varName hmem
        exact Classical.byContradiction (fun hnoValue =>
          hnone ⟨varName, hmem, fun value hvalue =>
            hnoValue ⟨value, hvalue⟩⟩))
    rcases hmissingExists with
      ⟨missingVar, hmissingLeft, hmissingValue⟩
    have hmissing : Execution.inputValueBoolean? variableValues
        (.variable missingVar) = none := by
      cases hvalue : Execution.inputValueBoolean? variableValues
        (.variable missingVar) with
      | none => rfl
      | some value => exact False.elim (hmissingValue value hvalue)
    have hmissingRight : missingVar ∈ rightVar :: rightVariables :=
      (hvariables missingVar).1 hmissingLeft
    have hleftCollect :=
      collectFields_completeNormalSelectionSet_eq_nil_of_missing_variable
        schema variableValues parentType source hleftNormal hmissingLeft hmissing
    have hrightCollect :=
      collectFields_completeNormalSelectionSet_eq_nil_of_missing_variable
        schema variableValues parentType source hrightNormal hmissingRight hmissing
    have hcollect :
        Execution.collectFields schema variableValues parentType source left =
          Execution.collectFields schema variableValues parentType source right :=
      hleftCollect.trans hrightCollect.symm
    have hexecute := executeSelectionSet_eq_of_collectFields_eq schema resolvers
      variableValues fuel parentType source left right hcollect
    unfold Execution.executeSelectionSetAsResponse
    rw [hexecute]
    exact ⟨rfl, rfl⟩

theorem complete_normal_operations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : completeNormalOperationsEqualUpToReorderingSemanticallyEquivalent
        schema left right := by
  intro hleftNormal hrightNormal hdefinitions hequal
  have hvariables :=
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering
      hequal
  rcases hequal with ⟨_hroot, hselectionEqual⟩
  have hrootType : (left.rootType schema) = (right.rootType schema) := by
    cases left.operationType
    cases right.operationType
    rfl
  have hselectionSem : selectionSetsSemanticallyEquivalent schema (left.rootType schema)
      left.selectionSet right.selectionSet := by
    cases hleftVars : operationBoolVars left with
    | nil =>
        have hrightVars : operationBoolVars right = [] :=
          operationBoolVars_eq_nil_of_equivalent_left_nil hvariables hleftVars
        have hleftShape := hleftNormal
        have hrightShape := hrightNormal
        simp [completeNormalOperation, completeNormalSelectionSet, hleftVars]
          at hleftShape
        simp [completeNormalOperation, completeNormalSelectionSet, hrightVars]
          at hrightShape
        have hrightSelectionNormal :
            selectionSetNormal schema (left.rootType schema) right.selectionSet := by
          simpa only [hrootType] using hrightShape.1
        have hselectionEqualGround :
            SelectionSetEqualUpToReordering left.selectionSet
              right.selectionSet := by
          simpa [hleftVars] using hselectionEqual
        intro ObjectRef resolvers variableValues fuel source hsource
        exact
          GroundTypeNormalization.selectionSetsSemanticallyEquivalent_of_equalUpToReordering
            hleftShape.2 hrightShape.2 hleftShape.1 hrightSelectionNormal
            hselectionEqualGround resolvers variableValues fuel source hsource
    | cons leftVar leftVariables =>
        cases hrightVars : operationBoolVars right with
        | nil =>
            have hleftVarRight : leftVar ∈ operationBoolVars right :=
              (hvariables leftVar).1 (by simp [hleftVars])
            simp [hrightVars] at hleftVarRight
        | cons rightVar rightVariables =>
            have hleftComplete : completeNormalSelectionSet schema
                (leftVar :: leftVariables) (left.rootType schema) left.selectionSet := by
              simpa [completeNormalOperation, hleftVars] using hleftNormal
            have hrightComplete : completeNormalSelectionSet schema
                (rightVar :: rightVariables) (left.rootType schema) right.selectionSet := by
              simpa [completeNormalOperation, hrightVars, hrootType] using
                hrightNormal
            have hselectionEqualComplete :
                CompleteNormalSelectionSetEqualUpToReordering
                  (leftVar :: leftVariables) (rightVar :: rightVariables)
                  left.selectionSet right.selectionSet := by
              simpa [hleftVars, hrightVars] using hselectionEqual
            have hvariablesAtSupports : ∀ varName,
                varName ∈ leftVar :: leftVariables ↔
                  varName ∈ rightVar :: rightVariables := by
              intro varName
              simpa [hleftVars, hrightVars] using (hvariables varName)
            intro ObjectRef resolvers variableValues fuel source hsource
            exact completeNormalSelectionSets_semanticallyEquivalent_of_equal
              hleftComplete hrightComplete hvariablesAtSupports
              hselectionEqualComplete resolvers variableValues fuel source hsource
  intro ObjectRef resolvers variableValues fuel source
  have hcoercedValues :
      Execution.coerceVariableValues right variableValues =
        Execution.coerceVariableValues left variableValues := by
    simp [Execution.coerceVariableValues, hdefinitions]
  have hrootApplies :
      Execution.rootSourceAppliesBool schema left source =
        Execution.rootSourceAppliesBool schema right source := by
    simp [Execution.rootSourceAppliesBool, hrootType]
  cases hleftRoot : Execution.rootSourceAppliesBool schema left source with
  | false =>
      have hrightRoot :
          Execution.rootSourceAppliesBool schema right source = false := by
        simpa [hleftRoot] using hrootApplies.symm
      simp [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
        Execution.Response.semanticEquivalent,
        Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical]
  | true =>
      have hrightRoot :
          Execution.rootSourceAppliesBool schema right source = true := by
        simpa [hleftRoot] using hrootApplies.symm
      have hsource :=
        GroundTypeNormalization.rootSourceAppliesBool_true_object schema left
          source hleftRoot
      simpa [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
        hcoercedValues,
        Execution.executeSelectionSetAsResponse,
        Execution.executeSelectionSet, hrootType] using
          hselectionSem resolvers
            (Execution.coerceVariableValues left variableValues)
            fuel source hsource

theorem completeNormalizeOperations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : completeNormalizeOperationsEqualUpToReorderingSemanticallyEquivalent
        schema left right := by
  intro hschema hleftValid hrightValid hdefinitions hvariables hequal
  have hleftNormal : completeNormalOperation schema
      (completeNormalizeOperation schema left) :=
    completeNormalizeOperation_normal schema left hschema hleftValid
  have hrightNormal : completeNormalOperation schema
      (completeNormalizeOperation schema right) :=
    completeNormalizeOperation_normal schema right hschema hrightValid
  have hnormalizedDefinitions :
      (completeNormalizeOperation schema left).variableDefinitions =
        (completeNormalizeOperation schema right).variableDefinitions := by
    simpa [completeNormalizeOperation_variableDefinitions] using hdefinitions
  have hnormalizedSemantics : operationsSemanticallyEquivalent schema
      (completeNormalizeOperation schema left)
      (completeNormalizeOperation schema right) :=
    complete_normal_operations_equalUpToReordering_semanticallyEquivalent
      hleftNormal hrightNormal hnormalizedDefinitions hequal
  intro ObjectRef resolvers variableValues fuel source hleftComplete
  have hrightComplete : operationBoolVarsComplete right variableValues := by
    intro varName hmem
    exact hleftComplete varName ((hvariables varName).2 hmem)
  have hleftPreserved := completeNormalizationSemanticsPreserved schema left
    hschema hleftValid resolvers variableValues fuel source hleftComplete
  have hrightPreserved := completeNormalizationSemanticsPreserved schema right
    hschema hrightValid resolvers variableValues fuel source hrightComplete
  rw [hleftPreserved, hrightPreserved]
  exact hnormalizedSemantics resolvers variableValues fuel source

end CompleteNormalization

end NormalForm

end GraphQL
