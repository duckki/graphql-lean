import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.CaseBodies
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.RestrictedSemantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.SemanticVariables
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness

/-!
Operation-level assembly for complete-normalization uniqueness.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

private theorem selectionSetsSemanticallyEquivalentForCompleteBoolVars_of_operations
    {schema : Schema} {variables : List BoolVar} {left right : Operation}
    : (left.rootType schema) = (right.rootType schema)
      -> operationsSemanticallyEquivalentForCompleteBoolVars schema variables left right
      -> selectionSetsSemanticallyEquivalentForCompleteBoolVars schema variables
          (Execution.coerceVariableValues left)
          (Execution.coerceVariableValues right)
          (left.rootType schema) left.selectionSet right.selectionSet := by
  intro hroot hsem
  refine ⟨?_, ?_, ?_⟩
  · intro variableValues name value hvalue
    exact inputValueBoolean?_coerceVariableValues_eq_some
      left variableValues hvalue
  · intro variableValues name value hvalue
    exact inputValueBoolean?_coerceVariableValues_eq_some
      right variableValues hvalue
  · intro ObjectRef resolvers variableValues fuel source hcomplete hsource
    rcases hsource with ⟨runtimeType, _ref, hsourceEq, hinclude⟩
    have hleftRoot :
        Execution.rootSourceAppliesBool schema left source = true := by
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
        hsourceEq, hinclude]
    have hrightInclude :
        schema.typeIncludesObjectBool (right.rootType schema) runtimeType = true := by
      simpa [← hroot] using hinclude
    have hrightRoot :
        Execution.rootSourceAppliesBool schema right source = true := by
      simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
        hsourceEq, hrightInclude]
    simpa [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
      Execution.executeSelectionSetAsResponse,
      Execution.selectionSetResultToResponse,
      Execution.executeSelectionSet, hroot] using
        hsem resolvers variableValues fuel source hcomplete

private theorem completeNormalBoolCase_of_operationBoolVarsEquivalent
    {left right : Operation} {boolCase : BoolCase}
    (hvariables : operationBoolVarsEquivalent left right)
    (hcomplete : completeNormalBoolCase (operationBoolVars left) boolCase)
    : completeNormalBoolCase (operationBoolVars right) boolCase := by
  exact completeNormalBoolCase_of_variable_mem_iff hcomplete
    (operationBoolVars_nodup right) fun varName =>
      (hcomplete.2.2 varName).trans (hvariables varName)

private theorem list_map_nodup_of_injective_on
    {source : List α} {target : α -> β}
    (hsourceNodup : source.Nodup)
    (hinjective
      : ∀ left,
          left ∈ source
          -> ∀ right, right ∈ source -> target left = target right -> left = right)
    : (source.map target).Nodup := by
  have htargetPairwise :
      List.Pairwise (fun left right => target left ≠ target right) source :=
    List.Pairwise.imp_of_mem
      (fun {left right} hleftMem hrightMem hleftNe htargetEq =>
        hleftNe (hinjective left hleftMem right hrightMem htargetEq))
      hsourceNodup
  exact List.Pairwise.map target (fun _left _right hne => hne)
    htargetPairwise

theorem complete_normal_operations_equalUpToReordering_of_complete_bool_vars_semantics
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hvariables : operationBoolVarsEquivalent left right)
    (hsem
      : operationsSemanticallyEquivalentForCompleteBoolVars schema
          (operationBoolVars left) left right)
    : completeNormalOperationsEqualUpToReordering left right := by
  classical
  have hroot : (left.rootType schema) = (right.rootType schema) :=
    GroundTypeNormalization.operation_rootType_eq_of_operationDefinitionValid
      hleftValid hrightValid
  refine ⟨by
    cases left.operationType
    cases right.operationType
    rfl, ?_⟩
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
      have hsemAll : operationsSemanticallyEquivalent schema left right := by
        intro ObjectRef resolvers variableValues fuel source
        exact hsem resolvers variableValues fuel source (by
          simp [boolVarsComplete, hleftVars])
      have hground :=
        GroundTypeNormalization.normal_operations_semanticallyEquivalent_equalUpToReordering
          (schema := schema) (left := left) (right := right) hschema
          hleftValid hrightValid hleftShape.2 hrightShape.2
          hleftShape.1 hrightShape.1 hsemAll
      simpa [hleftVars] using hground.2
  | cons leftVar leftVariables =>
      cases hrightVars : operationBoolVars right with
      | nil =>
          have hleftVarRight : leftVar ∈ operationBoolVars right :=
            (hvariables leftVar).1 (by simp [hleftVars])
          simp [hrightVars] at hleftVarRight
      | cons rightVar rightVariables =>
          have hleftComplete :
              completeNormalSelectionSet schema (leftVar :: leftVariables)
                (left.rootType schema) left.selectionSet := by
            simpa [completeNormalOperation, hleftVars] using hleftNormal
          have hrightComplete :
              completeNormalSelectionSet schema (rightVar :: rightVariables)
                (left.rootType schema) right.selectionSet := by
            simpa [completeNormalOperation, hrightVars, hroot] using
              hrightNormal
          have hleftSelectionValid :
              Validation.selectionSetValid schema left.variableDefinitions
                (left.rootType schema) left.selectionSet :=
            Validation.operationDefinitionValid_selectionSetValid hleftValid
          have hrightSelectionValid :
              Validation.selectionSetValid schema right.variableDefinitions
                (left.rootType schema) right.selectionSet := by
            simpa [hroot] using
              Validation.operationDefinitionValid_selectionSetValid hrightValid
          have hobject : objectTypeNameBool schema (left.rootType schema) = true :=
            GroundTypeNormalization.operation_root_objectTypeNameBool_of_wf_valid
              hschema hleftValid
          have hselectionSem :
              selectionSetsSemanticallyEquivalentForCompleteBoolVars schema
                (leftVar :: leftVariables)
                (Execution.coerceVariableValues left)
                (Execution.coerceVariableValues right)
                (left.rootType schema) left.selectionSet right.selectionSet := by
            simpa only [hleftVars] using
              selectionSetsSemanticallyEquivalentForCompleteBoolVars_of_operations
                hroot hsem
          have hcaseLeftToRight : ∀ boolCase,
              completeNormalBoolCase (leftVar :: leftVariables) boolCase ->
                completeNormalBoolCase (rightVar :: rightVariables)
                  boolCase := by
            intro boolCase hcase
            have hcaseAtOperation :
                completeNormalBoolCase (operationBoolVars left) boolCase := by
              simpa [hleftVars] using hcase
            have htransport :=
              completeNormalBoolCase_of_operationBoolVarsEquivalent
                hvariables hcaseAtOperation
            simpa [hleftVars, hrightVars] using htransport
          have hvariablesSymm : operationBoolVarsEquivalent right left :=
            fun varName => (hvariables varName).symm
          have hcaseRightToLeft : ∀ boolCase,
              completeNormalBoolCase (rightVar :: rightVariables) boolCase ->
                completeNormalBoolCase (leftVar :: leftVariables)
                  boolCase := by
            intro boolCase hcase
            have hcaseAtOperation :
                completeNormalBoolCase (operationBoolVars right) boolCase := by
              simpa [hrightVars] using hcase
            have htransport :=
              completeNormalBoolCase_of_operationBoolVarsEquivalent
                hvariablesSymm hcaseAtOperation
            simpa [hleftVars, hrightVars] using htransport
          have hleftTotal : ∀ leftSelection,
              leftSelection ∈ left.selectionSet ->
                ∃ rightSelection,
                  rightSelection ∈ right.selectionSet
                    ∧ CompleteNormalSelectionMatch schema
                      (leftVar :: leftVariables)
                      (rightVar :: rightVariables) (left.rootType schema)
                      leftSelection rightSelection := by
            intro leftSelection hleftMem
            exact completeNormalSelection_has_match hschema
              hleftSelectionValid hrightSelectionValid hleftComplete
              hrightComplete hcaseLeftToRight hobject hselectionSem hleftMem
          have hrightTotal : ∀ rightSelection,
              rightSelection ∈ right.selectionSet ->
                ∃ leftSelection,
                  leftSelection ∈ left.selectionSet
                    ∧ CompleteNormalSelectionMatch schema
                      (rightVar :: rightVariables)
                      (leftVar :: leftVariables) (left.rootType schema)
                      rightSelection leftSelection := by
            have hselectionSemReverse :
                selectionSetsSemanticallyEquivalentForCompleteBoolVars schema
                  (rightVar :: rightVariables)
                  (Execution.coerceVariableValues right)
                  (Execution.coerceVariableValues left)
                  (left.rootType schema) right.selectionSet left.selectionSet := by
              refine ⟨hselectionSem.2.1, hselectionSem.1, ?_⟩
              intro ObjectRef resolvers variableValues fuel source
                hrightCompleteValues hsource
              have hleftCompleteValues :
                  boolVarsComplete (leftVar :: leftVariables)
                    variableValues := by
                intro varName hleftMem
                have hrightMem : varName ∈ rightVar :: rightVariables := by
                  have hleftOperationMem :
                      varName ∈ operationBoolVars left := by
                    simpa [hleftVars] using hleftMem
                  have hrightOperationMem :
                      varName ∈ operationBoolVars right :=
                    (hvariables varName).1 hleftOperationMem
                  simpa [hrightVars] using hrightOperationMem
                exact hrightCompleteValues varName hrightMem
              have hresponse := hselectionSem.2.2 resolvers variableValues fuel
                source hleftCompleteValues hsource
              exact ⟨hresponse.1.symm, hresponse.2.symm⟩
            intro rightSelection hrightMem
            exact completeNormalSelection_has_match hschema
              hrightSelectionValid hleftSelectionValid hrightComplete
              hleftComplete hcaseRightToLeft hobject
              hselectionSemReverse hrightMem
          let matchingRight (leftSelection : Selection) : Selection :=
            if hleftMem : leftSelection ∈ left.selectionSet then
              Classical.choose (hleftTotal leftSelection hleftMem)
            else
              leftSelection
          have matchingRight_spec (leftSelection : Selection)
              (hleftMem : leftSelection ∈ left.selectionSet) :
              matchingRight leftSelection ∈ right.selectionSet
                ∧ CompleteNormalSelectionMatch schema
                  (leftVar :: leftVariables)
                  (rightVar :: rightVariables) (left.rootType schema) leftSelection
                  (matchingRight leftSelection) := by
            simpa only [matchingRight, dif_pos hleftMem] using
              (Classical.choose_spec (hleftTotal leftSelection hleftMem))
          have hleftSetNodup : left.selectionSet.Nodup := hleftComplete.2.1
          have hrightSetNodup : right.selectionSet.Nodup :=
            hrightComplete.2.1
          have hmatchingInjective : ∀ leftFirst,
              leftFirst ∈ left.selectionSet ->
              ∀ leftSecond, leftSecond ∈ left.selectionSet ->
                matchingRight leftFirst = matchingRight leftSecond ->
                  leftFirst = leftSecond := by
            intro leftFirst hleftFirstMem leftSecond hleftSecondMem hequal
            have hfirst := (matchingRight_spec leftFirst hleftFirstMem).2
            have hsecond := (matchingRight_spec leftSecond hleftSecondMem).2
            rw [hequal] at hfirst
            exact completeNormalSelectionMatch_left_unique hleftComplete
              (by simp) (by simp) hleftFirstMem hleftSecondMem hfirst hsecond
          have hmatchingNodup :
              (left.selectionSet.map matchingRight).Nodup :=
            list_map_nodup_of_injective_on hleftSetNodup hmatchingInjective
          have hmatchingSubset : ∀ rightSelection,
              rightSelection ∈ left.selectionSet.map matchingRight ->
                rightSelection ∈ right.selectionSet := by
            intro rightSelection hrightMem
            rcases List.mem_map.mp hrightMem with
              ⟨leftSelection, hleftMem, rfl⟩
            exact (matchingRight_spec leftSelection hleftMem).1
          have hrightSubset : ∀ rightSelection,
              rightSelection ∈ right.selectionSet ->
                rightSelection ∈ left.selectionSet.map matchingRight := by
            intro rightSelection hrightMem
            rcases hrightTotal rightSelection hrightMem with
              ⟨leftSelection, hleftMem, hreverse⟩
            have hforward := matchingRight_spec leftSelection hleftMem
            have hequal :=
              completeNormalSelectionMatch_reverse_right_unique
                hrightComplete (by simp) (by simp) hforward.1 hrightMem
                hforward.2 hreverse
            exact List.mem_map.mpr ⟨leftSelection, hleftMem, hequal⟩
          have hmatchingPerm :
              (left.selectionSet.map matchingRight).Perm
                right.selectionSet :=
            letI : BEq Selection := instBEqOfDecidableEq
            GroundTypeNormalization.listPermOfNodupSubsetSubset
              hmatchingNodup hrightSetNodup hmatchingSubset hrightSubset
          let pairs := left.selectionSet.map fun leftSelection =>
            (leftSelection, matchingRight leftSelection)
          have hpairsLeft : (pairs.map Prod.fst).Perm left.selectionSet := by
            simp [pairs, Function.comp_def]
          have hpairsRight : (pairs.map Prod.snd).Perm right.selectionSet := by
            simpa [pairs, Function.comp_def] using hmatchingPerm
          have hpairsEqual : ∀ pair, pair ∈ pairs ->
              CompleteNormalSelectionEqualUpToReordering
                (leftVar :: leftVariables) (rightVar :: rightVariables)
                pair.1 pair.2 := by
            intro pair hpair
            rcases List.mem_map.mp hpair with
              ⟨leftSelection, hleftMem, rfl⟩
            exact completeNormalSelectionEqualUpToReordering_of_match
              (matchingRight_spec leftSelection hleftMem).2
          simpa [hleftVars] using
            (show CompleteNormalSelectionSetEqualUpToReordering
                (leftVar :: leftVariables) (rightVar :: rightVariables)
                left.selectionSet right.selectionSet from
              ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩)

theorem complete_normal_operations_semanticallyEquivalent_equalUpToReordering
    {schema : Schema} {left right : Operation}
    : completeNormalOperationsSemanticallyEquivalentEqualUpToReordering
        schema left right := by
  intro hschema hleftValid hrightValid hleftNormal hrightNormal hsem
  have hvariables :=
    operationBoolVarsEquivalent_of_completeNormal_semantics hschema
      hleftValid hrightValid hleftNormal hrightNormal hsem
  exact
    complete_normal_operations_equalUpToReordering_of_complete_bool_vars_semantics
      hschema hleftValid hrightValid hleftNormal hrightNormal hvariables
      (fun resolvers variableValues fuel source _hcomplete =>
        hsem resolvers variableValues fuel source)

end CompleteNormalization

end NormalForm

end GraphQL
