import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.CaseBodies
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness

/-!
Recovery of the Boolean-variable support of valid complete-normal operations from
unrestricted semantic equivalence.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

private theorem collectFields_ne_nil_of_normal_object_nonempty
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    {selectionSet : List Selection}
    (hobject : objectTypeNameBool schema parentType = true)
    (hnormal : selectionSetNormal schema parentType selectionSet)
    (hfree : selectionSetDirectiveFree selectionSet)
    (hnonempty : selectionSet ≠ [])
    : Execution.collectFields schema variableValues parentType source selectionSet
      ≠ [] := by
  rcases
      GroundTypeNormalization.selectionSetNormal_field_mem_of_object_nonempty
        hnormal hobject hnonempty with
    ⟨responseName, fieldName, arguments, directives, childSelectionSet, hmem⟩
  have hresponseNameMem :
      responseName ∈ selectionSet.filterMap Selection.responseName? :=
    List.mem_filterMap.mpr
      ⟨Selection.field responseName fieldName arguments directives
          childSelectionSet, hmem, by simp [Selection.responseName?]⟩
  have hcollectKey :
      responseName ∈
        (Execution.collectFields schema variableValues parentType source
          selectionSet).map Prod.fst :=
    (GroundTypeNormalization.ExecutionKeys.collectFields_normal_object_key_mem_iff
        schema variableValues
        parentType source responseName hobject hnormal hfree).2
      hresponseNameMem
  intro hnil
  simp [hnil] at hcollectKey

private theorem lookupVariableValue?_boolCaseVariableValues_base_of_not_mem
    (boolCase : BoolCase) (varName : BoolVar)
    (hnotMem : varName ∉ boolCase.map Prod.fst)
    : Execution.lookupVariableValue?
        (boolCaseVariableValues boolCase [(varName, .null)]) varName
      = some .null := by
  induction boolCase with
  | nil =>
      simp [boolCaseVariableValues, Execution.lookupVariableValue?]
  | cons pair rest ih =>
      rcases pair with ⟨candidate, value⟩
      have hcandidate : candidate ≠ varName := by
        intro heq
        subst candidate
        exact hnotMem (by simp)
      have hrest : varName ∉ rest.map Prod.fst := by
        intro hmem
        exact hnotMem (by simp [hmem])
      simpa [boolCaseVariableValues, Execution.lookupVariableValue?, hcandidate]
        using ih hrest

private theorem inputValueBoolean?_coerceVariableValues_eq_none_of_case_base_null
    (operation : Operation) (boolCase : BoolCase) (varName : BoolVar)
    (hnotMem : varName ∉ boolCase.map Prod.fst)
    : Execution.inputValueBoolean?
        (Execution.coerceVariableValues operation
          (boolCaseVariableValues boolCase [(varName, .null)]))
        (.variable varName)
      = none := by
  have hlookup :=
    lookupVariableValue?_boolCaseVariableValues_base_of_not_mem
      boolCase varName hnotMem
  have hcoerced :=
    lookupVariableValue?_coerceVariableValues_eq_some operation
      (boolCaseVariableValues boolCase [(varName, .null)]) hlookup
  simp [Execution.inputValueBoolean?, hcoerced, InputValue.staticBoolean?]

private theorem executeQueryWithFuel_zero_data_eq_null_of_collectFields_ne_nil
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation)
    (source : Execution.ResolverValue ObjectRef)
    (hroot : Execution.rootSourceAppliesBool schema operation source = true)
    (hcollect
      : Execution.collectFields schema
          (Execution.coerceVariableValues operation variableValues)
          operation.rootType source operation.selectionSet
        ≠ [])
    : (Execution.executeQueryWithFuel schema resolvers variableValues operation
        0 source).data
      = .null := by
  let coercedValues := Execution.coerceVariableValues operation variableValues
  have hwellFormed :=
    GroundTypeNormalization.collectFields_wellFormed schema coercedValues
      operation.rootType source operation.selectionSet
  generalize hgroups :
      Execution.collectFields schema coercedValues operation.rootType source
        operation.selectionSet = groups at hwellFormed
  have hgroupsNonempty : groups ≠ [] := by
    intro hnil
    apply hcollect
    simpa [coercedValues, hgroups] using hnil
  cases groups with
  | nil =>
      exact False.elim (hgroupsNonempty rfl)
  | cons group rest =>
      rcases group with ⟨responseName, fields⟩
      have hfields : fields ≠ [] :=
        (hwellFormed (responseName, fields) (by simp)).1
      cases fields with
      | nil =>
          exact False.elim (hfields rfl)
      | cons field fields =>
          cases htail :
              Execution.executeCollectedFields schema resolvers coercedValues
                0 source rest <;>
            simp [Execution.executeQueryWithFuel, hroot,
              Execution.executeRootSelectionSet, coercedValues, hgroups,
              Execution.executeCollectedFields, Execution.executeField,
              Execution.outOfFuel, Execution.Result.combine,
              Execution.selectionSetResultToResponse, htail]

private theorem exists_values_missing_for_left_active_for_right
    {schema : Schema} {left right : Operation} {varName : BoolVar}
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hrightNormal : completeNormalOperation schema right)
    (hobject : objectTypeNameBool schema right.rootType = true)
    (hnotRight : varName ∉ operationBoolVars right)
    (source : Execution.ResolverValue ObjectRef)
    : ∃ variableValues,
        Execution.inputValueBoolean?
            (Execution.coerceVariableValues left variableValues)
            (.variable varName)
          = none
        ∧ Execution.collectFields schema
            (Execution.coerceVariableValues right variableValues)
            right.rootType source right.selectionSet
          ≠ [] := by
  have hrightNonempty :=
    Validation.operationDefinitionValid_selectionSet_nonempty hrightValid
  have hrightSelectionValid :=
    Validation.operationDefinitionValid_selectionSetValid hrightValid
  cases hrightVars : operationBoolVars right with
  | nil =>
      have hshape := hrightNormal
      simp [completeNormalOperation, completeNormalSelectionSet, hrightVars]
        at hshape
      refine ⟨boolCaseVariableValues [] [(varName, .null)], ?_, ?_⟩
      · exact
          inputValueBoolean?_coerceVariableValues_eq_none_of_case_base_null
            left [] varName (by simp)
      · exact collectFields_ne_nil_of_normal_object_nonempty schema
          (Execution.coerceVariableValues right
            (boolCaseVariableValues [] [(varName, .null)]))
          right.rootType source hobject hshape.1 hshape.2 hrightNonempty
  | cons rightVar rightVariables =>
      have hcomplete :
          completeNormalSelectionSet schema (rightVar :: rightVariables)
            right.rootType right.selectionSet := by
        simpa [completeNormalOperation, hrightVars] using hrightNormal
      cases hselectionSet : right.selectionSet with
      | nil =>
          exact False.elim (hrightNonempty hselectionSet)
      | cons selection rest =>
          rcases hcomplete.2.2.1 selection (by simp [hselectionSet]) with
            ⟨boolCase, body, hcase, hstem, hbodyNormal, hbodyFree⟩
          have hselectionValid :
              Validation.selectionValid schema right.variableDefinitions
                right.rootType selection := by
            unfold Validation.selectionSetValid at hrightSelectionValid
            exact hrightSelectionValid selection (by simp [hselectionSet])
          have hbodyValidNonempty :=
            completeNormalBooleanStem_body_valid_nonempty hstem
              hselectionValid
          have hnotCase : varName ∉ boolCase.map Prod.fst := by
            intro hmem
            have hsupport : varName ∈ rightVar :: rightVariables :=
              (hcase.2.2 varName).1 hmem
            exact hnotRight (by simpa [hrightVars] using hsupport)
          let variableValues :=
            boolCaseVariableValues boolCase [(varName, .null)]
          have hagrees :
              variableValuesAgreeWithCase
                (Execution.coerceVariableValues right variableValues)
                boolCase (rightVar :: rightVariables) := by
            intro candidate hcandidate
            rcases boolVarsComplete_boolCaseVariableValues
                [(varName, .null)] hcase candidate hcandidate with
              ⟨value, hvalue⟩
            have hprepared :=
              inputValueBoolean?_coerceVariableValues_eq_some right
                variableValues hvalue
            exact hprepared.trans
              (hvalue.symm.trans
                (variableValuesAgreeWithCase_boolCaseVariableValues
                  [(varName, .null)] hcase candidate hcandidate))
          have hcollectBody :
              Execution.collectFields schema
                  (Execution.coerceVariableValues right variableValues)
                  right.rootType source right.selectionSet
                =
              Execution.collectFields schema
                  (Execution.coerceVariableValues right variableValues)
                  right.rootType source body := by
            exact
              collectFields_completeNormalSelectionSet_eq_body_of_equivalent_of_agrees
                schema (Execution.coerceVariableValues right variableValues)
                right.rootType source hcomplete (by simp [hselectionSet])
                hcase hcase hagrees
                (completeNormalBoolCasesEquivalent_refl boolCase)
                hstem hbodyFree
          have hbodyCollectNonempty :
              Execution.collectFields schema
                  (Execution.coerceVariableValues right variableValues)
                  right.rootType source body
                ≠ [] :=
            collectFields_ne_nil_of_normal_object_nonempty schema
              (Execution.coerceVariableValues right variableValues)
              right.rootType source hobject hbodyNormal hbodyFree
              hbodyValidNonempty.2
          refine ⟨variableValues, ?_, ?_⟩
          · exact
              inputValueBoolean?_coerceVariableValues_eq_none_of_case_base_null
                left boolCase varName hnotCase
          · intro hnil
            exact hbodyCollectNonempty (by
              rw [← hcollectBody]
              simpa [hselectionSet] using hnil)

private theorem operationBoolVars_subset_of_completeNormal_semantics
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hsem : operationsSemanticallyEquivalent schema left right)
    : ∀ varName,
        varName ∈ operationBoolVars left -> varName ∈ operationBoolVars right := by
  intro varName hleftMem
  apply Classical.byContradiction
  intro hrightMem
  have hroot :=
    GroundTypeNormalization.operation_rootType_eq_of_operationDefinitionValid
      hleftValid hrightValid
  have hleftObject :=
    GroundTypeNormalization.operation_root_objectTypeNameBool_of_wf_valid
      hschema hleftValid
  have hrightObject :
      objectTypeNameBool schema right.rootType = true := by
    simpa [← hroot] using hleftObject
  let source : Execution.ResolverValue PUnit :=
    .object left.rootType PUnit.unit
  rcases
      exists_values_missing_for_left_active_for_right
        (left := left) hrightValid hrightNormal hrightObject hrightMem source with
    ⟨variableValues, hleftMissing, hrightCollectNonempty⟩
  cases hleftVars : operationBoolVars left with
  | nil =>
      simp [hleftVars] at hleftMem
  | cons leftVar leftVariables =>
      have hleftComplete :
          completeNormalSelectionSet schema (leftVar :: leftVariables)
            left.rootType left.selectionSet := by
        simpa [completeNormalOperation, hleftVars] using hleftNormal
      have hleftVarMem : varName ∈ leftVar :: leftVariables := by
        simpa [hleftVars] using hleftMem
      have hleftCollect :
          Execution.collectFields schema
              (Execution.coerceVariableValues left variableValues)
              left.rootType source left.selectionSet
            = [] :=
        collectFields_completeNormalSelectionSet_eq_nil_of_missing_variable
          schema (Execution.coerceVariableValues left variableValues)
          left.rootType source hleftComplete hleftVarMem hleftMissing
      have hrootIncludes :
          schema.typeIncludesObjectBool left.rootType left.rootType = true :=
        GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
          schema hleftObject
      have hleftRoot :
          Execution.rootSourceAppliesBool schema left source = true := by
        simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
          source, hrootIncludes]
      have hrightRoot :
          Execution.rootSourceAppliesBool schema right source = true := by
        simp [Execution.rootSourceAppliesBool, Execution.runtimeObjectType?,
          source, ← hroot, hrootIncludes]
      let resolvers : Execution.Resolvers PUnit :=
        GroundTypeNormalization.schemaSuccessResolvers schema
      have hleftData :
          (Execution.executeQueryWithFuel schema resolvers variableValues left
            0 source).data
            = .object [] := by
        simp [Execution.executeQueryWithFuel, hleftRoot,
          Execution.executeRootSelectionSet, hleftCollect,
          Execution.executeCollectedFields,
          Execution.selectionSetResultToResponse]
      have hrightData :
          (Execution.executeQueryWithFuel schema resolvers variableValues right
            0 source).data
            = .null :=
        executeQueryWithFuel_zero_data_eq_null_of_collectFields_ne_nil
          schema resolvers variableValues right source hrightRoot
          hrightCollectNonempty
      have hresponse := hsem resolvers variableValues 0 source
      have hdata := hresponse.1
      rw [hleftData, hrightData] at hdata
      simp [Execution.ResponseValue.semanticEquivalent,
        Execution.ResponseValue.canonical] at hdata

theorem operationBoolVarsEquivalent_of_completeNormal_semantics
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hsem : operationsSemanticallyEquivalent schema left right)
    : operationBoolVarsEquivalent left right := by
  intro varName
  constructor
  · exact operationBoolVars_subset_of_completeNormal_semantics hschema
      hleftValid hrightValid hleftNormal hrightNormal hsem varName
  · have hsemSymm : operationsSemanticallyEquivalent schema right left := by
      intro ObjectRef resolvers variableValues fuel source
      have hresponse := hsem resolvers variableValues fuel source
      exact ⟨hresponse.1.symm, hresponse.2.symm⟩
    exact operationBoolVars_subset_of_completeNormal_semantics hschema
      hrightValid hleftValid hrightNormal hleftNormal hsemSymm varName

end CompleteNormalization

end NormalForm

end GraphQL
