import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.CaseBodies
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.ReorderingVariables
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.StemExecution
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Semantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ReadinessPreservation
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

private theorem completeNormalBooleanStem_body_argumentsNodup
    : ∀ {boolCase : BoolCase} {selection : Selection} {body : List Selection},
        completeNormalBooleanStem boolCase selection body
        -> Execution.selectionArgumentsNodup selection
        -> Execution.selectionSetArgumentsNodup body
  | [], _selection, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | [(varName, value)],
      .inlineFragment none [directive] selectionSet, body, hstem, hnodup => by
      rcases hstem with ⟨_hdirective, hbody⟩
      subst selectionSet
      exact hnodup
  | (varName, value) :: (nextVar, nextValue) :: rest,
      .inlineFragment none [directive] [child], body, hstem, hnodup => by
      rcases hstem with ⟨_hdirective, hchildStem⟩
      exact completeNormalBooleanStem_body_argumentsNodup hchildStem hnodup.1
  | _ :: _ :: _, .field _ _ _ _ _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none [] _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment none (_ :: _ :: _) _, _body, hstem,
      _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | _ :: _ :: _, .inlineFragment (some _) _ _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .field _ _ _ _ _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none [] _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment none (_ :: _ :: _) _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem
  | [_], .inlineFragment (some _) _ _, _body, hstem, _hnodup => by
      simp [completeNormalBooleanStem] at hstem

private theorem selection_size_pos_for_filter_nodup (selection : Selection)
    : 0 < selection.size := by
  cases selection <;> simp [Selection.size] <;> omega

private theorem selectionSet_size_tail_lt_cons_for_filter_nodup
    (selection : Selection) (rest : List Selection)
    : SelectionSet.size rest < SelectionSet.size (selection :: rest) := by
  simp [SelectionSet.size]
  exact Nat.lt_add_of_pos_left (selection_size_pos_for_filter_nodup selection)

private theorem selectionSet_size_child_lt_cons_field_for_filter_nodup
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem selectionSet_size_child_lt_cons_inline_for_filter_nodup
    (typeCondition : Option Name) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : SelectionSet.size selectionSet
      < SelectionSet.size
          (Selection.inlineFragment typeCondition directives selectionSet :: rest) := by
  simp [SelectionSet.size, Selection.size]
  omega

private theorem filterSelectionSetBoolCase_argumentsNodup (boolCase : BoolCase)
    : ∀ selectionSet,
        Execution.selectionSetArgumentsNodup selectionSet
        -> Execution.selectionSetArgumentsNodup
            (filterSelectionSetBoolCase boolCase selectionSet)
  | [], _hnodup => by
      simp [filterSelectionSetBoolCase, Execution.selectionSetArgumentsNodup]
  | selection :: rest, hnodup => by
      have hrest := filterSelectionSetBoolCase_argumentsNodup boolCase rest hnodup.2
      cases selection with
      | field responseName fieldName arguments directives selectionSet =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · have hchild := filterSelectionSetBoolCase_argumentsNodup boolCase
              selectionSet hnodup.1.2
            cases selectionSet with
            | nil =>
                simpa [filterSelectionSetBoolCase, hallow,
                  Execution.selectionSetArgumentsNodup,
                  Execution.selectionArgumentsNodup] using
                  (show Execution.selectionSetArgumentsNodup
                    (Selection.field responseName fieldName arguments [] [] ::
                      filterSelectionSetBoolCase boolCase rest) from
                    ⟨⟨hnodup.1.1, by simp [Execution.selectionSetArgumentsNodup]⟩,
                      hrest⟩)
            | cons child children =>
                cases hfiltered : filterSelectionSetBoolCase boolCase
                    (child :: children) with
                | nil =>
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered,
                      Execution.selectionSetArgumentsNodup,
                      Execution.selectionArgumentsNodup] using
                      (show Execution.selectionSetArgumentsNodup
                        (Selection.field responseName fieldName arguments [] [] ::
                          filterSelectionSetBoolCase boolCase rest) from
                        ⟨⟨hnodup.1.1,
                            by simp [Execution.selectionSetArgumentsNodup]⟩,
                          hrest⟩)
                | cons filteredChild filteredChildren =>
                    have hfilteredNodup :
                        Execution.selectionSetArgumentsNodup
                          (filteredChild :: filteredChildren) := by
                      simpa [hfiltered] using hchild
                    simpa [filterSelectionSetBoolCase, hallow, hfiltered,
                      Execution.selectionSetArgumentsNodup,
                      Execution.selectionArgumentsNodup] using
                      (show Execution.selectionSetArgumentsNodup
                        (Selection.field responseName fieldName arguments []
                          (filteredChild :: filteredChildren) ::
                            filterSelectionSetBoolCase boolCase rest) from
                        ⟨⟨hnodup.1.1, hfilteredNodup⟩, hrest⟩)
          · have hfalse : directivesAllowIn boolCase directives = false := by
              cases h : directivesAllowIn boolCase directives <;> simp_all
            simpa [filterSelectionSetBoolCase, hfalse] using hrest
      | inlineFragment typeCondition directives selectionSet =>
          by_cases hallow : directivesAllowIn boolCase directives = true
          · have hchild := filterSelectionSetBoolCase_argumentsNodup boolCase
              selectionSet hnodup.1
            cases hfiltered : filterSelectionSetBoolCase boolCase selectionSet with
            | nil =>
                simpa [filterSelectionSetBoolCase, hallow, hfiltered] using hrest
            | cons filteredChild filteredChildren =>
                have hfilteredNodup : Execution.selectionSetArgumentsNodup
                    (filteredChild :: filteredChildren) := by
                  simpa [hfiltered] using hchild
                simpa [filterSelectionSetBoolCase, hallow, hfiltered,
                  Execution.selectionSetArgumentsNodup,
                  Execution.selectionArgumentsNodup] using
                  (show Execution.selectionSetArgumentsNodup
                    (Selection.inlineFragment typeCondition []
                      (filteredChild :: filteredChildren) ::
                        filterSelectionSetBoolCase boolCase rest) from
                    ⟨hfilteredNodup, hrest⟩)
          · have hfalse : directivesAllowIn boolCase directives = false := by
              cases h : directivesAllowIn boolCase directives <;> simp_all
            simpa [filterSelectionSetBoolCase, hfalse] using hrest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    first
    | exact selectionSet_size_tail_lt_cons_for_filter_nodup selection rest
    | exact selectionSet_size_child_lt_cons_field_for_filter_nodup
        responseName fieldName arguments directives selectionSet rest
    | simp_all [SelectionSet.size, Selection.size]
      omega

private theorem wrapWithBoolCase_argumentsNodup
    (boolCase : BoolCase) {selectionSet : List Selection}
    (hnodup : Execution.selectionSetArgumentsNodup selectionSet)
    : Execution.selectionSetArgumentsNodup (wrapWithBoolCase boolCase selectionSet) := by
  induction boolCase with
  | nil => exact hnodup
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      simp [wrapWithBoolCase, Execution.selectionSetArgumentsNodup,
        Execution.selectionArgumentsNodup, ih]

private theorem selectionSetArgumentsNodup_flatten
    : ∀ selectionSets : List (List Selection),
        (∀ selectionSet,
          selectionSet ∈ selectionSets
          -> Execution.selectionSetArgumentsNodup selectionSet)
        -> Execution.selectionSetArgumentsNodup selectionSets.flatten
  | [], _hnodup => by simp [Execution.selectionSetArgumentsNodup]
  | selectionSet :: rest, hnodup => by
      rw [List.flatten_cons]
      exact GroundTypeNormalization.selectionSetArgumentsNodup_append
        (hnodup selectionSet (by simp))
        (selectionSetArgumentsNodup_flatten rest fun candidate hmem =>
          hnodup candidate (by simp [hmem]))

private theorem completeNormalizeRootSelectionSet_argumentsNodup
    (schema : Schema) (variables : List BoolVar) (parentType : Name)
    {selectionSet : List Selection}
    (hnodup : Execution.selectionSetArgumentsNodup selectionSet)
    : Execution.selectionSetArgumentsNodup
        (completeNormalizeRootSelectionSet schema variables parentType selectionSet) := by
  unfold completeNormalizeRootSelectionSet
  apply selectionSetArgumentsNodup_flatten
  intro normalizedBranch hbranch
  rcases List.mem_map.mp hbranch with ⟨boolCase, _hcase, rfl⟩
  have hfiltered := filterSelectionSetBoolCase_argumentsNodup boolCase
    selectionSet hnodup
  have hnormalized :=
    GroundTypeNormalization.normalizeSelectionSet_argumentsNodup schema
      parentType (filterSelectionSetBoolCase boolCase selectionSet) hfiltered
  cases hcaseNormalized
        : normalizeSelectionSet schema
            parentType (filterSelectionSetBoolCase boolCase selectionSet) with
  | nil => simp [Execution.selectionSetArgumentsNodup]
  | cons selection rest =>
      apply wrapWithBoolCase_argumentsNodup
      simpa [hcaseNormalized] using hnormalized

private theorem completeNormalizeOperation_selectionSetArgumentsNodup
    (schema : Schema) (operation : Operation)
    (hnodup : Execution.selectionSetArgumentsNodup operation.selectionSet)
    : Execution.selectionSetArgumentsNodup
        (completeNormalizeOperation schema operation).selectionSet := by
  rw [completeNormalizeOperation_selectionSet]
  exact completeNormalizeRootSelectionSet_argumentsNodup schema
    (operationBoolVars operation) (operation.rootType schema) hnodup

private def CompleteNormalBodyEquality
    (schema : Schema) (leftOperation rightOperation : Operation)
    (parentType : Name) (leftVariables rightVariables : List BoolVar)
    (leftCase rightCase : BoolCase) (leftBody rightBody : List Selection)
    : Prop :=
  ∀ variableValues,
    operationArgumentsCoercible schema variableValues leftOperation
    -> operationArgumentsCoercible schema variableValues rightOperation
    -> boolVarsComplete leftVariables variableValues
    -> variableValuesAgreeWithCase
        (Execution.coerceVariableValues leftOperation variableValues)
        leftCase leftVariables
    -> variableValuesAgreeWithCase
        (Execution.coerceVariableValues rightOperation variableValues)
        rightCase rightVariables
    -> SelectionSetEqualUpToReorderingWithCoercion schema
        (Execution.coerceVariableValues leftOperation variableValues)
        (Execution.coerceVariableValues rightOperation variableValues)
        parentType leftBody rightBody

private theorem variableValuesAgreeWithCase_of_equivalent
    {leftValues rightValues : Execution.VariableValues}
    (hvalues : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    {leftVariables rightVariables : List BoolVar}
    (hvariables : ∀ name, name ∈ leftVariables ↔ name ∈ rightVariables)
    {leftCase rightCase : BoolCase}
    (hleftCase : completeNormalBoolCase leftVariables leftCase)
    (hrightCase : completeNormalBoolCase rightVariables rightCase)
    (hcases : completeNormalBoolCasesEquivalent leftCase rightCase)
    (hagrees : variableValuesAgreeWithCase leftValues leftCase leftVariables)
    : variableValuesAgreeWithCase rightValues rightCase rightVariables := by
  intro name hrightMem
  have hleftMem : name ∈ leftVariables := (hvariables name).2 hrightMem
  have hleftPairMem : name ∈ leftCase.map Prod.fst :=
    (hleftCase.2.2 name).2 hleftMem
  rcases List.mem_map.mp hleftPairMem with
    ⟨⟨candidate, value⟩, hleftPair, hcandidate⟩
  change candidate = name at hcandidate
  subst candidate
  have hrightPair : (name, value) ∈ rightCase :=
    (hcases name value).1 hleftPair
  have hleftLookup : BoolCase.lookup? leftCase name = some value :=
    BoolCase.lookup?_eq_of_pair_mem_nodup hleftCase.2.1 hleftPair
  have hrightLookup : BoolCase.lookup? rightCase name = some value :=
    BoolCase.lookup?_eq_of_pair_mem_nodup hrightCase.2.1 hrightPair
  rw [hrightLookup, ← hleftLookup, ← hagrees name hleftMem]
  exact (inputValueBoolean?_eq_of_variableValuesCoercionEquivalent hvalues
          (.variable name)).symm

private theorem completeNormalSelectionSets_semanticallyEquivalent_of_equal
    {schema : Schema} {leftOperation rightOperation : Operation}
    {variableValues : Execution.VariableValues} {parentType : Name}
    {leftVar rightVar : BoolVar}
    {leftVariables rightVariables : List BoolVar}
    {left right : List Selection}
    (hleftArgumentsNodup : Execution.selectionSetArgumentsNodup left)
    (hrightArgumentsNodup : Execution.selectionSetArgumentsNodup right)
    (hleftNormal
      : completeNormalSelectionSet schema (leftVar :: leftVariables) parentType left)
    (hrightNormal
      : completeNormalSelectionSet schema (rightVar :: rightVariables) parentType right)
    (hvariables
      : ∀ varName,
          varName ∈ leftVar :: leftVariables ↔ varName ∈ rightVar :: rightVariables)
    (hleftDefinitionsNodup
      : (leftOperation.variableDefinitions.map VariableDefinition.name).Nodup)
    (hrightDefinitionsNodup
      : (rightOperation.variableDefinitions.map VariableDefinition.name).Nodup)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent
          leftOperation.variableDefinitions rightOperation.variableDefinitions)
    (hleftValues
      : Execution.coerceVariableValues leftOperation variableValues = variableValues)
    (hleftOperationReady
      : operationArgumentsCoercible schema variableValues leftOperation)
    (hrightOperationReady
      : operationArgumentsCoercible schema variableValues rightOperation)
    (hcomplete : boolVarsComplete (leftVar :: leftVariables) variableValues)
    (hobject : objectTypeNameBool schema parentType = true)
    (hequal
      : CompleteNormalSelectionSetEqualUpToReorderingWithCoercion schema
          leftOperation rightOperation parentType
          (leftVar :: leftVariables) (rightVar :: rightVariables) left right)
    : selectionSetsSemanticallyEquivalentAtVariableValues schema
        variableValues variableValues parentType left right := by
  classical
  rcases hequal with ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩
  have hpreparedValues :
      Execution.variableValuesCoercionEquivalent variableValues
        (Execution.coerceVariableValues rightOperation variableValues) := by
    have hcoerced :=
      Execution.coerceVariableValues_coercionEquivalent_of_variableDefinitionsSyntacticallyEquivalent
        (left := leftOperation) (right := rightOperation)
        hleftDefinitionsNodup hrightDefinitionsNodup
        (Execution.variableValuesCoercionEquivalent_refl variableValues)
        hdefinitions
    rwa [hleftValues] at hcoerced
  intro ObjectRef resolvers fuel source hsource
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
          ∧ CompleteNormalBodyEquality schema leftOperation rightOperation
              parentType (leftVar :: leftVariables) (rightVar :: rightVariables)
              leftCase rightCase leftBody rightBody
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
      have hleftBodyArgumentsNodup :=
        completeNormalBooleanStem_body_argumentsNodup hleftStem
          (Execution.selectionArgumentsNodup_of_mem hleftArgumentsNodup hleftMem)
      have hrightBodyArgumentsNodup :=
        completeNormalBooleanStem_body_argumentsNodup hrightStem
          (Execution.selectionArgumentsNodup_of_mem hrightArgumentsNodup hrightMem)
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
      have hagreesLeftCase :
          variableValuesAgreeWithCase variableValues leftCase
            (leftVar :: leftVariables) :=
        variableValuesAgreeWithCase_of_equivalent
          (Execution.variableValuesCoercionEquivalent_refl variableValues)
          (fun name => Iff.rfl) hruntimeLeft hleftCase hruntimeEqual hagreesLeft
      have hagreesRightCase :
          variableValuesAgreeWithCase
            (Execution.coerceVariableValues rightOperation variableValues)
            rightCase (rightVar :: rightVariables) :=
        variableValuesAgreeWithCase_of_equivalent hpreparedValues hvariables
          hleftCase hrightCase hcasesEqual hagreesLeftCase
      have hbodiesEqualCross := hbodiesEqual variableValues hleftOperationReady
        hrightOperationReady hcomplete
        (by simpa [hleftValues] using hagreesLeftCase) hagreesRightCase
      rw [hleftValues] at hbodiesEqualCross
      have hbodiesEqualSame :=
        GroundTypeNormalization.selectionSetEqualUpToReorderingWithCoercion_right_to_left
          hpreparedValues hbodiesEqualCross
      have hbodySem :
          selectionSetsSemanticallyEquivalentAtVariableValues schema
            variableValues variableValues parentType leftBody rightBody :=
        GroundTypeNormalization.selectionSetsSemanticallyEquivalent_of_equalUpToReordering
          hleftBodyArgumentsNodup hrightBodyArgumentsNodup hleftBody.2
          hrightBody.2 hleftBody.1 hrightBody.1 hobject hbodiesEqualSame
      unfold Execution.executeSelectionSetAsResponse
      rw [hleftExecute, hrightExecute]
      simpa [Execution.executeSelectionSetAsResponse] using
        hbodySem resolvers fuel source hsource
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
            CompleteNormalBodyEquality schema leftOperation rightOperation
              parentType (leftVar :: leftVariables) (rightVar :: rightVariables)
              candidate rightCase body rightBody := by
          simpa [CompleteNormalBodyEquality, hcaseBodyEq.1, hcaseBodyEq.2] using
            hbodiesEqual
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
            CompleteNormalBodyEquality schema leftOperation rightOperation
              parentType (leftVar :: leftVariables) (rightVar :: rightVariables)
              leftCase candidate leftBody body := by
          simpa [CompleteNormalBodyEquality, hcaseBodyEq.1, hcaseBodyEq.2] using
            hbodiesEqual
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

private theorem
    complete_normal_operations_equalUpToReordering_semanticallyEquivalent_of_argumentsNodup
    {schema : Schema} {left right : Operation}
    (hrootObject : objectTypeNameBool schema (left.rootType schema) = true)
    (hleftArgumentsNodup : Execution.selectionSetArgumentsNodup left.selectionSet)
    (hrightArgumentsNodup : Execution.selectionSetArgumentsNodup right.selectionSet)
    (hleftDefinitionsNodup : (left.variableDefinitions.map VariableDefinition.name).Nodup)
    (hrightDefinitionsNodup
      : (right.variableDefinitions.map VariableDefinition.name).Nodup)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hdefinitions
      : variableDefinitionsSyntacticallyEquivalent left.variableDefinitions
          right.variableDefinitions)
    (hequal : completeNormalOperationsEqualUpToReorderingWithCoercion schema left right)
    : operationsSemanticallyEquivalentForCompleteBoolVars schema
        (operationBoolVars left) left right := by
  rcases hequal with ⟨_hroot, hvariables, hselectionEqual⟩
  have hrootType : (left.rootType schema) = (right.rootType schema) := by
    cases left.operationType
    cases right.operationType
    rfl
  intro ObjectRef resolvers variableValues fuel source hboolComplete
    hleftOperationReady hrightOperationReady
  have hcoercedValues :
      Execution.variableValuesCoercionEquivalent
        (Execution.coerceVariableValues left variableValues)
        (Execution.coerceVariableValues right variableValues) :=
    Execution.coerceVariableValues_coercionEquivalent_of_variableDefinitionsSyntacticallyEquivalent
      hleftDefinitionsNodup hrightDefinitionsNodup
      (Execution.variableValuesCoercionEquivalent_refl variableValues)
      hdefinitions
  have hleftEffectiveReady :
      operationArgumentsCoercible schema
        (Execution.coerceVariableValues left variableValues) left := by
    unfold operationArgumentsCoercible at hleftOperationReady ⊢
    rw [coerceVariableValues_idempotent]
    exact hleftOperationReady
  have hrightEffectiveReady :
      operationArgumentsCoercible schema
        (Execution.coerceVariableValues left variableValues) right := by
    unfold operationArgumentsCoercible at hrightOperationReady ⊢
    apply selectionSetArgumentsCoercible_of_variableValuesCoercionEquivalent
      (parentType := right.rootType schema)
      (selectionSet := right.selectionSet)
      (rightValues := Execution.coerceVariableValues right variableValues)
    · have hdefinitionsRefl :
          variableDefinitionsSyntacticallyEquivalent right.variableDefinitions
            right.variableDefinitions := by
        constructor
        <;> intro definition hmember
        <;>
            refine ⟨definition, hmember, rfl, rfl, ?_⟩
        <;> cases definition.defaultValue with
        | none => trivial
        | some defaultValue =>
            exact GroundTypeNormalization.inputValue_equivalent_refl _
      have hcoercedAgain :=
        Execution.coerceVariableValues_coercionEquivalent_of_variableDefinitionsSyntacticallyEquivalent
          (left := right) (right := right) hrightDefinitionsNodup
          hrightDefinitionsNodup hcoercedValues hdefinitionsRefl
      simpa [coerceVariableValues_idempotent] using hcoercedAgain
    · exact hrightOperationReady
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
      have hselectionResponse :
          Execution.Response.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues left variableValues) fuel
              (left.rootType schema) source left.selectionSet)
            (Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues left variableValues) fuel
              (left.rootType schema) source right.selectionSet) := by
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
                selectionSetNormal schema (left.rootType schema)
                  right.selectionSet := by
              simpa only [hrootType] using hrightShape.1
            have hselectionEqualCross :
                SelectionSetEqualUpToReorderingWithCoercion schema
                  (Execution.coerceVariableValues left variableValues)
                  (Execution.coerceVariableValues right variableValues)
                  (left.rootType schema) left.selectionSet right.selectionSet := by
              have hselectionEqualGround := hselectionEqual
              rw [hleftVars] at hselectionEqualGround
              exact hselectionEqualGround variableValues hleftOperationReady
                hrightOperationReady
            have hselectionEqualSame :=
              GroundTypeNormalization.selectionSetEqualUpToReorderingWithCoercion_right_to_left
                hcoercedValues hselectionEqualCross
            exact
              GroundTypeNormalization.selectionSetsSemanticallyEquivalent_of_equalUpToReordering
                hleftArgumentsNodup hrightArgumentsNodup hleftShape.2
                hrightShape.2 hleftShape.1 hrightSelectionNormal hrootObject
                hselectionEqualSame resolvers fuel source hsource
        | cons leftVar leftVariables =>
            cases hrightVars : operationBoolVars right with
            | nil =>
                have hleftVarRight : leftVar ∈ operationBoolVars right :=
                  (hvariables leftVar).1 (by simp [hleftVars])
                simp [hrightVars] at hleftVarRight
            | cons rightVar rightVariables =>
                have hleftComplete : completeNormalSelectionSet schema
                    (leftVar :: leftVariables) (left.rootType schema)
                    left.selectionSet := by
                  simpa [completeNormalOperation, hleftVars] using hleftNormal
                have hrightComplete : completeNormalSelectionSet schema
                    (rightVar :: rightVariables) (left.rootType schema)
                    right.selectionSet := by
                  simpa [completeNormalOperation, hrightVars, hrootType] using
                    hrightNormal
                have hselectionEqualComplete :
                    CompleteNormalSelectionSetEqualUpToReorderingWithCoercion
                      schema left right (left.rootType schema)
                      (leftVar :: leftVariables) (rightVar :: rightVariables)
                      left.selectionSet right.selectionSet := by
                  simpa [hleftVars, hrightVars] using hselectionEqual
                have hvariablesAtSupports : ∀ varName,
                    varName ∈ leftVar :: leftVariables ↔
                      varName ∈ rightVar :: rightVariables := by
                  intro varName
                  simpa [hleftVars, hrightVars] using (hvariables varName)
                exact completeNormalSelectionSets_semanticallyEquivalent_of_equal
                  hleftArgumentsNodup hrightArgumentsNodup hleftComplete
                  hrightComplete hvariablesAtSupports hleftDefinitionsNodup
                  hrightDefinitionsNodup hdefinitions
                  (coerceVariableValues_idempotent left variableValues)
                  hleftEffectiveReady hrightEffectiveReady
                  (by
                    have hcoerced :=
                      operationBoolVarsComplete_coerceVariableValues left
                        variableValues hboolComplete
                    intro varName hmem
                    exact hcoerced varName (by simpa [hleftVars] using hmem))
                  hrootObject hselectionEqualComplete resolvers fuel source hsource
      have hrightExecution :
          Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues left variableValues) fuel
              (left.rootType schema) source right.selectionSet =
            Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues right variableValues) fuel
              (left.rootType schema) source right.selectionSet := by
        unfold Execution.executeSelectionSetAsResponse
        rw [executeSelectionSet_eq_of_variableValuesCoercionEquivalent schema
          resolvers hcoercedValues fuel (left.rootType schema) source
          right.selectionSet]
      have hselectionResponse' :
          Execution.Response.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues left variableValues) fuel
              (left.rootType schema) source left.selectionSet)
            (Execution.executeSelectionSetAsResponse schema resolvers
              (Execution.coerceVariableValues right variableValues) fuel
              (left.rootType schema) source right.selectionSet) := by
        rw [← hrightExecution]
        exact hselectionResponse
      simpa [Execution.executeQueryWithFuel, hleftRoot, hrightRoot,
        Execution.executeSelectionSetAsResponse, Execution.executeSelectionSet,
        Execution.executeRootSelectionSet, hrootType] using hselectionResponse'

theorem complete_normal_operations_equalUpToReordering_semanticallyEquivalent
    {schema : Schema} {left right : Operation}
    : completeNormalOperationsEqualUpToReorderingSemanticallyEquivalent
        schema left right := by
  intro hschema hleftValid hrightValid hleftNormal hrightNormal hdefinitions hequal
  exact
    complete_normal_operations_equalUpToReordering_semanticallyEquivalent_of_argumentsNodup
      (GroundTypeNormalization.operation_root_objectTypeNameBool_of_wf_valid
        hschema hleftValid)
      (Execution.selectionSetArgumentsNodup_of_selectionSetValid
        (Validation.operationDefinitionValid_selectionSetValid hleftValid))
      (Execution.selectionSetArgumentsNodup_of_selectionSetValid
        (Validation.operationDefinitionValid_selectionSetValid hrightValid))
      (Validation.operationDefinitionValid_variableDefinitionsValid hleftValid).1
      (Validation.operationDefinitionValid_variableDefinitionsValid hrightValid).1
      hleftNormal hrightNormal hdefinitions hequal

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
      variableDefinitionsSyntacticallyEquivalent
        (completeNormalizeOperation schema left).variableDefinitions
        (completeNormalizeOperation schema right).variableDefinitions := by
    simpa [completeNormalizeOperation_variableDefinitions] using hdefinitions
  have hnormalizedSemantics :
      operationsSemanticallyEquivalentForCompleteBoolVars schema
        (operationBoolVars (completeNormalizeOperation schema left))
        (completeNormalizeOperation schema left)
        (completeNormalizeOperation schema right) :=
    complete_normal_operations_equalUpToReordering_semanticallyEquivalent_of_argumentsNodup
      (by
        simpa [completeNormalizeOperation, Operation.rootType,
          OperationType.rootType] using
          GroundTypeNormalization.operation_root_objectTypeNameBool_of_wf_valid
            hschema hleftValid)
      (completeNormalizeOperation_selectionSetArgumentsNodup schema left
        (Execution.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hleftValid)))
      (completeNormalizeOperation_selectionSetArgumentsNodup schema right
        (Execution.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hrightValid)))
      (by
        simpa [completeNormalizeOperation_variableDefinitions] using
          (Validation.operationDefinitionValid_variableDefinitionsValid hleftValid).1)
      (by
        simpa [completeNormalizeOperation_variableDefinitions] using
          (Validation.operationDefinitionValid_variableDefinitionsValid hrightValid).1)
      hleftNormal hrightNormal hnormalizedDefinitions hequal
  intro ObjectRef resolvers variableValues fuel source hleftComplete hleftReady
    hrightReady
  have hrightComplete : operationBoolVarsComplete right variableValues := by
    intro varName hmem
    exact hleftComplete varName ((hvariables varName).2 hmem)
  have hleftPreserved := completeNormalizationSemanticsPreserved schema left
    hschema hleftValid resolvers variableValues fuel source
    (operationBoolVarsComplete_coerceVariableValues
      left variableValues hleftComplete)
  have hrightPreserved := completeNormalizationSemanticsPreserved schema right
    hschema hrightValid resolvers variableValues fuel source
    (operationBoolVarsComplete_coerceVariableValues
      right variableValues hrightComplete)
  have hleftNormalizedReady :
      operationArgumentsCoercible schema variableValues
        (completeNormalizeOperation schema left) :=
    operationArgumentsCoercible_completeNormalizeOperation schema left
      variableValues hschema hleftValid hleftComplete hleftReady
  have hrightNormalizedReady :
      operationArgumentsCoercible schema variableValues
        (completeNormalizeOperation schema right) :=
    operationArgumentsCoercible_completeNormalizeOperation schema right
      variableValues hschema hrightValid hrightComplete hrightReady
  have hrootObjectLeft : objectTypeNameBool schema (left.rootType schema) = true :=
    GroundTypeNormalization.operation_root_objectTypeNameBool_of_wf_valid
      hschema hleftValid
  -- Normalization only introduces case-wrapper directives over the source operation's
  -- Boolean support, so the normalized support is a subset of the original one.
  have hnormalizedLeftSubset : ∀ varName,
      varName ∈ operationBoolVars (completeNormalizeOperation schema left)
      -> varName ∈ operationBoolVars left := by
    intro varName hmem
    unfold operationBoolVars at hmem
    rw [completeNormalizeOperation_selectionSet] at hmem
    rw [mem_dedupBoolVars_iff] at hmem
    cases hleftVars : operationBoolVars left with
    | nil =>
        rw [hleftVars] at hmem
        have hnormal :=
          completeNormalizeRootSelectionSet_normal_nil schema hschema
            (left.rootType schema) left.selectionSet
            (completeNormalizeRootSelectionSet schema [] (left.rootType schema)
              left.selectionSet) hrootObjectLeft rfl
        rw [selectionSetDirectiveFree_booleanVariables_nil _ hnormal.2.2] at hmem
        simp at hmem
    | cons headVar restVariables =>
        have hvariablesNodup : (headVar :: restVariables).Nodup := by
          simpa [hleftVars] using operationBoolVars_nodup left
        have hnormal :=
          completeNormalizeRootSelectionSet_normal_cons schema hschema headVar
            restVariables hvariablesNodup (left.rootType schema) left.selectionSet
            (completeNormalizeRootSelectionSet schema (headVar :: restVariables)
              (left.rootType schema) left.selectionSet) hrootObjectLeft rfl
        rw [hleftVars] at hmem
        rcases hnormal with ⟨_hvariablesNodup, _hselectionSetNodup, hbranches, _hunique⟩
        exact selectionSetBooleanVariables_mem_of_completeNormalBranches
          hbranches hmem
  have hnormalizedComplete :
      boolVarsComplete
        (operationBoolVars (completeNormalizeOperation schema left))
        variableValues := by
    intro varName hmem
    exact hleftComplete varName (hnormalizedLeftSubset varName hmem)
  rw [hleftPreserved, hrightPreserved]
  exact hnormalizedSemantics resolvers variableValues fuel source
    hnormalizedComplete hleftNormalizedReady hrightNormalizedReady

end CompleteNormalization

end NormalForm

end GraphQL
