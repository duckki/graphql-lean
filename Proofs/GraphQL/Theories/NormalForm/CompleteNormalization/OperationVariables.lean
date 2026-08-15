import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.BoolCaseWrappers

/-!
Operation-global directive-variable and boolCase facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

private theorem lookupVariableValue?_foldlDefaults_eq_some
    (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues)
    {name : Name} {value : Execution.CoercedInputValue}
    (hlookup : Execution.lookupVariableValue? variableValues name = some value)
    : Execution.lookupVariableValue?
        (variableDefinitions.foldl
          (fun coercedValues variableDefinition =>
            match Execution.lookupVariableValue?
                    coercedValues variableDefinition.name with
            | some _value => coercedValues
            | none =>
                match variableDefinition.defaultValue with
                | some defaultValue =>
                    (variableDefinition.name, defaultValue) :: coercedValues
                | none => coercedValues)
          variableValues)
        name
      = some value := by
  induction variableDefinitions generalizing variableValues with
  | nil =>
      exact hlookup
  | cons variableDefinition variableDefinitions ih =>
      simp only [List.foldl_cons]
      apply ih
      split
      · exact hlookup
      · rename_i hmissing
        split
        · simp only [Execution.lookupVariableValue?]
          split
          · rename_i heq
            subst name
            rw [hlookup] at hmissing
            contradiction
          · exact hlookup
        · exact hlookup

theorem lookupVariableValue?_coerceVariableValues_eq_some
    (operation : Operation)
    (variableValues : Execution.VariableValues)
    {name : Name} {value : Execution.CoercedInputValue}
    (hlookup : Execution.lookupVariableValue? variableValues name = some value)
    : Execution.lookupVariableValue?
        (Execution.coerceVariableValues operation variableValues) name
      = some value := by
  exact lookupVariableValue?_foldlDefaults_eq_some
    operation.variableDefinitions variableValues hlookup

private theorem lookupVariableValue?_foldlDefaults_default_eq_some
    (variableDefinitions : List VariableDefinition)
    (variableValues : Execution.VariableValues)
    {variableDefinition : VariableDefinition} {defaultValue : ConstInputValue}
    (hmem : variableDefinition ∈ variableDefinitions)
    (hdefault : variableDefinition.defaultValue = some defaultValue)
    : ∃ value,
        Execution.lookupVariableValue?
          (variableDefinitions.foldl
            (fun coercedValues definition =>
              match Execution.lookupVariableValue? coercedValues definition.name with
              | some _value => coercedValues
              | none =>
                  match definition.defaultValue with
                  | some defaultValue =>
                      (definition.name, defaultValue) :: coercedValues
                  | none => coercedValues)
            variableValues)
          variableDefinition.name
        = some value := by
  rcases List.mem_iff_append.mp hmem with ⟨pref, suffix, hdefinitions⟩
  subst variableDefinitions
  rw [List.foldl_append]
  simp only [List.foldl_cons]
  let prefixValues := pref.foldl
    (fun coercedValues definition =>
      match Execution.lookupVariableValue? coercedValues definition.name with
      | some _value => coercedValues
      | none =>
          match definition.defaultValue with
          | some defaultValue =>
              (definition.name, defaultValue) :: coercedValues
          | none => coercedValues)
    variableValues
  cases hlookup : Execution.lookupVariableValue? prefixValues variableDefinition.name with
  | some value =>
      exact ⟨value,
        lookupVariableValue?_foldlDefaults_eq_some suffix prefixValues hlookup⟩
  | none =>
      have hadd :
          Execution.lookupVariableValue?
              ((variableDefinition.name, defaultValue) :: prefixValues)
              variableDefinition.name = some defaultValue := by
        simp [Execution.lookupVariableValue?]
      simpa [prefixValues, hlookup, hdefault] using
        (show ∃ value,
            Execution.lookupVariableValue?
              (suffix.foldl
                (fun coercedValues definition =>
                  match Execution.lookupVariableValue? coercedValues definition.name with
                  | some _value => coercedValues
                  | none =>
                      match definition.defaultValue with
                      | some candidateDefault =>
                          (definition.name, candidateDefault) :: coercedValues
                      | none => coercedValues)
                ((variableDefinition.name, defaultValue) :: prefixValues))
              variableDefinition.name = some value from
          ⟨defaultValue,
            lookupVariableValue?_foldlDefaults_eq_some suffix _ hadd⟩)

private theorem foldlDefaults_eq_self_of_defaults_present
    : ∀ (variableDefinitions : List VariableDefinition)
        (variableValues : Execution.VariableValues),
        (∀ variableDefinition defaultValue,
          variableDefinition ∈ variableDefinitions
          -> variableDefinition.defaultValue = some defaultValue
          -> ∃ value,
              Execution.lookupVariableValue? variableValues variableDefinition.name
              = some value)
        -> variableDefinitions.foldl
              (fun coercedValues variableDefinition =>
                match Execution.lookupVariableValue?
                        coercedValues variableDefinition.name with
                | some _value => coercedValues
                | none =>
                    match variableDefinition.defaultValue with
                    | some defaultValue =>
                        (variableDefinition.name, defaultValue) :: coercedValues
                    | none => coercedValues)
              variableValues
            = variableValues
  | [], _variableValues, _hpresent => rfl
  | variableDefinition :: rest, variableValues, hpresent => by
      simp only [List.foldl_cons]
      cases hlookup : Execution.lookupVariableValue? variableValues
          variableDefinition.name with
      | some value =>
          exact foldlDefaults_eq_self_of_defaults_present rest variableValues
            (fun definition defaultValue hmem hdefault =>
              hpresent definition defaultValue (by simp [hmem]) hdefault)
      | none =>
          cases hdefault : variableDefinition.defaultValue with
          | none =>
              exact foldlDefaults_eq_self_of_defaults_present rest variableValues
                (fun definition defaultValue hmem hsome =>
                  hpresent definition defaultValue (by simp [hmem]) hsome)
          | some defaultValue =>
              rcases hpresent variableDefinition defaultValue (by simp) hdefault with
                ⟨value, hvalue⟩
              rw [hlookup] at hvalue
              contradiction

theorem coerceVariableValues_idempotent
    (operation : Operation) (variableValues : Execution.VariableValues)
    : Execution.coerceVariableValues operation
        (Execution.coerceVariableValues operation variableValues)
      = Execution.coerceVariableValues operation variableValues := by
  unfold Execution.coerceVariableValues
  apply foldlDefaults_eq_self_of_defaults_present
  intro variableDefinition defaultValue hmem hdefault
  exact lookupVariableValue?_foldlDefaults_default_eq_some
    operation.variableDefinitions variableValues hmem hdefault

theorem inputValueBoolean?_coerceVariableValues_eq_some
    (operation : Operation)
    (variableValues : Execution.VariableValues)
    {name : Name} {value : Bool}
    (hlookup : Execution.inputValueBoolean? variableValues (.variable name) = some value)
    : Execution.inputValueBoolean?
        (Execution.coerceVariableValues operation variableValues) (.variable name)
      = some value := by
  cases hvariable : Execution.lookupVariableValue? variableValues name with
  | none =>
      simp [Execution.inputValueBoolean?, hvariable] at hlookup
  | some inputValue =>
      have hcoerced :=
        lookupVariableValue?_coerceVariableValues_eq_some
          operation variableValues hvariable
      simpa [Execution.inputValueBoolean?, hvariable, hcoerced] using hlookup

theorem operationBoolVarsComplete_coerceVariableValues
    (operation : Operation)
    (variableValues : Execution.VariableValues)
    (hcomplete : operationBoolVarsComplete operation variableValues)
    : operationBoolVarsComplete operation
        (Execution.coerceVariableValues operation variableValues) := by
  intro name hmem
  rcases hcomplete name hmem with ⟨value, hlookup⟩
  exact ⟨value,
    inputValueBoolean?_coerceVariableValues_eq_some
      operation variableValues hlookup⟩

theorem completeNormalizeOperation_uses_global_variables (operation : Operation)
    : operationBoolVars operation
      = dedupBoolVars (selectionSetBooleanVariables operation.selectionSet) := by
  rfl

theorem operationBoolVars_nodup (operation : Operation)
    : (operationBoolVars operation).Nodup := by
  exact dedupBoolVars_nodup
    (selectionSetBooleanVariables operation.selectionSet)

theorem allBoolCases_operationBoolVars_nodup (operation : Operation)
    : (allBoolCases (operationBoolVars operation)).Nodup := by
  exact allBoolCases_nodup
    (operationBoolVars_nodup operation)

theorem allBoolCases_operationBoolVars_split (operation : Operation) {boolCase : BoolCase}
    : boolCase ∈ allBoolCases (operationBoolVars operation)
      -> ∃ before after,
          allBoolCases (operationBoolVars operation) = before ++ boolCase :: after
          ∧ (∀ candidate, candidate ∈ before -> candidate ≠ boolCase)
          ∧ (∀ candidate, candidate ∈ after -> candidate ≠ boolCase) := by
  intro hmem
  exact allBoolCases_split_case
    (operationBoolVars_nodup operation) hmem

theorem directivesAllowInCase_eq_execution_of_operationVariables
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (operation : Operation)
    (directives : List DirectiveApplication)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName ∈ directivesBooleanVariables directives
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives
          = Execution.selectionDirectivesAllowBool variableValues directives := by
  intro hagrees hvars
  exact directivesAllowInCase_eq_execution variableValues boolCase
    (operationBoolVars operation) directives hagrees
    (by
      intro varName hmem
      exact mem_operationBoolVars_of_selectionSet operation
        varName (hvars varName hmem))

theorem directivesAllowInCase_eq_execution_of_sourceSelectionSet
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (operation : Operation)
    (sourceSelectionSet : List Selection)
    (directiveApplications : List DirectiveApplication)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName ∈ directivesBooleanVariables directiveApplications
            -> varName ∈ selectionSetBooleanVariables sourceSelectionSet)
      -> (∀ varName,
            varName ∈ selectionSetBooleanVariables sourceSelectionSet
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directiveApplications
          = Execution.selectionDirectivesAllowBool variableValues
              directiveApplications := by
  intro hagrees hdirectiveVars hsourceVars
  exact directivesAllowInCase_eq_execution_of_operationVariables
    variableValues boolCase operation directiveApplications hagrees
    (by
      intro varName hmem
      exact hsourceVars varName (hdirectiveVars varName hmem))

theorem directivesAllowInCase_eq_execution_of_field_head
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (operation : Operation)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives
          = Execution.selectionDirectivesAllowBool variableValues directives := by
  intro hagrees hsourceVars
  exact directivesAllowInCase_eq_execution_of_sourceSelectionSet
    variableValues boolCase operation
    (Selection.field responseName fieldName arguments directives selectionSet
      :: rest)
    directives hagrees
    (by
      intro varName hmem
      exact directivesBooleanVariables_mem_selectionSetBooleanVariables_field_head
        varName responseName fieldName arguments directives selectionSet rest
        hmem)
    hsourceVars

theorem directivesAllowInCase_eq_execution_of_inline_head
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (operation : Operation)
    (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment typeCondition directives selectionSet :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives
          = Execution.selectionDirectivesAllowBool variableValues directives := by
  intro hagrees hsourceVars
  exact directivesAllowInCase_eq_execution_of_sourceSelectionSet
    variableValues boolCase operation
    (Selection.inlineFragment typeCondition directives selectionSet :: rest)
    directives hagrees
    (by
      intro varName hmem
      exact directivesBooleanVariables_mem_selectionSetBooleanVariables_inline_head
        varName typeCondition directives selectionSet rest hmem)
    hsourceVars

theorem inlineSomeBranchAllowInCase_eq_execution_of_inline_head
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (boolCase : BoolCase)
    (operation : Operation)
    (groundType typeCondition : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.inlineFragment (some typeCondition) directives selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> (directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType)
          = (Execution.selectionDirectivesAllowBool variableValues directives
              && schema.typeIncludesObjectBool typeCondition groundType) := by
  intro hagrees hsourceVars
  rw [directivesAllowInCase_eq_execution_of_inline_head
    variableValues boolCase operation (some typeCondition) directives
    selectionSet rest hagrees hsourceVars]

theorem operationBoolVars_caseForVariableValues
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    : (∀ varName,
        varName ∈ operationBoolVars operation
        -> ∃ value,
            Execution.inputValueBoolean? variableValues (.variable varName) = some value)
      -> ∃ boolCase,
          boolCase ∈ allBoolCases (operationBoolVars operation)
          ∧ variableValuesAgreeWithCase variableValues boolCase
              (operationBoolVars operation) := by
  intro hcomplete
  exact allBoolCases_complete_for_variableValues variableValues
    (operationBoolVars operation) hcomplete

theorem operationBoolVarsComplete_caseForVariableValues
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    : operationBoolVarsComplete operation variableValues
      -> ∃ boolCase,
          boolCase ∈ allBoolCases (operationBoolVars operation)
          ∧ variableValuesAgreeWithCase variableValues boolCase
              (operationBoolVars operation) := by
  intro hcomplete
  exact operationBoolVars_caseForVariableValues
    variableValues operation hcomplete

theorem operationBoolVars_case_unique
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    {left right : BoolCase}
    : left ∈ allBoolCases (operationBoolVars operation)
      -> right ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues left (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues right (operationBoolVars operation)
      -> left = right := by
  intro hleft hright hleftAgree hrightAgree
  exact allBoolCases_variableValuesAgree_unique variableValues
    (operationBoolVars_nodup operation)
    hleft hright hleftAgree hrightAgree

theorem operationBoolVars_case_mismatch_of_ne
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    {left right : BoolCase}
    : left ∈ allBoolCases (operationBoolVars operation)
      -> right ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues left (operationBoolVars operation)
      -> right ≠ left
      -> ∃ varName value,
          (varName, value) ∈ right
          ∧ Execution.inputValueBoolean? variableValues (.variable varName)
            = some (!value) := by
  intro hleft hright hagrees hne
  exact allBoolCases_mismatch_of_ne_agree variableValues
    (operationBoolVars_nodup operation)
    hleft hright hagrees hne

theorem collectFields_wrapWithBoolCase_of_nonruntime_case
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    {runtimeCase candidateCase : BoolCase}
    : runtimeCase ∈ allBoolCases (operationBoolVars operation)
      -> candidateCase ∈ allBoolCases (operationBoolVars operation)
      -> variableValuesAgreeWithCase variableValues runtimeCase
          (operationBoolVars operation)
      -> candidateCase ≠ runtimeCase
      -> Execution.collectFields schema variableValues parentType source
            (wrapWithBoolCase candidateCase selectionSet)
          = [] := by
  intro hruntime hcandidate hagrees hne
  rcases
      operationBoolVars_case_mismatch_of_ne
        variableValues operation hruntime hcandidate hagrees hne with
    ⟨varName, value, hpair, hmismatch⟩
  exact collectFields_wrapWithBoolCase_of_mismatch_pair schema
    variableValues parentType source selectionSet candidateCase varName
    value hpair hmismatch

end CompleteNormalization

end NormalForm

end GraphQL
