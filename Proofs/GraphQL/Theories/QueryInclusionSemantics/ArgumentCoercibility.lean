import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ArgumentCoercibility
import Proofs.GraphQL.Theories.QueryInclusion.Algebra
import Proofs.GraphQL.Theories.QueryInclusion.Execution

/-! Concrete argument defaults supply witnesses for every comparison Boolean case.

One-sided variable definitions are allowed. Shared names have compatible types,
so both operations can use one fully supplied environment. Only comparison
condition variables are overwritten by the Boolean case.
-/

namespace GraphQL.QueryInclusionSemantics
open Execution QueryInclusion NormalForm.CompleteNormalization

private theorem combinedVariableTypes_consistent
    {schema : Schema} {left right : Operation}
    (hleft : Validation.operationDefinitionValid schema left)
    (hright : Validation.operationDefinitionValid schema right)
    (hshared
      : sharedVariableDefinitionsSyntacticallyCompatible
          left.variableDefinitions right.variableDefinitions)
    : ∀ first,
        first ∈ left.variableDefinitions ++ right.variableDefinitions
        -> ∀ second,
            second ∈ left.variableDefinitions ++ right.variableDefinitions
            -> first.name = second.name
            -> first.typeRef = second.typeRef := by
  have hleftNodup := (Validation.operationDefinitionValid_variableDefinitionsValid hleft).1
  have hrightNodup := (Validation.operationDefinitionValid_variableDefinitionsValid hright).1
  intro first hfirst second hsecond hname
  rcases List.mem_append.mp hfirst with hfirst | hfirst <;>
    rcases List.mem_append.mp hsecond with hsecond | hsecond
  · exact (sharedVariableDefinitionsSyntacticallyCompatible_of_mem
      (sharedVariableDefinitionsSyntacticallyCompatible_refl _ hleftNodup)
      hleftNodup hfirst hsecond hname).2.1
  · exact (sharedVariableDefinitionsSyntacticallyCompatible_of_mem
      hshared hrightNodup hfirst hsecond hname).2.1
  · exact (sharedVariableDefinitionsSyntacticallyCompatible_of_mem
      hshared hrightNodup hsecond hfirst hname.symm).2.1.symm
  · exact (sharedVariableDefinitionsSyntacticallyCompatible_of_mem
      (sharedVariableDefinitionsSyntacticallyCompatible_refl _ hrightNodup)
      hrightNodup hfirst hsecond hname).2.1

private theorem conditionVariable_hasBooleanDefinition {schema : Schema}
    {operation : Operation}
    (hvalid : Validation.operationDefinitionValid schema operation) {name : Name}
    (hname
      : name ∈ SelectionConditions.selectionSetBooleanVariables operation.selectionSet)
    : ∃ definition,
        definition ∈ operation.variableDefinitions
        ∧ definition.name = name
        ∧ (definition.typeRef = .named "Boolean"
            ∨ definition.typeRef = .nonNull (.named "Boolean")) := by
  have hname := selectionSetConditionVariables_mem_normalForm operation.selectionSet name hname
  obtain ⟨definition, hlookup, _⟩ := directiveIfArgumentValid_of_selectionSetBooleanVariables
    schema operation.variableDefinitions name (operation.rootType schema) operation.selectionSet
    hname (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hmem : definition ∈ operation.variableDefinitions := List.mem_of_find?_eq_some hlookup
  have heq : definition.name = name := by simpa using List.find?_some hlookup
  refine ⟨definition, hmem, heq, operationBoolVars_haveBooleanTypes hvalid ?_ hmem heq⟩
  exact (mem_dedupBoolVars_iff name _).2 hname

private theorem inputValueBoolean_filtered_case
    (variables : List Name) (baseValues : VariableValues) (name : Name) (bit : Bool)
    (hname : name ∈ variables)
    : ∀ assignment : BoolCase,
        inputValueBoolean? (boolCaseVariableValues assignment) (.variable name) = some bit
        -> inputValueBoolean?
              (boolCaseVariableValues
                (assignment.filter fun entry => variables.contains entry.1) baseValues)
              (.variable name)
            = some bit := by
  intro assignment
  induction assignment with
  | nil => simp [boolCaseVariableValues, inputValueBoolean?, lookupVariableValue?]
  | cons head rest ih =>
      rcases head with ⟨headName, headBit⟩
      intro hvalue
      by_cases heq : headName = name
      · subst headName
        simpa [List.filter, hname, boolCaseVariableValues, inputValueBoolean?, lookupVariableValue?,
          ConstInputValue.toInputValue, InputValue.staticBoolean?] using hvalue
      · have htail
            : inputValueBoolean? (boolCaseVariableValues rest) (.variable name)
              = some bit := by
          simpa [boolCaseVariableValues, inputValueBoolean?, lookupVariableValue?, heq]
            using hvalue
        by_cases hhead : headName ∈ variables
        · simpa [List.filter, hhead, boolCaseVariableValues, inputValueBoolean?,
            lookupVariableValue?, heq]
            using ih htail
        · simpa [List.filter, hhead] using ih htail

theorem comparisonBranchesArgumentCoercible_of_possibleTypes
    {schema : Schema} {left right : Operation}
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleft : Validation.operationDefinitionValid schema left)
    (hright : Validation.operationDefinitionValid schema right)
    (hleftFields : operationCoercibleInPossibleTypes schema left)
    (hrightFields : operationCoercibleInPossibleTypes schema right)
    (hshared
      : sharedVariableDefinitionsSyntacticallyCompatible
          left.variableDefinitions right.variableDefinitions)
    : comparisonBranchesArgumentCoercible schema left right := by
  have hconsistent := combinedVariableTypes_consistent hleft hright hshared
  obtain ⟨baseValues, hbase⟩ := exists_variablesHaveNonNullValues_of_consistentTypes hschema
    (definitions := left.variableDefinitions ++ right.variableDefinitions)
    (by intro definition hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact ((Validation.operationDefinitionValid_variableDefinitionsValid hleft).2
            definition hmem).1
        · exact ((Validation.operationDefinitionValid_variableDefinitionsValid hright).2
            definition hmem).1) hconsistent
  dsimp only [comparisonBranchesArgumentCoercible]
  intro assignment hcomplete
  let variables := comparisonConditionVariables left.selectionSet right.selectionSet
  let selectedCase := assignment.filter fun entry => variables.contains entry.1
  have hvalues : variablesHaveNonNullValues schema
      (left.variableDefinitions ++ right.variableDefinitions)
      (boolCaseVariableValues selectedCase baseValues) := by
    apply variablesHaveNonNullValues_boolCase hbase selectedCase
    intro name bit hmem definition hdefinition heq
    have hcondition : name ∈ variables := by
      simpa using (List.mem_filter.mp hmem).2
    have hsource : ∃ source,
        source ∈ left.variableDefinitions ++ right.variableDefinitions ∧ source.name = name ∧
        (source.typeRef = .named "Boolean" ∨ source.typeRef = .nonNull (.named "Boolean")) := by
      have hcases : name ∈ SelectionConditions.selectionSetBooleanVariables left.selectionSet ∨
          name ∈ SelectionConditions.selectionSetBooleanVariables right.selectionSet := by
        simpa [variables, comparisonConditionVariables] using hcondition
      rcases hcases with hname | hname
      · obtain ⟨source, hmem, hname, htype⟩ := conditionVariable_hasBooleanDefinition hleft hname
        exact ⟨source, List.mem_append_left _ hmem, hname, htype⟩
      · obtain ⟨source, hmem, hname, htype⟩ := conditionVariable_hasBooleanDefinition hright hname
        exact ⟨source, List.mem_append_right _ hmem, hname, htype⟩
    obtain ⟨source, hsource, hname, htype⟩ := hsource
    have htypeEq := hconsistent source hsource definition hdefinition (hname.trans heq.symm)
    exact htypeEq ▸ htype
  refine ⟨boolCaseVariableValues selectedCase baseValues, ?_, ?_, ?_⟩
  · intro name hname
    obtain ⟨bit, hbit⟩ := hcomplete name hname
    rw [hbit]
    exact inputValueBoolean_filtered_case variables baseValues name bit hname assignment hbit
  · exact ExecutionReadiness.operationArgumentsCoercible_of_defaults hschema hleft
      (fun definition hmem => hvalues definition (List.mem_append_left _ hmem)) hleftFields
  · exact ExecutionReadiness.operationArgumentsCoercible_of_defaults hschema hright
      (fun definition hmem => hvalues definition (List.mem_append_right _ hmem)) hrightFields

end GraphQL.QueryInclusionSemantics
