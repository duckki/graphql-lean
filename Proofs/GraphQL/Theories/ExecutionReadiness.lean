import GraphQL.Theories.ExecutionReadiness
import Proofs.GraphQL.Execution.ArgumentCoercion

/-! Structural facts for shared execution-readiness predicates. -/

namespace GraphQL

theorem selectionArgumentsCoercible_of_mem
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {selectionSet : List Selection} {selection : Selection}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (hmem : selection ∈ selectionSet)
    : selectionArgumentsCoercible schema variableValues parentType selection := by
  induction selectionSet with
  | nil => simp at hmem
  | cons head rest ih =>
      simp only [selectionSetArgumentsCoercible] at hready
      rcases hready with ⟨hhead, hrest⟩
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact hhead
      · exact ih hrest htail

theorem selectionSetArgumentsCoercible_field_success {schema : Schema}
    {variableValues : Execution.VariableValues} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection} {fieldDefinition : FieldDefinition}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (hmem
      : Selection.field responseName fieldName arguments directives childSelectionSet
        ∈ selectionSet)
    (hdirectives
      : Execution.selectionDirectivesAllowBool variableValues directives = true)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    : (Execution.coerceArgumentValues schema variableValues fieldDefinition.arguments
        arguments).isSuccess
      = true := by
  have hfield := selectionArgumentsCoercible_of_mem hready hmem
  exact (hfield hdirectives fieldDefinition hlookup).1

theorem selectionSetArgumentsCoercible_field_child
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType responseName fieldName runtimeType : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (hmem
      : Selection.field responseName fieldName arguments directives childSelectionSet
        ∈ selectionSet)
    (hdirectives
      : Execution.selectionDirectivesAllowBool variableValues directives = true)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hinclude
      : schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
        = true)
    : selectionSetArgumentsCoercible schema variableValues runtimeType
        childSelectionSet := by
  have hfield := selectionArgumentsCoercible_of_mem hready hmem
  exact (hfield hdirectives fieldDefinition hlookup).2 runtimeType hinclude

theorem selectionSetArgumentsCoercible_field_children
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (hmem
      : Selection.field responseName fieldName arguments directives childSelectionSet
        ∈ selectionSet)
    (hdirectives
      : Execution.selectionDirectivesAllowBool variableValues directives = true)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    : selectionSetArgumentsCoercibleInPossibleTypes schema variableValues
        fieldDefinition.outputType.namedType childSelectionSet := by
  intro runtimeType hinclude
  exact selectionSetArgumentsCoercible_field_child hready hmem hdirectives hlookup
    hinclude

theorem selectionSetArgumentsCoercible_inlineFragment_child {schema : Schema}
    {variableValues : Execution.VariableValues} {parentType : Name}
    {typeCondition : Option Name} {directives : List DirectiveApplication}
    {childSelectionSet selectionSet : List Selection}
    (hready
      : selectionSetArgumentsCoercible schema variableValues parentType selectionSet)
    (hmem
      : Selection.inlineFragment typeCondition directives childSelectionSet
        ∈ selectionSet)
    (hdirectives
      : Execution.selectionDirectivesAllowBool variableValues directives = true)
    (htypeCondition
      : match typeCondition with
        | none => True
        | some condition =>
            schema.typeIncludesObjectBool condition parentType = true)
    : selectionSetArgumentsCoercible schema variableValues parentType
        childSelectionSet := by
  cases typeCondition with
  | none =>
      exact selectionArgumentsCoercible_of_mem hready hmem hdirectives trivial
  | some condition =>
      exact selectionArgumentsCoercible_of_mem hready hmem hdirectives
        htypeCondition

theorem selectionSetArgumentsCoercible_append
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    (left right : List Selection)
    : selectionSetArgumentsCoercible schema variableValues parentType (left ++ right)
      ↔ selectionSetArgumentsCoercible schema variableValues parentType left
        ∧ selectionSetArgumentsCoercible schema variableValues parentType right := by
  induction left with
  | nil => simp [selectionSetArgumentsCoercible]
  | cons head rest ih =>
      simp only [List.cons_append, selectionSetArgumentsCoercible, ih]
      constructor
      · rintro ⟨hhead, hrest, hright⟩
        exact ⟨⟨hhead, hrest⟩, hright⟩
      · rintro ⟨⟨hhead, hrest⟩, hright⟩
        exact ⟨hhead, hrest, hright⟩

theorem selectionSetArgumentsCoercible_of_subset
    {schema : Schema} {variableValues : Execution.VariableValues}
    {parentType : Name} {left right : List Selection}
    (hready : selectionSetArgumentsCoercible schema variableValues parentType right)
    (hsubset : ∀ selection, selection ∈ left -> selection ∈ right)
    : selectionSetArgumentsCoercible schema variableValues parentType left := by
  induction left with
  | nil => simp [selectionSetArgumentsCoercible]
  | cons head rest ih =>
      constructor
      · exact selectionArgumentsCoercible_of_mem hready (hsubset head (by simp))
      · exact ih fun selection hmem => hsubset selection (by simp [hmem])

theorem fieldArgumentCoercionSucceeds_of_equivalent
    {schema : Schema} {variableValues : Execution.VariableValues}
    {definitions : List InputValueDefinition} {left right : List Argument}
    (hleftNodup : (left.map Argument.name).Nodup)
    (hrightNodup : (right.map Argument.name).Nodup)
    (hequivalent : Argument.argumentsEquivalent left right)
    (hleft
      : (Execution.coerceArgumentValues schema variableValues definitions left).isSuccess
        = true)
    : (Execution.coerceArgumentValues schema variableValues definitions right).isSuccess
      = true := by
  rw [← Execution.coerceArgumentValues_isSuccess_eq_of_equivalent schema
    variableValues definitions hleftNodup hrightNodup hequivalent]
  exact hleft

private theorem inputValue_staticBoolean?_eq_of_equivalent_forReadiness
    {left right : InputValue} (hequivalent : left.equivalent right)
    : left.staticBoolean? = right.staticBoolean? := by
  have hcanonical :=
    Execution.inputValue_canonical_eq_of_equivalent hequivalent
  cases left <;> cases right <;>
    simp [InputValue.staticBoolean?, InputValue.canonical] at hcanonical ⊢
  exact hcanonical

private theorem inputValueBoolean?_eq_of_variableValuesCoercionEquivalent_forReadiness
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    (value : InputValue)
    : Execution.inputValueBoolean? leftValues value
      = Execution.inputValueBoolean? rightValues value := by
  cases value <;> try rfl
  rename_i name
  have hlookup := hequivalent.1 name
  cases hleft : Execution.lookupVariableValue? leftValues name with
  | none =>
      cases hright : Execution.lookupVariableValue? rightValues name with
      | none => simp [Execution.inputValueBoolean?, hleft, hright]
      | some right => simp [hleft, hright] at hlookup
  | some left =>
      cases hright : Execution.lookupVariableValue? rightValues name with
      | none => simp [hleft, hright] at hlookup
      | some right =>
          simp [hleft, hright] at hlookup
          simpa [Execution.inputValueBoolean?, hleft, hright] using
            inputValue_staticBoolean?_eq_of_equivalent_forReadiness hlookup

private theorem
    directiveAllowsSelectionBool_eq_of_variableValuesCoercionEquivalent_forReadiness
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    (directive : DirectiveApplication)
    : Execution.directiveAllowsSelectionBool leftValues directive
      = Execution.directiveAllowsSelectionBool rightValues directive := by
  cases directive <;>
    simp only [Execution.directiveAllowsSelectionBool,
      inputValueBoolean?_eq_of_variableValuesCoercionEquivalent_forReadiness
        hequivalent]

private theorem
    selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent_forReadiness
    {leftValues rightValues : Execution.VariableValues}
    (hequivalent : Execution.variableValuesCoercionEquivalent leftValues rightValues)
    : ∀ directives,
        Execution.selectionDirectivesAllowBool leftValues directives
        = Execution.selectionDirectivesAllowBool rightValues directives
  | [] => rfl
  | directive :: rest => by
      simp only [Execution.selectionDirectivesAllowBool, List.all_cons]
      rw [
        directiveAllowsSelectionBool_eq_of_variableValuesCoercionEquivalent_forReadiness
          hequivalent directive]
      change (Execution.directiveAllowsSelectionBool rightValues directive &&
          Execution.selectionDirectivesAllowBool leftValues rest) =
        (Execution.directiveAllowsSelectionBool rightValues directive &&
          Execution.selectionDirectivesAllowBool rightValues rest)
      rw [
        selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent_forReadiness
          hequivalent rest]

mutual
  theorem selectionArgumentsCoercible_of_variableValuesCoercionEquivalent
      {schema : Schema} {leftValues rightValues : Execution.VariableValues}
      (hvalues : Execution.variableValuesCoercionEquivalent leftValues rightValues)
      (parentType : Name)
      : ∀ selection,
          selectionArgumentsCoercible schema rightValues parentType selection
          -> selectionArgumentsCoercible schema leftValues parentType selection
    | .field responseName fieldName arguments directives childSelectionSet => by
        intro hready hdirectives definition hlookup
        have hrightDirectives :
            Execution.selectionDirectivesAllowBool rightValues directives = true := by
          rw [←
            selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent_forReadiness
              hvalues directives]
          exact hdirectives
        rcases hready hrightDirectives definition hlookup with
          ⟨harguments, hchildren⟩
        constructor
        · rw [Execution.coerceArgumentValues_isSuccess_eq_of_variableValuesCoercionEquivalent
            schema hvalues definition.arguments arguments]
          exact harguments
        · intro runtimeType hinclude
          exact
            selectionSetArgumentsCoercible_of_variableValuesCoercionEquivalent
              hvalues runtimeType childSelectionSet (hchildren runtimeType hinclude)
    | .inlineFragment typeCondition directives childSelectionSet => by
        intro hready hdirectives htypeCondition
        have hrightDirectives :
            Execution.selectionDirectivesAllowBool rightValues directives = true := by
          rw [←
            selectionDirectivesAllowBool_eq_of_variableValuesCoercionEquivalent_forReadiness
              hvalues directives]
          exact hdirectives
        exact
          selectionSetArgumentsCoercible_of_variableValuesCoercionEquivalent
            hvalues parentType childSelectionSet
              (hready hrightDirectives htypeCondition)

  theorem selectionSetArgumentsCoercible_of_variableValuesCoercionEquivalent
      {schema : Schema} {leftValues rightValues : Execution.VariableValues}
      (hvalues : Execution.variableValuesCoercionEquivalent leftValues rightValues)
      (parentType : Name)
      : ∀ selectionSet,
          selectionSetArgumentsCoercible schema rightValues parentType selectionSet
          -> selectionSetArgumentsCoercible schema leftValues parentType selectionSet
    | [] => by simp [selectionSetArgumentsCoercible]
    | selection :: rest => by
        rintro ⟨hselection, hrest⟩
        exact ⟨
          selectionArgumentsCoercible_of_variableValuesCoercionEquivalent
            hvalues parentType selection hselection,
          selectionSetArgumentsCoercible_of_variableValuesCoercionEquivalent
            hvalues parentType rest hrest
        ⟩
end

end GraphQL
