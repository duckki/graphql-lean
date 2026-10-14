import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Validation.SelectionValidity

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.NormalForm

mutual
  def selectionLookupValid (schema : Schema) (parentType : Name) : Selection -> Prop
    | .field _responseName fieldName _arguments _directives _selectionSet =>
        ∃ fieldDefinition, schema.lookupField parentType fieldName = some fieldDefinition
    | .inlineFragment none _directives selectionSet =>
        selectionSetLookupValid schema parentType selectionSet
    | .inlineFragment (some typeCondition) _directives selectionSet =>
        selectionSetLookupValid schema typeCondition selectionSet

  def selectionSetLookupValid (schema : Schema)
      (parentType : Name) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet -> selectionLookupValid schema parentType selection
end

theorem selectionSetLookupValid_nil (schema : Schema) (parentType : Name)
    : selectionSetLookupValid schema parentType [] := by
  simp [selectionSetLookupValid]

mutual
  theorem selectionLookupValid_of_selectionValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name}
      : ∀ selection,
          Validation.selectionValid schema variableDefinitions parentType selection
          -> selectionLookupValid schema parentType selection
    | .field _responseName fieldName _arguments _directives _selectionSet,
        hvalid => by
        rcases Validation.selectionValid_field_lookup hvalid with
          ⟨fieldDefinition, hlookup, _harguments, _hchild⟩
        simpa [selectionLookupValid] using ⟨fieldDefinition, hlookup⟩
    | .inlineFragment none _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_none_selectionSetValid
              hvalid)
    | .inlineFragment (some typeCondition) _directives selectionSet, hvalid => by
        simpa [selectionLookupValid] using
          selectionSetLookupValid_of_selectionSetValid selectionSet
            (Validation.selectionValid_inlineFragment_some_selectionSetValid
              hvalid)

  theorem selectionSetLookupValid_of_selectionSetValid
      {schema : Schema} {variableDefinitions : List VariableDefinition}
      {parentType : Name}
      : ∀ selectionSet,
          Validation.selectionSetValid schema variableDefinitions parentType selectionSet
          -> selectionSetLookupValid schema parentType selectionSet
    | [], _hvalid => by
        exact selectionSetLookupValid_nil schema parentType
    | selection :: rest, hvalid => by
        have hhead :
            Validation.selectionValid schema variableDefinitions parentType
              selection := by
          simp [Validation.selectionSetValid] at hvalid
          exact hvalid.1
        have htail :
            Validation.selectionSetValid schema variableDefinitions parentType
              rest :=
          Validation.selectionSetValid_tail hvalid
        simp [selectionSetLookupValid]
        constructor
        · exact selectionLookupValid_of_selectionValid selection hhead
        · simpa [selectionSetLookupValid] using
            selectionSetLookupValid_of_selectionSetValid rest htail
end

end GraphQL.NormalForm
