import GraphQL.Validation
import Proofs.GraphQL.SchemaWellFormedness.FieldLookup

/-! Ordinary field validation enforces the implicit type-name field's signature. -/

namespace GraphQL.Validation

theorem typename_selection_valid (schema : Schema) (variables : List VariableDefinition)
    (parentType responseName : Name) (directives : List DirectiveApplication)
    (hparent : schema.isCompositeType parentType)
    (hdirectives : directivesValid schema variables directives)
    : selectionValid schema variables parentType
        (.field responseName "__typename" [] directives []) := by
  unfold selectionValid
  refine ⟨hdirectives, Schema.typenameFieldDefinition,
    Schema.lookupField_typename hparent, ?_, ?_⟩
  · simp [argumentsValid, Schema.typenameFieldDefinition]
  · unfold fieldSelectionSetValid
    exact ⟨(SchemaWellFormedness.typenameFieldDefinition_wellFormed schema).1,
      Or.inl ⟨⟨.builtinScalar .string, rfl, trivial⟩, rfl⟩⟩

theorem typename_selection_arguments_eq_nil (schema : Schema)
    (variables : List VariableDefinition) (parentType responseName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (children : List Selection) (hparent : schema.isCompositeType parentType)
    (hvalid
      : selectionValid schema variables parentType
          (.field responseName "__typename" arguments directives children))
    : arguments = [] := by
  unfold selectionValid at hvalid
  obtain ⟨_, definition, hlookup, harguments, _⟩ := hvalid
  rw [Schema.lookupField_typename hparent] at hlookup
  cases hlookup
  cases arguments with
  | nil => rfl
  | cons argument rest =>
      obtain ⟨definition, hlookup, _⟩ := harguments.2.1 argument (by simp)
      simp [Schema.typenameFieldDefinition, Schema.lookupArgumentDefinition] at hlookup

theorem typename_selection_children_eq_nil (schema : Schema)
    (variables : List VariableDefinition) (parentType responseName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (children : List Selection) (hparent : schema.isCompositeType parentType)
    (hvalid
      : selectionValid schema variables parentType
          (.field responseName "__typename" arguments directives children))
    : children = [] := by
  unfold selectionValid at hvalid
  obtain ⟨_, definition, hlookup, _, hchildren⟩ := hvalid
  rw [Schema.lookupField_typename hparent] at hlookup
  cases hlookup
  unfold fieldSelectionSetValid at hchildren
  rcases hchildren.2 with ⟨_, hnil⟩ | ⟨hcomposite, _⟩
  · exact hnil
  · obtain ⟨definition, hlookup, hcomposite⟩ := hcomposite
    have hstring : schema.lookupType "String" = some (.builtinScalar .string) := rfl
    change schema.lookupType "String" = some definition at hlookup
    rw [hstring] at hlookup
    cases hlookup
    exact False.elim hcomposite

end GraphQL.Validation
