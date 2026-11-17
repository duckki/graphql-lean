import Proofs.GraphQL.Theories.NormalForm.Shared.SemanticReadiness.Readiness
import Proofs.GraphQL.Theories.NormalForm.Shared.RuntimeMergeSource

/-! Runtime-source compatibility for semantic readiness. -/

namespace GraphQL.NormalForm

theorem runtimeLookupValid_field_head_lookup_none_false
    {schema : Schema} {parentType responseName fieldName : Name}
    {arguments : List Argument} {directives : List DirectiveApplication}
    {children rest : List Selection}
    (hvalid
      : selectionSetLookupValid schema parentType
          (Selection.field responseName fieldName arguments directives children :: rest))
    (hnone : schema.lookupField parentType fieldName = none)
    : False := by
  have hhead := selectionSetLookupValid_head hvalid
  simp only [selectionLookupValid] at hhead
  rcases hhead with ⟨definition, hlookup⟩
  rw [hnone] at hlookup
  contradiction

theorem runtimeMergeSource_fieldHead_semanticsReady (schema : Schema)
    {parentType responseName fieldName runtimeType : Name}
    {arguments : List Argument} {children rest : List Selection}
    {definition : FieldDefinition}
    (hsource
      : runtimeMergeSource schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (hready
      : selectionSetSemanticsReady schema parentType
          (Selection.field responseName fieldName arguments [] children :: rest))
    (hlookup : schema.lookupField parentType fieldName = some definition)
    (hinclude
      : schema.typeIncludesObjectBool definition.outputType.namedType runtimeType = true)
    : selectionSetSemanticsReady schema runtimeType
        (children
          ++ mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                rest)) := by
  let group := Selection.field responseName fieldName arguments [] children ::
    fieldSelectionsWithResponseNameInScope schema parentType responseName rest
  have hhead : Selection.field responseName fieldName arguments [] children ∈
      fieldSelectionsWithResponseNameInScope schema parentType responseName
        (Selection.field responseName fieldName arguments [] children :: rest) := by
    simp [fieldSelectionsWithResponseNameInScope]
  have hresult : selectionSetSemanticsReady schema runtimeType (mergeSelectionSets group) := by
    apply selectionSetSemanticsReady_mergeSelectionSets_of_subselections
    intro selection hselection
    have hselected : selection ∈ fieldSelectionsWithResponseNameInScope schema parentType
        responseName (Selection.field responseName fieldName arguments [] children :: rest) := by
      simpa [group, fieldSelectionsWithResponseNameInScope] using hselection
    rcases fieldSelectionsWithResponseNameInScope_mem_field schema parentType responseName
      _ selection hselected with ⟨name, args, dirs, body, rfl⟩
    have hname := (runtimeMergeSource_identity hsource hhead hselected).1
    subst name
    rcases fieldSelectionsWithResponseNameInScope_field_semanticsReady schema parentType
      responseName _ fieldName args dirs body hready hselected with
      ⟨selectedDefinition, hselectedLookup, hchildren⟩
    rw [hlookup] at hselectedLookup
    cases hselectedLookup
    exact hchildren runtimeType hinclude
  exact hresult

end GraphQL.NormalForm
