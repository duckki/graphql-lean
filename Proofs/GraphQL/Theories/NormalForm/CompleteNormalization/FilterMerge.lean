import GraphQL.Theories.NormalForm
import Proofs.GraphQL.Validation.FieldMerge

/-! Declared-scope merge compatibility preserved by Boolean case filtering. -/

namespace GraphQL.NormalForm.CompleteNormalization

theorem filterSelectionSetBoolCase_cons
    (boolCase : BoolCase) (selection : Selection) (rest : List Selection)
    : filterSelectionSetBoolCase boolCase (selection :: rest)
      = filterSelectionSetBoolCase boolCase [selection]
        ++ filterSelectionSetBoolCase boolCase rest := by
  cases selection with
  | field responseName fieldName arguments directives selectionSet =>
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow]
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase (child :: children) <;>
              simp [filterSelectionSetBoolCase, hallow, hchild]
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse]
  | inlineFragment typeCondition directives selectionSet =>
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet <;>
          simp [filterSelectionSetBoolCase, hallow, hchild]
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse]

theorem filterSelectionSetBoolCase_append (boolCase : BoolCase)
    : ∀ left right,
        filterSelectionSetBoolCase boolCase (left ++ right)
        = filterSelectionSetBoolCase boolCase left
          ++ filterSelectionSetBoolCase boolCase right
  | [], right => by
      simp [filterSelectionSetBoolCase]
  | selection :: rest, right => by
      calc
        filterSelectionSetBoolCase boolCase
            ((selection :: rest) ++ right)
            =
          filterSelectionSetBoolCase boolCase [selection]
            ++ filterSelectionSetBoolCase boolCase (rest ++ right) := by
              simpa [List.cons_append] using
                filterSelectionSetBoolCase_cons boolCase selection
                  (rest ++ right)
        _ =
          filterSelectionSetBoolCase boolCase [selection]
            ++ (filterSelectionSetBoolCase boolCase rest
              ++ filterSelectionSetBoolCase boolCase right) := by
              rw [filterSelectionSetBoolCase_append boolCase rest right]
        _ =
          (filterSelectionSetBoolCase boolCase [selection]
            ++ filterSelectionSetBoolCase boolCase rest)
              ++ filterSelectionSetBoolCase boolCase right := by
              simp [List.append_assoc]
        _ =
          filterSelectionSetBoolCase boolCase (selection :: rest)
              ++ filterSelectionSetBoolCase boolCase right := by
              rw [filterSelectionSetBoolCase_cons boolCase selection rest]

structure BoolFilteredScopedFieldSourceForMerge
    (schema : Schema) (boolCase : BoolCase)
    (source filtered : FieldMerge.ScopedField)
    : Prop where
  parentType : filtered.parentType = source.parentType
  responseName : filtered.responseName = source.responseName
  fieldName : filtered.fieldName = source.fieldName
  arguments : filtered.arguments = source.arguments
  outputType : filtered.outputType = source.outputType
  selectionSet
    : filtered.selectionSet = filterSelectionSetBoolCase boolCase source.selectionSet

theorem collectFields_filterSelectionSetBoolCase_mem_source_forMerge
    (schema : Schema) (boolCase : BoolCase)
    : ∀ parentType selectionSet filteredField,
        filteredField
          ∈ FieldMerge.collectFields schema parentType
              (filterSelectionSetBoolCase boolCase selectionSet)
        -> ∃ sourceField,
            sourceField ∈ FieldMerge.collectFields schema parentType selectionSet
            ∧ BoolFilteredScopedFieldSourceForMerge schema boolCase sourceField
                filteredField
  | _parentType, [], _filteredField, hfield => by
      simp [filterSelectionSetBoolCase, FieldMerge.collectFields] at hfield
  | parentType,
    Selection.field responseName fieldName arguments directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow,
              FieldMerge.collectFields] at hfield
            cases hlookup : schema.lookupField parentType fieldName with
            | none =>
                simp [hlookup] at hfield
                rcases
                  collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                    schema boolCase parentType rest filteredField hfield with
                  ⟨sourceField, hsourceMem, hsource⟩
                exact ⟨sourceField, by
                  simp [FieldMerge.collectFields, hlookup, hsourceMem],
                  hsource⟩
            | some fieldDefinition =>
                simp [hlookup] at hfield
                rcases hfield with hhead | htail
                · subst filteredField
                  refine ⟨{
                    parentType := parentType,
                    responseName := responseName,
                    fieldName := fieldName,
                    arguments := arguments,
                    outputType := fieldDefinition.outputType,
                    selectionSet := []
                  }, ?_, ?_⟩
                  · simp [FieldMerge.collectFields, hlookup]
                  · exact ⟨rfl, rfl, rfl, rfl, rfl, by
                      simp [filterSelectionSetBoolCase]⟩
                · rcases
                    collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                      schema boolCase parentType rest filteredField htail with
                    ⟨sourceField, hsourceMem, hsource⟩
                  exact ⟨sourceField, by
                    simp [FieldMerge.collectFields, hlookup, hsourceMem],
                    hsource⟩
        | cons child children =>
            cases hchild :
                filterSelectionSetBoolCase boolCase
                  (child :: children) with
            | nil =>
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                        schema boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [filterSelectionSetBoolCase, hallow, hchild,
                      FieldMerge.collectFields, hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
            | cons filteredChild filteredChildren =>
                simp [filterSelectionSetBoolCase, hallow, hchild,
                  FieldMerge.collectFields] at hfield
                cases hlookup : schema.lookupField parentType fieldName with
                | none =>
                    simp [hlookup] at hfield
                    rcases
                      collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                        schema boolCase parentType rest filteredField hfield with
                      ⟨sourceField, hsourceMem, hsource⟩
                    exact ⟨sourceField, by
                      simp [FieldMerge.collectFields, hlookup, hsourceMem],
                      hsource⟩
                | some fieldDefinition =>
                    simp [hlookup] at hfield
                    rcases hfield with hhead | htail
                    · subst filteredField
                      refine ⟨{
                        parentType := parentType,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        outputType := fieldDefinition.outputType,
                        selectionSet := child :: children
                      }, ?_, ?_⟩
                      · simp [FieldMerge.collectFields, hlookup]
                      · exact ⟨rfl, rfl, rfl, rfl, rfl, hchild.symm⟩
                    · rcases
                        collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                          schema boolCase parentType rest filteredField htail with
                        ⟨sourceField, hsourceMem, hsource⟩
                      exact ⟨sourceField, by
                        simp [FieldMerge.collectFields, hlookup, hsourceMem],
                        hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          cases hlookup : schema.lookupField parentType fieldName
          <;> simp [FieldMerge.collectFields, hlookup, hsourceMem],
          hsource⟩
  | parentType,
    Selection.inlineFragment none directives selectionSet :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                schema boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase parentType selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩
  | parentType,
    Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest,
    filteredField, hfield => by
      by_cases hallow : directivesAllowIn boolCase directives = true
      · cases hchild :
          filterSelectionSetBoolCase boolCase selectionSet with
        | nil =>
            simp [filterSelectionSetBoolCase, hallow, hchild] at hfield
            rcases
              collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                schema boolCase parentType rest filteredField hfield with
              ⟨sourceField, hsourceMem, hsource⟩
            exact ⟨sourceField, by
              simp [FieldMerge.collectFields, hsourceMem], hsource⟩
        | cons filteredChild filteredChildren =>
            simp [filterSelectionSetBoolCase, hallow, hchild,
              FieldMerge.collectFields] at hfield
            rcases hfield with hchildField | htail
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase typeCondition selectionSet filteredField
                  (by simpa [hchild] using hchildField) with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
            · rcases
                collectFields_filterSelectionSetBoolCase_mem_source_forMerge
                  schema boolCase parentType rest filteredField htail with
                ⟨sourceField, hsourceMem, hsource⟩
              exact ⟨sourceField, by
                simp [FieldMerge.collectFields, hsourceMem], hsource⟩
      · have hfalse :
            directivesAllowIn boolCase directives = false := by
          cases hmatch : directivesAllowIn boolCase directives
          · rfl
          · contradiction
        simp [filterSelectionSetBoolCase, hfalse] at hfield
        rcases
          collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema
            boolCase parentType rest filteredField hfield with
          ⟨sourceField, hsourceMem, hsource⟩
        exact ⟨sourceField, by
          simp [FieldMerge.collectFields, hsourceMem], hsource⟩

theorem fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics
    (schema : Schema) (boolCase : BoolCase)
    {parentType : Name} {selectionSet : List Selection}
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (filterSelectionSetBoolCase boolCase selectionSet) := by
  intro hmerge
  refine FieldMerge.fieldsInSetCanMerge_transport
    (BoolFilteredScopedFieldSourceForMerge schema boolCase) ?_ ?_ hmerge
    parentType (filterSelectionSetBoolCase boolCase selectionSet) ?_
  · intro source target hsource
    exact ⟨hsource.parentType, hsource.responseName, hsource.fieldName,
      hsource.arguments, hsource.outputType⟩
  · intro sourceLeft sourceRight targetLeft targetRight hleft hright field hfield
    simp only [FieldMerge.collectSubfields, List.mem_append] at hfield
    rcases hfield with hfield | hfield
    · rw [hleft.outputType, hleft.selectionSet] at hfield
      rcases collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema boolCase
          sourceLeft.outputType.namedType sourceLeft.selectionSet field hfield with
        ⟨sourceField, hsourceField, hsource⟩
      exact ⟨sourceField, List.mem_append_left _ hsourceField, hsource⟩
    · rw [hright.outputType, hright.selectionSet] at hfield
      rcases collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema boolCase
          sourceRight.outputType.namedType sourceRight.selectionSet field hfield with
        ⟨sourceField, hsourceField, hsource⟩
      exact ⟨sourceField, List.mem_append_right _ hsourceField, hsource⟩
  · exact collectFields_filterSelectionSetBoolCase_mem_source_forMerge schema boolCase
      parentType selectionSet

end GraphQL.NormalForm.CompleteNormalization
