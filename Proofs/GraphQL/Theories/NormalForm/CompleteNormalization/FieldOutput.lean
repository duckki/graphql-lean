import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ScopedSelections

/-!
Scoped field-output facts for complete-normalization proofs.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

def completeScopedFieldOutputsInclude
    (schema : Schema) (runtimeType : Name)
    (scopedSelections : List CompleteScopedSelection)
    : Prop :=
  ∀ scopedSelection,
    scopedSelection ∈ scopedSelections
    -> ∃ responseName fieldName arguments directives subselections fieldDefinition,
        scopedSelection.selection
          = Selection.field responseName fieldName arguments directives subselections
        ∧ schema.lookupField scopedSelection.lookupParent fieldName = some fieldDefinition
        ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true

theorem completeScopedFieldOutputsInclude_append
    {schema : Schema} {runtimeType : Name}
    {left right : List CompleteScopedSelection}
    : completeScopedFieldOutputsInclude schema runtimeType left
      -> completeScopedFieldOutputsInclude schema runtimeType right
      -> completeScopedFieldOutputsInclude schema runtimeType (left ++ right) := by
  intro hleft hright scopedSelection hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft scopedSelection hmem
  · exact hright scopedSelection hmem

theorem completeScopedFieldOutputsInclude_append_left
    {schema : Schema} {runtimeType : Name}
    {left right : List CompleteScopedSelection}
    : completeScopedFieldOutputsInclude schema runtimeType (left ++ right)
      -> completeScopedFieldOutputsInclude schema runtimeType left := by
  intro hmatches scopedSelection hmem
  exact hmatches scopedSelection (List.mem_append.mpr (Or.inl hmem))

theorem completeScopedFieldOutputsInclude_append_right
    {schema : Schema} {runtimeType : Name}
    {left right : List CompleteScopedSelection}
    : completeScopedFieldOutputsInclude schema runtimeType (left ++ right)
      -> completeScopedFieldOutputsInclude schema runtimeType right := by
  intro hmatches scopedSelection hmem
  exact hmatches scopedSelection (List.mem_append.mpr (Or.inr hmem))

theorem completeScopedFieldOutputsInclude_tail
    {schema : Schema} {runtimeType : Name}
    {scopedSelection : CompleteScopedSelection}
    {rest : List CompleteScopedSelection}
    : completeScopedFieldOutputsInclude schema runtimeType (scopedSelection :: rest)
      -> completeScopedFieldOutputsInclude schema runtimeType rest := by
  intro hmatches candidate hcandidate
  exact hmatches candidate
    (List.mem_cons_of_mem scopedSelection hcandidate)

theorem completeScopedFieldOutputsInclude_head
    {schema : Schema} {runtimeType : Name}
    {scopedSelection : CompleteScopedSelection}
    {rest : List CompleteScopedSelection}
    : completeScopedFieldOutputsInclude schema runtimeType (scopedSelection :: rest)
      -> ∃ responseName fieldName arguments directives subselections fieldDefinition,
          scopedSelection.selection
            = Selection.field responseName fieldName arguments directives subselections
          ∧ schema.lookupField scopedSelection.lookupParent fieldName
            = some fieldDefinition
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hmatches
  exact hmatches scopedSelection (by simp)

theorem completeScopedFieldOutputsInclude_selection_field
    {schema : Schema} {runtimeType : Name}
    {scopedSelection : CompleteScopedSelection}
    {scopedSelections : List CompleteScopedSelection}
    : completeScopedFieldOutputsInclude schema runtimeType scopedSelections
      -> scopedSelection ∈ scopedSelections
      -> ∃ responseName fieldName arguments directives subselections,
          scopedSelection.selection
          = Selection.field responseName fieldName arguments directives
              subselections := by
  intro hmatches hmem
  rcases hmatches scopedSelection hmem with
    ⟨responseName, fieldName, arguments, directives, subselections,
      _fieldDefinition, hselection, _hlookup, _hincludes⟩
  exact ⟨responseName, fieldName, arguments, directives, subselections,
    hselection⟩

theorem completeScopedFieldOutputsInclude_lookup
    {schema : Schema} {runtimeType : Name}
    {scopedSelection : CompleteScopedSelection}
    {scopedSelections : List CompleteScopedSelection}
    {responseName fieldName : Name} {arguments : List Argument}
    {directives : List DirectiveApplication}
    {subselections : List Selection}
    : completeScopedFieldOutputsInclude schema runtimeType scopedSelections
      -> scopedSelection ∈ scopedSelections
      -> scopedSelection.selection
          = Selection.field responseName fieldName arguments directives subselections
      -> ∃ fieldDefinition,
          schema.lookupField scopedSelection.lookupParent fieldName = some fieldDefinition
          ∧ schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
            = true := by
  intro hmatches hmem hselection
  rcases hmatches scopedSelection hmem with
    ⟨matchedResponseName, matchedFieldName, matchedArguments,
      matchedDirectives, matchedSubselections, fieldDefinition,
      hmatchedSelection, hlookup, hincludes⟩
  rw [hselection] at hmatchedSelection
  cases hmatchedSelection
  exact ⟨fieldDefinition, hlookup, hincludes⟩

theorem completeScopedFieldOutputsInclude_staticScopedFieldsWithResponseName_object
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName runtimeType : Name)
    (fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.objectType lookupParent
      -> selectionSetLookupValid schema lookupParent
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema lookupParent
          (Selection.field responseName fieldName arguments directives selectionSet
            :: rest)
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> schema.typeIncludesObjectBool lookupParent groundType = true
      -> schema.typeIncludesObjectBool fieldDefinition.outputType.namedType runtimeType
          = true
      -> completeScopedFieldOutputsInclude schema runtimeType
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName rest) := by
  intro hschema hobject hlookupValid hmerge hlookup hground hincludes
    scopedSelection hmem
  rcases
      staticScopedFieldsWithResponseName_mem_field schema boolCase
        lookupParent groundType responseName rest scopedSelection hmem with
    ⟨matchedResponseName, matchedFieldName, matchedArguments,
      matchedDirectives, matchedSubselections, hselection⟩
  have htailLookup :
      selectionSetLookupValid schema lookupParent rest :=
    selectionSetLookupValid_tail hlookupValid
  rcases
      staticScopedFieldsWithResponseName_mem_fieldMergeCollectFields_lookupValid
        schema boolCase lookupParent groundType responseName rest
        scopedSelection matchedResponseName matchedFieldName matchedArguments
        matchedDirectives matchedSubselections htailLookup hmem hselection with
    ⟨matchedScopedField, hmatchedMemRest, hmatchedParent, hmatchedResponse,
      hmatchedField, hmatchedArguments, hmatchedSelectionSet⟩
  let headScopedField : FieldMerge.ScopedField := {
    parentType := lookupParent,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := selectionSet
  }
  have hheadMem :
      headScopedField ∈ FieldMerge.collectFields schema lookupParent
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
    simp [headScopedField, FieldMerge.collectFields, hlookup]
  have hmatchedMem :
      matchedScopedField ∈ FieldMerge.collectFields schema lookupParent
        (Selection.field responseName fieldName arguments directives
          selectionSet :: rest) := by
    simpa [FieldMerge.collectFields, hlookup] using Or.inr hmatchedMemRest
  have hmatchedResponseName : matchedResponseName = responseName := by
    have heraseMem :
        scopedSelection.selection ∈
          eraseCompleteScopedSelectionSet
            (staticScopedFieldsWithResponseName schema boolCase
              lookupParent groundType responseName rest) :=
      eraseCompleteScopedSelectionSet_mem_of_mem hmem
    have hvalidField :
        scopedSelection.selection ∈
          fieldSelectionsWithResponseNameInScope schema lookupParent responseName rest :=
      erase_staticScopedFieldsWithResponseName_mem_fieldSelectionsWithResponseNameInScope
        schema boolCase lookupParent groundType responseName rest
        scopedSelection.selection hground heraseMem
    rcases
        fieldSelectionsWithResponseNameInScope_mem_field schema lookupParent responseName
          rest scopedSelection.selection hvalidField with
      ⟨validFieldName, validArguments, validDirectives,
        validSubselections, hvalidSelection⟩
    rw [hselection] at hvalidSelection
    injection hvalidSelection with hresponse _hfield _harguments
      _hdirectives _hsubselections
  have hresponseEq :
      headScopedField.responseName = matchedScopedField.responseName := by
    simp [headScopedField, hmatchedResponse, hmatchedResponseName]
  have hfieldMerge :
      FieldMerge.fieldsForNameCanMerge schema headScopedField
        matchedScopedField :=
    FieldMerge.fieldsInSetCanMerge_pair hmerge hheadMem hmatchedMem
      hresponseEq
  have hlookupParentEqGround : groundType = lookupParent :=
    object_typeIncludesObjectBool_eq_self schema hobject hground
  have hmatchedGround :
      schema.typeIncludesObjectBool scopedSelection.lookupParent lookupParent =
        true := by
    have hmatches :=
      staticScopedFieldsWithResponseName_groundApplies schema boolCase
        lookupParent groundType responseName rest hground scopedSelection hmem
    simpa [hlookupParentEqGround] using hmatches
  have hparents :
      headScopedField.parentType = matchedScopedField.parentType
        ∨ ¬ schema.objectType headScopedField.parentType
        ∨ ¬ schema.objectType matchedScopedField.parentType := by
    by_cases hmatchedObject : schema.objectType matchedScopedField.parentType
    · have hmatchedParentInclude :
          schema.typeIncludesObjectBool matchedScopedField.parentType
            lookupParent = true := by
        simpa [hmatchedParent] using hmatchedGround
      have hmatchedParentEq :
          lookupParent = matchedScopedField.parentType :=
        object_typeIncludesObjectBool_eq_self schema hmatchedObject
          hmatchedParentInclude
      exact Or.inl (by simp [headScopedField, hmatchedParentEq])
    · exact Or.inr (Or.inr hmatchedObject)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents
  have hmatchedFieldName : matchedFieldName = fieldName := by
    have hsame : headScopedField.fieldName = matchedScopedField.fieldName :=
      hidentity.1
    exact hmatchedField.symm.trans (hsame.symm.trans (by rfl))
  rcases
      collectFields_scoped_mem_lookupValid schema lookupParent rest
        matchedScopedField htailLookup hmatchedMemRest with
    ⟨matchedDefinition, hmatchedLookup, hmatchedOutput⟩
  have hmatchedLookupSelection :
      schema.lookupField scopedSelection.lookupParent matchedFieldName =
        some matchedDefinition := by
    simpa [hmatchedParent, hmatchedField] using hmatchedLookup
  have hmatchedIncludes :
      schema.typeIncludesObjectBool matchedDefinition.outputType.namedType
        runtimeType = true := by
    by_cases hmatchedObject : schema.objectType matchedScopedField.parentType
    · have hmatchedParentInclude :
          schema.typeIncludesObjectBool matchedScopedField.parentType
            lookupParent = true := by
        simpa [hmatchedParent] using hmatchedGround
      have hmatchedParentEq :
          lookupParent = matchedScopedField.parentType :=
        object_typeIncludesObjectBool_eq_self schema hmatchedObject
          hmatchedParentInclude
      have hlookup' :
          schema.lookupField lookupParent fieldName =
            some matchedDefinition := by
        simpa [hmatchedParentEq, hmatchedFieldName, hmatchedField] using
          hmatchedLookup
      rw [hlookup] at hlookup'
      cases hlookup'
      exact hincludes
    · have hpossibleParent :
          lookupParent ∈
            schema.getPossibleTypes matchedScopedField.parentType := by
        have hmatchedParentInclude :
            schema.typeIncludesObjectBool matchedScopedField.parentType
              lookupParent = true := by
          simpa [hmatchedParent] using hmatchedGround
        exact List.contains_iff_mem.mp hmatchedParentInclude
      have himplementationLookup :
          schema.lookupField lookupParent matchedScopedField.fieldName =
            some fieldDefinition := by
        simpa [hmatchedFieldName, hmatchedField] using hlookup
      have hsubtype :
          schema.outputTypeSubtype fieldDefinition.outputType
            matchedDefinition.outputType :=
        SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
          hschema hpossibleParent hmatchedLookup himplementationLookup
      exact typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
        hsubtype hincludes
  exact ⟨matchedResponseName, matchedFieldName, matchedArguments,
    matchedDirectives, matchedSubselections, matchedDefinition, hselection,
    hmatchedLookupSelection, by simpa [hmatchedOutput] using hmatchedIncludes⟩

end CompleteNormalization

end NormalForm

end GraphQL
