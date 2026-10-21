import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection

/-! Declared merge-source witnesses for collected executable fields. -/

namespace GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

open GraphQL.Execution

mutual
  theorem collectSelection_entry_runtimeField
      {ObjectRef : Type} (schema : Schema) (values : VariableValues)
      (collectParent runtimeType : Name) (identity : ObjectRef)
      (hobject : schema.objectType runtimeType)
      (selection : Selection) (responseName : Name) (field : ExecutableField)
      (hfield
        : (responseName, field)
          ∈ collectedExecutableEntries
              (GraphQL.Execution.collectSelection schema values collectParent
                (.object runtimeType identity) selection))
      : ∃ directives,
          Selection.field responseName field.fieldName field.arguments directives
            field.selectionSet
          ∈ NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
              responseName [selection] := by
    cases selection with
    | field name fieldName arguments directives children =>
        by_cases hallows : selectionDirectivesAllowBool values directives = true
        · simp [GraphQL.Execution.collectSelection, hallows,
            collectedExecutableEntries] at hfield
          rcases hfield with ⟨rfl, rfl⟩
          exact ⟨directives, by simp [NormalForm.fieldSelectionsWithResponseNameInScope]⟩
        · have hfalse : selectionDirectivesAllowBool values directives = false := by
            cases h : selectionDirectivesAllowBool values directives <;> simp_all
          simp [GraphQL.Execution.collectSelection, hfalse, collectedExecutableEntries] at hfield
    | inlineFragment condition directives children =>
        by_cases hallows : selectionDirectivesAllowBool values directives = true
        · cases condition with
          | none =>
              simp only [GraphQL.Execution.collectSelection, hallows, ↓reduceIte] at hfield
              simpa [NormalForm.fieldSelectionsWithResponseNameInScope]
                using collectFields_entry_runtimeField schema values collectParent
                  runtimeType identity hobject children responseName field hfield
          | some condition =>
              by_cases happlies : doesFragmentTypeApplyBool schema collectParent
                  (.object runtimeType identity) condition = true
              · simp only [GraphQL.Execution.collectSelection, hallows, happlies,
                  ↓reduceIte] at hfield
                have hinclude : schema.typeIncludesObjectBool condition runtimeType = true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using happlies
                have hoverlap : schema.typesOverlapBool runtimeType condition = true := by
                  unfold Schema.typesOverlapBool
                  exact List.any_eq_true.mpr ⟨runtimeType,
                    List.contains_iff_mem.mp
                      (NormalForm.object_typeIncludesObjectBool_self schema hobject), hinclude⟩
                simpa [NormalForm.fieldSelectionsWithResponseNameInScope, hoverlap]
                  using collectFields_entry_runtimeField schema values collectParent
                    runtimeType identity hobject children responseName field hfield
              · have hfalse : doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) condition = false := by
                  cases h : doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) condition <;> simp_all
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  collectedExecutableEntries] at hfield
        · have hfalse : selectionDirectivesAllowBool values directives = false := by
            cases h : selectionDirectivesAllowBool values directives <;> simp_all
          cases condition <;> simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableEntries] at hfield

  theorem collectFields_entry_runtimeField
      {ObjectRef : Type} (schema : Schema) (values : VariableValues)
      (collectParent runtimeType : Name) (identity : ObjectRef)
      (hobject : schema.objectType runtimeType)
      (selections : List Selection) (responseName : Name) (field : ExecutableField)
      (hfield
        : (responseName, field)
          ∈ collectedExecutableEntries
              (GraphQL.Execution.collectFields schema values collectParent
                (.object runtimeType identity) selections))
      : ∃ directives,
          Selection.field responseName field.fieldName field.arguments directives
            field.selectionSet
          ∈ NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
              responseName selections := by
    cases selections with
    | nil => simp [GraphQL.Execution.collectFields, collectedExecutableEntries] at hfield
    | cons selection rest =>
        simp only [GraphQL.Execution.collectFields,
          collectedExecutableEntries_mem_mergeExecutableGroups] at hfield
        have hmem : ∃ directives,
            Selection.field responseName field.fieldName field.arguments directives
                field.selectionSet
              ∈ NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
                  responseName [selection]
                ++ NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
                  responseName rest := by
          rcases hfield with hhead | htail
          · rcases collectSelection_entry_runtimeField schema values collectParent runtimeType
              identity hobject selection responseName field hhead with ⟨directives, hmem⟩
            exact ⟨directives, List.mem_append_left _ hmem⟩
          · rcases collectFields_entry_runtimeField schema values collectParent runtimeType
              identity hobject rest responseName field htail with ⟨directives, hmem⟩
            exact ⟨directives, List.mem_append_right _ hmem⟩
        have hcons : NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
            responseName (selection :: rest)
            = NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
                responseName [selection]
              ++ NormalForm.fieldSelectionsWithResponseNameInScope schema runtimeType
                responseName rest := by
          cases selection with
          | field name fieldName arguments directives children =>
              simp only [NormalForm.fieldSelectionsWithResponseNameInScope]
              split <;> simp
          | inlineFragment condition directives children =>
              cases condition with
              | none => simp [NormalForm.fieldSelectionsWithResponseNameInScope]
              | some condition =>
                  simp only [NormalForm.fieldSelectionsWithResponseNameInScope]
                  split <;> simp
        simpa only [hcons] using hmem
end

theorem executableFieldSelections_runtimeField_mem
    (schema : Schema) (runtimeType responseName name : Name)
    (fields : List ExecutableField) (selection : Selection)
    (hselection
      : selection
        ∈ NormalForm.fieldSelectionsWithResponseNameInScope
            schema runtimeType name (executableFieldSelections responseName fields))
    : selection ∈ executableFieldSelections responseName fields := by
  induction fields with
  | nil => simp [executableFieldSelections,
      NormalForm.fieldSelectionsWithResponseNameInScope] at hselection
  | cons field rest ih =>
      simp only [executableFieldSelections, List.map_cons, executableFieldSelection,
        NormalForm.fieldSelectionsWithResponseNameInScope] at hselection ⊢
      split at hselection
      · rcases List.mem_cons.mp hselection with rfl | htail
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih htail)
      · exact List.mem_cons_of_mem _ (ih hselection)

theorem runtimeMergeSource_executableFields
    (schema : Schema) (runtimeType responseName : Name)
    (fields : List ExecutableField) (sources : List FieldMerge.ScopedField)
    (hvalid
      : ∀ source,
          source ∈ sources
          -> ∃ definition,
              schema.lookupField source.parentType source.fieldName = some definition
              ∧ definition.outputType = source.outputType
              ∧ NormalForm.selectionSetDeclaredLookupReady schema
                  source.outputType.namedType source.selectionSet)
    (hmerge
      : ∀ left,
          left ∈ sources
          -> ∀ right,
              right ∈ sources
              -> left.responseName = right.responseName
              -> FieldMerge.fieldsForNameCanMerge schema left right)
    (hscoped
      : ExecutableEntriesRuntimeScopedBy schema runtimeType sources
          (fields.map (fun field => (responseName, field))))
    : NormalForm.runtimeMergeSource schema runtimeType
        (executableFieldSelections responseName fields) := by
  refine ⟨sources, hvalid, hmerge, ?_⟩
  intro name fieldName arguments directives children hfield
  have hmem := executableFieldSelections_runtimeField_mem schema runtimeType responseName
    name fields _ hfield
  rcases List.mem_map.mp hmem with ⟨field, hfield, heq⟩
  have heq' : responseName = name ∧ field.fieldName = fieldName
      ∧ field.arguments = arguments ∧ directives = [] ∧ field.selectionSet = children := by
    simpa [executableFieldSelection] using heq
  rcases hscoped (responseName, field) (List.mem_map.mpr ⟨field, hfield, rfl⟩) with
    ⟨source, hsource, hresponse, hmatch, happlies⟩
  exact ⟨source, hsource, happlies, hresponse.trans heq'.1,
    hmatch.1.trans heq'.2.1, hmatch.2.1.trans heq'.2.2.1,
    hmatch.2.2.trans heq'.2.2.2.2⟩

theorem collectFields_executableFields_runtimeMergeSource
    {ObjectRef : Type} (schema : Schema) (values : VariableValues)
    (collectParent runtimeType : Name) (identity : ObjectRef)
    (selections : List Selection) (responseName : Name) (fields : List ExecutableField)
    (hobject : schema.objectType runtimeType)
    (hsource : NormalForm.runtimeMergeSource schema runtimeType selections)
    (hfields
      : ∀ field,
          field ∈ fields
          -> (responseName, field)
              ∈ collectedExecutableEntries
                  (GraphQL.Execution.collectFields schema values collectParent
                    (.object runtimeType identity) selections))
    : NormalForm.runtimeMergeSource schema runtimeType
        (executableFieldSelections responseName fields) := by
  rcases hsource with ⟨sources, hvalid, hmerge, hcover⟩
  apply runtimeMergeSource_executableFields schema runtimeType responseName fields sources
    hvalid hmerge
  intro entry hentry
  rcases List.mem_map.mp hentry with ⟨field, hfield, rfl⟩
  rcases collectFields_entry_runtimeField schema values collectParent runtimeType identity
    hobject selections responseName field (hfields field hfield) with ⟨directives, hfield⟩
  rcases hcover _ _ _ _ _ hfield with
    ⟨source, hsource, happlies, hresponse, hname, harguments, hchildren⟩
  exact ⟨source, hsource, hresponse, ⟨hname, harguments, hchildren⟩, happlies⟩

theorem runtimeMergeSource_mergedExecutableFields
    (schema : Schema) (hschema : SchemaWellFormedness.schemaWellFormed schema)
    {parentType responseName childRuntime : Name} {field : ExecutableField}
    {fields : List ExecutableField} {definition : FieldDefinition}
    (hsource
      : NormalForm.runtimeMergeSource schema parentType
          (executableFieldSelections responseName (field :: fields)))
    (hlookup : schema.lookupField parentType field.fieldName = some definition)
    (hinclude
      : schema.typeIncludesObjectBool definition.outputType.namedType childRuntime = true)
    : NormalForm.runtimeMergeSource schema childRuntime
        (GraphQL.Execution.mergedFieldSelectionSet (field :: fields)) := by
  have hrest : NormalForm.fieldSelectionsWithResponseNameInScope schema parentType responseName
      (executableFieldSelections responseName fields)
        = executableFieldSelections responseName fields := by
    clear hsource
    induction fields with
    | nil => simp [executableFieldSelections,
        NormalForm.fieldSelectionsWithResponseNameInScope]
    | cons candidate rest ih =>
        simpa [executableFieldSelections, executableFieldSelection,
          NormalForm.fieldSelectionsWithResponseNameInScope] using congrArg
            (executableFieldSelection responseName candidate :: ·) ih
  have hmerged : NormalForm.mergeSelectionSets (executableFieldSelections responseName fields)
      = GraphQL.Execution.mergedFieldSelectionSet fields := by
    clear hsource hrest
    induction fields with
    | nil => rfl
    | cons candidate rest ih =>
        simpa [executableFieldSelections, executableFieldSelection,
          NormalForm.mergeSelectionSets, GraphQL.Execution.mergedFieldSelectionSet,
          Selection.subselections] using congrArg (candidate.selectionSet ++ ·) ih
  have hresult := NormalForm.runtimeMergeSource_fieldHead_merged schema hschema hsource
    hlookup hinclude
  change NormalForm.runtimeMergeSource schema childRuntime
    (field.selectionSet ++ NormalForm.mergeSelectionSets
      (NormalForm.fieldSelectionsWithResponseNameInScope schema parentType responseName
        (executableFieldSelections responseName fields))) at hresult
  simpa only [hrest, hmerged, GraphQL.Execution.mergedFieldSelectionSet] using hresult

theorem collectFields_fieldCompatible_of_runtimeMergeSource {ObjectRef : Type}
    (schema : Schema) (values : VariableValues) (collectParent runtimeType : Name)
    (identity : ObjectRef) (selections : List Selection)
    (hobject : schema.objectType runtimeType)
    (hsource : NormalForm.runtimeMergeSource schema runtimeType selections)
    : CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema values collectParent
          (.object runtimeType identity) selections) := by
  intro responseName fields hgroup first later hfirst hlater
  rcases collectFields_entry_runtimeField schema values collectParent runtimeType identity
    hobject selections responseName first
    (collectedExecutableEntries_mem_of_group_mem hgroup hfirst) with ⟨firstDirectives, hfirst⟩
  rcases collectFields_entry_runtimeField schema values collectParent runtimeType identity
    hobject selections responseName later
    (collectedExecutableEntries_mem_of_group_mem hgroup hlater) with ⟨laterDirectives, hlater⟩
  exact NormalForm.runtimeMergeSource_identity hsource hfirst hlater

theorem collectFields_group_mergedRuntimeSource
    {ObjectRef : Type} (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (values : VariableValues) (parentType runtimeType : Name) (identity : ObjectRef)
    (selections : List Selection) (responseName : Name) (fields : List ExecutableField)
    (first : ExecutableField) (definition : FieldDefinition) (childRuntime : Name)
    (hobject : schema.objectType runtimeType) (hparent : parentType = runtimeType)
    (hsource : NormalForm.runtimeMergeSource schema runtimeType selections)
    (hgroup
      : (responseName, fields)
        ∈ GraphQL.Execution.collectFields schema values
            parentType (.object runtimeType identity) selections)
    (hfirst : first ∈ fields)
    (hlookup : schema.lookupField parentType first.fieldName = some definition)
    (hinclude
      : schema.typeIncludesObjectBool definition.outputType.namedType childRuntime = true)
    : NormalForm.runtimeMergeSource schema childRuntime
        (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  cases fields with
  | nil => simp at hfirst
  | cons head tail =>
      have hfields := collectFields_executableFields_runtimeMergeSource schema values
        parentType runtimeType identity selections responseName (head :: tail) hobject hsource
        (fun _ hfield => collectedExecutableEntries_mem_of_group_mem hgroup hfield)
      have hname := (collectFields_fieldCompatible_of_runtimeMergeSource schema values
        parentType runtimeType identity selections hobject hsource responseName (head :: tail)
        hgroup head first (by simp) hfirst).1
      exact runtimeMergeSource_mergedExecutableFields schema hschema hfields
        (by simpa [hparent, hname] using hlookup) hinclude

end GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
