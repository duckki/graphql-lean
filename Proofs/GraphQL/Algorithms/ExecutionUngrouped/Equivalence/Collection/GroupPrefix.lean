import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection

/-!
Collected group-prefix facts for merged field selection sets.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

theorem collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) := by
  intro hparentRuntime hvalid hgroup hprefix
  have hscopedAll :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet)) :=
    collectFields_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet hparentRuntime hvalid
  apply
    ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
      (FieldMerge.collectFields schema validParent selectionSet)
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet))
      (field :: prefixTail)
  · intro candidate hcandidate
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  · exact hscopedAll

theorem collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) := by
  intro hparentRuntime hvalid hgroup hprefix
  have hscopedAll :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet)) :=
    collectFields_runtimeScopedBy_of_selectionSetValid_object schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet hparentRuntime hvalid
  apply
    ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
      (FieldMerge.collectFields schema validParent selectionSet)
      (collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet))
      (field :: prefixTail)
  · intro candidate hcandidate
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  · exact hscopedAll

theorem collectFields_group_prefix_responseName
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : (responseName, field :: fields)
        ∈ GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ∀ candidate,
          candidate ∈ field :: prefixTail -> candidate.responseName = responseName := by
  intro hgroup hprefix candidate hcandidate
  apply
    collectFields_responseName schema variableValues collectParent
      (.object runtimeType identity) selectionSet responseName
      (field :: fields) hgroup candidate
  rcases List.mem_cons.mp hcandidate with hhead | htail
  · subst candidate
    simp
  · exact List.mem_cons_of_mem field (hprefix candidate htail)

theorem collectFields_group_prefix_childFieldSemanticsReady_of_selectionSetValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> (∀ candidate,
            candidate ∈ field :: prefixTail
            -> ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                      childRuntime
                    = true)
      -> ∀ candidate,
          candidate ∈ field :: prefixTail
          -> NormalForm.selectionSetSemanticsReady schema childRuntime
              candidate.selectionSet := by
  intro hschema hparentRuntime hvalid hgroup hprefix hcompatible candidate
    hcandidate
  have hscopedPrefix :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) :=
    collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid schema
      variableDefinitions variableValues collectParent validParent runtimeType
      identity selectionSet responseName field fields prefixTail
      hparentRuntime hvalid hgroup hprefix
  rcases
      executableFieldsRuntimeScopedBy_scopedSelectionSetValid_field schema
        variableDefinitions validParent runtimeType selectionSet
        (field :: prefixTail) hvalid hscopedPrefix candidate hcandidate with
    ⟨scopedField, hscopedMem, hmatch, hruntime, hselectionSetValid⟩
  exact
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_possibleObject
      schema variableDefinitions scopedField.outputType.namedType
      childRuntime hschema
      (List.contains_iff_mem.mp
        (hcompatible candidate hcandidate scopedField hscopedMem hmatch
          hruntime))
      candidate.selectionSet hselectionSetValid

theorem collectFields_group_prefix_childFieldSemanticsReady_of_selectionSetValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> (∀ candidate,
            candidate ∈ field :: prefixTail
            -> ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                      childRuntime
                    = true)
      -> ∀ candidate,
          candidate ∈ field :: prefixTail
          -> NormalForm.selectionSetSemanticsReady schema childRuntime
              candidate.selectionSet := by
  intro hschema hparentRuntime hvalid hgroup hprefix hcompatible candidate
    hcandidate
  have hscopedPrefix :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) :=
    collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet responseName field fields prefixTail
      hparentRuntime hvalid hgroup hprefix
  rcases
      executableFieldsRuntimeScopedBy_scopedSelectionSetValid_field schema
        variableDefinitions validParent runtimeType selectionSet
        (field :: prefixTail) hvalid hscopedPrefix candidate hcandidate with
    ⟨scopedField, hscopedMem, hmatch, hruntime, hselectionSetValid⟩
  exact
    NormalForm.selectionSetSemanticsReady_of_selectionSetValid_possibleObject
      schema variableDefinitions scopedField.outputType.namedType
      childRuntime hschema
      (List.contains_iff_mem.mp
        (hcompatible candidate hcandidate scopedField hscopedMem hmatch
          hruntime))
      candidate.selectionSet hselectionSetValid

theorem
    collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetValid_object
    {ObjectIdentity : Type} (schema : Schema)
    (variableDefinitions : List VariableDefinition) (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (responseName childRuntime : Name)
    (field : ExecutableField) (fields prefixTail : List ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> (∀ candidate,
            candidate ∈ field :: prefixTail
            -> ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                      childRuntime
                    = true)
      -> NormalForm.selectionSetLookupValid schema childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hschema hparentRuntime hvalid hgroup hprefix hcompatible
  apply selectionSetLookupValid_mergedFieldSelectionSet_of_semanticsReady
  intro candidate hcandidate
  exact
    collectFields_group_prefix_childFieldSemanticsReady_of_selectionSetValid_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet responseName childRuntime field fields
      prefixTail hschema hparentRuntime hvalid hgroup hprefix hcompatible
      candidate hcandidate

mutual
  theorem collectSelection_childLookupValid_of_selectionValidInPossibleTypes_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      (candidate : ExecutableField) (childRuntime : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionValid schema variableDefinitions validParent selection
        -> candidate
            ∈ collectedExecutableFields
                (GraphQL.Execution.collectSelection schema variableValues
                  collectParent (.object runtimeType identity) selection)
        -> (∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent [selection]
              -> ScopedFieldMatchesExecutableIdentity scopedField candidate
              -> ScopedFieldRuntimeApplies schema runtimeType scopedField
              -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                    childRuntime
                  = true)
        -> NormalForm.selectionSetLookupValid schema childRuntime
            candidate.selectionSet := by
    intro hschema hparentRuntime himplementation hcandidate hcompatible
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · have hcandidateEq :
              candidate =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa [GraphQL.Execution.collectSelection, hallows,
              collectedExecutableFields] using hcandidate
          subst candidate
          rcases Validation.selectionValid_field_lookup himplementation with
            ⟨fieldDefinition, hlookup, _harguments, hchild⟩
          let scopedField : FieldMerge.ScopedField :=
            { parentType := validParent
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              outputType := fieldDefinition.outputType
              selectionSet := selectionSet }
          have hscopedMem :
              scopedField ∈
                FieldMerge.collectFields schema validParent
                  [Selection.field responseName fieldName arguments directives
                    selectionSet] := by
            simp [scopedField, FieldMerge.collectFields, hlookup]
          have hmatch :
              ScopedFieldMatchesExecutableIdentity scopedField
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simp [scopedField, ScopedFieldMatchesExecutableIdentity]
          have hinclude :
              schema.typeIncludesObjectBool
                  scopedField.outputType.namedType childRuntime =
                true :=
            hcompatible scopedField hscopedMem hmatch
              (by
                simpa [scopedField, ScopedFieldRuntimeApplies,
                  ScopedParentRuntimeApplies] using hparentRuntime)
          have hchildValid :
              Validation.selectionSetValid schema variableDefinitions
                fieldDefinition.outputType.namedType selectionSet :=
            NormalForm.fieldSelectionSetValid_child_of_possibleType hchild
              (List.contains_iff_mem.mp hinclude)
          exact
            NormalForm.selectionSetLookupValid_of_selectionSetValid_possibleObject
              schema variableDefinitions fieldDefinition.outputType.namedType
              childRuntime hschema (List.contains_iff_mem.mp hinclude)
              selectionSet hchildValid
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableFields] at hcandidate
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hbody :
                Validation.selectionSetValid schema
                  variableDefinitions validParent selectionSet := by
              exact Validation.selectionValid_inlineFragment_none_selectionSetValid
                himplementation
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · simp [GraphQL.Execution.collectSelection, hallows] at hcandidate
              exact
                collectFields_childLookupValid_of_selectionSetValidInPossibleTypes_object
                  schema variableDefinitions variableValues collectParent
                  validParent runtimeType identity selectionSet candidate
                  childRuntime hschema hparentRuntime hbody hcandidate
                  (by
                    intro scopedField hscoped hmatch hruntime
                    exact hcompatible scopedField
                      (by
                        simpa [FieldMerge.collectFields] using hscoped)
                      hmatch hruntime)
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = true
              · have hcondition :
                    schema.typeIncludesObjectBool typeCondition runtimeType =
                      true := by
                  simpa [doesFragmentTypeApplyBool, runtimeObjectType?] using
                    happly
                have hoverlap :
                    schema.typesOverlapBool validParent typeCondition =
                      true := by
                  unfold Schema.typesOverlapBool
                  exact List.any_eq_true.mpr
                    ⟨runtimeType, List.contains_iff_mem.mp hparentRuntime,
                      hcondition⟩
                have hbody :
                    Validation.selectionSetValid schema
                      variableDefinitions typeCondition selectionSet :=
                  Validation.selectionValid_inlineFragment_some_selectionSetValid
                    himplementation
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hcandidate
                exact
                  collectFields_childLookupValid_of_selectionSetValidInPossibleTypes_object
                    schema variableDefinitions variableValues collectParent
                    typeCondition runtimeType identity selectionSet candidate
                    childRuntime hschema
                    (ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                      schema runtimeType typeCondition hcondition)
                    hbody hcandidate
                    (by
                      intro scopedField hscoped hmatch hruntime
                      exact hcompatible scopedField
                        (by
                          simpa [FieldMerge.collectFields] using hscoped)
                        hmatch hruntime)
              · have hfalse :
                    doesFragmentTypeApplyBool schema collectParent
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema collectParent
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, hallows, hfalse,
                  collectedExecutableFields] at hcandidate
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, hfalse,
                collectedExecutableFields] at hcandidate

  theorem collectFields_childLookupValid_of_selectionSetValidInPossibleTypes_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      (candidate : ExecutableField) (childRuntime : Name)
      : SchemaWellFormedness.schemaWellFormed schema
        -> ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionSetValid schema
            variableDefinitions validParent selectionSet
        -> candidate
            ∈ collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues collectParent
                  (.object runtimeType identity) selectionSet)
        -> (∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
              -> ScopedFieldMatchesExecutableIdentity scopedField candidate
              -> ScopedFieldRuntimeApplies schema runtimeType scopedField
              -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                    childRuntime
                  = true)
        -> NormalForm.selectionSetLookupValid schema childRuntime
            candidate.selectionSet := by
    intro hschema hparentRuntime himplementation hcandidate hcompatible
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hcandidate
    | cons selection rest =>
        have hhead :
            Validation.selectionValid schema variableDefinitions
              validParent selection := by
          unfold Validation.selectionSetValid at himplementation
          exact himplementation selection (by simp)
        have htail :
            Validation.selectionSetValid schema
              variableDefinitions validParent rest := by
          exact Validation.selectionSetValid_tail himplementation
        simp [GraphQL.Execution.collectFields] at hcandidate
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) rest)
              candidate).mp hcandidate with hselection | hrest
        · exact
            collectSelection_childLookupValid_of_selectionValidInPossibleTypes_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity selection candidate childRuntime hschema
              hparentRuntime hhead hselection
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inl hscoped))
                  hmatch hruntime)
        · exact
            collectFields_childLookupValid_of_selectionSetValidInPossibleTypes_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity rest candidate childRuntime hschema
              hparentRuntime htail hrest
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inr hscoped))
                  hmatch hruntime)
end

theorem
    collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetValidInPossibleTypes_object
    {ObjectIdentity : Type} (schema : Schema)
    (variableDefinitions : List VariableDefinition) (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (responseName childRuntime : Name)
    (field : ExecutableField) (fields prefixTail : List ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> (∀ candidate,
            candidate ∈ field :: prefixTail
            -> ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                      childRuntime
                    = true)
      -> NormalForm.selectionSetLookupValid schema childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hschema hparentRuntime hvalid himplementation hgroup hprefix hcompatible
  apply selectionSetLookupValid_mergedFieldSelectionSet
  intro candidate hcandidate
  have hcollected :
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  exact
    collectFields_childLookupValid_of_selectionSetValidInPossibleTypes_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet candidate childRuntime hschema
      hparentRuntime hvalid hcollected
      (hcompatible candidate hcandidate)

mutual
  theorem collectSelection_childImplementation_of_selectionValidInPossibleTypes_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      (candidate : ExecutableField) (childRuntime : Name)
      : Selection.isField selection
        -> ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionValidInPossibleTypes schema variableDefinitions
            validParent selection
        -> candidate
            ∈ collectedExecutableFields
                (GraphQL.Execution.collectSelection schema variableValues
                  collectParent (.object runtimeType identity) selection)
        -> (∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent [selection]
              -> ScopedFieldMatchesExecutableIdentity scopedField candidate
              -> ScopedFieldRuntimeApplies schema runtimeType scopedField
              -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                    childRuntime
                  = true)
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions childRuntime candidate.selectionSet := by
    intro hselectionField hparentRuntime himplementation hcandidate hcompatible
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · have hcandidateEq :
              candidate =
                {
                  parentType := collectParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } := by
            simpa [GraphQL.Execution.collectSelection, hallows,
              collectedExecutableFields] using hcandidate
          subst candidate
          cases hlookup : schema.lookupField validParent fieldName with
          | none =>
              simp [Validation.selectionValidInPossibleTypes, hlookup] at himplementation
          | some fieldDefinition =>
              let scopedField : FieldMerge.ScopedField :=
                { parentType := validParent
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  outputType := fieldDefinition.outputType
                  selectionSet := selectionSet }
              have hscopedMem :
                  scopedField ∈
                    FieldMerge.collectFields schema validParent
                      [Selection.field responseName fieldName arguments
                        directives selectionSet] := by
                simp [scopedField, FieldMerge.collectFields, hlookup]
              have hmatch :
                  ScopedFieldMatchesExecutableIdentity scopedField
                    {
                      parentType := collectParent,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet := selectionSet
                    } := by
                simp [scopedField, ScopedFieldMatchesExecutableIdentity]
              have hinclude :
                  schema.typeIncludesObjectBool
                      scopedField.outputType.namedType childRuntime =
                    true :=
                hcompatible scopedField hscopedMem hmatch
                  (by
                    simpa [scopedField, ScopedFieldRuntimeApplies,
                      ScopedParentRuntimeApplies] using hparentRuntime)
              exact
                NormalForm.GroundTypeNormalization.selectionValidInPossibleTypes_field_child
                  himplementation hlookup
                  (by
                    simpa [scopedField] using
                      (List.contains_iff_mem.mp hinclude))
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch :
                selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, hfalse,
            collectedExecutableFields] at hcandidate
    | inlineFragment typeCondition directives selectionSet =>
        cases hselectionField

  theorem collectFields_childImplementation_of_selectionSetValidInPossibleTypes_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableDefinitions : List VariableDefinition)
      (variableValues : VariableValues)
      (collectParent validParent runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      (candidate : ExecutableField) (childRuntime : Name)
      : NormalForm.selectionsAllFields selectionSet
        -> ScopedParentRuntimeApplies schema runtimeType validParent
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions validParent selectionSet
        -> candidate
            ∈ collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues collectParent
                  (.object runtimeType identity) selectionSet)
        -> (∀ scopedField,
              scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
              -> ScopedFieldMatchesExecutableIdentity scopedField candidate
              -> ScopedFieldRuntimeApplies schema runtimeType scopedField
              -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                    childRuntime
                  = true)
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions childRuntime candidate.selectionSet := by
    intro hall hparentRuntime himplementation hcandidate hcompatible
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hcandidate
    | cons selection rest =>
        have hhead :
            Validation.selectionValidInPossibleTypes schema variableDefinitions
              validParent selection := by
          simpa [Validation.selectionSetValidInPossibleTypes] using
            himplementation.1
        have hheadAll : Selection.isField selection :=
          hall selection (by simp)
        have htailAll : NormalForm.selectionsAllFields rest := by
          intro candidate hcandidate
          exact hall candidate (List.mem_cons_of_mem selection hcandidate)
        have htail :
            Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions validParent rest := by
          simpa [Validation.selectionSetValidInPossibleTypes] using
            himplementation.2
        simp [GraphQL.Execution.collectFields] at hcandidate
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                collectParent (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) rest)
              candidate).mp hcandidate with hselection | hrest
        · exact
            collectSelection_childImplementation_of_selectionValidInPossibleTypes_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity selection candidate childRuntime
              hheadAll hparentRuntime hhead hselection
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inl hscoped))
                  hmatch hruntime)
        · exact
            collectFields_childImplementation_of_selectionSetValidInPossibleTypes_object
              schema variableDefinitions variableValues collectParent validParent
              runtimeType identity rest candidate childRuntime htailAll hparentRuntime
              htail hrest
              (by
                intro scopedField hscoped hmatch hruntime
                exact hcompatible scopedField
                  (by
                    rw [show selection :: rest = [selection] ++ rest by rfl]
                    rw [FieldMerge.collectFields_append]
                    exact List.mem_append.mpr (Or.inr hscoped))
                  hmatch hruntime)
end

theorem collectFields_group_prefix_mergedFieldSelectionSet_validInPossibleTypes
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (childRuntime : Name) (field : ExecutableField)
    (prefixTail : List ExecutableField)
    : (∀ candidate,
        candidate ∈ field :: prefixTail
        -> Validation.selectionSetValidInPossibleTypes schema
            variableDefinitions childRuntime candidate.selectionSet)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hfields
  exact
    selectionSetValidInPossibleTypes_mergedFieldSelectionSet schema
      variableDefinitions childRuntime (field :: prefixTail) hfields

theorem
    collectFields_group_prefix_mergedFieldSelectionSet_validInPossibleTypes_of_selectionSetValidInPossibleTypes_object
    {ObjectIdentity : Type} (schema : Schema)
    (variableDefinitions : List VariableDefinition) (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection) (responseName childRuntime : Name)
    (field : ExecutableField) (fields prefixTail : List ExecutableField)
    : ScopedParentRuntimeApplies schema runtimeType validParent
      -> NormalForm.selectionsAllFields selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> (∀ candidate,
            candidate ∈ field :: prefixTail
            -> ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                      childRuntime
                    = true)
      -> Validation.selectionSetValidInPossibleTypes schema
          variableDefinitions childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hparentRuntime hall himplementation hgroup hprefix hcompatible
  apply collectFields_group_prefix_mergedFieldSelectionSet_validInPossibleTypes
  intro candidate hcandidate
  have hcollected :
      candidate ∈
        collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet) := by
    apply collectedExecutableFields_mem_of_group_mem hgroup
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  exact
    collectFields_childImplementation_of_selectionSetValidInPossibleTypes_object
      schema variableDefinitions variableValues collectParent validParent
      runtimeType identity selectionSet candidate childRuntime hall hparentRuntime
      himplementation hcollected (hcompatible candidate hcandidate)

theorem collectFields_group_fieldParentRuntime
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields : List ExecutableField)
    : (responseName, field :: fields)
        ∈ GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet
      -> schema.typeIncludesObjectBool collectParent runtimeType = true
      -> schema.typeIncludesObjectBool field.parentType runtimeType = true := by
  intro hgroup hparentRuntime
  have hparents :
      CollectedGroupsParent collectParent
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (.object runtimeType identity) selectionSet) :=
    collectFields_parent schema variableValues collectParent
      (.object runtimeType identity) selectionSet
  have hfieldParent : field.parentType = collectParent :=
    hparents responseName (field :: fields) hgroup field (by simp)
  simpa [hfieldParent] using hparentRuntime

theorem fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
    (schema : Schema) (parentType runtimeType : Name)
    (selectionSet : List Selection) (responseName : Name)
    (fields : List ExecutableField)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> (∀ field, field ∈ fields -> field.responseName = responseName)
      -> ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema parentType selectionSet) fields
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hmerge hresponses hscoped objectType
  apply FieldMerge.fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise
  intro first hfirst later hlater
  rcases hscoped first hfirst with
    ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
  rcases hscoped later hlater with
    ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
  rcases hfirstMatch with
    ⟨hfirstResponse, _hfirstField, _hfirstArguments, hfirstSelectionSet⟩
  rcases hlaterMatch with
    ⟨hlaterResponse, _hlaterField, _hlaterArguments, hlaterSelectionSet⟩
  have hscopedResponse :
      firstScoped.responseName = laterScoped.responseName := by
    rw [hfirstResponse, hlaterResponse, hresponses first hfirst,
      hresponses later hlater]
  have hparents :
      firstScoped.parentType = laterScoped.parentType
        ∨ ¬schema.objectType firstScoped.parentType
        ∨ ¬schema.objectType laterScoped.parentType :=
    ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
      firstScoped laterScoped hfirstRuntime hlaterRuntime
  simpa [hfirstSelectionSet, hlaterSelectionSet] using
    FieldMerge.fieldsInSetCanMerge_pair_subfields schema parentType
      selectionSet firstScoped laterScoped hmerge hfirstScopedMem
      hlaterScopedMem hscopedResponse hparents objectType

theorem collectFields_group_prefix_mergedFieldSelectionSet_canMerge_runtimeScoped
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hvalid hmerge hparentRuntime hgroup hprefix objectType
  apply
    fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
      schema validParent runtimeType selectionSet responseName
      (field :: prefixTail) hmerge
  · exact collectFields_group_prefix_responseName schema variableValues
      collectParent runtimeType identity selectionSet responseName field
      fields prefixTail hgroup hprefix
  · intro candidate hcandidate
    have hscopedPrefix :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) :=
      collectFields_group_prefix_runtimeScopedBy_of_selectionSetValid schema
        variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName field fields prefixTail
        hparentRuntime hvalid hgroup hprefix
    exact hscopedPrefix candidate hcandidate

theorem collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hlookupValid hmerge hparentRuntime hgroup hprefix objectType
  apply
    fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
      schema validParent runtimeType selectionSet responseName
      (field :: prefixTail) hmerge
  · exact collectFields_group_prefix_responseName schema variableValues
      collectParent runtimeType identity selectionSet responseName field
      fields prefixTail hgroup hprefix
  · intro candidate hcandidate
    have hscopedPrefix :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) := by
      have hscopedAll :
          ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) selectionSet)) :=
        collectFields_runtimeScopedBy_of_selectionSetLookupValid schema
          variableValues collectParent validParent runtimeType identity
          selectionSet hparentRuntime hlookupValid
      apply
        ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet))
          (field :: prefixTail)
      · intro executable hexecutable
        apply collectedExecutableFields_mem_of_group_mem hgroup
        rcases List.mem_cons.mp hexecutable with hhead | htail
        · subst executable
          simp
        · exact List.mem_cons_of_mem field (hprefix executable htail)
      · exact hscopedAll
    exact hscopedPrefix candidate hcandidate

theorem collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail)) := by
  intro hlookupValid hmerge hparentRuntime hgroup hprefix objectType
  apply
    fieldsInSetCanMerge_mergedFieldSelectionSet_of_runtimeScoped_pairwise
      schema validParent runtimeType selectionSet responseName
      (field :: prefixTail) hmerge
  · intro candidate hcandidate
    apply
      collectFields_responseName schema variableValues collectParent
        (.object runtimeType identity) selectionSet responseName
        (field :: fields) hgroup candidate
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      simp
    · exact List.mem_cons_of_mem field (hprefix candidate htail)
  · intro candidate hcandidate
    have hscopedPrefix :
        ExecutableFieldsRuntimeScopedBy schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (field :: prefixTail) := by
      have hscopedAll :
          ExecutableFieldsRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema validParent selectionSet)
            (collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues
                collectParent (.object runtimeType identity) selectionSet)) :=
        collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
          variableValues collectParent validParent runtimeType identity
          selectionSet hparentRuntime hlookupValid
      apply
        ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
          (FieldMerge.collectFields schema validParent selectionSet)
          (collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet))
          (field :: prefixTail)
      · intro executable hexecutable
        apply collectedExecutableFields_mem_of_group_mem hgroup
        rcases List.mem_cons.mp hexecutable with hhead | htail
        · subst executable
          simp
        · exact List.mem_cons_of_mem field (hprefix executable htail)
      · exact hscopedAll
    exact hscopedPrefix candidate hcandidate

theorem collectFields_group_prefix_outputCompatible_of_concreteParent
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> collectParent = validParent
      -> schema.objectType validParent
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> ∀ childRuntime,
          schema.typeIncludesObjectBool
              ((schema.fieldReturnType? field.parentType field.fieldName).getD
                field.fieldName)
              childRuntime
            = true
          -> ∀ candidate,
              candidate ∈ field :: prefixTail
              -> ∀ scopedField,
                  scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                  -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                  -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                  -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                        childRuntime
                      = true := by
  intro hschema hparentEq hvalidObject hparentRuntime hlookup hmerge hgroup
    hprefix childRuntime hinclude candidate hcandidate scopedField hscoped
    hmatch hruntime
  subst collectParent
  have hruntimeEq : runtimeType = validParent :=
    object_typeIncludesObjectBool_eq_self schema hvalidObject hparentRuntime
  have hfieldParent : field.parentType = validParent := by
    have hparents :
        CollectedGroupsParent validParent
          (GraphQL.Execution.collectFields schema variableValues validParent
            (.object runtimeType identity) selectionSet) :=
      collectFields_parent schema variableValues validParent
        (.object runtimeType identity) selectionSet
    exact hparents responseName (field :: fields) hgroup field (by simp)
  have hscopedAll :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues validParent
            (.object runtimeType identity) selectionSet)) :=
    collectFields_runtimeScopedBy_of_selectionSetLookupValid_object schema
      variableValues validParent validParent runtimeType identity selectionSet
      hparentRuntime hlookup
  have hscopedPrefix :
      ExecutableFieldsRuntimeScopedBy schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (field :: prefixTail) := by
    apply
      ExecutableFieldsRuntimeScopedBy.mono schema runtimeType
        (FieldMerge.collectFields schema validParent selectionSet)
        (collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues validParent
            (.object runtimeType identity) selectionSet))
        (field :: prefixTail)
    · intro executable hexecutable
      apply collectedExecutableFields_mem_of_group_mem hgroup
      rcases List.mem_cons.mp hexecutable with hhead | htail
      · subst executable
        simp
      · exact List.mem_cons_of_mem field (hprefix executable htail)
    · exact hscopedAll
  rcases hscopedPrefix field (by simp) with
    ⟨headScoped, hheadScopedMem, hheadMatch, hheadRuntime⟩
  rcases hheadMatch with
    ⟨_hheadResponse, hheadField, _hheadArguments, _hheadSelection⟩
  rcases
      GraphQL.NormalForm.fieldMerge_collectFields_mem_lookupField_outputType
        schema validParent selectionSet headScoped hheadScopedMem with
    ⟨headExpectedDefinition, hheadExpectedLookup, _hheadOutput⟩
  have hheadPossible :
      validParent ∈ schema.getPossibleTypes headScoped.parentType := by
    have hheadRuntime' :
        schema.typeIncludesObjectBool headScoped.parentType validParent =
          true := by
      simpa [ScopedFieldRuntimeApplies, hruntimeEq] using hheadRuntime
    exact List.contains_iff_mem.mp hheadRuntime'
  rcases
      SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_exists
        hschema hheadPossible hheadExpectedLookup with
    ⟨headImplementationDefinition, hheadImplementationLookup⟩
  have hheadImplementationLookupField :
      schema.lookupField validParent field.fieldName =
        some headImplementationDefinition := by
    simpa [hheadField] using hheadImplementationLookup
  have hheadInclude :
      schema.typeIncludesObjectBool
        headImplementationDefinition.outputType.namedType childRuntime =
        true := by
    have hlookupAtFieldParent :
        schema.lookupField field.parentType field.fieldName =
          some headImplementationDefinition := by
      simpa [hfieldParent] using hheadImplementationLookupField
    simpa [Schema.fieldReturnType?, hlookupAtFieldParent] using hinclude
  have hresponseNames :
      ∀ candidate, candidate ∈ field :: prefixTail ->
        candidate.responseName = responseName := by
    intro executable hexecutable
    apply
      collectFields_responseName schema variableValues validParent
        (.object runtimeType identity) selectionSet responseName
        (field :: fields) hgroup executable
    rcases List.mem_cons.mp hexecutable with hhead | htail
    · subst executable
      simp
    · exact List.mem_cons_of_mem field (hprefix executable htail)
  have hexecutableCompatible :
      ExecutableFieldsFieldValidationMergeCompatible (field :: prefixTail) := by
    intro first later hfirst hlater hresponse
    rcases hscopedPrefix first hfirst with
      ⟨firstScoped, hfirstScopedMem, hfirstMatch, hfirstRuntime⟩
    rcases hscopedPrefix later hlater with
      ⟨laterScoped, hlaterScopedMem, hlaterMatch, hlaterRuntime⟩
    rcases hfirstMatch with
      ⟨hfirstResponse, hfirstField, hfirstArguments, _hfirstSelection⟩
    rcases hlaterMatch with
      ⟨hlaterResponse, hlaterField, hlaterArguments, _hlaterSelection⟩
    have hscopedResponse :
        firstScoped.responseName = laterScoped.responseName := by
      rw [hfirstResponse, hlaterResponse]
      exact hresponse
    have hfieldMerge :
        FieldMerge.fieldsForNameCanMerge schema firstScoped laterScoped :=
      FieldMerge.fieldsInSetCanMerge_pair hmerge hfirstScopedMem
        hlaterScopedMem hscopedResponse
    rcases
        FieldMerge.fieldsForNameCanMerge_identity hfieldMerge
          (ScopedFieldRuntimeApplies.mergeIdentityCondition schema runtimeType
            firstScoped laterScoped hfirstRuntime hlaterRuntime) with
      ⟨hfield, hargumentsEquivalent⟩
    constructor
    · rw [← hfirstField, ← hlaterField]
      exact hfield
    · rw [← hfirstArguments, ← hlaterArguments]
      exact hargumentsEquivalent
  have hfieldEq : field.fieldName = candidate.fieldName := by
    exact (hexecutableCompatible field candidate (by simp) hcandidate
            (by
              rw [hresponseNames field (by simp),
                hresponseNames candidate hcandidate])).1
  rcases hmatch with
    ⟨_hscopedResponse, hscopedFieldName, _hscopedArguments,
      _hscopedSelection⟩
  have hscopedFieldEq : scopedField.fieldName = field.fieldName :=
    hscopedFieldName.trans hfieldEq.symm
  rcases
      GraphQL.NormalForm.fieldMerge_collectFields_mem_lookupField_outputType
        schema validParent selectionSet scopedField hscoped with
    ⟨scopedDefinition, hscopedLookup, hscopedOutput⟩
  have hscopedPossible :
      validParent ∈ schema.getPossibleTypes scopedField.parentType := by
    have hruntime' :
        schema.typeIncludesObjectBool scopedField.parentType validParent =
          true := by
      simpa [ScopedFieldRuntimeApplies, hruntimeEq] using hruntime
    exact List.contains_iff_mem.mp hruntime'
  have himplementationLookupForScoped :
      schema.lookupField validParent scopedField.fieldName =
        some headImplementationDefinition := by
    simpa [hscopedFieldEq] using hheadImplementationLookupField
  have hsubtype :
      schema.outputTypeSubtype headImplementationDefinition.outputType
        scopedDefinition.outputType :=
    SchemaWellFormedness.schemaWellFormed_possibleObject_lookupField_outputTypeSubtype
      hschema hscopedPossible hscopedLookup himplementationLookupForScoped
  have hscopedDefinitionInclude :
      schema.typeIncludesObjectBool scopedDefinition.outputType.namedType
        childRuntime = true :=
    typeIncludesObjectBool_of_outputTypeSubtype_namedType schema hsubtype
      hheadInclude
  simpa [hscopedOutput] using hscopedDefinitionInclude

theorem collectFields_group_prefix_mergedFieldSelectionSet_childLocalFacts_object
    {ObjectIdentity : Type}
    (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectIdentity)
    (selectionSet : List Selection)
    (responseName childRuntime : Name) (field : ExecutableField)
    (fields prefixTail : List ExecutableField)
    : SchemaWellFormedness.schemaWellFormed schema
      -> ScopedParentRuntimeApplies schema runtimeType validParent
      -> Validation.selectionSetValid schema variableDefinitions validParent selectionSet
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> Validation.selectionSetValidInPossibleTypes schema variableDefinitions
          validParent selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> NormalForm.selectionsAllFields selectionSet
      -> (responseName, field :: fields)
          ∈ GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet
      -> (∀ candidate, candidate ∈ prefixTail -> candidate ∈ fields)
      -> (∀ candidate,
            candidate ∈ field :: prefixTail
            -> ∀ scopedField,
                scopedField ∈ FieldMerge.collectFields schema validParent selectionSet
                -> ScopedFieldMatchesExecutableIdentity scopedField candidate
                -> ScopedFieldRuntimeApplies schema runtimeType scopedField
                -> schema.typeIncludesObjectBool scopedField.outputType.namedType
                      childRuntime
                    = true)
      -> NormalForm.selectionSetLookupValid schema childRuntime
            (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
          ∧ Validation.selectionSetValidInPossibleTypes schema
              variableDefinitions childRuntime
              (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))
          ∧ (∀ objectType,
              FieldMerge.fieldsInSetCanMerge schema objectType
                (GraphQL.Execution.mergedFieldSelectionSet (field :: prefixTail))) := by
  intro hschema hparentRuntime hvalid hlookupValid himplementation hmerge hall
    hgroup hprefix hcompatible
  constructor
  · exact
      collectFields_group_prefix_mergedFieldSelectionSet_lookupValid_of_selectionSetValid_object
        schema variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName childRuntime field fields
        prefixTail hschema hparentRuntime hvalid hgroup hprefix hcompatible
  constructor
  · exact
      collectFields_group_prefix_mergedFieldSelectionSet_validInPossibleTypes_of_selectionSetValidInPossibleTypes_object
        schema variableDefinitions variableValues collectParent validParent
        runtimeType identity selectionSet responseName childRuntime field fields
        prefixTail hparentRuntime hall himplementation hgroup hprefix
        hcompatible
  · exact
      collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
        schema variableValues collectParent validParent runtimeType identity
        selectionSet responseName field fields prefixTail hlookupValid hmerge
        hparentRuntime hgroup hprefix

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
