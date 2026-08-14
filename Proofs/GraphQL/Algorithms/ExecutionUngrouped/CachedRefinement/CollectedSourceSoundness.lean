import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.SourceSoundness

/-!
Collected-field source soundness for cached ungrouped execution.

Validated field collection supplies the field universe used to preserve
resolver-source soundness across syntax-order visits.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

theorem collectedExecutableFields_argumentsNodup
    {groups : List (Name × List ExecutableField)}
    (hnodup : ExecutionUngroupedUncached.Eager.CollectedGroupsArgumentsNodup groups)
    : ExecutionUngroupedUncached.Eager.ExecutableFieldsArgumentsNodup
        (ExecutionUngroupedUncached.Eager.collectedExecutableFields groups) := by
  intro field hfield
  induction groups with
  | nil => simp [ExecutionUngroupedUncached.Eager.collectedExecutableFields] at hfield
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp only [ExecutionUngroupedUncached.Eager.collectedExecutableFields,
        List.mem_append] at hfield
      rcases hfield with hfield | hfield
      · exact hnodup responseName fields (by simp) field hfield
      · apply ih
        · intro restResponseName restFields hrest
          exact hnodup restResponseName restFields (by simp [hrest])
        · exact hfield

theorem OutputCacheSoundForFields.merge_depthZero {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef) (fields : List ExecutableField)
    (output : FieldCacheValue ObjectRef) (responseName : Name)
    : OutputCacheSoundForFields schema resolvers variableValues source fields output
      -> FieldCacheMergeReady output
      -> OutputCacheSoundForFields schema resolvers variableValues source fields
          (GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject
            responseName
            (match objectField? responseName output with
              | some previous => previous
              | none => .null)
            output) := by
  intro hsound hready
  apply OutputCacheSoundForFields.mergeResponseFieldIntoObject
  · exact hsound
  · intro field fieldDefinition hfield hresponse hlookup
    cases hprevious : objectField? responseName output with
    | none =>
        exact
          PreviousCacheSound.null schema resolvers source fieldDefinition field
    | some previous =>
        simpa [hprevious] using
          hsound field fieldDefinition previous hfield
            (by simpa [hresponse] using hprevious) hlookup

mutual
  def SelectionFieldsWithin {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (fields : List ExecutableField)
      : Selection -> Prop
    | .field responseName fieldName arguments directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> executableField parentType responseName fieldName arguments selectionSet
            ∈ fields
    | .inlineFragment none directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> SelectionSetFieldsWithin schema variableValues parentType source fields
            selectionSet
    | .inlineFragment (some typeCondition) directives selectionSet =>
        selectionDirectivesAllowBool variableValues directives = true
        -> doesFragmentTypeApplyBool schema parentType source typeCondition = true
        -> SelectionSetFieldsWithin schema variableValues parentType source fields
            selectionSet

  def SelectionSetFieldsWithin {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (fields : List ExecutableField) (selectionSet : List Selection)
      : Prop :=
    ∀ selection,
      selection ∈ selectionSet
      -> SelectionFieldsWithin schema variableValues parentType source fields selection
end

mutual
  theorem visitSelection_outputCacheSoundForFields {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (fields : List ExecutableField)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (hparents
        : ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields)
      (hcompatible
        : ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
            fields)
      (hargumentsNodup
        : ExecutionUngroupedUncached.Eager.ExecutableFieldsArgumentsNodup fields)
      (hlookup
        : ∀ field,
            field ∈ fields
            -> ∃ fieldDefinition,
                schema.lookupField field.parentType field.fieldName
                = some fieldDefinition)
      : ∀ selection output,
          SelectionFieldsWithin schema variableValues parentType source fields selection
          -> FieldCacheMergeReady output
          -> ObjectFieldCachesInternallyAligned output
          -> OutputCacheSoundForFields schema resolvers variableValues source fields
              output
          -> OutputCacheSoundForFields schema resolvers variableValues source fields
              (visitSelection schema resolvers variableValues fuel parentType source
                selection output).value := by
    intro selection output hwithin hready haligned hsound
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · let field :=
            executableField parentType responseName fieldName arguments selectionSet
          have hfield : field ∈ fields := by
            have hwithin' := hwithin
            simp [SelectionFieldsWithin] at hwithin'
            exact hwithin' hallows
          cases fuel with
          | zero =>
              have hvalue :
                  resultValueOrNull
                      (match objectField? responseName output with
                        | some previous => .ok (previous, 0)
                        | none => outOfFuel)
                    =
                    match objectField? responseName output with
                    | some previous => previous
                    | none => .null := by
                cases objectField? responseName output <;>
                  simp [outOfFuel, resultValueOrNull]
              simp only [visitSelection, hallows, if_true,
                mergeResponseFieldResult]
              exact
                Eq.mpr
                  (congrArg
                    (fun incoming =>
                      OutputCacheSoundForFields schema resolvers variableValues source fields
                        (GraphQL.Algorithms.ExecutionUngrouped.mergeResponseFieldIntoObject
                          responseName incoming output))
                    hvalue)
                  (OutputCacheSoundForFields.merge_depthZero schema resolvers
                    variableValues source fields output responseName hsound hready)
          | succ completionFuel =>
              rcases hlookup field hfield with ⟨fieldDefinition, hfieldLookup⟩
              simp only [visitSelection, hallows, if_true,
                mergeResponseFieldResult]
              exact
                OutputCacheSoundForFields.merge_executeField schema resolvers
                  variableValues completionFuel parentType source fields output field
                  fieldDefinition hschema hparents hcompatible hargumentsNodup hsound
                  hready haligned hfield hfieldLookup
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simpa [visitSelection, hfalse] using hsound
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases typeCondition with
          | none =>
              have hwithin' := hwithin
              simp [SelectionFieldsWithin] at hwithin'
              simpa [visitSelection, hallows] using
                visitSubfields_outputCacheSoundForFields schema resolvers
                  variableValues fuel parentType source fields hschema hparents
                  hcompatible hargumentsNodup hlookup selectionSet output
                  (hwithin' hallows) hready haligned hsound
          | some typeCondition =>
              have hwithin' := hwithin
              simp [SelectionFieldsWithin] at hwithin'
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition =
                    true
              · simpa [visitSelection, hallows, happly] using
                  visitSubfields_outputCacheSoundForFields schema resolvers
                    variableValues fuel parentType source fields hschema hparents
                    hcompatible hargumentsNodup hlookup selectionSet output
                    (hwithin' hallows happly) hready haligned hsound
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source typeCondition =
                      false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source typeCondition
                  · rfl
                  · contradiction
                simpa [visitSelection, hallows, hfalse] using hsound
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          cases typeCondition <;> simpa [visitSelection, hfalse] using hsound
  termination_by selection output _hwithin _hready _haligned _hsound =>
    (sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem visitSubfields_outputCacheSoundForFields {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues) (fuel : Nat)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (fields : List ExecutableField)
      (hschema : SchemaWellFormedness.schemaWellFormed schema)
      (hparents
        : ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType fields)
      (hcompatible
        : ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
            fields)
      (hargumentsNodup
        : ExecutionUngroupedUncached.Eager.ExecutableFieldsArgumentsNodup fields)
      (hlookup
        : ∀ field,
            field ∈ fields
            -> ∃ fieldDefinition,
                schema.lookupField field.parentType field.fieldName
                = some fieldDefinition)
      : ∀ selectionSet output,
          SelectionSetFieldsWithin schema variableValues parentType source fields
            selectionSet
          -> FieldCacheMergeReady output
          -> ObjectFieldCachesInternallyAligned output
          -> OutputCacheSoundForFields schema resolvers variableValues source fields
              output
          -> OutputCacheSoundForFields schema resolvers variableValues source fields
              (visitSubfields schema resolvers variableValues fuel parentType source
                selectionSet output).value := by
    intro selectionSet output hwithin hready haligned hsound
    cases selectionSet with
    | nil => simpa [visitSubfields] using hsound
    | cons selection rest =>
        unfold SelectionSetFieldsWithin at hwithin
        let head :=
          visitSelection schema resolvers variableValues fuel parentType source
            selection output
        have hselectionWithin :
            SelectionFieldsWithin schema variableValues parentType source fields
              selection :=
          hwithin selection (by simp)
        have hrestWithin :
            SelectionSetFieldsWithin schema variableValues parentType source fields
              rest := by
          unfold SelectionSetFieldsWithin
          intro restSelection hrest
          exact hwithin restSelection (by simp [hrest])
        have hheadReady : FieldCacheMergeReady head.value :=
          visitSelection_cacheReady schema resolvers variableValues fuel parentType
            source selection output hready
        have hheadAligned : ObjectFieldCachesInternallyAligned head.value :=
          visitSelection_objectFieldCachesInternallyAligned schema resolvers
            variableValues fuel parentType source selection output hready haligned
        have hheadSound :
            OutputCacheSoundForFields schema resolvers variableValues source fields head.value :=
          visitSelection_outputCacheSoundForFields schema resolvers variableValues
            fuel parentType source fields hschema hparents hcompatible hargumentsNodup
            hlookup selection output hselectionWithin hready haligned hsound
        cases hstatus : head.status with
        | error errors =>
            simpa [visitSubfields, head, hstatus] using hheadSound
        | ok ok =>
            have htailSound :=
              visitSubfields_outputCacheSoundForFields schema resolvers
                variableValues fuel parentType source fields hschema hparents hcompatible
                hargumentsNodup hlookup rest head.value hrestWithin
                hheadReady hheadAligned hheadSound
            simpa [visitSubfields, head, hstatus] using htailSound
  termination_by selectionSet output _hwithin _hready _haligned _hsound =>
    (sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

mutual
  theorem SelectionFieldsWithin.mono {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (sourceFields targetFields : List ExecutableField)
      (hsubset : ∀ field, field ∈ sourceFields -> field ∈ targetFields)
      : ∀ selection,
          SelectionFieldsWithin schema variableValues parentType source sourceFields
            selection
          -> SelectionFieldsWithin schema variableValues parentType source targetFields
              selection := by
    intro selection hwithin
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        simp [SelectionFieldsWithin] at hwithin ⊢
        intro hallows
        exact hsubset _ (hwithin hallows)
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            simp [SelectionFieldsWithin] at hwithin ⊢
            intro hallows
            exact
              SelectionSetFieldsWithin.mono schema variableValues parentType source
                sourceFields targetFields hsubset selectionSet (hwithin hallows)
        | some typeCondition =>
            simp [SelectionFieldsWithin] at hwithin ⊢
            intro hallows happly
            exact
              SelectionSetFieldsWithin.mono schema variableValues parentType source
                sourceFields targetFields hsubset selectionSet
                (hwithin hallows happly)
  termination_by selection _hwithin => (sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      apply Prod.Lex.left
      omega

  theorem SelectionSetFieldsWithin.mono {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      (sourceFields targetFields : List ExecutableField)
      (hsubset : ∀ field, field ∈ sourceFields -> field ∈ targetFields)
      : ∀ selectionSet,
          SelectionSetFieldsWithin schema variableValues parentType source sourceFields
            selectionSet
          -> SelectionSetFieldsWithin schema variableValues parentType source targetFields
              selectionSet := by
    intro selectionSet hwithin
    unfold SelectionSetFieldsWithin at hwithin ⊢
    intro selection hselection
    have hsize := List.sizeOf_lt_of_mem hselection
    exact
      SelectionFieldsWithin.mono schema variableValues parentType source
        sourceFields targetFields hsubset selection
        (hwithin selection hselection)
  termination_by selectionSet _hwithin => (sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      apply Prod.Lex.left
      simp_all
end

mutual
  theorem selectionFieldsWithin_collectSelection {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selection,
          SelectionFieldsWithin schema variableValues parentType source
            (ExecutionUngroupedUncached.Eager.collectedExecutableFields
              (GraphQL.Execution.collectSelection schema variableValues parentType
                source selection))
            selection := by
    intro selection
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [SelectionFieldsWithin, GraphQL.Execution.collectSelection,
            hallows, ExecutionUngroupedUncached.Eager.collectedExecutableFields]
          simp [executableField]
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [SelectionFieldsWithin, hfalse]
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases typeCondition with
          | none =>
              simp [SelectionFieldsWithin, GraphQL.Execution.collectSelection,
                hallows]
              exact
                selectionSetFieldsWithin_collectFields schema variableValues
                  parentType source selectionSet
          | some typeCondition =>
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition =
                    true
              · simp [SelectionFieldsWithin, GraphQL.Execution.collectSelection,
                  hallows, happly]
                exact
                  selectionSetFieldsWithin_collectFields schema variableValues
                    parentType source selectionSet
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType source typeCondition =
                      false := by
                  cases h :
                      doesFragmentTypeApplyBool schema parentType source typeCondition
                  · rfl
                  · contradiction
                simp [SelectionFieldsWithin, GraphQL.Execution.collectSelection,
                  hallows, hfalse]
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          cases typeCondition <;>
            simp [SelectionFieldsWithin, GraphQL.Execution.collectSelection,
              hfalse]
  termination_by selection => (sizeOf selection, 0)
  decreasing_by
    all_goals
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem selectionSetFieldsWithin_collectFields {ObjectRef : Type}
      (schema : Schema) (variableValues : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef)
      : ∀ selectionSet,
          SelectionSetFieldsWithin schema variableValues parentType source
            (ExecutionUngroupedUncached.Eager.collectedExecutableFields
              (GraphQL.Execution.collectFields schema variableValues parentType
                source selectionSet))
            selectionSet := by
    intro selectionSet
    cases selectionSet with
    | nil =>
        unfold SelectionSetFieldsWithin
        intro selection hmem
        simp at hmem
    | cons selection rest =>
        unfold SelectionSetFieldsWithin
        intro candidate hcandidate
        simp at hcandidate
        rcases hcandidate with hhead | hrest
        · subst candidate
          apply
            SelectionFieldsWithin.mono schema variableValues parentType source
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectSelection schema variableValues
                  parentType source selection))
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source (selection :: rest)))
          · intro field hfield
            exact (ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_mergeExecutableGroups
                    (GraphQL.Execution.collectSelection schema variableValues
                      parentType source selection)
                    (GraphQL.Execution.collectFields schema variableValues parentType
                      source rest)
                    field).mpr
                    (Or.inl hfield)
          · exact
              selectionFieldsWithin_collectSelection schema variableValues
                parentType source selection
        · apply
            SelectionFieldsWithin.mono schema variableValues parentType source
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source rest))
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  source (selection :: rest)))
          · intro field hfield
            exact (ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_mergeExecutableGroups
                    (GraphQL.Execution.collectSelection schema variableValues
                      parentType source selection)
                    (GraphQL.Execution.collectFields schema variableValues parentType
                      source rest)
                    field).mpr
                    (Or.inr hfield)
          · have hwithin :=
              selectionSetFieldsWithin_collectFields schema variableValues
                parentType source rest
            have hwithin' := hwithin
            unfold SelectionSetFieldsWithin at hwithin'
            exact hwithin' candidate hrest
  termination_by selectionSet => (sizeOf selectionSet, 1)
  decreasing_by
    all_goals
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega
end

theorem collectedExecutableFields_parent (parentType : Name)
    : ∀ groups : List (Name × List ExecutableField),
        ExecutionUngroupedUncached.Eager.CollectedGroupsParent parentType groups
        -> ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType
            (ExecutionUngroupedUncached.Eager.collectedExecutableFields groups)
  | [], _hparents => by
      intro field hfield
      simp [ExecutionUngroupedUncached.Eager.collectedExecutableFields] at hfield
  | (responseName, fields) :: rest, hparents => by
      intro field hfield
      simp [ExecutionUngroupedUncached.Eager.collectedExecutableFields] at hfield
      rcases hfield with hfield | hfield
      · exact hparents responseName fields (by simp) field hfield
      · exact
          collectedExecutableFields_parent parentType rest
            (ExecutionUngroupedUncached.Eager.CollectedGroupsParent_tail hparents)
            field hfield

theorem collectFields_flat_parent {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType
        (ExecutionUngroupedUncached.Eager.collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues parentType source
            selectionSet)) :=
  collectedExecutableFields_parent parentType
    (GraphQL.Execution.collectFields schema variableValues parentType source selectionSet)
    (ExecutionUngroupedUncached.Eager.collectFields_parent schema variableValues
      parentType source selectionSet)

theorem collectFields_flat_fieldCompatible_of_canMerge_lookupValid_object
    {ObjectRef : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectRef)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType validParent
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          (ExecutionUngroupedUncached.Eager.collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues collectParent
              (.object runtimeType identity) selectionSet)) := by
  intro hmerge hparentRuntime hlookupValid
  exact
    ExecutionUngroupedUncached.Eager.fieldsInSetCanMerge_executable_runtimeScoped
      schema validParent runtimeType selectionSet
      (ExecutionUngroupedUncached.Eager.collectedExecutableFields
        (GraphQL.Execution.collectFields schema variableValues collectParent
          (ResolverValue.object runtimeType identity) selectionSet))
      hmerge
      (ExecutionUngroupedUncached.Eager.collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
        schema variableValues collectParent validParent runtimeType identity
        selectionSet hparentRuntime hlookupValid)

theorem collectFields_flat_pair_selectionSets_canMerge_of_canMerge_lookupValid_object
    {ObjectRef : Type}
    (schema : Schema)
    (variableValues : VariableValues)
    (collectParent validParent runtimeType : Name)
    (identity : ObjectRef)
    (selectionSet : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema validParent selectionSet
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType validParent
      -> NormalForm.selectionSetLookupValid schema validParent selectionSet
      -> ∀ first,
          first
            ∈ ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues collectParent
                  (.object runtimeType identity) selectionSet)
          -> ∀ later,
              later
                ∈ ExecutionUngroupedUncached.Eager.collectedExecutableFields
                    (GraphQL.Execution.collectFields schema variableValues collectParent
                      (.object runtimeType identity) selectionSet)
              -> first.responseName = later.responseName
              -> ∀ objectType,
                  FieldMerge.fieldsInSetCanMerge schema objectType
                    (first.selectionSet ++ later.selectionSet) := by
  intro hmerge hparentRuntime hlookupValid first hfirst later hlater
    hresponse objectType
  have hscoped :
      ExecutionUngroupedUncached.Eager.ExecutableFieldsRuntimeScopedBy schema
        runtimeType (FieldMerge.collectFields schema validParent selectionSet)
        (ExecutionUngroupedUncached.Eager.collectedExecutableFields
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) selectionSet)) :=
    ExecutionUngroupedUncached.Eager.collectFields_runtimeScopedBy_of_selectionSetLookupValid_object
      schema variableValues collectParent validParent runtimeType identity
      selectionSet hparentRuntime hlookupValid
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
    rw [hfirstResponse, hlaterResponse]
    exact hresponse
  have hparents :
      firstScoped.parentType = laterScoped.parentType
        ∨ ¬schema.objectType firstScoped.parentType
        ∨ ¬schema.objectType laterScoped.parentType :=
    ExecutionUngroupedUncached.Eager.ScopedFieldRuntimeApplies.mergeIdentityCondition
      schema runtimeType firstScoped laterScoped hfirstRuntime hlaterRuntime
  simpa [hfirstSelectionSet, hlaterSelectionSet] using
    FieldMerge.fieldsInSetCanMerge_pair_subfields schema validParent selectionSet
      firstScoped laterScoped hmerge hfirstScopedMem hlaterScopedMem
      hscopedResponse hparents objectType

theorem collectFields_flat_lookupValid_of_selectionSetSemanticsReady_object
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (identity : ObjectRef)
    (selectionSet : List Selection)
    : schema.objectType parentType
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType parentType
      -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
      -> ∀ field,
          field
            ∈ ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  (.object runtimeType identity) selectionSet)
          -> ∃ fieldDefinition,
              schema.lookupField field.parentType field.fieldName
              = some fieldDefinition := by
  intro hobject hparentRuntime hready
  intro field hfield
  have hlookup :=
    ExecutionUngroupedUncached.Eager.collectFields_lookupValid_of_selectionSetSemanticsReady_object
      schema variableValues parentType runtimeType identity selectionSet hobject
      hparentRuntime hready field hfield
  have hparent :=
    collectFields_flat_parent schema variableValues parentType
      (.object runtimeType identity) selectionSet field hfield
  simpa [hparent] using hlookup

theorem collectFields_flat_childSemanticsReady_of_selectionSetSemanticsReady_object
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (identity : ObjectRef)
    (selectionSet : List Selection)
    : schema.objectType parentType
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType parentType
      -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
      -> ∀ field,
          field
            ∈ ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  (.object runtimeType identity) selectionSet)
          -> ∀ fieldDefinition,
              schema.lookupField field.parentType field.fieldName = some fieldDefinition
              -> ∀ childRuntime,
                  schema.typeIncludesObjectBool
                      fieldDefinition.outputType.namedType childRuntime
                    = true
                  -> NormalForm.selectionSetSemanticsReady schema childRuntime
                      field.selectionSet := by
  intro hobject hparentRuntime hready
  exact
    ExecutionUngroupedUncached.Eager.collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
      schema variableValues parentType runtimeType identity selectionSet hobject
      hparentRuntime hready

theorem visitSubfields_outputCacheSoundForCollectedFields_object
    {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (parentType runtimeType : Name) (identity : ObjectRef)
    (selectionSet : List Selection)
    : SchemaWellFormedness.schemaWellFormed schema
      -> schema.objectType parentType
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType parentType
      -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> Execution.selectionSetArgumentsNodup selectionSet
      -> OutputCacheSoundForFields schema resolvers variableValues
          (.object runtimeType identity)
          (ExecutionUngroupedUncached.Eager.collectedExecutableFields
            (GraphQL.Execution.collectFields schema variableValues parentType
              (.object runtimeType identity) selectionSet))
          (visitSubfields schema resolvers variableValues fuel parentType
            (.object runtimeType identity) selectionSet
            (.object (.object runtimeType identity) [])).value := by
  intro hschema hobject hparentRuntime hready hmerge hargumentsNodup
  let source : ResolverValue ObjectRef := .object runtimeType identity
  let fields :=
    ExecutionUngroupedUncached.Eager.collectedExecutableFields
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
  have hlookupValid :
      NormalForm.selectionSetLookupValid schema parentType selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
      hready
  apply
    visitSubfields_outputCacheSoundForFields schema resolvers variableValues fuel
      parentType source fields hschema
      (collectFields_flat_parent schema variableValues parentType source selectionSet)
      (collectFields_flat_fieldCompatible_of_canMerge_lookupValid_object schema
        variableValues parentType parentType runtimeType identity selectionSet
        hmerge hparentRuntime hlookupValid)
      (collectedExecutableFields_argumentsNodup
        (ExecutionUngroupedUncached.Eager.collectFields_argumentsAndChildrenNodup
          schema variableValues parentType source selectionSet hargumentsNodup).1)
      (collectFields_flat_lookupValid_of_selectionSetSemanticsReady_object schema
        variableValues parentType runtimeType identity selectionSet hobject
        hparentRuntime hready)
      selectionSet (.object source [])
  · exact
      selectionSetFieldsWithin_collectFields schema variableValues parentType source
        selectionSet
  · exact
      FieldCacheMergeReady.object source [] (by
        unfold FieldCacheKeysNodup
        simp) (by
        intro responseName response hresponse
        simp at hresponse)
  · intro responseName previous hprevious
    simp [objectField?, lookupField?] at hprevious
  · exact OutputCacheSoundForFields.empty_object schema resolvers variableValues
      source source fields

end ExecutionUngrouped
end Algorithms

end GraphQL
