import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.TreeSoundness.Completion

/-!
Traversal erasure for recursively sound cache trees.

This layer lifts completion soundness through selection visits and establishes
the global cached-to-uncached execution bridge.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

mutual
  theorem visitSelection_output_eq_uncached_and_treeSound_object
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel parentType runtimeType (ref : ObjectRef) universeSet selection
          outputFields,
          SchemaWellFormedness.schemaWellFormed schema
          -> schema.objectType parentType
          -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
              runtimeType parentType
          -> NormalForm.selectionSetSemanticsReady schema parentType universeSet
          -> FieldMerge.fieldsInSetCanMerge schema parentType universeSet
          -> SelectionFieldsWithin schema variableValues parentType
              (.object runtimeType ref)
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  (.object runtimeType ref) universeSet))
              selection
          -> OutputCacheTreeSoundForGroups schema resolvers variableValues fuel
              (.object runtimeType ref)
              (GraphQL.Execution.collectFields schema variableValues parentType
                (.object runtimeType ref) universeSet)
              (.object (.object runtimeType ref) outputFields)
          -> outputVisitResult
                  (visitSelection schema resolvers variableValues fuel parentType
                    (.object runtimeType ref) selection
                    (.object (.object runtimeType ref) outputFields))
                = ExecutionUngroupedUncached.visitSelection schema resolvers
                    variableValues fuel parentType (.object runtimeType ref)
                    selection
                    (.object (ExecutionUngrouped.outputFields outputFields))
              ∧ OutputCacheTreeSoundForGroups schema resolvers variableValues fuel
                  (.object runtimeType ref)
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    (.object runtimeType ref) universeSet)
                  (visitSelection schema resolvers variableValues fuel parentType
                    (.object runtimeType ref) selection
                    (.object (.object runtimeType ref) outputFields)).value := by
    intro fuel parentType runtimeType ref universeSet selection outputFields hschema
      hobject hparentRuntime hready hmerge hwithin htree
    let source : ResolverValue ObjectRef := .object runtimeType ref
    let groups :=
      GraphQL.Execution.collectFields schema variableValues parentType source
        universeSet
    let flatFields :=
      ExecutionUngroupedUncached.Eager.collectedExecutableFields groups
    have hresponses :
        ExecutionUngroupedUncached.Eager.CollectedGroupsResponseName groups := by
      exact
        ExecutionUngroupedUncached.Eager.collectFields_responseName schema
          variableValues parentType source universeSet
    have hgroupsNodup :
        ExecutionUngroupedUncached.Eager.PairKeysNodup groups := by
      exact
        ExecutionUngroupedUncached.Eager.collectFields_pairKeysNodup schema
          variableValues parentType source universeSet
    have hparents :
        ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType
          flatFields :=
      collectFields_flat_parent schema variableValues parentType source universeSet
    have hlookupValid :
        NormalForm.selectionSetLookupValid schema parentType universeSet :=
      NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady universeSet
        hready
    have hcompatible :
        ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
          flatFields :=
      collectFields_flat_fieldCompatible_of_canMerge_lookupValid_object schema
        variableValues parentType parentType runtimeType ref universeSet hmerge
        hparentRuntime hlookupValid
    have hlookups :
        ∀ field,
          field ∈ flatFields
          -> ∃ fieldDefinition,
              schema.lookupField field.parentType field.fieldName
                = some fieldDefinition :=
      collectFields_flat_lookupValid_of_selectionSetSemanticsReady_object schema
        variableValues parentType runtimeType ref universeSet hobject
        hparentRuntime hready
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · let field :=
            executableField parentType responseName fieldName arguments selectionSet
          have hfield : field ∈ flatFields := by
            have hwithin' := hwithin
            simp [SelectionFieldsWithin] at hwithin'
            exact hwithin' hallows
          rcases collectedExecutableFields_mem_exists_group groups field hfield with
            ⟨groupName, groupFields, hgroup, hfieldGroup⟩
          have hgroupName : responseName = groupName := by
            have hname :=
              hresponses groupName groupFields hgroup field hfieldGroup
            change responseName = groupName at hname
            exact hname
          subst groupName
          cases fuel with
          | zero =>
              cases hprevious
                    : objectField? responseName
                        (.object (.object runtimeType ref) outputFields) with
              | none =>
                  have hpreviousOut :
                      ExecutionUngroupedUncached.responseObjectField? responseName
                          (.object (ExecutionUngrouped.outputFields outputFields))
                        = none := by
                    have hmap := objectField?_output (ObjectRef := ObjectRef)
                      responseName (.object (.object runtimeType ref) outputFields)
                    simpa [hprevious] using hmap.symm
                  constructor
                  · simp [visitSelection,
                      ExecutionUngroupedUncached.visitSelection, hallows,
                      hprevious, hpreviousOut, mergeResponseFieldResult_output,
                      outputResult, outOfFuel]
                  · exact
                      OutputCacheTreeSoundForGroups.zero source groups _
              | some previous =>
                  have hpreviousOut :
                      ExecutionUngroupedUncached.responseObjectField? responseName
                          (.object (ExecutionUngrouped.outputFields outputFields))
                        = some previous.output := by
                    have hmap := objectField?_output (ObjectRef := ObjectRef)
                      responseName (.object (.object runtimeType ref) outputFields)
                    simpa [hprevious] using hmap.symm
                  constructor
                  · simp [visitSelection,
                      ExecutionUngroupedUncached.visitSelection, hallows,
                      hprevious, hpreviousOut, mergeResponseFieldResult_output,
                      outputResult]
                  · exact
                      OutputCacheTreeSoundForGroups.zero source groups _
          | succ completionFuel =>
              cases htree with
              | succ _ _ _ _ hmergeReady haligned hsource hobjects hlists =>
                  rcases hlookups field hfield with
                    ⟨fieldDefinition, hfieldLookup⟩
                  have hchildVisit :
                      ∀ visitFuel childRuntime (childRef : ObjectRef) childFields,
                        visitFuel < completionFuel + 1
                        -> schema.typeIncludesObjectBool
                              fieldDefinition.outputType.namedType childRuntime
                            = true
                        -> OutputCacheTreeSoundForGroups schema resolvers
                            variableValues visitFuel (.object childRuntime childRef)
                            (GraphQL.Execution.collectFields schema variableValues
                              childRuntime (.object childRuntime childRef)
                              (GraphQL.Execution.mergedFieldSelectionSet groupFields))
                            (.object (.object childRuntime childRef) childFields)
                        -> outputVisitResult
                              (visitSubfields schema resolvers variableValues
                                visitFuel childRuntime
                                (.object childRuntime childRef) selectionSet
                                (.object (.object childRuntime childRef) childFields))
                            = ExecutionUngroupedUncached.visitSubfields schema
                                resolvers variableValues visitFuel childRuntime
                                (.object childRuntime childRef) selectionSet
                                (.object (ExecutionUngrouped.outputFields childFields)) := by
                    intro visitFuel childRuntime childRef childFields hlt hinclude
                      hchildTree
                    have hchildParentRuntime :
                        ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies
                          schema childRuntime
                          fieldDefinition.outputType.namedType :=
                      ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                        schema childRuntime fieldDefinition.outputType.namedType
                        hinclude
                    have hchildObject : schema.objectType childRuntime :=
                      ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.runtimeObjectType
                        schema hschema hchildParentRuntime
                    have hchildSelf :
                        ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies
                          schema childRuntime childRuntime :=
                      ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.runtimeSelf
                        schema hschema hchildParentRuntime
                    have hchildReady :=
                      collectedGroup_mergedFieldSelectionSet_semanticsReady schema
                        variableValues parentType runtimeType ref universeSet
                        responseName groupFields field fieldDefinition childRuntime
                        hobject hparentRuntime hready hmerge hgroup hfieldGroup
                        hfieldLookup hinclude
                    have hchildMerge :=
                      collectedGroup_mergedFieldSelectionSet_canMerge schema
                        variableValues parentType runtimeType ref universeSet
                        responseName groupFields hmerge hparentRuntime hlookupValid
                        hgroup
                    have hchildWithin :
                        SelectionSetFieldsWithin schema variableValues childRuntime
                          (.object childRuntime childRef)
                          (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                            (GraphQL.Execution.collectFields schema variableValues
                              childRuntime (.object childRuntime childRef)
                              (GraphQL.Execution.mergedFieldSelectionSet groupFields)))
                          selectionSet := by
                      apply
                        SelectionSetFieldsWithin.of_selectionSet_subset schema
                          variableValues childRuntime (.object childRuntime childRef)
                          (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                            (GraphQL.Execution.collectFields schema variableValues
                              childRuntime (.object childRuntime childRef)
                              (GraphQL.Execution.mergedFieldSelectionSet groupFields)))
                          (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                          selectionSet
                      · intro childSelection hchildSelection
                        exact
                          selection_mem_mergedFieldSelectionSet_of_field_mem field
                            groupFields hfieldGroup childSelection hchildSelection
                      · exact
                          selectionSetFieldsWithin_collectFields schema variableValues
                            childRuntime (.object childRuntime childRef)
                            (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                    exact (visitSubfields_output_eq_uncached_and_treeSound_object schema
                            resolvers variableValues visitFuel childRuntime childRuntime
                            childRef
                            (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                            selectionSet childFields hschema hchildObject hchildSelf
                            hchildReady (hchildMerge childRuntime) hchildWithin
                            hchildTree).1
                  have hcompletionExact :
                      ∀ resolved completionPrevious?,
                        (∀ previous,
                          completionPrevious? = some previous
                          -> FieldCacheTreeSound schema resolvers variableValues
                              completionFuel
                              (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                              resolved previous)
                        -> CompletionCacheSound schema resolvers variableValues
                            completionFuel fieldDefinition.outputType selectionSet
                            resolved completionPrevious? := by
                    intro resolved completionPrevious? hpreviousTree
                    exact
                      CompletionCacheSound.of_treeSound_and_visit schema resolvers
                        variableValues
                        (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                        selectionSet fieldDefinition.outputType.namedType
                        (completionFuel + 1) hchildVisit completionFuel
                        fieldDefinition.outputType resolved completionPrevious?
                        (by omega) rfl hpreviousTree
                  have hcompletionTree :
                      ∀ resolved completionPrevious?,
                        (∀ previous,
                          completionPrevious? = some previous
                          -> FieldCacheTreeSound schema resolvers variableValues
                              completionFuel
                              (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                              resolved previous)
                        -> FieldCacheTreeSound schema resolvers variableValues
                            completionFuel
                            (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                            resolved
                            (resultValueOrNull
                              (completeValue schema resolvers variableValues
                                completionFuel fieldDefinition.outputType selectionSet
                                resolved completionPrevious?)) := by
                    intro resolved completionPrevious? hpreviousTree
                    exact
                      FieldCacheTreeSound.completeValue_result_of_treeSound_and_visit
                        schema resolvers variableValues
                        (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                        selectionSet fieldDefinition.outputType.namedType
                        (completionFuel + 1)
                        (by
                          intro visitFuel childRuntime childRef childFields hlt
                            hinclude hchildTree
                          exact
                            (visitSubfields_output_eq_uncached_and_treeSound_object
                              schema resolvers variableValues visitFuel childRuntime
                              childRuntime childRef
                              (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                              selectionSet childFields hschema
                              (ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.runtimeObjectType
                                schema hschema
                                (ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                                  schema childRuntime
                                  fieldDefinition.outputType.namedType hinclude))
                              (ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.runtimeSelf
                                schema hschema
                                (ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies.of_typeIncludesObjectBool
                                  schema childRuntime
                                  fieldDefinition.outputType.namedType hinclude))
                              (collectedGroup_mergedFieldSelectionSet_semanticsReady
                                schema variableValues parentType runtimeType ref
                                universeSet responseName groupFields field
                                fieldDefinition childRuntime hobject hparentRuntime
                                hready hmerge hgroup hfieldGroup hfieldLookup hinclude)
                              ((collectedGroup_mergedFieldSelectionSet_canMerge
                                schema variableValues parentType runtimeType ref
                                universeSet responseName groupFields hmerge
                                hparentRuntime hlookupValid hgroup) childRuntime)
                              (by
                                apply
                                  SelectionSetFieldsWithin.of_selectionSet_subset
                                    schema variableValues childRuntime
                                    (.object childRuntime childRef)
                                    (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                                      (GraphQL.Execution.collectFields schema
                                        variableValues childRuntime
                                        (.object childRuntime childRef)
                                        (GraphQL.Execution.mergedFieldSelectionSet
                                          groupFields)))
                                    (GraphQL.Execution.mergedFieldSelectionSet
                                      groupFields)
                                    selectionSet
                                · intro childSelection hchildSelection
                                  exact
                                    selection_mem_mergedFieldSelectionSet_of_field_mem
                                      field groupFields hfieldGroup childSelection
                                      hchildSelection
                                · exact
                                    selectionSetFieldsWithin_collectFields schema
                                      variableValues childRuntime
                                      (.object childRuntime childRef)
                                      (GraphQL.Execution.mergedFieldSelectionSet
                                        groupFields))
                              hchildTree).2)
                        completionFuel fieldDefinition.outputType resolved
                        completionPrevious? (by omega) rfl hpreviousTree
                  have hexecute :
                      outputResult FieldCacheValue.output
                          (executeField schema resolvers variableValues completionFuel
                            source
                            (objectField? responseName
                              (.object source outputFields))
                            field)
                        = ExecutionUngroupedUncached.executeField schema resolvers
                            variableValues completionFuel source
                            ((objectField? responseName
                              (.object source outputFields)).map
                              FieldCacheValue.output)
                            field :=
                    executeField_output_of_completionCacheSound schema resolvers
                      variableValues completionFuel source
                      (objectField? responseName (.object source outputFields)) field
                      (by
                        intro candidateDefinition resolved hlookup hresolve
                        rw [hfieldLookup] at hlookup
                        injection hlookup with hdefinition
                        subst candidateDefinition
                        exact hcompletionExact resolved none (by
                          intro previous hprevious
                          simp at hprevious))
                      (by
                        intro candidateDefinition previous hlookup hprevious
                        rw [hfieldLookup] at hlookup
                        injection hlookup with hdefinition
                        subst candidateDefinition
                        constructor
                        · exact
                            hsource responseName groupFields field fieldDefinition
                              previous hgroup hfieldGroup hprevious hfieldLookup
                        · cases previous with
                          | object previousSource previousFields =>
                              exact
                                hcompletionExact previousSource
                                  (some (.object previousSource previousFields)) (by
                                    intro candidate hcandidate
                                    injection hcandidate with hcandidate
                                    subst candidate
                                    exact
                                      hobjects responseName groupFields
                                        previousSource previousFields hgroup
                                        hprevious)
                          | list sourceValues? previousValues =>
                              cases sourceValues? with
                              | none => trivial
                              | some sourceValues =>
                                  exact
                                    hcompletionExact (.list sourceValues)
                                      (some (.list (some sourceValues) previousValues))
                                      (by
                                        intro candidate hcandidate
                                        injection hcandidate with hcandidate
                                        subst candidate
                                        exact
                                          hlists responseName groupFields
                                            sourceValues previousValues hgroup
                                            hprevious)
                          | null => trivial
                          | scalar value => trivial)
                  let incoming :=
                    resultValueOrNull
                      (executeField schema resolvers variableValues completionFuel
                        source
                        (objectField? responseName (.object source outputFields))
                        field)
                  have hincoming :
                      FieldCacheContinuationTreeSound schema resolvers variableValues
                        completionFuel
                        (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                        incoming :=
                    executeField_result_continuationTreeSound schema resolvers
                      variableValues completionFuel source field
                      (objectField? responseName (.object source outputFields))
                      (GraphQL.Execution.mergedFieldSelectionSet groupFields)
                      (by
                        intro candidateDefinition resolved completionPrevious?
                          hlookup hprevious
                        rw [hfieldLookup] at hlookup
                        injection hlookup with hdefinition
                        subst candidateDefinition
                        exact hcompletionTree resolved completionPrevious? hprevious)
                      (by
                        intro candidateDefinition previous hlookup hprevious
                        rw [hfieldLookup] at hlookup
                        injection hlookup with hdefinition
                        subst candidateDefinition
                        cases previous with
                        | object previousSource previousFields =>
                            simpa [FieldCacheContinuationTreeSound] using
                              hobjects responseName groupFields previousSource
                                previousFields hgroup hprevious
                        | list sourceValues? previousValues =>
                            cases sourceValues? with
                            | none => trivial
                            | some sourceValues =>
                                simpa [FieldCacheContinuationTreeSound] using
                                  hlists responseName groupFields sourceValues
                                    previousValues hgroup hprevious
                        | null => trivial
                        | scalar value => trivial)
                  have habsorbs :
                      ∀ previous,
                        objectField? responseName (.object source outputFields)
                            = some previous
                        -> FieldCacheAbsorbs previous incoming := by
                    intro previous hprevious
                    exact
                      visitFieldResult_absorbs_previous schema resolvers
                        variableValues (completionFuel + 1) parentType source
                        responseName fieldName arguments selectionSet
                        (.object source outputFields) hmergeReady haligned previous
                        hprevious
                  have hpostReady :=
                    visitSelection_cacheReady schema resolvers variableValues
                      (completionFuel + 1) parentType source
                      (.field responseName fieldName arguments directives selectionSet)
                      (.object source outputFields) hmergeReady
                  have hpostAligned :=
                    visitSelection_objectFieldCachesInternallyAligned schema resolvers
                      variableValues (completionFuel + 1) parentType source
                      (.field responseName fieldName arguments directives selectionSet)
                      (.object source outputFields) hmergeReady haligned
                  have hpostSourceFlat :=
                    visitSelection_outputCacheSoundForFields schema resolvers
                      variableValues (completionFuel + 1) parentType source flatFields
                      hschema hparents hcompatible hlookups
                      (.field responseName fieldName arguments directives selectionSet)
                      (.object source outputFields) hwithin hmergeReady haligned
                      (OutputCacheSoundForGroups.to_flat schema resolvers source
                        groups (.object source outputFields) hresponses hsource)
                  have hpostSource :=
                    OutputCacheSoundForFields.to_groups schema resolvers source groups
                      (visitSelection schema resolvers variableValues
                        (completionFuel + 1) parentType source
                        (.field responseName fieldName arguments directives selectionSet)
                        (.object source outputFields)).value
                      hresponses hpostSourceFlat
                  have hpostTree :
                      OutputCacheTreeSoundForGroups schema resolvers variableValues
                        (completionFuel + 1) source groups
                        (visitSelection schema resolvers variableValues
                          (completionFuel + 1) parentType source
                          (.field responseName fieldName arguments directives
                            selectionSet)
                          (.object source outputFields)).value := by
                    simpa [visitSelection, hallows, mergeResponseFieldResult,
                      incoming, field, source] using
                      OutputCacheTreeSoundForGroups.merge_field schema resolvers
                        variableValues completionFuel source source groups outputFields
                        responseName groupFields incoming hgroupsNodup hgroup
                        (OutputCacheTreeSoundForGroups.succ completionFuel source
                          groups (.object source outputFields) hmergeReady haligned
                          hsource hobjects hlists)
                        hincoming habsorbs (by
                          simpa [visitSelection, hallows, mergeResponseFieldResult,
                            incoming, source] using hpostReady) (by
                          simpa [visitSelection, hallows, mergeResponseFieldResult,
                            incoming, source] using hpostAligned) (by
                          simpa [visitSelection, hallows, mergeResponseFieldResult,
                            incoming, source] using hpostSource)
                  constructor
                  · dsimp [field, source] at hexecute
                    have hpreviousOut := objectField?_output (ObjectRef := ObjectRef)
                      responseName (.object source outputFields)
                    rw [hpreviousOut] at hexecute
                    have hmerged :=
                      congrArg
                        (fun result =>
                          ExecutionUngroupedUncached.mergeResponseFieldResult
                            responseName result
                            (.object
                              (ExecutionUngrouped.outputFields outputFields)))
                        hexecute
                    simpa [visitSelection,
                      ExecutionUngroupedUncached.visitSelection, hallows,
                      mergeResponseFieldResult_output, executableField,
                      ExecutionUngroupedUncached.executableField, source] using
                      hmerged
                  · simpa [source, groups] using hpostTree
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          constructor
          · simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
              hfalse, outputVisitResult, visitOk,
              ExecutionUngroupedUncached.visitOk]
          · simpa [visitSelection, hfalse] using htree
    | inlineFragment typeCondition directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases typeCondition with
          | none =>
              have hwithin' := hwithin
              simp [SelectionFieldsWithin] at hwithin'
              simpa [visitSelection, ExecutionUngroupedUncached.visitSelection,
                hallows] using
                visitSubfields_output_eq_uncached_and_treeSound_object schema
                  resolvers variableValues fuel parentType runtimeType ref universeSet
                  selectionSet outputFields hschema hobject hparentRuntime hready
                  hmerge (hwithin' hallows) htree
          | some typeCondition =>
              have hwithin' := hwithin
              simp [SelectionFieldsWithin] at hwithin'
              by_cases happly :
                  doesFragmentTypeApplyBool schema parentType
                      (.object runtimeType ref) typeCondition
                    = true
              · simpa [visitSelection,
                  ExecutionUngroupedUncached.visitSelection, hallows, happly] using
                  visitSubfields_output_eq_uncached_and_treeSound_object schema
                    resolvers variableValues fuel parentType runtimeType ref
                    universeSet selectionSet outputFields hschema hobject
                    hparentRuntime hready hmerge (hwithin' hallows happly) htree
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType
                        (.object runtimeType ref) typeCondition
                      = false := by
                  cases h :
                    doesFragmentTypeApplyBool schema parentType
                      (.object runtimeType ref) typeCondition
                  · rfl
                  · contradiction
                constructor
                · simp [visitSelection,
                    ExecutionUngroupedUncached.visitSelection, hallows, hfalse,
                    outputVisitResult, visitOk,
                    ExecutionUngroupedUncached.visitOk]
                · simpa [visitSelection, hallows, hfalse, source] using htree
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          constructor
          · cases typeCondition <;>
              simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
                hfalse, outputVisitResult, visitOk,
                ExecutionUngroupedUncached.visitOk]
          · cases typeCondition <;>
              simpa [visitSelection, hfalse] using htree
  termination_by fuel parentType runtimeType ref universeSet selection outputFields
      _hschema _hobject _hparentRuntime _hready _hmerge _hwithin _htree =>
    (fuel, sizeOf selection, 0)
  decreasing_by
    all_goals
      try subst_vars
      simp_wf
      try simp [List._sizeOf_1]
      repeat first
        | apply Prod.Lex.right
        | apply Prod.Lex.left
      omega

  theorem visitSubfields_output_eq_uncached_and_treeSound_object
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : ∀ fuel parentType runtimeType (ref : ObjectRef) universeSet selectionSet
          outputFields,
          SchemaWellFormedness.schemaWellFormed schema
          -> schema.objectType parentType
          -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
              runtimeType parentType
          -> NormalForm.selectionSetSemanticsReady schema parentType universeSet
          -> FieldMerge.fieldsInSetCanMerge schema parentType universeSet
          -> SelectionSetFieldsWithin schema variableValues parentType
              (.object runtimeType ref)
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  (.object runtimeType ref) universeSet))
              selectionSet
          -> OutputCacheTreeSoundForGroups schema resolvers variableValues fuel
              (.object runtimeType ref)
              (GraphQL.Execution.collectFields schema variableValues parentType
                (.object runtimeType ref) universeSet)
              (.object (.object runtimeType ref) outputFields)
          -> outputVisitResult
                  (visitSubfields schema resolvers variableValues fuel parentType
                    (.object runtimeType ref) selectionSet
                    (.object (.object runtimeType ref) outputFields))
                = ExecutionUngroupedUncached.visitSubfields schema resolvers
                    variableValues fuel parentType (.object runtimeType ref)
                    selectionSet
                    (.object (ExecutionUngrouped.outputFields outputFields))
              ∧ OutputCacheTreeSoundForGroups schema resolvers variableValues fuel
                  (.object runtimeType ref)
                  (GraphQL.Execution.collectFields schema variableValues parentType
                    (.object runtimeType ref) universeSet)
                  (visitSubfields schema resolvers variableValues fuel parentType
                    (.object runtimeType ref) selectionSet
                    (.object (.object runtimeType ref) outputFields)).value := by
    intro fuel parentType runtimeType ref universeSet selectionSet outputFields
      hschema hobject hparentRuntime hready hmerge hwithin htree
    cases selectionSet with
    | nil =>
        constructor
        · simp [visitSubfields, ExecutionUngroupedUncached.visitSubfields,
            outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk]
        · simpa [visitSubfields] using htree
    | cons selection rest =>
        unfold SelectionSetFieldsWithin at hwithin
        have hselectionWithin := hwithin selection (by simp)
        have hrestWithin :
            SelectionSetFieldsWithin schema variableValues parentType
              (.object runtimeType ref)
              (ExecutionUngroupedUncached.Eager.collectedExecutableFields
                (GraphQL.Execution.collectFields schema variableValues parentType
                  (.object runtimeType ref) universeSet))
              rest := by
          unfold SelectionSetFieldsWithin
          intro candidate hcandidate
          exact hwithin candidate (by simp [hcandidate])
        let head :=
          visitSelection schema resolvers variableValues fuel parentType
            (.object runtimeType ref) selection
            (.object (.object runtimeType ref) outputFields)
        have hheadEq :
            visitSelection schema resolvers variableValues fuel parentType
                (.object runtimeType ref) selection
                (.object (.object runtimeType ref) outputFields)
              = head := rfl
        have hhead :=
          visitSelection_output_eq_uncached_and_treeSound_object schema resolvers
            variableValues fuel parentType runtimeType ref universeSet selection
            outputFields hschema hobject hparentRuntime hready hmerge
            hselectionWithin htree
        rcases hhead with ⟨hheadOutput, hheadTree⟩
        rw [hheadEq] at hheadOutput hheadTree
        rcases
            visitSelection_value_object schema resolvers variableValues fuel
              parentType (.object runtimeType ref) selection
              (.object runtimeType ref) outputFields with
          ⟨headFields, hheadValue⟩
        rw [hheadEq] at hheadValue
        rw [hheadValue] at hheadTree
        cases hstatus : head.status with
        | error errors =>
            have huncachedHead :
                ExecutionUngroupedUncached.visitSelection schema resolvers
                    variableValues fuel parentType (.object runtimeType ref) selection
                    (.object (ExecutionUngrouped.outputFields outputFields))
                  = (head.value.output, .error errors) := by
              rw [← hheadOutput]
              simp [outputVisitResult, hstatus]
            constructor
            · simp [visitSubfields, ExecutionUngroupedUncached.visitSubfields,
                hheadEq, hstatus, huncachedHead, outputVisitResult]
            · simp [visitSubfields, hheadEq, hstatus]
              rw [hheadValue]
              exact hheadTree
        | ok ok =>
            have huncachedHead :
                ExecutionUngroupedUncached.visitSelection schema resolvers
                    variableValues fuel parentType (.object runtimeType ref) selection
                    (.object (ExecutionUngrouped.outputFields outputFields))
                  = (head.value.output, .ok ok) := by
              rw [← hheadOutput]
              simp [outputVisitResult, hstatus]
            rw [hheadValue] at huncachedHead
            have htail :=
              visitSubfields_output_eq_uncached_and_treeSound_object schema
                resolvers variableValues fuel parentType runtimeType ref universeSet
                rest headFields hschema hobject hparentRuntime hready hmerge
                hrestWithin hheadTree
            rcases htail with ⟨htailOutput, htailTree⟩
            constructor
            · simp [visitSubfields, ExecutionUngroupedUncached.visitSubfields,
                hheadEq, hstatus, huncachedHead, outputVisitResult,
                combineVisitStatus, ExecutionUngroupedUncached.combineVisitStatus]
              rw [← htailOutput]
              simp [outputVisitResult, hheadValue]
            · simp [visitSubfields, hheadEq, hstatus]
              rw [hheadValue]
              exact htailTree
  termination_by fuel parentType runtimeType ref universeSet selectionSet outputFields
      _hschema _hobject _hparentRuntime _hready _hmerge _hwithin _htree =>
    (fuel, sizeOf selectionSet, 1)
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
  theorem visitSubfields_output_eq_uncached_of_globalCacheSound
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hcache : GlobalFieldPreviousCacheSound schema resolvers)
      : ∀ fuel parentType source selectionSet output,
          outputVisitResult
            (visitSubfields schema resolvers variableValues fuel parentType source
              selectionSet output)
          = ExecutionUngroupedUncached.visitSubfields schema resolvers variableValues
              fuel parentType source selectionSet output.output
    | fuel, parentType, source, [], output => by
        simp [visitSubfields, ExecutionUngroupedUncached.visitSubfields,
          outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk]
    | fuel, parentType, source, selection :: rest, output => by
        unfold visitSubfields ExecutionUngroupedUncached.visitSubfields
        generalize hhead :
          visitSelection schema resolvers variableValues fuel parentType source
              selection output
          =
          head
        have hsel :=
          visitSelection_output_eq_uncached_of_globalCacheSound schema resolvers
            variableValues hcache fuel parentType source selection output
        rw [hhead] at hsel
        cases hstatus : head.status with
        | error errors =>
            have huncachedHead :
                ExecutionUngroupedUncached.visitSelection schema resolvers
                    variableValues fuel parentType source selection output.output
                  =
                  (head.value.output, .error errors) := by
              rw [← hsel]
              simp [outputVisitResult, hstatus]
            simp [hstatus, huncachedHead, outputVisitResult]
        | ok ok =>
            have huncachedHead :
                ExecutionUngroupedUncached.visitSelection schema resolvers
                    variableValues fuel parentType source selection output.output
                  =
                  (head.value.output, .ok ok) := by
              rw [← hsel]
              simp [outputVisitResult, hstatus]
            have htail :=
              visitSubfields_output_eq_uncached_of_globalCacheSound schema
                resolvers variableValues hcache fuel parentType source rest
                head.value
            simp [hstatus, huncachedHead, outputVisitResult, combineVisitStatus,
              ExecutionUngroupedUncached.combineVisitStatus]
            rw [← htail]
            simp [outputVisitResult]

  theorem visitSelection_output_eq_uncached_of_globalCacheSound
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hcache : GlobalFieldPreviousCacheSound schema resolvers)
      : ∀ fuel parentType source selection output,
          outputVisitResult
            (visitSelection schema resolvers variableValues fuel parentType source
              selection output)
          = ExecutionUngroupedUncached.visitSelection schema resolvers
              variableValues fuel parentType source selection output.output
    | fuel, parentType, source,
      .field responseName fieldName arguments directives selectionSet, output => by
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · cases fuel with
          | zero =>
              cases hprevious : objectField? responseName output with
              | none =>
                  have hpreviousOut :
                      ExecutionUngroupedUncached.responseObjectField? responseName
                          output.output
                        =
                        none := by
                    have hmap := objectField?_output (ObjectRef := ObjectRef)
                      responseName output
                    simpa [hprevious] using hmap.symm
                  simp [visitSelection,
                    ExecutionUngroupedUncached.visitSelection, hallows,
                    hprevious, hpreviousOut, mergeResponseFieldResult_output,
                    outputResult, outOfFuel]
              | some cachedPrevious =>
                  have hpreviousOut :
                      ExecutionUngroupedUncached.responseObjectField? responseName
                          output.output
                        =
                        some cachedPrevious.output := by
                    have hmap := objectField?_output (ObjectRef := ObjectRef)
                      responseName output
                    simpa [hprevious] using hmap.symm
                  simp [visitSelection,
                    ExecutionUngroupedUncached.visitSelection, hallows,
                    hprevious, hpreviousOut, mergeResponseFieldResult_output,
                    outputResult]
          | succ fuel' =>
              let field :=
                executableField parentType responseName fieldName arguments
                  selectionSet
              have hs :
                  FieldPreviousCacheSound schema resolvers source
                    (objectField? responseName output) field := by
                intro fieldDefinition previous hlookup hpreviousEq
                cases hprevious : objectField? responseName output with
                | none =>
                    rw [hprevious] at hpreviousEq
                    contradiction
                | some cachedPrevious =>
                    have hs0 :=
                      hcache source output parentType responseName fieldName
                        arguments selectionSet cachedPrevious hprevious
                    rw [hprevious] at hpreviousEq
                    injection hpreviousEq with hcachedEq
                    subst previous
                    exact hs0 fieldDefinition cachedPrevious hlookup rfl
              have hexec :=
                executeField_output_of_completeValue_and_fieldPreviousCacheSound
                  schema resolvers variableValues fuel' source
                  (objectField? responseName output) field
                  (fun fieldType selectionSet value previous? =>
                    completeValue_output_eq_uncached_of_globalCacheSound schema
                      resolvers variableValues hcache fuel' fieldType
                      selectionSet value previous?)
                  hs
              dsimp [field, executableField,
                ExecutionUngroupedUncached.executableField] at hexec
              have hpreviousOut := objectField?_output (ObjectRef := ObjectRef)
                responseName output
              simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
                hallows, mergeResponseFieldResult_output, executableField,
                ExecutionUngroupedUncached.executableField]
              rw [hexec]
              rw [hpreviousOut]
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases h : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
            hfalse, outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk]
    | fuel, parentType, source,
      .inlineFragment none directives selectionSet, output => by
        by_cases hskip :
            (!selectionDirectivesAllowBool variableValues directives) = true
        · simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
            hskip, outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk]
        · have hallow :
              selectionDirectivesAllowBool variableValues directives = true := by
            cases hdir : selectionDirectivesAllowBool variableValues directives
            · simp [hdir] at hskip
            · rfl
          have hvisit :=
            visitSubfields_output_eq_uncached_of_globalCacheSound schema resolvers
              variableValues hcache fuel parentType source selectionSet output
          simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
            hallow, hvisit]
    | fuel, parentType, source,
      .inlineFragment (some typeCondition) directives selectionSet, output => by
        by_cases hskip :
            (!selectionDirectivesAllowBool variableValues directives) = true
        · simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
            hskip, outputVisitResult, visitOk, ExecutionUngroupedUncached.visitOk]
        · have hallow :
              selectionDirectivesAllowBool variableValues directives = true := by
            cases hdir : selectionDirectivesAllowBool variableValues directives
            · simp [hdir] at hskip
            · rfl
          by_cases hdoes :
              (!doesFragmentTypeApplyBool schema parentType source typeCondition) =
                true
          · have hnotApply :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  false := by
              cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · rfl
              · simp [happly] at hdoes
            simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
              hallow, hnotApply, outputVisitResult, visitOk,
              ExecutionUngroupedUncached.visitOk]
          · have happly :
                doesFragmentTypeApplyBool schema parentType source typeCondition =
                  true := by
              cases happly :
                  doesFragmentTypeApplyBool schema parentType source typeCondition
              · simp [happly] at hdoes
              · rfl
            have hvisit :=
              visitSubfields_output_eq_uncached_of_globalCacheSound schema
                resolvers variableValues hcache fuel parentType source selectionSet
                output
            simp [visitSelection, ExecutionUngroupedUncached.visitSelection,
              hallow, happly, hvisit]

  theorem executeField_output_eq_uncached_of_globalCacheSound
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hcache : GlobalFieldPreviousCacheSound schema resolvers)
      : ∀ completionFuel source previous? field,
          FieldPreviousCacheSound schema resolvers source previous? field
          -> outputResult FieldCacheValue.output
                (executeField schema resolvers variableValues completionFuel source
                  previous? field)
              = ExecutionUngroupedUncached.executeField schema resolvers variableValues
                  completionFuel source (previous?.map FieldCacheValue.output) field
    | completionFuel, source, previous?, field, hsound =>
        executeField_output_of_completeValue_and_fieldPreviousCacheSound schema
          resolvers variableValues completionFuel source previous? field
          (fun fieldType selectionSet value previous? =>
            completeValue_output_eq_uncached_of_globalCacheSound schema resolvers
              variableValues hcache completionFuel fieldType selectionSet value
              previous?)
          hsound

  theorem completeValue_output_eq_uncached_of_globalCacheSound
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hcache : GlobalFieldPreviousCacheSound schema resolvers)
      : ∀ fuel fieldType selectionSet value previous?,
          outputResult FieldCacheValue.output
            (completeValue schema resolvers variableValues fuel fieldType
              selectionSet value previous?)
          = ExecutionUngroupedUncached.completeValue schema resolvers
              variableValues fuel fieldType selectionSet value
              (previous?.map FieldCacheValue.output)
    | 0, fieldType, selectionSet, value, previous? => by
        simp [completeValue, ExecutionUngroupedUncached.completeValue,
          outputResult, outOfFuel]
    | fuel + 1, fieldType, selectionSet, value, previous? => by
        cases previous? with
        | none =>
            cases fieldType with
            | nonNull inner =>
                have hinner :=
                  completeValue_output_eq_uncached_of_globalCacheSound schema
                    resolvers variableValues hcache (fuel + 1) inner
                    selectionSet value none
                simp [completeValue, ExecutionUngroupedUncached.completeValue,
                  nonNullCompletion_output, hinner]
            | named typeName =>
                cases value with
                | null =>
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      outputResult]
                | scalar value =>
                    by_cases hcomp :
                        (TypeRef.named typeName).isCompositeBool schema = true
                    · simp [completeValue,
                        ExecutionUngroupedUncached.completeValue, hcomp,
                        outputResult]
                    · have hcompFalse :
                          (TypeRef.named typeName).isCompositeBool schema =
                            false := by
                        cases h : (TypeRef.named typeName).isCompositeBool schema
                        · rfl
                        · contradiction
                      simp [completeValue,
                        ExecutionUngroupedUncached.completeValue, hcompFalse,
                        outputResult]
                | object runtimeType ref =>
                    by_cases hinclude :
                        schema.typeIncludesObjectBool typeName runtimeType = true
                    · simp [completeValue,
                        ExecutionUngroupedUncached.completeValue, hinclude]
                      have hvisit :=
                        visitSubfields_output_eq_uncached_of_globalCacheSound
                          schema resolvers variableValues hcache fuel runtimeType
                          (ResolverValue.object runtimeType ref) selectionSet
                          (FieldCacheValue.object
                            (ResolverValue.object runtimeType ref) [])
                      exact
                        catchVisitBubbleAsNull_output_of_outputVisitResult
                          (visitSubfields schema resolvers variableValues fuel
                            runtimeType (ResolverValue.object runtimeType ref)
                            selectionSet
                            (FieldCacheValue.object
                              (ResolverValue.object runtimeType ref) []))
                          (ExecutionUngroupedUncached.visitSubfields schema
                            resolvers variableValues fuel runtimeType
                            (ResolverValue.object runtimeType ref) selectionSet
                            (ResponseValue.object []))
                          hvisit
                    · have hincludeFalse :
                          schema.typeIncludesObjectBool typeName runtimeType =
                            false := by
                        cases h :
                            schema.typeIncludesObjectBool typeName runtimeType
                        · rfl
                        · contradiction
                      simp [completeValue,
                        ExecutionUngroupedUncached.completeValue, hincludeFalse,
                        outputResult]
                | list values =>
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      outputResult]
            | list inner =>
                cases value with
                | list values =>
                    by_cases hcomp : inner.isCompositeBool schema = true
                    · have hlist :=
                        completeValueList_output_eq_uncached_of_globalCacheSound
                          schema resolvers variableValues hcache fuel inner
                          selectionSet values []
                      simp [completeValue,
                        ExecutionUngroupedUncached.completeValue,
                        reuseOrCreateList?,
                        ExecutionUngroupedUncached.reuseOrCreateList?, hcomp]
                      rw [catchBubbleAsNull_list_output, hlist]
                      simp
                    · have hcompFalse : inner.isCompositeBool schema = false := by
                        cases h : inner.isCompositeBool schema
                        · rfl
                        · contradiction
                      have hlist :=
                        completeValueList_output_eq_uncached_of_globalCacheSound
                          schema resolvers variableValues hcache fuel inner
                          selectionSet values []
                      simp [completeValue,
                        ExecutionUngroupedUncached.completeValue,
                        reuseOrCreateList?,
                        ExecutionUngroupedUncached.reuseOrCreateList?,
                        hcompFalse]
                      rw [catchBubbleAsNull_list_output, hlist]
                      simp
                | null =>
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      outputResult]
                | scalar scalarValue =>
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      outputResult]
                | object runtimeType ref =>
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      outputResult]
        | some previous =>
            cases previous with
            | null =>
                simp [completeValue, ExecutionUngroupedUncached.completeValue,
                  outputResult]
            | scalar previousValue =>
                simp [completeValue, ExecutionUngroupedUncached.completeValue,
                  outputResult]
            | object previousSource fields =>
                cases fieldType with
                | nonNull inner =>
                    have hinner :=
                      completeValue_output_eq_uncached_of_globalCacheSound schema
                        resolvers variableValues hcache (fuel + 1) inner
                        selectionSet value
                        (some (FieldCacheValue.object previousSource fields))
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      nonNullCompletion_output, hinner]
                | named typeName =>
                    cases value with
                    | object runtimeType ref =>
                        by_cases hinclude :
                            schema.typeIncludesObjectBool typeName runtimeType =
                              true
                        · simp [completeValue,
                            ExecutionUngroupedUncached.completeValue, hinclude,
                            reuseOrCreateObject?,
                            ExecutionUngroupedUncached.reuseOrCreateObject?]
                          have hvisit :=
                            visitSubfields_output_eq_uncached_of_globalCacheSound
                              schema resolvers variableValues hcache fuel
                              runtimeType (ResolverValue.object runtimeType ref)
                              selectionSet
                              (FieldCacheValue.object previousSource fields)
                          exact
                            catchVisitBubbleAsNull_output_of_outputVisitResult
                              (visitSubfields schema resolvers variableValues fuel
                                runtimeType
                                (ResolverValue.object runtimeType ref)
                                selectionSet
                                (FieldCacheValue.object previousSource fields))
                              (ExecutionUngroupedUncached.visitSubfields schema
                                resolvers variableValues fuel runtimeType
                                (ResolverValue.object runtimeType ref)
                                selectionSet
                                (ResponseValue.object (outputFields fields)))
                              hvisit
                        · have hincludeFalse :
                              schema.typeIncludesObjectBool typeName runtimeType =
                                false := by
                            cases h :
                                schema.typeIncludesObjectBool typeName runtimeType
                            · rfl
                            · contradiction
                          simp [completeValue,
                            ExecutionUngroupedUncached.completeValue,
                            hincludeFalse, outputResult]
                    | null =>
                        simp [completeValue,
                          ExecutionUngroupedUncached.completeValue, outputResult]
                    | scalar scalarValue =>
                        simp [completeValue,
                          ExecutionUngroupedUncached.completeValue, outputResult]
                    | list values =>
                        simp [completeValue,
                          ExecutionUngroupedUncached.completeValue, outputResult]
                | list inner =>
                    cases value <;>
                      simp [completeValue,
                        ExecutionUngroupedUncached.completeValue,
                        reuseOrCreateList?,
                        ExecutionUngroupedUncached.reuseOrCreateList?,
                        outputResult]
            | list sourceValues? values =>
                cases fieldType with
                | nonNull inner =>
                    have hinner :=
                      completeValue_output_eq_uncached_of_globalCacheSound schema
                        resolvers variableValues hcache (fuel + 1) inner
                        selectionSet value
                        (some (FieldCacheValue.list sourceValues? values))
                    simp [completeValue, ExecutionUngroupedUncached.completeValue,
                      nonNullCompletion_output, hinner]
                | named typeName =>
                    cases value <;>
                      simp [completeValue,
                        ExecutionUngroupedUncached.completeValue,
                        reuseOrCreateObject?,
                        ExecutionUngroupedUncached.reuseOrCreateObject?,
                        outputResult]
                | list inner =>
                    cases value with
                    | list newValues =>
                        cases sourceValues? with
                        | none =>
                            have hlist :=
                              completeValueList_output_eq_uncached_of_globalCacheSound
                                schema resolvers variableValues hcache fuel inner
                                selectionSet newValues values
                            simp [completeValue,
                              ExecutionUngroupedUncached.completeValue,
                              reuseOrCreateList?,
                              ExecutionUngroupedUncached.reuseOrCreateList?]
                            rw [catchBubbleAsNull_list_output, hlist]
                        | some sourceValues =>
                            have hlist :=
                              completeValueList_output_eq_uncached_of_globalCacheSound
                                schema resolvers variableValues hcache fuel inner
                                selectionSet newValues values
                            simp [completeValue,
                              ExecutionUngroupedUncached.completeValue,
                              reuseOrCreateList?,
                              ExecutionUngroupedUncached.reuseOrCreateList?]
                            rw [catchBubbleAsNull_list_output, hlist]
                    | null =>
                        simp [completeValue,
                          ExecutionUngroupedUncached.completeValue, outputResult]
                    | scalar scalarValue =>
                        simp [completeValue,
                          ExecutionUngroupedUncached.completeValue, outputResult]
                    | object runtimeType ref =>
                        simp [completeValue,
                          ExecutionUngroupedUncached.completeValue, outputResult]

  theorem completeValueList_output_eq_uncached_of_globalCacheSound
      {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      (hcache : GlobalFieldPreviousCacheSound schema resolvers)
      : ∀ fuel itemType selectionSet values previousValues,
          outputResult outputValues
            (completeValueList schema resolvers variableValues fuel itemType
              selectionSet values previousValues)
          = ExecutionUngroupedUncached.completeValueList schema resolvers
              variableValues fuel itemType selectionSet values
              (outputValues previousValues) := by
    intro fuel itemType selectionSet values previousValues
    exact
      completeValueList_output_of_completeValue schema resolvers variableValues
        fuel itemType selectionSet
        (fun value previous? =>
          completeValue_output_eq_uncached_of_globalCacheSound schema resolvers
            variableValues hcache fuel itemType selectionSet value previous?)
        values previousValues
end

end ExecutionUngrouped
end Algorithms

end GraphQL
