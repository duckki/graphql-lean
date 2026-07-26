import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Semantics.GeneratedFields

/-!
Semantic-ready aligned execution bridge for ungrouped execution.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

variable {ObjectRef : Type}

private theorem selectionSet_size_append_semantics (left right : List Selection)
    : SelectionSet.size (left ++ right)
      = SelectionSet.size left + SelectionSet.size right := by
  induction left with
  | nil => simp [SelectionSet.size]
  | cons selection rest ih =>
      simp [SelectionSet.size, ih, Nat.add_assoc]

theorem executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
    {ObjectIdentity : Type}
    {schema : Schema} {resolvers : Resolvers ObjectIdentity}
    {variableValues : VariableValues} {completionDepth : Nat}
    {parentType runtimeType : Name} {identity : ObjectIdentity}
    (prefixFields : List ExecutableField)
    (hparents : ExecutableFieldsParent parentType prefixFields)
    (hprefixLookups
      : ∀ field,
          field ∈ prefixFields
          -> ∃ fieldDefinition,
              schema.lookupField parentType field.fieldName = some fieldDefinition)
    : (selectionSet : List Selection)
      -> schema.objectType parentType
          -> ScopedParentRuntimeApplies schema runtimeType parentType
          -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
          -> ∃ normalized,
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType (.object runtimeType identity)
                (executableFieldSelections prefixFields ++ selectionSet) normalized
  | [], _hobject, _hparentRuntime, _hready => by
      rcases
          SelectionSetFreshPlanNormalizes.executableFieldsNormalizes
            (schema := schema) (resolvers := resolvers)
            (variableValues := variableValues)
            (completionDepth := completionDepth) (parentType := parentType)
            (source := .object runtimeType identity) prefixFields hparents
            hprefixLookups with
        ⟨normalized, hnormalized⟩
      exact ⟨normalized, by simpa using hnormalized⟩
  | .field responseName fieldName arguments directives selectionSet :: rest,
      hobject, hparentRuntime, hready => by
      have hheadReady :
          NormalForm.selectionSemanticsReady schema parentType
            (.field responseName fieldName arguments directives selectionSet) := by
        unfold NormalForm.selectionSetSemanticsReady at hready
        exact hready
          (.field responseName fieldName arguments directives selectionSet)
          (by simp)
      have hfieldLookup :
          ∃ fieldDefinition, schema.lookupField parentType fieldName =
            some fieldDefinition := by
        have hfieldReady :
            ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
                ∧ ∀ runtimeType,
                  schema.typeIncludesObjectBool
                      fieldDefinition.outputType.namedType runtimeType =
                    true ->
                  NormalForm.selectionSetSemanticsReady schema runtimeType
                    selectionSet := by
          simpa [NormalForm.selectionSemanticsReady] using hheadReady
        rcases hfieldReady with ⟨fieldDefinition, hlookup, _hchildReady⟩
        exact ⟨fieldDefinition, hlookup⟩
      have hrestReady :
          NormalForm.selectionSetSemanticsReady schema parentType rest :=
        NormalForm.selectionSetSemanticsReady_tail hready
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · let field :=
          executableField parentType responseName fieldName arguments
            selectionSet
        have hparents' :
            ExecutableFieldsParent parentType (prefixFields ++ [field]) := by
          intro candidate hcandidate
          rcases List.mem_append.mp hcandidate with hprefix | hfield
          · exact hparents candidate hprefix
          · rcases List.mem_singleton.mp hfield
            simp [field, executableField]
        have hlookups' :
            ∀ candidate, candidate ∈ prefixFields ++ [field] ->
              ∃ fieldDefinition,
                schema.lookupField parentType candidate.fieldName =
                  some fieldDefinition := by
          intro candidate hcandidate
          rcases List.mem_append.mp hcandidate with hprefix | hfield
          · exact hprefixLookups candidate hprefix
          · rcases List.mem_singleton.mp hfield with rfl
            simpa [field, executableField] using hfieldLookup
        rcases
            executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (runtimeType := runtimeType) (identity := identity)
              (prefixFields ++ [field]) hparents' hlookups' rest hobject
              hparentRuntime hrestReady with
          ⟨normalized, tail⟩
        have tail' :
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType (.object runtimeType identity)
              (executableFieldSelections prefixFields ++
                executableFieldSelections
                  [executableField parentType responseName fieldName arguments
                    selectionSet] ++
                rest)
              normalized := by
          simpa [field, executableFieldSelections, List.map_append,
            List.append_assoc] using tail
        exact
          ⟨normalized,
            SelectionSetFreshPlanNormalizes.executablePrefixFieldConsAllowed
              prefixFields responseName fieldName arguments directives
              selectionSet rest normalized hallows tail'⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (runtimeType := runtimeType) (identity := identity)
              prefixFields hparents hprefixLookups rest hobject
              hparentRuntime hrestReady with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            SelectionSetFreshPlanNormalizes.executablePrefixFieldConsSkipped
              prefixFields responseName fieldName arguments directives
              selectionSet rest normalized hskip tail⟩
  | .inlineFragment none directives rawChild :: rest, hobject, hparentRuntime,
      hready => by
      have hheadReady :
          NormalForm.selectionSemanticsReady schema parentType
            (.inlineFragment none directives rawChild) := by
        unfold NormalForm.selectionSetSemanticsReady at hready
        exact hready (.inlineFragment none directives rawChild) (by simp)
      have hchildReady :
          NormalForm.selectionSetSemanticsReady schema parentType rawChild := by
        simpa [NormalForm.selectionSemanticsReady] using hheadReady
      have hrestReady :
          NormalForm.selectionSetSemanticsReady schema parentType rest :=
        NormalForm.selectionSetSemanticsReady_tail hready
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · have happendReady :
            NormalForm.selectionSetSemanticsReady schema parentType
              (rawChild ++ rest) :=
          NormalForm.selectionSetSemanticsReady_append hchildReady hrestReady
        rcases
            executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (runtimeType := runtimeType) (identity := identity)
              prefixFields hparents hprefixLookups (rawChild ++ rest) hobject
              hparentRuntime happendReady with
          ⟨normalized, tail⟩
        have tail' :
            SelectionSetFreshPlanNormalizes schema resolvers variableValues
              completionDepth parentType (.object runtimeType identity)
              (executableFieldSelections prefixFields ++ rawChild ++ rest)
              normalized := by
          simpa [List.append_assoc] using tail
        exact
          ⟨normalized,
            SelectionSetFreshPlanNormalizes.executablePrefixInlineFragmentNoneConsFlatten
              prefixFields directives hallows tail'⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (runtimeType := runtimeType) (identity := identity)
              prefixFields hparents hprefixLookups rest hobject
              hparentRuntime hrestReady with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            SelectionSetFreshPlanNormalizes.executablePrefixInlineFragmentNoneConsSkipped
              prefixFields directives rawChild hskip tail⟩
  | .inlineFragment (some typeCondition) directives rawChild :: rest,
      hobject, hparentRuntime, hready => by
      have hheadReady :
          NormalForm.selectionSemanticsReady schema parentType
            (.inlineFragment (some typeCondition) directives rawChild) := by
        unfold NormalForm.selectionSetSemanticsReady at hready
        exact hready (.inlineFragment (some typeCondition) directives rawChild)
          (by simp)
      have hreadyPair :
          NormalForm.selectionSetLookupValid schema typeCondition rawChild
            ∧ (schema.typesOverlapBool parentType typeCondition = true ->
              NormalForm.selectionSetSemanticsReady schema parentType rawChild) := by
        simpa [NormalForm.selectionSemanticsReady] using hheadReady
      have hrestReady :
          NormalForm.selectionSetSemanticsReady schema parentType rest :=
        NormalForm.selectionSetSemanticsReady_tail hready
      by_cases hallows :
          selectionDirectivesAllowBool variableValues directives = true
      · by_cases happly :
            doesFragmentTypeApplyBool schema parentType
              (.object runtimeType identity) typeCondition = true
        · have hchildReady :
              NormalForm.selectionSetSemanticsReady schema parentType
                rawChild := by
            have hruntimeEq : runtimeType = parentType :=
              object_typeIncludesObjectBool_eq_self schema hobject
                hparentRuntime
            have htypeIncludes :
                schema.typeIncludesObjectBool typeCondition parentType = true := by
              simpa [doesFragmentTypeApplyBool, runtimeObjectType?, hruntimeEq]
                using happly
            have hparentIncludes :
                schema.typeIncludesObjectBool parentType parentType = true :=
              NormalForm.object_typeIncludesObjectBool_self schema hobject
            have hoverlap :
                schema.typesOverlapBool parentType typeCondition = true := by
              unfold Schema.typesOverlapBool
              exact List.any_eq_true.mpr
                ⟨parentType, List.contains_iff_mem.mp hparentIncludes,
                  htypeIncludes⟩
            exact hreadyPair.2 hoverlap
          have happendReady :
              NormalForm.selectionSetSemanticsReady schema parentType
                (rawChild ++ rest) :=
            NormalForm.selectionSetSemanticsReady_append hchildReady hrestReady
          rcases
              executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth) (parentType := parentType)
                (runtimeType := runtimeType) (identity := identity)
                prefixFields hparents hprefixLookups (rawChild ++ rest) hobject
                hparentRuntime happendReady with
            ⟨normalized, tail⟩
          have tail' :
              SelectionSetFreshPlanNormalizes schema resolvers variableValues
                completionDepth parentType (.object runtimeType identity)
                (executableFieldSelections prefixFields ++ rawChild ++ rest)
                normalized := by
            simpa [List.append_assoc] using tail
          exact
            ⟨normalized,
              SelectionSetFreshPlanNormalizes.executablePrefixInlineFragmentSomeConsFlatten
                prefixFields typeCondition directives hallows happly tail'⟩
        · have hnotApply :
              doesFragmentTypeApplyBool schema parentType
                (.object runtimeType identity) typeCondition = false := by
            cases h :
                doesFragmentTypeApplyBool schema parentType
                  (.object runtimeType identity) typeCondition
            · rfl
            · exact False.elim (happly h)
          rcases
              executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
                (schema := schema) (resolvers := resolvers)
                (variableValues := variableValues)
                (completionDepth := completionDepth) (parentType := parentType)
                (runtimeType := runtimeType) (identity := identity)
                prefixFields hparents hprefixLookups rest hobject
                hparentRuntime hrestReady with
            ⟨normalized, tail⟩
          exact
            ⟨normalized,
              SelectionSetFreshPlanNormalizes.executablePrefixInlineFragmentSomeConsDoesNotApply
                prefixFields typeCondition directives rawChild hallows hnotApply
                tail⟩
      · have hskip :
            selectionDirectivesAllowBool variableValues directives = false := by
          cases h :
              selectionDirectivesAllowBool variableValues directives
          · rfl
          · exact False.elim (hallows h)
        rcases
            executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
              (schema := schema) (resolvers := resolvers)
              (variableValues := variableValues)
              (completionDepth := completionDepth) (parentType := parentType)
              (runtimeType := runtimeType) (identity := identity)
              prefixFields hparents hprefixLookups rest hobject
              hparentRuntime hrestReady with
          ⟨normalized, tail⟩
        exact
          ⟨normalized,
            SelectionSetFreshPlanNormalizes.executablePrefixInlineFragmentSomeConsSkipped
              prefixFields typeCondition directives rawChild hskip tail⟩
termination_by selectionSet _ _ _ => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp [selectionSet_size_append_semantics, SelectionSet.size, Selection.size]
    try omega

theorem VisitSubfieldsFlatCollectsFreshPrefixes_of_selectionSetSemanticsReady_object
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (completionDepth : Nat)
    (parentType runtimeType : Name) (identity : ObjectIdentity)
    (selectionSet : List Selection)
    : schema.objectType parentType
      -> ScopedParentRuntimeApplies schema runtimeType parentType
      -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
      -> VisitSubfieldsFlatCollectsFreshPrefixes schema resolvers variableValues
          (completionDepth + 1) parentType (.object runtimeType identity)
          selectionSet := by
  intro hobject hparentRuntime hready
  have hparents :
      ExecutableFieldsParent parentType ([] : List ExecutableField) := by
    intro field hfield
    simp at hfield
  rcases
      executablePrefixRawNormalizes_of_selectionSetSemanticsReady_object
        (schema := schema) (resolvers := resolvers)
        (variableValues := variableValues)
        (completionDepth := completionDepth) (parentType := parentType)
        (runtimeType := runtimeType) (identity := identity)
        ([] : List ExecutableField) hparents
        (by
          intro field hfield
          simp at hfield)
        selectionSet hobject hparentRuntime hready with
    ⟨normalized, hnormalized⟩
  simpa [executableFieldSelections] using hnormalized.rawFreshFlat

theorem executionCollectedFieldInvariant_of_collectedFieldCompatibility
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (depth : Nat) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : CollectedGroupsFieldValidationMergeCompatible
        (GraphQL.Execution.collectFields schema variableValues parentType source
          selectionSet)
      -> ExecutionCollectedFieldInvariant
          {
            window :=
              {
                schema := schema
                resolvers := resolvers
                variableValues := variableValues
                depth := depth
                parentType := parentType
                source := source
                selectionSet := selectionSet
              }
            initial := .object []
          } := by
  intro hcompatible
  constructor
  · exact PairKeysNodup_of_executableGroupNamesNodup
      (GraphQL.Execution.collectFields schema variableValues parentType source
        selectionSet)
      (GraphQL.NormalForm.collectFields_namesNodup schema variableValues
        parentType source selectionSet)
  · intro responseName fields hgroup first later hfirst hlater hresponse
    have hparents :
        CollectedGroupsParent parentType
          (GraphQL.Execution.collectFields schema variableValues parentType
            source selectionSet) :=
      collectFields_parent schema variableValues parentType source selectionSet
    have hfirstParent : first.parentType = parentType :=
      hparents responseName fields hgroup first hfirst
    have hlaterParent : later.parentType = parentType :=
      hparents responseName fields hgroup later hlater
    rcases
        hcompatible responseName fields hgroup first later hfirst hlater
          hresponse with
      ⟨hfieldName, harguments⟩
    rw [hfirstParent, hlaterParent, hfieldName]
    exact resolvers.resolve_argumentsEquivalent parentType later.fieldName
      first.arguments later.arguments source harguments

noncomputable def executedGroupedSelectionSetAlignedState_of_selectionSetSemanticsReady_object
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    : ∀ depth parentType runtimeType (identity : ObjectRef)
          (selectionSet : List Selection),
        SchemaWellFormedness.schemaWellFormed schema
        -> schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
        -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
        -> ExecutedGroupedSelectionSetAlignedState schema resolvers variableValues
            depth parentType (.object runtimeType identity) selectionSet := by
  intro depth
  induction depth using Nat.strongRecOn with
  | ind depth ih =>
      intro parentType runtimeType identity selectionSet hschema hobject
        hparentRuntime hready hmerge
      cases depth with
      | zero =>
          exact
            ExecutedGroupedSelectionSetAlignedState.of_exact
              (ExecutedGroupedSelectionSetState.depth_zero_general schema
                resolvers variableValues parentType (.object runtimeType identity)
                selectionSet)
      | succ depth' =>
          let groups :=
            GraphQL.Execution.collectFields schema variableValues parentType
              (.object runtimeType identity) selectionSet
          have hcollect :
              GraphQL.Execution.collectFields schema variableValues parentType
                  (.object runtimeType identity) selectionSet =
                groups := rfl
          have hlookupReady :
              NormalForm.selectionSetLookupValid schema parentType selectionSet :=
            NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady
              selectionSet hready
          have hflat :
              VisitSubfieldsFlatCollects schema resolvers variableValues
                (depth' + 1) parentType (.object runtimeType identity)
                selectionSet (.object []) :=
            (VisitSubfieldsFlatCollectsFreshPrefixes_of_selectionSetSemanticsReady_object
              schema resolvers variableValues depth' parentType runtimeType identity
              selectionSet hobject hparentRuntime hready).empty
          have hlookups :
              CollectedGroupsFieldLookupValid schema parentType groups := by
            intro responseName field fields hgroup
            have hgroupMem :
                (responseName, field :: fields) ∈
                  GraphQL.Execution.collectFields schema variableValues parentType
                    (.object runtimeType identity) selectionSet := by
              simpa [groups] using hgroup
            exact
              collectFields_lookupValid_of_selectionSetSemanticsReady_object
                schema variableValues parentType runtimeType identity selectionSet
                hobject hparentRuntime hready field
                (collectedExecutableFields_mem_of_group_mem hgroupMem (by simp))
          have hcompatible :
              CollectedGroupsFieldValidationMergeCompatible groups := by
            simpa [groups] using
              collectFields_fieldCompatible_of_canMerge_lookupValid_object
                schema variableValues parentType parentType runtimeType identity
                selectionSet hmerge hparentRuntime hlookupReady
          have hcollected :
              ExecutionCollectedFieldInvariant
                { window :=
                  { schema := schema
                    resolvers := resolvers
                    variableValues := variableValues
                    depth := depth'
                    parentType := parentType
                    source := .object runtimeType identity
                    selectionSet := selectionSet }
                  initial := .object [] } :=
            executionCollectedFieldInvariant_of_collectedFieldCompatibility
              schema resolvers variableValues depth' parentType
              (.object runtimeType identity) selectionSet
              (by simpa [groups] using hcompatible)
          cases depth' with
          | zero =>
              exact
                ExecutedGroupedSelectionSetAlignedState.of_exact
                  (ExecutedGroupedSelectionSetState.of_collected_groups_collectedAppendInvariant
                    hcollect hflat hcollected hlookups hcompatible
                    (CollectedFieldGroupAppendInvariant.depth_zero schema
                      resolvers variableValues groups))
          | succ completionDepth =>
              have hresponses : CollectedGroupsResponseName groups := by
                rw [← hcollect]
                exact collectFields_responseName schema variableValues parentType
                  (.object runtimeType identity) selectionSet
              have hparents :
                  CollectedGroupsParent parentType groups := by
                rw [← hcollect]
                exact collectFields_parent schema variableValues parentType
                  (.object runtimeType identity) selectionSet
              let happend :
                  CollectedFieldGroupRecursiveAlignedAppendState schema resolvers
                    variableValues completionDepth (.object runtimeType identity)
                    groups :=
                { prefixChildren := by
                    intro responseName field fields prefixTail hgroup hprefix
                      childDepth childRuntime childIdentity hlt _hcontains
                      hincludes
                    have hgroupMem :
                        (responseName, field :: fields) ∈
                          GraphQL.Execution.collectFields schema variableValues
                            parentType (.object runtimeType identity)
                            selectionSet := by
                      simpa [groups] using hgroup
                    have hfieldParent : field.parentType = parentType :=
                      hparents responseName (field :: fields) hgroup field
                        (by simp)
                    have hprefixReady :
                        ∀ candidate, candidate ∈ field :: prefixTail ->
                          NormalForm.selectionSetSemanticsReady schema
                            childRuntime candidate.selectionSet := by
                      intro candidate hcandidate
                      have hcandidateInGroup :
                          candidate ∈ field :: fields := by
                        rcases List.mem_cons.mp hcandidate with hhead | htail
                        · subst candidate
                          simp
                        · exact List.mem_cons_of_mem field
                            (hprefix candidate htail)
                      have hcandidateCollected :
                          candidate ∈
                            collectedExecutableFields
                              (GraphQL.Execution.collectFields schema
                                variableValues parentType
                                (.object runtimeType identity) selectionSet) :=
                        collectedExecutableFields_mem_of_group_mem hgroupMem
                          hcandidateInGroup
                      have hcandidateParent : candidate.parentType = parentType :=
                        hparents responseName (field :: fields) hgroup candidate
                          hcandidateInGroup
                      have hfieldResponse : field.responseName = responseName :=
                        hresponses responseName (field :: fields) hgroup field
                          (by simp)
                      have hcandidateResponse :
                          candidate.responseName = responseName :=
                        hresponses responseName (field :: fields) hgroup
                          candidate hcandidateInGroup
                      have hsameResponse :
                          field.responseName = candidate.responseName := by
                        rw [hfieldResponse, hcandidateResponse]
                      have hfieldName :
                          field.fieldName = candidate.fieldName :=
                        (hcompatible responseName (field :: fields) hgroup
                          field candidate (by simp) hcandidateInGroup
                          hsameResponse).1
                      rcases
                          collectFields_lookupValid_of_selectionSetSemanticsReady_object
                            schema variableValues parentType runtimeType identity
                            selectionSet hobject hparentRuntime hready candidate
                            hcandidateCollected with
                        ⟨candidateDefinition, hcandidateLookupAtParent⟩
                      have hcandidateLookup :
                          schema.lookupField candidate.parentType
                              candidate.fieldName =
                            some candidateDefinition := by
                        simpa [hcandidateParent] using hcandidateLookupAtParent
                      have hcandidateIncludeReturn :
                          schema.typeIncludesObjectBool
                              ((schema.fieldReturnType? candidate.parentType
                                candidate.fieldName).getD candidate.fieldName)
                              childRuntime =
                            true := by
                        simpa [hcandidateParent, hfieldParent, ← hfieldName]
                          using hincludes
                      have hcandidateInclude :
                          schema.typeIncludesObjectBool
                              candidateDefinition.outputType.namedType
                              childRuntime =
                            true := by
                        simpa [Schema.fieldReturnType?, hcandidateLookup] using
                          hcandidateIncludeReturn
                      exact
                        collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
                          schema variableValues parentType runtimeType identity
                          selectionSet hobject hparentRuntime hready candidate
                          hcandidateCollected candidateDefinition hcandidateLookup
                          childRuntime hcandidateInclude
                    have hchildReady :
                        NormalForm.selectionSetSemanticsReady schema childRuntime
                          (GraphQL.Execution.mergedFieldSelectionSet
                            (field :: prefixTail)) :=
                      selectionSetSemanticsReady_mergedFieldSelectionSet schema
                        childRuntime (field :: prefixTail) hprefixReady
                    have hchildMerge :
                        FieldMerge.fieldsInSetCanMerge schema childRuntime
                          (GraphQL.Execution.mergedFieldSelectionSet
                            (field :: prefixTail)) :=
                      collectFields_group_prefix_mergedFieldSelectionSet_canMerge_lookupValid_object
                        schema variableValues parentType parentType runtimeType
                        identity selectionSet responseName field fields
                        prefixTail hlookupReady hmerge hparentRuntime hgroupMem
                        hprefix childRuntime
                    have hchildParentRuntime :
                        ScopedParentRuntimeApplies schema childRuntime
                          ((schema.fieldReturnType? field.parentType
                            field.fieldName).getD field.fieldName) :=
                      ScopedParentRuntimeApplies.of_typeIncludesObjectBool schema
                        childRuntime
                        ((schema.fieldReturnType? field.parentType
                          field.fieldName).getD field.fieldName)
                        hincludes
                    have hchildObject : schema.objectType childRuntime :=
                      ScopedParentRuntimeApplies.runtimeObjectType schema hschema
                        hchildParentRuntime
                    have hchildSelf :
                        ScopedParentRuntimeApplies schema childRuntime
                          childRuntime :=
                      ScopedParentRuntimeApplies.runtimeSelf schema hschema
                        hchildParentRuntime
                    exact
                      ih childDepth (by omega) childRuntime childRuntime
                        childIdentity
                        (GraphQL.Execution.mergedFieldSelectionSet
                          (field :: prefixTail))
                        hschema hchildObject hchildSelf hchildReady hchildMerge
                  absorbs := by
                    intro responseName field fields prefixTail later hgroup
                      hprefix hlater childDepth childRuntime childIdentity _hlt
                      _hcontains
                    exact
                      visitSubfields_absorbs_from_empty_object_prefix schema
                        resolvers variableValues childDepth childRuntime
                        childIdentity
                        (GraphQL.Execution.mergedFieldSelectionSet
                          (field :: prefixTail))
                        later.selectionSet }
              exact
                ExecutedGroupedSelectionSetAlignedState.of_collected_groups_recursiveAlignedAppendState
                  hcollect hflat hcollected hlookups hcompatible happend

end ExecutionUngrouped
end Algorithms

end GraphQL
