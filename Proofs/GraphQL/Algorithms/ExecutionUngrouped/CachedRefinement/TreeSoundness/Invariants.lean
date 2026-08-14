import Proofs.GraphQL.Algorithms.ExecutionUngrouped.CachedRefinement.CollectedSourceSoundness

/-!
Recursive cache-tree invariants.

These predicates describe retained object and list sources at every completion
depth and connect them to collected response-name groups.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionUngrouped

open GraphQL.Execution

mutual
  inductive FieldCacheTreeSound {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> List Selection -> ResolverValue ObjectRef
        -> FieldCacheValue ObjectRef -> Prop where
    | zero selectionSet source value
      : FieldCacheTreeSound schema resolvers variableValues 0 selectionSet source value
    | null fuel selectionSet source
      : FieldCacheTreeSound schema resolvers variableValues (fuel + 1) selectionSet
          source .null
    | scalar fuel selectionSet value
      : FieldCacheTreeSound schema resolvers variableValues (fuel + 1) selectionSet
          (.scalar value) (.scalar value)
    | object fuel selectionSet runtimeType ref fields
      (houtput
        : OutputCacheTreeSoundForGroups schema resolvers variableValues fuel
            (.object runtimeType ref)
            (GraphQL.Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ref) selectionSet)
            (.object (.object runtimeType ref) fields))
      : FieldCacheTreeSound schema resolvers variableValues (fuel + 1) selectionSet
          (.object runtimeType ref) (.object (.object runtimeType ref) fields)
    | cachedList fuel selectionSet sourceValues values
      (hvalues
        : FieldCacheTreesSound schema resolvers variableValues fuel selectionSet
            sourceValues values)
      : FieldCacheTreeSound schema resolvers variableValues (fuel + 1) selectionSet
          (.list sourceValues) (.list (some sourceValues) values)
    | finalList fuel selectionSet sourceValues values
      (hvalues
        : FieldCacheTreesSound schema resolvers variableValues fuel selectionSet
            sourceValues values)
      : FieldCacheTreeSound schema resolvers variableValues (fuel + 1) selectionSet
          (.list sourceValues) (.list none values)

  inductive FieldCacheTreesSound {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> List Selection -> List (ResolverValue ObjectRef)
        -> List (FieldCacheValue ObjectRef) -> Prop where
    | nil : FieldCacheTreesSound schema resolvers variableValues fuel selectionSet [] []
    | cons {source value sourceRest valueRest}
      (hvalue
        : FieldCacheTreeSound schema resolvers variableValues fuel selectionSet
            source value)
      (hrest
        : FieldCacheTreesSound schema resolvers variableValues fuel selectionSet
            sourceRest valueRest)
      : FieldCacheTreesSound schema resolvers variableValues fuel selectionSet
          (source :: sourceRest) (value :: valueRest)

  inductive FieldCacheTreesPrefixSound {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> List Selection -> List (ResolverValue ObjectRef)
        -> List (FieldCacheValue ObjectRef) -> Prop where
    | nil sources
      : FieldCacheTreesPrefixSound schema resolvers variableValues fuel
          selectionSet sources []
    | cons {source value sourceRest valueRest}
      (hvalue
        : FieldCacheTreeSound schema resolvers variableValues fuel selectionSet
            source value)
      (hrest
        : FieldCacheTreesPrefixSound schema resolvers variableValues fuel
            selectionSet sourceRest valueRest)
      : FieldCacheTreesPrefixSound schema resolvers variableValues fuel selectionSet
          (source :: sourceRest) (value :: valueRest)

  inductive OutputCacheTreeSoundForGroups {ObjectRef : Type}
      (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variableValues : VariableValues)
      : Nat -> ResolverValue ObjectRef
        -> List (Name × List ExecutableField) -> FieldCacheValue ObjectRef -> Prop where
    | zero source groups output
      : OutputCacheTreeSoundForGroups schema resolvers variableValues 0 source
          groups output
    | succ fuel source groups output
      (hready : FieldCacheMergeReady output)
      (haligned : ObjectFieldCachesInternallyAligned output)
      (hsource
        : OutputCacheSoundForGroups schema resolvers variableValues source groups output)
      (hobjects
        : ∀ responseName fields previousSource previousFields,
            (responseName, fields) ∈ groups
            -> objectField? responseName output
                = some (.object previousSource previousFields)
            -> FieldCacheTreeSound schema resolvers variableValues fuel
                (GraphQL.Execution.mergedFieldSelectionSet fields)
                previousSource (.object previousSource previousFields))
      (hlists
        : ∀ responseName fields sourceValues previousValues,
            (responseName, fields) ∈ groups
            -> objectField? responseName output
                = some (.list (some sourceValues) previousValues)
            -> FieldCacheTreeSound schema resolvers variableValues fuel
                (GraphQL.Execution.mergedFieldSelectionSet fields)
                (.list sourceValues) (.list (some sourceValues) previousValues))
      : OutputCacheTreeSoundForGroups schema resolvers variableValues (fuel + 1)
          source groups output
end

def FieldCacheContinuationTreeSound {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (selectionSet : List Selection)
    : FieldCacheValue ObjectRef -> Prop
  | .object source fields =>
      FieldCacheTreeSound schema resolvers variableValues fuel selectionSet source
        (.object source fields)
  | .list (some sourceValues) values =>
      FieldCacheTreeSound schema resolvers variableValues fuel selectionSet
        (.list sourceValues) (.list (some sourceValues) values)
  | _ => True

theorem FieldCacheTreeSound.toContinuationTreeSound {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (selectionSet : List Selection) (source : ResolverValue ObjectRef)
    (value : FieldCacheValue ObjectRef)
    : FieldCacheTreeSound schema resolvers variableValues fuel selectionSet source value
      -> FieldCacheContinuationTreeSound schema resolvers variableValues fuel
          selectionSet value := by
  intro hsound
  cases fuel with
  | zero =>
      cases value <;> simp [FieldCacheContinuationTreeSound]
      · exact FieldCacheTreeSound.zero selectionSet _ _
      · rename_i sourceValues? values
        cases sourceValues? <;> simp
        exact FieldCacheTreeSound.zero selectionSet _ _
  | succ fuel =>
      cases hsound <;> simp [FieldCacheContinuationTreeSound]
      case object houtput => exact FieldCacheTreeSound.object _ _ _ _ _ houtput
      case cachedList hvalues =>
        exact FieldCacheTreeSound.cachedList _ _ _ _ hvalues

theorem FieldCacheTreesSound.toPrefixSound {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (selectionSet : List Selection)
    : ∀ {sources : List (ResolverValue ObjectRef)}
        {values : List (FieldCacheValue ObjectRef)},
        FieldCacheTreesSound schema resolvers variableValues fuel selectionSet
          sources values
        -> FieldCacheTreesPrefixSound schema resolvers variableValues fuel
            selectionSet sources values
  | [], [], FieldCacheTreesSound.nil =>
      FieldCacheTreesPrefixSound.nil []
  | _source :: _sourceRest,
    _value :: _valueRest,
    FieldCacheTreesSound.cons hvalue hrest =>
      FieldCacheTreesPrefixSound.cons hvalue
        (FieldCacheTreesSound.toPrefixSound schema resolvers variableValues fuel
          selectionSet hrest)

theorem FieldCacheTreeSound.resultValueOrNull_nonNullCompletion
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (selectionSet : List Selection) (source : ResolverValue ObjectRef)
    (completed : Result (FieldCacheValue ObjectRef))
    : FieldCacheTreeSound schema resolvers variableValues fuel selectionSet source
        (resultValueOrNull completed)
      -> FieldCacheTreeSound schema resolvers variableValues fuel selectionSet source
          (resultValueOrNull (nonNullCompletion completed)) := by
  intro hsound
  cases completed with
  | error errors =>
      simpa [resultValueOrNull, nonNullCompletion] using hsound
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      cases value with
      | null =>
          cases errors <;>
            simpa [resultValueOrNull, nonNullCompletion] using hsound
      | scalar value =>
          simpa [resultValueOrNull, nonNullCompletion] using hsound
      | object source fields =>
          simpa [resultValueOrNull, nonNullCompletion] using hsound
      | list sourceValues? values =>
          simpa [resultValueOrNull, nonNullCompletion] using hsound

theorem OutputCacheTreeSoundForGroups.empty_object {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (fuel : Nat)
    (source objectSource : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    : OutputCacheTreeSoundForGroups schema resolvers variableValues fuel source
        groups (.object objectSource []) := by
  cases fuel with
  | zero => exact OutputCacheTreeSoundForGroups.zero source groups _
  | succ fuel =>
      apply OutputCacheTreeSoundForGroups.succ fuel source groups
      · exact
          FieldCacheMergeReady.object objectSource [] (by
            unfold FieldCacheKeysNodup
            simp) (by
            intro responseName response hresponse
            simp at hresponse)
      · intro responseName previous hprevious
        simp [objectField?, lookupField?] at hprevious
      · exact
          OutputCacheSoundForGroups.empty_object schema resolvers variableValues
            source objectSource groups
      · intro responseName fields previousSource previousFields hgroup hprevious
        simp [objectField?, lookupField?] at hprevious
      · intro responseName fields sourceValues previousValues hgroup hprevious
        simp [objectField?, lookupField?] at hprevious

theorem selection_mem_mergedFieldSelectionSet_of_field_mem
    (field : ExecutableField) (fields : List ExecutableField)
    : field ∈ fields
      -> ∀ selection,
          selection ∈ field.selectionSet
          -> selection ∈ GraphQL.Execution.mergedFieldSelectionSet fields := by
  intro hfield selection hselection
  induction fields with
  | nil => simp at hfield
  | cons head rest ih =>
      simp at hfield
      rcases hfield with rfl | hrest
      · simp [GraphQL.Execution.mergedFieldSelectionSet, hselection]
      · exact
          List.mem_append.mpr (Or.inr (ih hrest))

theorem SelectionSetFieldsWithin.of_selectionSet_subset {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef)
    (fields : List ExecutableField) (universeSet active : List Selection)
    : (∀ selection, selection ∈ active -> selection ∈ universeSet)
      -> SelectionSetFieldsWithin schema variableValues parentType source fields
          universeSet
      -> SelectionSetFieldsWithin schema variableValues parentType source fields
          active := by
  intro hsubset hwithin
  unfold SelectionSetFieldsWithin at hwithin ⊢
  intro selection hselection
  exact hwithin selection (hsubset selection hselection)

theorem collectedGroup_mergedFieldSelectionSet_semanticsReady
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (identity : ObjectRef)
    (selectionSet : List Selection)
    (responseName : Name) (fields : List ExecutableField)
    (first : ExecutableField) (firstDefinition : FieldDefinition)
    (childRuntime : Name)
    : schema.objectType parentType
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType parentType
      -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
      -> FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> (responseName, fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType
              (.object runtimeType identity) selectionSet
      -> first ∈ fields
      -> schema.lookupField first.parentType first.fieldName = some firstDefinition
      -> schema.typeIncludesObjectBool firstDefinition.outputType.namedType childRuntime
          = true
      -> NormalForm.selectionSetSemanticsReady schema childRuntime
          (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hobject hparentRuntime hready hmerge hgroup hfirst hlookupFirst hinclude
  let source : ResolverValue ObjectRef := .object runtimeType identity
  let groups :=
    GraphQL.Execution.collectFields schema variableValues parentType source
      selectionSet
  let flatFields :=
    ExecutionUngroupedUncached.Eager.collectedExecutableFields groups
  have hlookupValid :
      NormalForm.selectionSetLookupValid schema parentType selectionSet :=
    NormalForm.selectionSetLookupValid_of_selectionSetSemanticsReady selectionSet
      hready
  have hparents :
      ExecutionUngroupedUncached.Eager.ExecutableFieldsParent parentType
        flatFields :=
    collectFields_flat_parent schema variableValues parentType source selectionSet
  have hcompatible :
      ExecutionUngroupedUncached.Eager.ExecutableFieldsFieldValidationMergeCompatible
        flatFields :=
    collectFields_flat_fieldCompatible_of_canMerge_lookupValid_object schema
      variableValues parentType parentType runtimeType identity selectionSet
      hmerge hparentRuntime hlookupValid
  have hfirstFlat : first ∈ flatFields :=
    ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_of_group_mem
      hgroup hfirst
  apply
    ExecutionUngroupedUncached.Eager.selectionSetSemanticsReady_mergedFieldSelectionSet
      schema childRuntime fields
  intro candidate hcandidate
  have hcandidateFlat : candidate ∈ flatFields :=
    ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_of_group_mem
      hgroup hcandidate
  have hresponseFirst : first.responseName = responseName :=
    (ExecutionUngroupedUncached.Eager.collectFields_responseName schema
      variableValues parentType source selectionSet) responseName fields hgroup
      first hfirst
  have hresponseCandidate : candidate.responseName = responseName :=
    (ExecutionUngroupedUncached.Eager.collectFields_responseName schema
      variableValues parentType source selectionSet) responseName fields hgroup
      candidate hcandidate
  have hresponse : first.responseName = candidate.responseName := by
    rw [hresponseFirst, hresponseCandidate]
  rcases hcompatible first candidate hfirstFlat hcandidateFlat hresponse with
    ⟨hfieldName, _harguments⟩
  rcases
      collectFields_flat_lookupValid_of_selectionSetSemanticsReady_object schema
        variableValues parentType runtimeType identity selectionSet hobject
        hparentRuntime hready candidate hcandidateFlat with
    ⟨candidateDefinition, hlookupCandidate⟩
  have hparentFirst : first.parentType = parentType :=
    hparents first hfirstFlat
  have hparentCandidate : candidate.parentType = parentType :=
    hparents candidate hcandidateFlat
  have hlookupCandidateAtFirst :
      schema.lookupField first.parentType first.fieldName
        = some candidateDefinition := by
    rw [hparentFirst, hfieldName]
    rw [hparentCandidate] at hlookupCandidate
    exact hlookupCandidate
  rw [hlookupFirst] at hlookupCandidateAtFirst
  injection hlookupCandidateAtFirst with hdefinition
  subst candidateDefinition
  exact
    collectFields_flat_childSemanticsReady_of_selectionSetSemanticsReady_object
      schema variableValues parentType runtimeType identity selectionSet hobject
      hparentRuntime hready candidate hcandidateFlat firstDefinition
      hlookupCandidate childRuntime hinclude

theorem collectedGroup_mergedFieldSelectionSet_canMerge
    {ObjectRef : Type}
    (schema : Schema) (variableValues : VariableValues)
    (parentType runtimeType : Name) (identity : ObjectRef)
    (selectionSet : List Selection)
    (responseName : Name) (fields : List ExecutableField)
    : FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      -> ExecutionUngroupedUncached.Eager.ScopedParentRuntimeApplies schema
          runtimeType parentType
      -> NormalForm.selectionSetLookupValid schema parentType selectionSet
      -> (responseName, fields)
          ∈ GraphQL.Execution.collectFields schema variableValues parentType
              (.object runtimeType identity) selectionSet
      -> ∀ objectType,
          FieldMerge.fieldsInSetCanMerge schema objectType
            (GraphQL.Execution.mergedFieldSelectionSet fields) := by
  intro hmerge hparentRuntime hlookupValid hgroup objectType
  apply
    FieldMerge.fieldsInSetCanMerge_mergedFieldSelectionSet_of_pairwise schema
      objectType fields
  intro first hfirst later hlater
  apply
    collectFields_flat_pair_selectionSets_canMerge_of_canMerge_lookupValid_object
      schema variableValues parentType parentType runtimeType identity selectionSet
      hmerge hparentRuntime hlookupValid first
  · exact
      ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_of_group_mem
        hgroup hfirst
  · exact
      ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_of_group_mem
        hgroup hlater
  · have hresponses :=
      ExecutionUngroupedUncached.Eager.collectFields_responseName schema
        variableValues parentType (.object runtimeType identity) selectionSet
    rw [hresponses responseName fields hgroup first hfirst,
      hresponses responseName fields hgroup later hlater]

theorem collectedExecutableFields_mem_exists_group
    (groups : List (Name × List ExecutableField)) (field : ExecutableField)
    : field ∈ ExecutionUngroupedUncached.Eager.collectedExecutableFields groups
      -> ∃ responseName fields, (responseName, fields) ∈ groups ∧ field ∈ fields := by
  intro hfield
  induction groups with
  | nil =>
      simp [ExecutionUngroupedUncached.Eager.collectedExecutableFields] at hfield
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      simp [ExecutionUngroupedUncached.Eager.collectedExecutableFields] at hfield
      rcases hfield with hfield | hfield
      · exact ⟨responseName, fields, by simp, hfield⟩
      · rcases ih hfield with ⟨targetName, targetFields, hgroup, htarget⟩
        exact ⟨targetName, targetFields, by simp [hgroup], htarget⟩

theorem OutputCacheSoundForGroups.to_flat {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (output : FieldCacheValue ObjectRef)
    : ExecutionUngroupedUncached.Eager.CollectedGroupsResponseName groups
      -> OutputCacheSoundForGroups schema resolvers variableValues source groups output
      -> OutputCacheSoundForFields schema resolvers variableValues source
          (ExecutionUngroupedUncached.Eager.collectedExecutableFields groups)
          output := by
  intro hresponses hsound field fieldDefinition previous hfield hprevious hlookup
  rcases collectedExecutableFields_mem_exists_group groups field hfield with
    ⟨responseName, fields, hgroup, hfield⟩
  have hresponse : field.responseName = responseName :=
    hresponses responseName fields hgroup field hfield
  exact
    hsound responseName fields field fieldDefinition previous hgroup hfield
      (by simpa [hresponse] using hprevious) hlookup

theorem OutputCacheSoundForFields.to_groups {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues)
    (source : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (output : FieldCacheValue ObjectRef)
    : ExecutionUngroupedUncached.Eager.CollectedGroupsResponseName groups
      -> OutputCacheSoundForFields schema resolvers variableValues source
          (ExecutionUngroupedUncached.Eager.collectedExecutableFields groups)
          output
      -> OutputCacheSoundForGroups schema resolvers variableValues source groups
          output := by
  intro hresponses hsound responseName fields field fieldDefinition previous hgroup hfield
    hprevious hlookup
  have hflat :
      field ∈ ExecutionUngroupedUncached.Eager.collectedExecutableFields groups :=
    ExecutionUngroupedUncached.Eager.collectedExecutableFields_mem_of_group_mem
      hgroup hfield
  have hresponse : field.responseName = responseName :=
    hresponses responseName fields hgroup field hfield
  exact
    hsound field fieldDefinition previous hflat
      (by simpa [hresponse] using hprevious) hlookup

theorem objectField?_mergeResponseFieldIntoObject_self_of_absorbs
    {ObjectRef : Type} (objectSource : ResolverValue ObjectRef)
    (responseName : Name) (incoming : FieldCacheValue ObjectRef)
    (fields : List (Name × FieldCacheValue ObjectRef))
    : (∀ previous,
        lookupField? responseName fields = some previous
        -> FieldCacheAbsorbs previous incoming)
      -> objectField? responseName
            (mergeResponseFieldIntoObject responseName incoming
              (.object objectSource fields))
          = some incoming := by
  intro habsorbs
  simp only [mergeResponseFieldIntoObject, objectField?]
  rw [lookupField?_mergeResponseField_self]
  cases hprevious : lookupField? responseName fields with
  | none => simp
  | some previous =>
      simp
      exact habsorbs previous hprevious

theorem PairKeysNodup.value_eq_of_mem {α : Type} (responseName : Name) (first second : α)
    : ∀ pairs : List (Name × α),
        ExecutionUngroupedUncached.Eager.PairKeysNodup pairs
        -> (responseName, first) ∈ pairs
        -> (responseName, second) ∈ pairs
        -> first = second
  | [], _hnodup, hfirst, _hsecond => by simp at hfirst
  | (headName, headValue) :: rest, hnodup, hfirst, hsecond => by
      have hrestNodup :=
        ExecutionUngroupedUncached.Eager.PairKeysNodup.tail hnodup
      simp at hfirst hsecond
      rcases hfirst with hfirst | hfirst
      · rcases hfirst with ⟨hname, hvalue⟩
        subst headName
        subst headValue
        rcases hsecond with hsecond | hsecond
        · rcases hsecond with ⟨_hname, hvalue⟩
          exact hvalue.symm
        · have hnameMem : responseName ∈ rest.map Prod.fst := by
            exact List.mem_map.mpr ⟨(responseName, second), hsecond, rfl⟩
          exact
            (ExecutionUngroupedUncached.Eager.PairKeysNodup.head_not_mem_tail
              hnodup hnameMem).elim
      · rcases hsecond with hsecond | hsecond
        · rcases hsecond with ⟨hname, _hvalue⟩
          subst headName
          have hnameMem : responseName ∈ rest.map Prod.fst := by
            exact List.mem_map.mpr ⟨(responseName, first), hfirst, rfl⟩
          exact
            (ExecutionUngroupedUncached.Eager.PairKeysNodup.head_not_mem_tail
              hnodup hnameMem).elim
        · exact
            PairKeysNodup.value_eq_of_mem responseName first second rest hrestNodup
              hfirst hsecond

theorem OutputCacheTreeSoundForGroups.merge_field {ObjectRef : Type}
    (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source objectSource : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (outputFields : List (Name × FieldCacheValue ObjectRef))
    (responseName : Name) (fields : List ExecutableField)
    (incoming : FieldCacheValue ObjectRef)
    : ExecutionUngroupedUncached.Eager.PairKeysNodup groups
      -> (responseName, fields) ∈ groups
      -> OutputCacheTreeSoundForGroups schema resolvers variableValues
          (completionFuel + 1) source groups (.object objectSource outputFields)
      -> FieldCacheContinuationTreeSound schema resolvers variableValues
          completionFuel (GraphQL.Execution.mergedFieldSelectionSet fields) incoming
      -> (∀ previous,
            objectField? responseName (.object objectSource outputFields) = some previous
            -> FieldCacheAbsorbs previous incoming)
      -> FieldCacheMergeReady
          (mergeResponseFieldIntoObject responseName incoming
            (.object objectSource outputFields))
      -> ObjectFieldCachesInternallyAligned
          (mergeResponseFieldIntoObject responseName incoming
            (.object objectSource outputFields))
      -> OutputCacheSoundForGroups schema resolvers variableValues source groups
          (mergeResponseFieldIntoObject responseName incoming
            (.object objectSource outputFields))
      -> OutputCacheTreeSoundForGroups schema resolvers variableValues
          (completionFuel + 1) source groups
          (mergeResponseFieldIntoObject responseName incoming
            (.object objectSource outputFields)) := by
  intro hgroupsNodup hgroup htree hincoming habsorbs hready haligned hsource
  cases htree with
  | succ _ _ _ _ _ _ _ hobjects hlists =>
      apply OutputCacheTreeSoundForGroups.succ completionFuel source groups
        (mergeResponseFieldIntoObject responseName incoming
          (.object objectSource outputFields)) hready haligned hsource
      · intro targetName targetFields previousSource previousFields htarget
          hprevious
        by_cases hname : targetName = responseName
        · subst targetName
          have hfields : targetFields = fields :=
            PairKeysNodup.value_eq_of_mem responseName targetFields fields groups
              hgroupsNodup htarget hgroup
          subst targetFields
          have hself :=
            objectField?_mergeResponseFieldIntoObject_self_of_absorbs objectSource
              responseName incoming outputFields habsorbs
          rw [hself] at hprevious
          injection hprevious with hincomingEq
          subst incoming
          simpa [FieldCacheContinuationTreeSound] using hincoming
        · exact hobjects targetName targetFields previousSource previousFields
            htarget (by
              simpa [mergeResponseFieldIntoObject, objectField?] using
                (show
                  lookupField? targetName outputFields
                    = some (.object previousSource previousFields) by
                  rw [← lookupField?_mergeResponseField_other targetName
                    responseName incoming hname]
                  simpa [mergeResponseFieldIntoObject, objectField?] using hprevious))
      · intro targetName targetFields sourceValues previousValues htarget
          hprevious
        by_cases hname : targetName = responseName
        · subst targetName
          have hfields : targetFields = fields :=
            PairKeysNodup.value_eq_of_mem responseName targetFields fields groups
              hgroupsNodup htarget hgroup
          subst targetFields
          have hself :=
            objectField?_mergeResponseFieldIntoObject_self_of_absorbs objectSource
              responseName incoming outputFields habsorbs
          rw [hself] at hprevious
          injection hprevious with hincomingEq
          subst incoming
          simpa [FieldCacheContinuationTreeSound] using hincoming
        · exact
            hlists targetName targetFields sourceValues previousValues htarget (by
              simpa [mergeResponseFieldIntoObject, objectField?] using
                (show
                  lookupField? targetName outputFields
                    = some (.list (some sourceValues) previousValues) by
                  rw [← lookupField?_mergeResponseField_other targetName
                    responseName incoming hname]
                  simpa [mergeResponseFieldIntoObject, objectField?] using hprevious))

theorem executeField_output_of_completeValue_and_previousCacheSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef)) (field : ExecutableField)
    (hcomplete
      : ∀ fieldType selectionSet value previous?,
          outputResult FieldCacheValue.output
            (completeValue schema resolvers variableValues completionFuel fieldType
              selectionSet value previous?)
          = ExecutionUngroupedUncached.completeValue schema resolvers variableValues
              completionFuel fieldType selectionSet value
              (previous?.map FieldCacheValue.output))
    (hsound
      : ∀ fieldDefinition previous,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          -> previous? = some previous
          -> PreviousCacheSound schema resolvers variableValues source fieldDefinition
              field previous)
    : outputResult FieldCacheValue.output
        (executeField schema resolvers variableValues completionFuel source
          previous? field)
      = ExecutionUngroupedUncached.executeField schema resolvers variableValues
          completionFuel source (previous?.map FieldCacheValue.output) field := by
  unfold executeField ExecutionUngroupedUncached.executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [outputResult]
  | some fieldDefinition =>
      cases previous? with
      | none =>
          cases hresolve
                : resolveFieldValue schema resolvers variableValues fieldDefinition
                    field.parentType field.fieldName field.arguments source with
          | none =>
              simp [hresolve, handleFieldError_output,
                ExecutionUngroupedUncached.reusablePreviousValue?]
          | some resolved =>
              simp [hresolve, hcomplete,
                ExecutionUngroupedUncached.reusablePreviousValue?]
      | some previous =>
          cases hreuse
                : reusablePreviousValue? schema fieldDefinition.outputType previous with
          | some reusable =>
              have hreuseOut :=
                reusablePreviousValue?_output schema fieldDefinition.outputType
                  previous reusable hreuse
              simp [hreuse, hreuseOut, outputResult]
          | none =>
              have hsoundPrev := hsound fieldDefinition previous hlookup rfl hreuse
              rcases hsoundPrev with ⟨hreuseOut, hresolve⟩
              cases previous with
              | null =>
                  contradiction
              | scalar value =>
                  contradiction
              | object previousSource fields =>
                  have hreuseOut' :
                      ExecutionUngroupedUncached.reusablePreviousValue? schema
                          fieldDefinition.outputType
                          (some (ResponseValue.object (outputFields fields)))
                        =
                        none := by
                    simpa using hreuseOut
                  have hresolve' :
                      resolveFieldValue schema resolvers variableValues fieldDefinition
                          field.parentType field.fieldName field.arguments source
                        =
                        some previousSource := by
                    simpa using hresolve
                  simp [hreuseOut', hresolve']
                  rw [hreuse]
                  exact
                    hcomplete fieldDefinition.outputType field.selectionSet
                      previousSource
                      (some (FieldCacheValue.object previousSource fields))
              | list sourceValues? values =>
                  cases sourceValues? with
                  | none =>
                      contradiction
                  | some sourceValues =>
                      have hreuseOut' :
                          ExecutionUngroupedUncached.reusablePreviousValue? schema
                              fieldDefinition.outputType
                              (some (ResponseValue.list (outputValues values)))
                            =
                            none := by
                        simpa using hreuseOut
                      have hresolve' :
                          resolveFieldValue schema resolvers variableValues fieldDefinition
                              field.parentType field.fieldName field.arguments source
                            =
                            some (ResolverValue.list sourceValues) := by
                        simpa using hresolve
                      simp [hreuseOut', hresolve']
                      rw [hreuse]
                      exact
                        hcomplete fieldDefinition.outputType field.selectionSet
                          (ResolverValue.list sourceValues)
                          (some (FieldCacheValue.list (some sourceValues) values))

theorem executeField_output_of_completeValue_and_fieldPreviousCacheSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef)) (field : ExecutableField)
    (hcomplete
      : ∀ fieldType selectionSet value previous?,
          outputResult FieldCacheValue.output
            (completeValue schema resolvers variableValues completionFuel fieldType
              selectionSet value previous?)
          = ExecutionUngroupedUncached.completeValue schema resolvers variableValues
              completionFuel fieldType selectionSet value
              (previous?.map FieldCacheValue.output))
    (hsound
      : FieldPreviousCacheSound schema resolvers variableValues source previous? field)
    : outputResult FieldCacheValue.output
        (executeField schema resolvers variableValues completionFuel source
          previous? field)
      = ExecutionUngroupedUncached.executeField schema resolvers variableValues
          completionFuel source (previous?.map FieldCacheValue.output) field :=
  executeField_output_of_completeValue_and_previousCacheSound schema resolvers
    variableValues completionFuel source previous? field hcomplete hsound

theorem executeField_output_of_completionCacheSound
    {ObjectRef : Type} (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variableValues : VariableValues) (completionFuel : Nat)
    (source : ResolverValue ObjectRef)
    (previous? : Option (FieldCacheValue ObjectRef)) (field : ExecutableField)
    (hfresh
      : ∀ fieldDefinition resolved,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          -> resolveFieldValue schema resolvers variableValues fieldDefinition
                field.parentType field.fieldName field.arguments source
              = some resolved
          -> CompletionCacheSound schema resolvers variableValues
              completionFuel fieldDefinition.outputType field.selectionSet resolved none)
    (hprevious
      : ∀ fieldDefinition previous,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          -> previous? = some previous
          -> FieldPreviousCacheContinuationSound schema resolvers variableValues
              completionFuel source fieldDefinition field previous)
    : outputResult FieldCacheValue.output
        (executeField schema resolvers variableValues completionFuel source
          previous? field)
      = ExecutionUngroupedUncached.executeField schema resolvers variableValues
          completionFuel source (previous?.map FieldCacheValue.output) field := by
  unfold executeField ExecutionUngroupedUncached.executeField
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [outputResult]
  | some fieldDefinition =>
      cases previous? with
      | none =>
          cases hresolve
                : resolveFieldValue schema resolvers variableValues fieldDefinition
                    field.parentType field.fieldName field.arguments source with
          | none =>
              simp [hresolve, handleFieldError_output,
                ExecutionUngroupedUncached.reusablePreviousValue?]
          | some resolved =>
              have hcompletion :=
                hfresh fieldDefinition resolved hlookup hresolve
              simpa [CompletionCacheSound, hresolve,
                ExecutionUngroupedUncached.reusablePreviousValue?] using
                hcompletion
      | some previous =>
          have hcontinuation := hprevious fieldDefinition previous hlookup rfl
          cases hreuse
                : reusablePreviousValue? schema fieldDefinition.outputType previous with
          | some reusable =>
              have hreuseOut :=
                reusablePreviousValue?_output schema fieldDefinition.outputType
                  previous reusable hreuse
              simp [hreuse, hreuseOut, outputResult]
          | none =>
              have hsoundPrev := hcontinuation.1 hreuse
              rcases hsoundPrev with ⟨hreuseOut, hresolve⟩
              cases previous with
              | null =>
                  contradiction
              | scalar value =>
                  contradiction
              | object previousSource fields =>
                  have hreuseOut' :
                      ExecutionUngroupedUncached.reusablePreviousValue? schema
                          fieldDefinition.outputType
                          (some (ResponseValue.object (outputFields fields)))
                        = none := by
                    simpa using hreuseOut
                  have hresolve' :
                      resolveFieldValue schema resolvers variableValues fieldDefinition
                          field.parentType field.fieldName field.arguments source
                        = some previousSource := by
                    simpa using hresolve
                  have hcompletion :
                      outputResult FieldCacheValue.output
                          (completeValue schema resolvers variableValues completionFuel
                            fieldDefinition.outputType field.selectionSet
                            previousSource
                            (some (FieldCacheValue.object previousSource fields)))
                        = ExecutionUngroupedUncached.completeValue schema resolvers
                            variableValues completionFuel fieldDefinition.outputType
                            field.selectionSet previousSource
                            (some (ResponseValue.object (outputFields fields))) := by
                    exact hcontinuation.2
                  simp [hreuseOut', hresolve']
                  rw [hreuse]
                  exact hcompletion
              | list sourceValues? values =>
                  cases sourceValues? with
                  | none =>
                      contradiction
                  | some sourceValues =>
                      have hreuseOut' :
                          ExecutionUngroupedUncached.reusablePreviousValue? schema
                              fieldDefinition.outputType
                              (some (ResponseValue.list (outputValues values)))
                            = none := by
                        simpa using hreuseOut
                      have hresolve' :
                          resolveFieldValue schema resolvers variableValues fieldDefinition
                              field.parentType field.fieldName field.arguments source
                            = some (ResolverValue.list sourceValues) := by
                        simpa using hresolve
                      have hcompletion :
                          outputResult FieldCacheValue.output
                              (completeValue schema resolvers variableValues
                                completionFuel fieldDefinition.outputType
                                field.selectionSet (.list sourceValues)
                                (some
                                  (FieldCacheValue.list (some sourceValues) values)))
                            = ExecutionUngroupedUncached.completeValue schema
                                resolvers variableValues completionFuel
                                fieldDefinition.outputType field.selectionSet
                                (.list sourceValues)
                                (some (ResponseValue.list (outputValues values))) := by
                        exact hcontinuation.2
                      simp [hreuseOut', hresolve']
                      rw [hreuse]
                      exact hcompletion

end ExecutionUngrouped
end Algorithms

end GraphQL
