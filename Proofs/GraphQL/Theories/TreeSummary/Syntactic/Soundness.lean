import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Coverage
import Proofs.GraphQL.Theories.TreeSummary.Soundness

/-! Direct execution soundness for the fast Syntactic tree-summary backend. -/

namespace GraphQL
namespace TreeSummary
namespace Syntactic

open GraphQL.Execution
open GraphQL.AnnotatedExecution
open GraphQL.ConditionTree
open GraphQL.ConditionTree.Termination
open GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
open TreeSummary.Measure

universe u v

private def GroupsFieldsValid (schema : Schema)
    (variableDefinitions : List VariableDefinition)
    (groups : List CollectedFieldGroup) : Prop :=
  ∀ group, group ∈ groups -> group.FieldsValid schema variableDefinitions

theorem Soundness.singleFieldResult_sound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (variableValues : VariableValues)
    (soundness : Soundness concrete abstract schema variableValues)
    (parentType responseName : Name) (field : ExecutableField)
    (definition : FieldDefinition)
    (completed : Result AnnotatedResponseValue)
    (groups : List CollectedFieldGroup) (traversal : Traversal)
    (hlookup : schema.lookupField parentType field.fieldName = some definition)
    (harguments : (field.arguments.map Argument.name).Nodup)
    (hnonempty : groups ≠ [])
    (hconditions : conditionsAllowGroupsAt variableValues parentType groups)
    (hmatch : groupsRepresentField groups field)
    (hdefinitions : ∀ group, group ∈ groups ->
      group.FieldDefinitionsCompatible schema)
    (hcompleted
      : soundness.approximates (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizeCollectedChildren abstract schema traversal groups) completed))
    : soundness.approximates
        (foldAnnotatedResponseFieldsResult concrete
          (singleAnnotatedResponseFieldResult schema variableValues definition
            parentType responseName field completed))
        (summarizeCollectedGroups abstract schema traversal groups) := by
  cases completed with
  | error errors => exact soundness.toSoundnessCore.empty_sound_any _
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      have hcompleted' :
          soundness.approximates (foldAnnotatedResponseValue concrete value)
            (foldChildSummaryForValue abstract
              (foldChildSummaries abstract
                (summarizedChildren abstract schema traversal) groups) value) := by
        rw [foldChildSummaries_eq_summarizeCollectedChildren]
        simpa [foldAnnotatedResponseValueResult,
          foldChildSummaryForValueResult] using hcompleted
      have hfield := soundness.field_sound parentType field definition value
        (foldAnnotatedResponseValue concrete value) groups
        (summarizedChildren abstract schema traversal)
        hnonempty hmatch hconditions hdefinitions harguments hlookup hcompleted'
      rw [foldFieldGroups_eq_summarizeCollectedGroups] at hfield
      simpa [singleAnnotatedResponseFieldResult,
        resolvedFieldProvenance,
        foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields,
        soundness.concreteLawful.combine_empty] using hfield

-- The sole execution-induction argument. Analyses instantiate `Soundness`; they do not
-- recurse over resolvers, completion, list bubbling, or response-name grouping.
private theorem annotatedResponseExecution_related_all
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (variableDefinitions : List VariableDefinition)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (summaryVariableValues : VariableValues)
    (hsummaryValues : BooleanValuesMatchRuntime variableValues summaryVariableValues)
    (soundness : Soundness concrete abstract schema variableValues)
    (traversal : Traversal)
    (htraversal : traversal.ExecutionComplete schema variableValues)
    (htraversalRuntime
      : traversal
        = Traversal.withRuntimeBooleanDefaults variableValues summaryVariableValues)
    : (forall fuel parentType source executionGroups,
        forall runtimeType (ref : ObjectRef) availableGroups,
          source = .object runtimeType ref
          -> parentType = runtimeType
          -> NormalForm.executableGroupsWellFormed executionGroups
          -> NormalForm.executableGroupNamesNodup executionGroups
          -> ExecutableGroupsValid schema parentType executionGroups
          -> inheritedConditionsAllowGroups variableValues availableGroups
          -> groupsCoverFields schema variableValues parentType runtimeType
              (.object runtimeType ref) availableGroups
              (flattenExecutableFieldGroups executionGroups)
          -> groupsRepresentFields schema variableValues parentType runtimeType
              (.object runtimeType ref) availableGroups
              (flattenExecutableFieldGroups executionGroups)
          -> GroupsFieldsValid schema variableDefinitions availableGroups
          -> soundness.approximates
              (foldAnnotatedResponseFieldsResult concrete
                (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                  parentType source executionGroups))
              (summarizeCollectedGroups abstract schema traversal availableGroups))
      ∧ (forall fuel parentType source responseName fields,
          forall runtimeType (ref : ObjectRef) groups,
            source = .object runtimeType ref
            -> parentType = runtimeType
            -> fields ≠ []
            -> ExecutableFieldGroupValid schema parentType fields
            -> groups ≠ []
            -> inheritedConditionsAllowGroups variableValues groups
            -> conditionsAllowGroupsAt variableValues runtimeType groups
            -> groupsCoverFields schema variableValues parentType runtimeType
                (.object runtimeType ref) groups
                (fields.map fun field => (responseName, field))
            -> groupsRepresentFields schema variableValues parentType runtimeType
              (.object runtimeType ref) groups
              (fields.map fun field => (responseName, field))
            -> GroupsFieldsValid schema variableDefinitions groups
            -> soundness.approximates
                (foldAnnotatedResponseFieldsResult concrete
                  (executeQueryAnnotatedField schema resolvers variableValues fuel
                    parentType source responseName fields))
                (summarizeCollectedGroups abstract schema traversal groups))
      ∧ (forall fuel fieldType fields value,
          forall runtimeType (ref : ObjectRef) responseName fieldName definition groups,
            fieldType.namedType = definition.outputType.namedType
            -> schema.lookupField runtimeType fieldName = some definition
            -> (∃ field, field ∈ fields ∧ field.fieldName = fieldName)
            -> fields ≠ []
            -> ExecutableFieldGroupValid schema runtimeType fields
            -> groups ≠ []
            -> inheritedConditionsAllowGroups variableValues groups
            -> conditionsAllowGroupsAt variableValues runtimeType groups
            -> groupsCoverFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups
                (fields.map fun field => (responseName, field))
            -> groupsRepresentFields schema variableValues runtimeType runtimeType
              (.object runtimeType ref) groups
              (fields.map fun field => (responseName, field))
            -> GroupsFieldsValid schema variableDefinitions groups
            -> soundness.approximates
                (foldAnnotatedResponseValueResult concrete
                  (completeAnnotatedResponseValue schema resolvers variableValues fuel
                    fieldType fields value))
                (foldChildSummaryForValueResult abstract
                  (summarizeCollectedChildren abstract schema traversal groups)
                  (completeAnnotatedResponseValue schema resolvers variableValues fuel
                    fieldType fields value)))
      ∧ (forall fuel itemType fields values,
          forall runtimeType (ref : ObjectRef) responseName fieldName definition groups,
            itemType.namedType = definition.outputType.namedType
            -> schema.lookupField runtimeType fieldName = some definition
            -> (∃ field, field ∈ fields ∧ field.fieldName = fieldName)
            -> fields ≠ []
            -> ExecutableFieldGroupValid schema runtimeType fields
            -> groups ≠ []
            -> inheritedConditionsAllowGroups variableValues groups
            -> conditionsAllowGroupsAt variableValues runtimeType groups
            -> groupsCoverFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups
                (fields.map fun field => (responseName, field))
            -> groupsRepresentFields schema variableValues runtimeType runtimeType
              (.object runtimeType ref) groups
              (fields.map fun field => (responseName, field))
            -> GroupsFieldsValid schema variableDefinitions groups
            -> soundness.approximates
                (foldAnnotatedResponseValuesResult concrete
                  (completeAnnotatedResponseValueList schema resolvers variableValues fuel
                    itemType fields values))
                (foldChildSummaryForValuesResult abstract
                  (summarizeCollectedChildren abstract schema traversal groups)
                  (completeAnnotatedResponseValueList schema resolvers variableValues
                    fuel itemType fields values))) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  case case1 =>
    intro fuel parentType source runtimeType ref availableGroups _hsource _hparents
      _hwellFormed _hnodup _hvalid _hinherited _hcover _hrepresent _hdefinitions
    simpa [executeQueryAnnotatedCollectedFields,
      foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields] using
      soundness.toSoundnessCore.empty_sound_any
        (summarizeCollectedGroups abstract schema traversal availableGroups)
  case case2 =>
    intro fuel parentType source responseName fields rest field_ih tail_ih
      runtimeType ref availableGroups hsource hparents hwellFormed hnodup
      hvalid hinherited hcover hrepresent hdefinitions
    subst source
    subst parentType
    have hgroupWellFormed :=
      hwellFormed (responseName, fields) (by simp)
    have hgroupValid := hvalid responseName fields (by simp)
    let activeGroups :=
      activeGroupsWithResponseName variableValues runtimeType responseName
        availableGroups
    have hfieldsCover :
        groupsCoverFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) availableGroups
          (fields.map fun field => (responseName, field)) := by
      intro candidate hcandidate
      apply hcover candidate
      simp [flattenExecutableFieldGroups, hcandidate]
    have hactiveInherited :
        inheritedConditionsAllowGroups variableValues activeGroups := by
      exact inheritedConditionsAllowGroups_filter variableValues availableGroups
        (fun group =>
          group.responseName == responseName
            && group.condition.allows variableValues runtimeType)
        hinherited
    have hactiveConditions :
        conditionsAllowGroupsAt variableValues runtimeType activeGroups :=
      activeGroupsWithResponseName_conditionAllows variableValues runtimeType
        responseName availableGroups
    have hactiveCover :
        groupsCoverFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) activeGroups
          (fields.map fun field => (responseName, field)) := by
      apply groupsCoverFields_activeGroupsWithResponseName schema variableValues
        runtimeType runtimeType responseName ref availableGroups
        (fields.map fun field => (responseName, field))
      · intro candidate hcandidate
        rcases List.mem_map.mp hcandidate with ⟨field, _hfield, rfl⟩
        rfl
      · exact hfieldsCover
    have hactiveNonempty : activeGroups ≠ [] := by
      intro hnil
      rcases hactiveCover (responseName, fields.head hgroupWellFormed)
          (List.mem_map_of_mem (List.head_mem hgroupWellFormed)) with
        ⟨group, hgroup, _hgroupCover⟩
      simp [hnil] at hgroup
    have hactiveRepresent :
        groupsRepresentFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) activeGroups
          (fields.map fun field => (responseName, field)) := by
      intro group hgroup
      have hgroupAvailable : group ∈ availableGroups :=
        (List.mem_filter.mp hgroup).1
      rcases hrepresent group hgroupAvailable with ⟨hnonempty, hselections⟩
      refine ⟨hnonempty, ?_⟩
      intro selection hselection hcondition
      rcases hselections selection hselection hcondition with
        ⟨candidate, hcandidate, hgroupCover, heq⟩
      have hcandidateFiltered :
          candidate ∈
            (flattenExecutableFieldGroups ((responseName, fields) :: rest)).filter
              (fun entry => entry.1 == responseName) := by
        apply List.mem_filter.mpr
        refine ⟨hcandidate, ?_⟩
        have hname := hgroupCover.2.2.1
        have hactiveName : group.responseName = responseName := by
          have := (List.mem_filter.mp hgroup).2
          simp only [Bool.and_eq_true, beq_iff_eq] at this
          exact this.1
        simp [hname, hactiveName]
      have hcandidateHead :
          candidate ∈ fields.map fun field => (responseName, field) := by
        have hcandidateFiltered' :
            candidate ∈
              (ConditionTree.flattenExecutableFieldGroups
                ((responseName, fields) :: rest)).filter
                (fun entry => entry.1 == responseName) := by
          simpa only [ConditionTree.flattenExecutableFieldGroups,
            Execution.FieldGroups.flattenExecutableFieldGroups_eq_flatMap] using
            hcandidateFiltered
        have hfilterEq := Execution.FieldGroups.filter_flattenExecutableFieldGroups_head_eq
          responseName fields rest
          ((Execution.FieldGroups.executableGroupNamesNodup_iff_map_fst_nodup _).mp
            hnodup)
        rw [hfilterEq] at hcandidateFiltered'
        exact hcandidateFiltered'
      exact ⟨candidate, hcandidateHead, hgroupCover, heq⟩
    have hhead := field_ih runtimeType ref activeGroups rfl rfl
      hgroupWellFormed hgroupValid hactiveNonempty
      hactiveInherited hactiveConditions hactiveCover hactiveRepresent (by
        intro group hgroup
        exact hdefinitions group (List.mem_filter.mp hgroup).1)
    have hhead' := soundness.approximates_upward _ _ _ hhead
      (activeGroupsWithResponseName_le abstract soundness.abstractLawful schema
        traversal variableValues runtimeType responseName availableGroups)
    have htail := tail_ih runtimeType ref
      (groupsWithoutResponseName responseName availableGroups) rfl
      rfl
      (NormalForm.GroundTypeNormalization.executableGroupsWellFormed_tail hwellFormed)
      hnodup.2
      (by
        intro tailResponseName tailFields htailGroup
        exact hvalid tailResponseName tailFields (by simp [htailGroup]))
      (by
        exact inheritedConditionsAllowGroups_filter variableValues availableGroups
          (fun group => !(group.responseName == responseName)) hinherited)
      (groupsWithoutResponseName_cover_tail schema variableValues runtimeType
        responseName ref fields rest availableGroups hwellFormed hnodup hcover)
      (by
        intro group hgroup
        have hgroupAvailable := (List.mem_filter.mp hgroup).1
        rcases hrepresent group hgroupAvailable with ⟨hfields, hselections⟩
        refine ⟨hfields, ?_⟩
        intro selection hselection hcondition
        rcases hselections selection hselection hcondition with
          ⟨candidate, hcandidate, hgroupCover, heq⟩
        have hcandidateRest : candidate ∈ flattenExecutableFieldGroups rest := by
          change candidate ∈
            (fields.map fun field => (responseName, field))
              ++ flattenExecutableFieldGroups rest at hcandidate
          rcases List.mem_append.mp hcandidate with hhead | hrest
          · have hheadName : candidate.1 = responseName := by
              rcases List.mem_map.mp hhead with ⟨field, _hfield, rfl⟩
              rfl
            have hgroupNe : group.responseName ≠ responseName := by
              have hfiltered := (List.mem_filter.mp hgroup).2
              intro heq
              simp [heq] at hfiltered
            exact False.elim
              (hgroupNe (hgroupCover.2.2.1.symm.trans hheadName))
          · exact hrest
        exact ⟨candidate, hcandidateRest, hgroupCover, heq⟩)
      (by
        intro group hgroup
        exact hdefinitions group (List.mem_filter.mp hgroup).1)
    rw [executeQueryAnnotatedCollectedFields,
      summarizeCollectedGroups_partition_responseName abstract
        soundness.abstractLawful schema traversal responseName availableGroups]
    exact soundness.toSoundnessCore.combineFieldsResult_sound _ _ _ _ hhead' htail
  case case3 =>
    intro fuel parentType source responseName runtimeType ref groups _hsource _hparents
      hnonempty _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
      _hdefinitions
    exact False.elim (hnonempty rfl)
  case case4 =>
    intro parentType source responseName field rest runtimeType ref groups _hsource _hparents
      _hnonempty _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
      _hdefinitions
    simpa [executeQueryAnnotatedField, foldAnnotatedResponseFieldsResult] using
      soundness.toSoundnessCore.empty_sound_any
        (summarizeCollectedGroups abstract schema traversal groups)
  case case5 =>
    intro parentType source responseName field rest fuel hlookup runtimeType ref groups
      _hsource _hparents _hnonempty _hvalid _hgroups _hinherited _hconditions
      _hcover _hrepresent _hdefinitions
    simpa [executeQueryAnnotatedField, hlookup,
      foldAnnotatedResponseFieldsResult] using
      soundness.toSoundnessCore.empty_sound_any
        (summarizeCollectedGroups abstract schema traversal groups)
  case case6 =>
    intro parentType source responseName field rest fuel definition hlookup hcoerce
      runtimeType ref groups hsource hparents _hnonempty hvalid hgroups
      hinherited hconditions hcover hrepresent hdefinitions
    subst source
    subst parentType
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted :
        soundness.approximates (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizeCollectedChildren abstract schema traversal groups) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact soundness.toSoundnessCore.empty_sound_any _
    have hmatch : groupsRepresentField groups field :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        responseName groups (field :: rest) field (by simp)
        hvalid.mergeCompatible hconditions hrepresent
    have hsingle := soundness.singleFieldResult_sound schema variableValues
      runtimeType responseName field definition completed groups traversal hlookup
      (hvalid.argumentsNodup field (by simp)) hgroups
      hconditions hmatch (fun group hgroup =>
        (hdefinitions group hgroup).definitionsCompatible) hcompleted
    simp only [executeQueryAnnotatedField, hlookup]
    rw [hcoerce]
    exact hsingle
  case case7 =>
    intro parentType source responseName field rest fuel definition hlookup coercedArguments hcoerce
      hresolve runtimeType ref groups hsource hparents _hnonempty hvalid hgroups
      hinherited hconditions hcover hrepresent hdefinitions
    subst source
    subst parentType
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted :
        soundness.approximates (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizeCollectedChildren abstract schema traversal groups) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact soundness.toSoundnessCore.empty_sound_any _
    have hmatch : groupsRepresentField groups field :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        responseName groups (field :: rest) field (by simp)
        hvalid.mergeCompatible hconditions hrepresent
    have hsingle := soundness.singleFieldResult_sound schema variableValues
      runtimeType responseName field definition completed groups traversal hlookup
      (hvalid.argumentsNodup field (by simp)) hgroups
      hconditions hmatch (fun group hgroup =>
        (hdefinitions group hgroup).definitionsCompatible) hcompleted
    simp only [executeQueryAnnotatedField, hlookup, hcoerce]
    rw [hresolve]
    exact hsingle
  case case8 =>
    intro parentType source responseName field rest fuel definition hlookup coercedArguments hcoerce
      resolved hresolve
      complete_ih runtimeType ref groups hsource hparents hnonempty hvalid hgroups
      hinherited hconditions hcover hrepresent hdefinitions
    subst source
    subst parentType
    have hcompleted := complete_ih runtimeType ref responseName field.fieldName
      definition groups rfl
      hlookup
      ⟨field, by simp, rfl⟩
      hnonempty hvalid hgroups hinherited
      hconditions hcover hrepresent hdefinitions
    have hmatch : groupsRepresentField groups field :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        responseName groups (field :: rest) field (by simp)
        hvalid.mergeCompatible hconditions hrepresent
    have hsingle := soundness.singleFieldResult_sound schema variableValues
      runtimeType responseName field definition
      (completeAnnotatedResponseValue schema resolvers variableValues fuel
        definition.outputType (field :: rest) resolved)
      groups traversal hlookup (hvalid.argumentsNodup field (by simp)) hgroups
      hconditions hmatch (fun group hgroup =>
        (hdefinitions group hgroup).definitionsCompatible) hcompleted
    simpa [executeQueryAnnotatedField, hlookup, hcoerce, hresolve] using hsingle
  case case9 =>
    intro fieldType fields value runtimeType ref responseName fieldName definition
      groups _hnamed _hlookup _hwitness _hnonempty _hvalid _hgroups
      _hinherited _hconditions _hcover _hrepresent _hdefinitions
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case10 =>
    intro fuel inner fields value hfuel complete_ih runtimeType ref responseName
      fieldName definition groups hnamed hlookup hwitness hnonempty
      hvalid hgroups hinherited hconditions hcover hrepresent hdefinitions
    have hinner := complete_ih runtimeType ref responseName fieldName definition groups
      (by simpa [TypeRef.namedType] using hnamed) hlookup hwitness hnonempty
      hvalid hgroups hinherited hconditions hcover hrepresent hdefinitions
    simpa [completeAnnotatedResponseValue, hfuel] using
      soundness.toSoundnessCore.completeNonNullResult_sound
        (completeAnnotatedResponseValue schema resolvers variableValues fuel inner fields
          value)
        (summarizeCollectedChildren abstract schema traversal groups) hinner
  case case11 =>
    intro fuel fieldType fields hnotNonNull runtimeType ref responseName fieldName
      definition groups _hnamed _hlookup _hwitness _hnonempty
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent _hdefinitions
    simpa [completeAnnotatedResponseValue, hnotNonNull,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      soundness.empty_sound
  case case12 =>
    intro fuel typeName fields value hcomposite runtimeType ref responseName fieldName
      definition groups _hnamed _hlookup _hwitness _hnonempty
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent _hdefinitions
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case13 =>
    intro fuel typeName fields value hnotComposite runtimeType ref responseName
      fieldName definition groups _hnamed _hlookup _hwitness _hnonempty
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent _hdefinitions
    have hcomposite : (TypeRef.named typeName).isCompositeBool schema = false := by
      cases hvalue : (TypeRef.named typeName).isCompositeBool schema with
      | false => rfl
      | true => exact False.elim (hnotComposite hvalue)
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValue,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      soundness.empty_sound
  case case14 =>
    intro fuel childParentType fields childRuntimeType childRef hinclude childGroups
      child_ih runtimeType ref responseName fieldName definition groups hnamed hlookup
      hwitness hnonempty hvalid hgroups hinherited hconditions hcover
      hrepresent hdefinitions
    have hchildParent :
        childParentType = definition.outputType.namedType := by
      simpa [TypeRef.namedType] using hnamed
    subst childParentType
    let childAvailable :=
      candidateChildGroupsFor schema definition.outputType.namedType childRuntimeType
        traversal groups
    have hchildWellFormed :
        NormalForm.executableGroupsWellFormed childGroups := by
      simpa [childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
        NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
          variableValues childRuntimeType (.object childRuntimeType childRef)
          (Execution.mergedFieldSelectionSet fields)
    have hchildNodup : NormalForm.executableGroupNamesNodup childGroups := by
      simpa [childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
        NormalForm.collectFields_namesNodup schema variableValues childRuntimeType
          (.object childRuntimeType childRef)
          (Execution.mergedFieldSelectionSet fields)
    rcases hwitness with ⟨first, hfirst, hfirstName⟩
    have hlookupFirst :
        schema.lookupField runtimeType first.fieldName = some definition := by
      rw [hfirstName]
      exact hlookup
    rcases hvalid.childrenValid first definition childRuntimeType hfirst hlookupFirst
      hinclude with
      ⟨hchildObject, hchildReady, hchildMerge⟩
    have hchildArguments : selectionSetArgumentsNodup
        (Execution.mergedFieldSelectionSet fields) :=
      selectionSetArgumentsNodup_mergedFieldSelectionSet fields
        hvalid.childArgumentsNodup
    have hchildValid : ExecutableGroupsValid schema childRuntimeType childGroups := by
      have hcollected := collectFields_executableGroupsValid schema variableValues
        childRuntimeType childRef (Execution.mergedFieldSelectionSet fields)
        hschema hchildObject hchildReady hchildMerge hchildArguments
      simpa [childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
        hcollected
    have hchildInherited :
        inheritedConditionsAllowGroups variableValues childAvailable := by
      exact candidateChildGroupsFor_inheritedConditionAllows schema variableValues
        runtimeType definition.outputType.namedType childRuntimeType groups traversal
        hinherited hconditions
    have hchildCover :
        groupsCoverFields schema variableValues childRuntimeType childRuntimeType
          (.object childRuntimeType childRef) childAvailable
          (flattenExecutableFieldGroups childGroups) := by
      exact candidateChildGroupsFor_cover_subfields schema variableValues runtimeType
        runtimeType ref definition.outputType.namedType childRuntimeType responseName
        childRef groups fields traversal htraversal hinclude hinherited hcover
    have hchildRepresent :
        groupsRepresentFields schema variableValues childRuntimeType childRuntimeType
          (.object childRuntimeType childRef) childAvailable
          (flattenExecutableFieldGroups childGroups) := by
      have hpossible :
          (schema.getPossibleTypes definition.outputType.namedType).contains
              childRuntimeType
            = true := by
        simpa [Schema.typeIncludesObjectBool] using hinclude
      simpa [childGroups] using
        candidateChildGroupsFor_represent_subfields schema variableValues runtimeType ref
          definition.outputType.namedType childRuntimeType childRef responseName groups fields
          traversal
          (by rw [htraversalRuntime]; exact hsummaryValues) hpossible hinherited hconditions
          hrepresent
    have hmatch : groupsRepresentField groups first :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        responseName groups fields first hfirst
        hvalid.mergeCompatible hconditions hrepresent
    have hchildDefinitions : GroupsFieldsValid schema variableDefinitions
        childAvailable := by
      intro childGroup hchildGroup
      unfold childAvailable candidateChildGroupsFor at hchildGroup
      rcases List.mem_flatMap.mp hchildGroup with
        ⟨group, hgroup, hchildGroup⟩
      have hrepresentative := representativeMatches_of_groupsRepresentField groups
        first hmatch group hgroup
      have hlookupRepresentative : schema.lookupField runtimeType
          group.representativeField.fieldName = some definition := by
        rw [hrepresentative.1, hfirstName]
        exact hlookup
      have hfieldNames : ∀ field, field ∈ group.fields ->
          field.fieldName = group.representativeField.fieldName := by
        intro field hfield
        have hselection : field.toSelection group.responseName ∈ group.selections := by
          exact List.mem_map.mpr ⟨field, hfield, rfl⟩
        rcases (hrepresent group hgroup).2 _ hselection (hconditions group hgroup) with
          ⟨candidate, hcandidate, _hcover, heq⟩
        rcases List.mem_map.mp hcandidate with
          ⟨candidateField, hcandidateField, rfl⟩
        have hfieldName : field.fieldName = candidateField.fieldName := by
          simp only [ConditionTree.Field.toSelection, Selection.field.injEq] at heq
          exact heq.2.1
        have hcandidateMatches := hvalid.mergeCompatible candidateField first
          hcandidateField hfirst
        exact hfieldName.trans
          (hcandidateMatches.1.trans hrepresentative.1.symm)
      let childTree := group.childTreeWithKnownFalsePruning schema
        definition.outputType.namedType traversal.summaryVariableValues
      have hchildTreeFields : TreeFieldsValid schema variableDefinitions childTree := by
        exact group.childTreeWithKnownFalsePruning_fieldsValid schema variableDefinitions
          runtimeType definition traversal.summaryVariableValues hschema
          (hdefinitions group hgroup)
          (List.contains_iff_mem.mp
            (Bool.and_eq_true_iff.mp (hconditions group hgroup)).1)
          hfieldNames hlookupRepresentative
      unfold candidateChildGroups at hchildGroup
      exact traversedCollectedGroup_fieldsValid schema variableDefinitions
        definition.outputType.namedType group.childInheritedBooleanCondition childTree
        (traversal.atRuntimeType schema childRuntimeType) childGroup hchildTreeFields
        (by simpa [childTree] using hchildGroup)
    have hchild := child_ih childRuntimeType childRef childAvailable rfl
      rfl hchildWellFormed hchildNodup hchildValid hchildInherited hchildCover
      hchildRepresent hchildDefinitions
    have hcandidatesLe :=
      candidateChildGroupsFor_le_summarizeCollectedChildren abstract
        soundness.abstractLawful schema definition.outputType.namedType childRuntimeType
        variableValues summaryVariableValues traversal hsummaryValues htraversalRuntime groups
        (List.contains_iff_mem.mp (by
          simpa [Schema.typeIncludesObjectBool] using hinclude))
        (by
          intro group hgroup
          have hrepresentative := representativeMatches_of_groupsRepresentField groups
            first hmatch group hgroup
          exact lookupField_childParentType_mem_of_condition_allows schema
            variableValues runtimeType group definition
            (hconditions group hgroup) (by
              rw [hrepresentative.1, hfirstName]
              exact hlookup))
    have hchild' := soundness.approximates_upward _ _ _ hchild hcandidatesLe
    cases hresult :
        executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          childRuntimeType (.object childRuntimeType childRef) childGroups with
    | error errors =>
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                childRuntimeType (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .error errors := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          soundness.empty_sound
    | ok completed =>
        rcases completed with ⟨childFields, errors⟩
        rw [hresult] at hchild'
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                childRuntimeType (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .ok (childFields, errors) := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        have hchildFields :
            soundness.approximates (foldAnnotatedResponseFields concrete childFields)
              (summarizeCollectedChildren abstract schema traversal groups) := by
          simpa [foldAnnotatedResponseFieldsResult] using hchild'
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue,
          soundness.abstractLawful.combine_empty] using hchildFields
  case case15 =>
    intro fuel parentType fields childRuntimeType childRef hnotInclude runtimeType ref
      responseName fieldName definition groups _hnamed _hlookup _hwitness
      _hnonempty _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
      _hdefinitions
    have hinclude : schema.typeIncludesObjectBool parentType childRuntimeType = false := by
      cases hvalue : schema.typeIncludesObjectBool parentType childRuntimeType with
      | false => rfl
      | true => exact False.elim (hnotInclude hvalue)
    simpa [completeAnnotatedResponseValue, hinclude,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case16 =>
    intro fuel inner fields values list_ih runtimeType ref responseName fieldName
      definition groups hnamed hlookup hwitness hnonempty hvalid hgroups
      hinherited hconditions hcover hrepresent hdefinitions
    have hlist := list_ih runtimeType ref responseName fieldName definition groups
      (by simpa [TypeRef.namedType] using hnamed) hlookup hwitness hnonempty
      hvalid hgroups hinherited hconditions hcover hrepresent hdefinitions
    cases hresult :
        completeAnnotatedResponseValueList schema resolvers variableValues fuel inner
          fields values with
    | error errors =>
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          soundness.empty_sound
    | ok completed =>
        rcases completed with ⟨completedValues, errors⟩
        rw [hresult] at hlist
        have hvalues :
            soundness.approximates (foldAnnotatedResponseValues concrete completedValues)
              (foldChildSummaryForValues abstract
                (summarizeCollectedChildren abstract schema traversal groups)
                completedValues) := by
          simpa [foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult] using hlist
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValue,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using hvalues
  case case17 =>
    intro fuel typeName fields values runtimeType ref responseName fieldName definition
      groups _hnamed _hlookup _hwitness _hnonempty _hvalid _hgroups
      _hinherited _hconditions _hcover _hrepresent _hdefinitions
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case18 =>
    intro fuel inner fields value hnotNull hnotList runtimeType ref responseName
      fieldName definition groups _hnamed _hlookup _hwitness _hnonempty
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent _hdefinitions
    simpa [completeAnnotatedResponseValue, hnotNull, hnotList,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      soundness.empty_sound
  case case19 =>
    intro fuel itemType fields runtimeType ref responseName fieldName definition
      groups _hnamed _hlookup _hwitness _hnonempty _hvalid _hgroups
      _hinherited _hconditions _hcover _hrepresent _hdefinitions
    simpa [completeAnnotatedResponseValueList,
      foldAnnotatedResponseValuesResult, foldAnnotatedResponseValues,
      foldChildSummaryForValuesResult, foldChildSummaryForValues] using
      soundness.empty_sound
  case case20 =>
    intro fuel itemType fields value values head_ih tail_ih runtimeType ref
      responseName fieldName definition groups hnamed hlookup hwitness hnonempty
      hvalid hgroups hinherited hconditions hcover hrepresent hdefinitions
    have hhead := head_ih runtimeType ref responseName fieldName definition groups
      hnamed hlookup hwitness hnonempty hvalid hgroups hinherited hconditions
      hcover hrepresent hdefinitions
    have htail := tail_ih runtimeType ref responseName fieldName definition groups
      hnamed hlookup hwitness hnonempty hvalid hgroups hinherited hconditions
      hcover hrepresent hdefinitions
    simpa [completeAnnotatedResponseValueList] using
      soundness.toSoundnessCore.combineValuesResult_sound
        (completeAnnotatedResponseValue schema resolvers variableValues fuel itemType
          fields value)
        (completeAnnotatedResponseValueList schema resolvers variableValues fuel itemType
          fields values)
        (summarizeCollectedChildren abstract schema traversal groups) hhead htail

-- Generic execution soundness with a Boolean environment already known to the abstract
-- traversal. The environment must agree with concrete execution wherever it supplies a
-- Boolean value.
theorem Soundness.executeQueryAnnotatedWithFuel_soundUsingVariables
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (operation : Operation)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (summaryVariableValues : VariableValues)
    (hsummaryValues
      : BooleanValuesMatchRuntime
          (coerceVariableValues operation variableValues) summaryVariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (soundness
      : Soundness concrete abstract schema
          (coerceVariableValues operation variableValues))
    : soundness.approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeSelectionSet abstract schema (operation.rootType schema) []
          operation.selectionSet summaryVariableValues) := by
  have hrootObject : schema.objectType (operation.rootType schema) := by
    rw [Validation.operationDefinitionValid_rootType_eq hoperation]
    exact hschema.2.1
  let coercedVariableValues := coerceVariableValues operation variableValues
  let traversal :=
    Traversal.withRuntimeBooleanDefaults coercedVariableValues summaryVariableValues
  have htraversal : traversal.ExecutionComplete schema coercedVariableValues := by
    exact Traversal.withRuntimeBooleanDefaults_executionComplete schema
      coercedVariableValues summaryVariableValues hsummaryValues
  have htraversalRuntime :
      traversal =
        Traversal.withRuntimeBooleanDefaults coercedVariableValues
          summaryVariableValues := rfl
  let tree :=
    ofSelectionSetInScopeWithKnownFalsePruning schema (operation.rootType schema) []
      summaryVariableValues operation.selectionSet
  let availableGroups :=
    traversedCollectedGroups (operation.rootType schema) [] tree
      (traversal.atRuntimeType schema (operation.rootType schema))
  cases hroot : rootSourceAppliesBool schema operation source with
  | false =>
      simpa [executeQueryAnnotatedWithFuel, hroot, foldAnnotatedResponse,
        foldAnnotatedResponseValue] using
        soundness.toSoundnessCore.empty_sound_any
          (summarizeSelectionSet abstract schema (operation.rootType schema) []
            operation.selectionSet summaryVariableValues)
  | true =>
      obtain ⟨runtimeType, ref, rfl, hinclude⟩ :=
        NormalForm.GroundTypeNormalization.rootSourceAppliesBool_true_object
          schema operation source hroot
      have hruntimeType : runtimeType = operation.rootType schema :=
        object_typeIncludesObjectBool_eq_self schema hrootObject hinclude
      subst runtimeType
      let executionGroups :=
        collectFields schema coercedVariableValues (operation.rootType schema)
          (.object (operation.rootType schema) ref) operation.selectionSet
      have hwellFormed : NormalForm.executableGroupsWellFormed executionGroups := by
        exact NormalForm.GroundTypeNormalization.collectFields_wellFormed schema
          coercedVariableValues (operation.rootType schema)
          (.object (operation.rootType schema) ref) operation.selectionSet
      have hnodup : NormalForm.executableGroupNamesNodup executionGroups := by
        exact NormalForm.collectFields_namesNodup schema coercedVariableValues
          (operation.rootType schema) (.object (operation.rootType schema) ref)
          operation.selectionSet
      have hready :
          NormalForm.selectionSetSemanticsReady schema (operation.rootType schema)
            operation.selectionSet :=
        NormalForm.selectionSetSemanticsReady_of_selectionSetValid_object schema
          operation.variableDefinitions (operation.rootType schema) hschema hrootObject
          operation.selectionSet
          (Validation.operationDefinitionValid_selectionSetValid hoperation)
      have hvalid : ExecutableGroupsValid schema (operation.rootType schema)
          executionGroups := by
        have harguments := Execution.selectionSetArgumentsNodup_of_selectionSetValid
          (Validation.operationDefinitionValid_selectionSetValid hoperation)
        exact collectFields_executableGroupsValid schema coercedVariableValues
          (operation.rootType schema) ref operation.selectionSet hschema hrootObject hready
          (Validation.operationDefinitionValid_fieldsInSetCanMerge hoperation) harguments
      have hinherited :
          inheritedConditionsAllowGroups coercedVariableValues availableGroups := by
        intro group hgroup
        have heq := traversedCollectedGroups_inherited (operation.rootType schema) [] tree
          (traversal.atRuntimeType schema (operation.rootType schema)) group hgroup
        simp [heq, booleanConditionAllows]
      have hpossible :
          (schema.getPossibleTypes (operation.rootType schema)).contains
              (operation.rootType schema)
            = true := by
        simpa [Schema.typeIncludesObjectBool] using hinclude
      have hsummary :
          summarizeCollectedGroups abstract schema traversal availableGroups
            = summarizeTreeAtRuntimeType abstract schema
                (operation.rootType schema) [] (operation.rootType schema) tree
                traversal := by
        simpa [availableGroups] using
          summarize_traversedCollectedGroupsAtRuntimeType abstract
            soundness.abstractLawful schema (operation.rootType schema) []
            (operation.rootType schema) tree traversal
      have hrootPossible :
          operation.rootType schema ∈ tree.condition.possibleTypes := by
        have hmem := List.contains_iff_mem.mp hpossible
        have hcondition :
            tree.condition = rootCondition schema (operation.rootType schema) := by
          unfold tree ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning
            ConditionTree.ofSelectionSetInScope
          rw [ConditionTree.Tree.insertSelections_condition]
          rfl
        rw [hcondition]
        simpa [rootCondition] using hmem
      have hsummaryLe :
          soundness.abstractLawful.le
            (summarizeCollectedGroups abstract schema traversal availableGroups)
            (summarizeSelectionSet abstract schema (operation.rootType schema) []
              operation.selectionSet summaryVariableValues) := by
        rw [hsummary]
        subst traversal
        unfold summarizeSelectionSet summarizeConditionTree
        simpa [tree, booleanConditionValues] using
          summarizeTreeAtRuntimeType_le abstract
            soundness.abstractLawful schema (operation.rootType schema) [] tree
            tree.condition.possibleTypes (operation.rootType schema)
            (by
              unfold tree
              exact ConditionTree.ofSelectionSetInScopeWithKnownFalsePruning_branchesCoherent
                schema (operation.rootType schema) [] summaryVariableValues
                operation.selectionSet)
            hrootPossible hrootPossible coercedVariableValues summaryVariableValues
            hsummaryValues
      have hcover :
          groupsCoverFields schema coercedVariableValues (operation.rootType schema)
            (operation.rootType schema) (.object (operation.rootType schema) ref)
            availableGroups (flattenExecutableFieldGroups executionGroups) := by
        exact htraversal (operation.rootType schema) [] operation.selectionSet
          (operation.rootType schema) (operation.rootType schema) ref rfl
          hpossible
      have hrepresent :
          groupsRepresentFields schema coercedVariableValues
            (operation.rootType schema) (operation.rootType schema)
            (.object (operation.rootType schema) ref) availableGroups
            (flattenExecutableFieldGroups executionGroups) := by
        intro group hgroup
        have hshape := traversedCollectedGroup_shape (operation.rootType schema) [] tree
          (traversal.atRuntimeType schema (operation.rootType schema)) group
          (by simpa [availableGroups] using hgroup)
        refine ⟨hshape.1, ?_⟩
        intro selection hselection hcondition
        simpa [tree, executionGroups] using
          traversedCollectedGroup_selection_producesField schema
            coercedVariableValues summaryVariableValues hsummaryValues
            (operation.rootType schema) [] operation.selectionSet
            (operation.rootType schema) (operation.rootType schema) ref
            (traversal.atRuntimeType schema (operation.rootType schema)) group rfl
            hpossible (by simpa [tree, availableGroups] using hgroup) hcondition
            selection hselection
      have htreeFields : TreeFieldsValid schema operation.variableDefinitions tree := by
        unfold tree
        exact ofSelectionSetInScopeWithKnownFalsePruning_fieldsValid schema
          operation.variableDefinitions (operation.rootType schema) []
          summaryVariableValues operation.selectionSet hschema
          (SelectionSetSourceValid.of_selectionSetValid
            (Validation.operationDefinitionValid_selectionSetValid hoperation))
      have hdefinitions : GroupsFieldsValid schema operation.variableDefinitions
          availableGroups := by
        intro group hgroup
        exact traversedCollectedGroup_fieldsValid schema operation.variableDefinitions
          (operation.rootType schema) [] tree
          (traversal.atRuntimeType schema (operation.rootType schema)) group htreeFields
          (by simpa [availableGroups] using hgroup)
      have hrelated :=
        (annotatedResponseExecution_related_all schema hschema
          operation.variableDefinitions resolvers
          coercedVariableValues summaryVariableValues hsummaryValues
          soundness traversal htraversal htraversalRuntime).1 fuel
          (operation.rootType schema) (.object (operation.rootType schema) ref)
          executionGroups (operation.rootType schema) ref availableGroups rfl rfl
          hwellFormed hnodup
          hvalid hinherited hcover hrepresent hdefinitions
      have hrelated' := soundness.approximates_upward _ _ _ hrelated hsummaryLe
      cases hresult
            : executeQueryAnnotatedCollectedFields schema resolvers coercedVariableValues
                fuel (operation.rootType schema)
                (.object (operation.rootType schema) ref) executionGroups with
      | error errors =>
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValue,
            foldAnnotatedResponseFieldsResult] using hrelated'
      | ok completed =>
          rcases completed with ⟨fields, errors⟩
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValue,
            foldAnnotatedResponseFieldsResult] using hrelated'

-- Unknown-variable specialization of the resolved Boolean-environment theorem.
theorem Soundness.executeQueryAnnotatedWithFuel_sound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (operation : Operation)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (soundness
      : Soundness concrete abstract schema
          (coerceVariableValues operation variableValues))
    : soundness.approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperation abstract schema operation) := by
  simpa [summarizeOperation] using
    Soundness.executeQueryAnnotatedWithFuel_soundUsingVariables schema operation
      resolvers variableValues []
      (booleanValuesMatchRuntime_empty
        (coerceVariableValues operation variableValues))
      fuel source hschema hoperation soundness

-- Proof-facing fuel variant used by concrete analyses and by the default-executor
-- theorem below. The public definition module exposes only `AnalysisSound`.
def OperationSoundWithFuel
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}} {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete abstract schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (soundnessFor coercedVariableValues).approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperation abstract schema operation)

-- Proof-facing fuel variant for variable-indexed syntactic algebras. The public
-- definition module exposes only `AnalysisWithVariablesSound`.
def OperationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v}) {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : Prop :=
  SchemaWellFormedness.schemaWellFormed schema
  -> Validation.operationDefinitionValid schema operation
  -> ∀ (ObjectRef : Type) (resolvers : Resolvers ObjectRef)
        (variableValues : VariableValues) (fuel : Nat)
        (source : ResolverValue ObjectRef),
      let coercedVariableValues := Execution.coerceVariableValues operation variableValues
      (soundnessFor coercedVariableValues).approximates
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperationWithVariables algebraFor schema variableValues operation)

theorem operationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v})
    {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationWithVariablesSoundWithFuel algebraFor soundnessFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  have hrelated :=
    Soundness.executeQueryAnnotatedWithFuel_soundUsingVariables schema operation
      resolvers variableValues coercedVariableValues
      (booleanValuesMatchRuntime_self coercedVariableValues) fuel source hschema hoperation
      (soundnessFor coercedVariableValues)
  simpa [summarizeOperationWithVariables, coercedVariableValues] using hrelated

theorem analysisWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v})
    {schema : Schema}
    (soundnessFor : ∀ values, Soundness concrete (algebraFor values) schema values)
    (operation : Operation)
    : AnalysisWithVariablesSound algebraFor soundnessFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  have hsound := operationWithVariablesSoundWithFuel algebraFor soundnessFor
    operation hschema hoperation ObjectRef resolvers variableValues
    (executeQueryFuelBound schema operation) source
  simpa [executeQueryAnnotated] using hsound

-- Generic witness for direct fuel-parameterized syntactic soundness. The soundness
-- provider supplies the local field-group obligation after operation variables are
-- coerced; no comparison with the exact-case summary is used.
theorem operationSoundWithFuel
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    {schema : Schema} {operation : Operation}
    (soundness : ∀ variableValues, Soundness concrete abstract schema variableValues)
    : OperationSoundWithFuel (concrete := concrete) (abstract := abstract)
        soundness operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  exact
    Soundness.executeQueryAnnotatedWithFuel_sound
      schema operation resolvers variableValues fuel source hschema hoperation
      (soundness coercedVariableValues)

-- Generic witness for direct default-executor syntactic soundness.
theorem analysisSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    {schema : Schema}
    (soundness : ∀ variableValues, Soundness concrete abstract schema variableValues)
    (operation : Operation)
    : AnalysisSound (concrete := concrete) (abstract := abstract)
        soundness operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  have hsound :=
    operationSoundWithFuel soundness hschema hoperation ObjectRef resolvers
      variableValues (executeQueryFuelBound schema operation) source
  simpa [executeQueryAnnotated] using hsound

end Syntactic
end TreeSummary
end GraphQL
