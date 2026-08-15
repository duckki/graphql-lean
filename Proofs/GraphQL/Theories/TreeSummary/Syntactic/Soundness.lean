import Proofs.GraphQL.Theories.TreeSummary.Syntactic.Coverage
import Proofs.GraphQL.Theories.TreeSummary.ResponseFold

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

theorem Compatible.singleFieldResult_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (variableValues : VariableValues)
    (compatible : Compatible concrete abstract schema variableValues)
    (runtimeType : Name) (ref : ObjectRef) (responseName : Name)
    (field : ExecutableField) (rest : List ExecutableField)
    (definition : FieldDefinition)
    (completed : Result AnnotatedResponseValue)
    (groups : List CollectedFieldGroup) (traversal : Traversal)
    (hparent : field.parentType = runtimeType)
    (hlookup : schema.lookupField field.parentType field.fieldName = some definition)
    (harguments : (field.arguments.map Argument.name).Nodup)
    (hnonempty : groups ≠ [])
    (hallows : inheritedConditionsAllowGroups variableValues groups)
    (hconditions : conditionsAllowGroupsAt variableValues runtimeType groups)
    (hcover
      : groupsCoverFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) groups (field :: rest))
    (hmatch : groupsRepresentField schema variableValues runtimeType ref groups field)
    (hcompleted
      : compatible.related (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizeCollectedChildren abstract schema traversal groups) completed))
    : compatible.related
        (foldAnnotatedResponseFieldsResult concrete
          (singleAnnotatedResponseFieldResult schema variableValues definition
            responseName field completed))
        (summarizeCollectedGroups abstract schema traversal groups) := by
  cases completed with
  | error errors => exact compatible.toCompatibilityCore.empty_related_any _
  | ok completed =>
      rcases completed with ⟨value, errors⟩
      have hcompleted' :
          compatible.related (foldAnnotatedResponseValueChildren concrete value)
            (foldChildSummaryForValue abstract
              (foldChildSummaries abstract
                (summarizedChildren abstract schema traversal) groups) value) := by
        rw [foldChildSummaries_eq_summarizeCollectedChildren]
        simpa [foldAnnotatedResponseValueResult,
          foldChildSummaryForValueResult] using hcompleted
      have hfield := compatible.field_related ObjectRef runtimeType
        ref responseName field rest definition value
        (foldAnnotatedResponseValueChildren concrete value) groups
        (summarizedChildren abstract schema traversal)
        hparent hlookup harguments hnonempty hallows hconditions hcover hmatch hcompleted'
      rw [foldFieldGroups_eq_summarizeCollectedGroups] at hfield
      simpa [singleAnnotatedResponseFieldResult,
        resolvedFieldProvenance,
        foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields,
        compatible.concreteLawful.combine_empty] using hfield

-- The sole execution-induction argument. Analyses instantiate `Compatible`; they do not
-- recurse over resolvers, completion, list bubbling, or response-name grouping.
private theorem annotatedResponseExecution_related_all
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (summaryVariableValues : VariableValues)
    (hsummaryValues : BooleanValuesMatchRuntime variableValues summaryVariableValues)
    (compatible : Compatible concrete abstract schema variableValues)
    (traversal : Traversal)
    (htraversal : traversal.ExecutionComplete schema variableValues)
    (htraversalRuntime
      : traversal
        = Traversal.withRuntimeBooleanDefaults variableValues summaryVariableValues)
    : (forall fuel source executionGroups,
        forall runtimeType (ref : ObjectRef) availableGroups,
          source = .object runtimeType ref
          -> CollectedGroupsParent runtimeType executionGroups
          -> NormalForm.executableGroupsWellFormed executionGroups
          -> NormalForm.executableGroupNamesNodup executionGroups
          -> ExecutableGroupsValid schema executionGroups
          -> inheritedConditionsAllowGroups variableValues availableGroups
          -> groupsCoverFields schema variableValues runtimeType runtimeType
              (.object runtimeType ref) availableGroups
              (flattenCollectedFields executionGroups)
          -> groupsRepresentFields schema variableValues runtimeType runtimeType
              (.object runtimeType ref) availableGroups
              (flattenCollectedFields executionGroups)
          -> compatible.related
              (foldAnnotatedResponseFieldsResult concrete
                (executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                  source executionGroups))
              (summarizeCollectedGroups abstract schema traversal availableGroups))
      ∧ (forall fuel source responseName fields,
          forall runtimeType (ref : ObjectRef) groups,
            source = .object runtimeType ref
            -> ExecutableFieldsParent runtimeType fields
            -> fields ≠ []
            -> ExecutableFieldsResponseName responseName fields
            -> (ExecutableFieldsFieldValidationMergeCompatible fields
                ∧ ExecutableFieldsChildrenValid schema fields
                ∧ ExecutableFieldsArgumentsNodup fields
                ∧ ∀ field,
                    field ∈ fields -> selectionSetArgumentsNodup field.selectionSet)
            -> groups ≠ []
            -> inheritedConditionsAllowGroups variableValues groups
            -> conditionsAllowGroupsAt variableValues runtimeType groups
            -> groupsCoverFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups fields
            -> groupsRepresentFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups fields
            -> compatible.related
                (foldAnnotatedResponseFieldsResult concrete
                  (executeQueryAnnotatedField schema resolvers variableValues fuel source
                    responseName fields))
                (summarizeCollectedGroups abstract schema traversal groups))
      ∧ (forall fuel fieldType fields value,
          forall runtimeType (ref : ObjectRef) responseName fieldName definition groups,
            fieldType.namedType = definition.outputType.namedType
            -> schema.lookupField runtimeType fieldName = some definition
            -> (∃ field, field ∈ fields ∧ field.fieldName = fieldName)
            -> ExecutableFieldsParent runtimeType fields
            -> fields ≠ []
            -> ExecutableFieldsResponseName responseName fields
            -> (ExecutableFieldsFieldValidationMergeCompatible fields
                ∧ ExecutableFieldsChildrenValid schema fields
                ∧ ExecutableFieldsArgumentsNodup fields
                ∧ ∀ field,
                    field ∈ fields -> selectionSetArgumentsNodup field.selectionSet)
            -> groups ≠ []
            -> inheritedConditionsAllowGroups variableValues groups
            -> conditionsAllowGroupsAt variableValues runtimeType groups
            -> groupsCoverFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups fields
            -> groupsRepresentFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups fields
            -> compatible.related
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
            -> ExecutableFieldsParent runtimeType fields
            -> fields ≠ []
            -> ExecutableFieldsResponseName responseName fields
            -> (ExecutableFieldsFieldValidationMergeCompatible fields
                ∧ ExecutableFieldsChildrenValid schema fields
                ∧ ExecutableFieldsArgumentsNodup fields
                ∧ ∀ field,
                    field ∈ fields -> selectionSetArgumentsNodup field.selectionSet)
            -> groups ≠ []
            -> inheritedConditionsAllowGroups variableValues groups
            -> conditionsAllowGroupsAt variableValues runtimeType groups
            -> groupsCoverFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups fields
            -> groupsRepresentFields schema variableValues runtimeType runtimeType
                (.object runtimeType ref) groups fields
            -> compatible.related
                (foldAnnotatedResponseValuesResult concrete
                  (completeAnnotatedResponseValueList schema resolvers variableValues fuel
                    itemType fields values))
                (foldChildSummaryForValuesResult abstract
                  (summarizeCollectedChildren abstract schema traversal groups)
                  (completeAnnotatedResponseValueList schema resolvers variableValues
                    fuel itemType fields values))) := by
  apply executeQueryAnnotatedCollectedFields.mutual_induct schema resolvers variableValues
  case case1 =>
    intro fuel source runtimeType ref availableGroups _hsource _hparents
      _hwellFormed _hnodup _hvalid _hinherited _hcover _hrepresent
    simpa [executeQueryAnnotatedCollectedFields,
      foldAnnotatedResponseFieldsResult, foldAnnotatedResponseFields] using
      compatible.toCompatibilityCore.empty_related_any
        (summarizeCollectedGroups abstract schema traversal availableGroups)
  case case2 =>
    intro fuel source responseName fields rest field_ih tail_ih
      runtimeType ref availableGroups hsource hparents hwellFormed hnodup
      hvalid hinherited hcover hrepresent
    subst source
    have hgroupWellFormed :=
      hwellFormed (responseName, fields) (by simp)
    have hgroupParent := hparents responseName fields (by simp)
    have hgroupValid := hvalid responseName fields (by simp)
    let activeGroups :=
      activeGroupsWithResponseName variableValues runtimeType responseName
        availableGroups
    have hactiveNonempty : activeGroups ≠ [] :=
      activeGroupsWithResponseName_ne_nil_of_cover schema variableValues
        runtimeType runtimeType responseName ref availableGroups
        (fields.head hgroupWellFormed.1) (fields.tail)
        (by
          intro candidate hcandidate
          exact hgroupWellFormed.2 candidate (by
            simpa [List.cons_head_tail hgroupWellFormed.1] using hcandidate))
        (by
          intro candidate hcandidate
          apply hcover candidate
          simpa [flattenCollectedFields, List.cons_head_tail hgroupWellFormed.1]
            using Or.inl hcandidate)
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
          (.object runtimeType ref) activeGroups fields := by
      apply groupsCoverFields_activeGroupsWithResponseName schema variableValues
        runtimeType runtimeType responseName ref availableGroups fields
        hgroupWellFormed.2
      intro candidate hcandidate
      apply hcover candidate
      simp [flattenCollectedFields, hcandidate]
    have hactiveRepresent :
        groupsRepresentFields schema variableValues runtimeType runtimeType
          (.object runtimeType ref) activeGroups fields := by
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
            (flattenCollectedFields ((responseName, fields) :: rest)).filter
              (fun executable => executable.responseName == responseName) := by
        apply List.mem_filter.mpr
        refine ⟨hcandidate, ?_⟩
        have hname := hgroupCover.2.2.1
        have hactiveName : group.responseName = responseName := by
          have := (List.mem_filter.mp hgroup).2
          simp only [Bool.and_eq_true, beq_iff_eq] at this
          exact this.1
        simp [hname, hactiveName]
      have hcandidateHead : candidate ∈ fields := by
        rw [ConditionTree.flattenCollectedFields_eq_fieldGroups]
          at hcandidateFiltered
        have hfilterEq := Execution.FieldGroups.filter_flattenCollectedFields_head_eq
          responseName fields rest hwellFormed
          ((Execution.FieldGroups.executableGroupNamesNodup_iff_map_fst_nodup _).mp
            hnodup)
        rw [hfilterEq] at hcandidateFiltered
        exact hcandidateFiltered
      exact ⟨candidate, hcandidateHead, hgroupCover, heq⟩
    have hhead := field_ih runtimeType ref activeGroups rfl hgroupParent
      hgroupWellFormed.1 hgroupWellFormed.2 hgroupValid hactiveNonempty
      hactiveInherited hactiveConditions hactiveCover hactiveRepresent
    have hhead' := compatible.related_mono _ _ _ hhead
      (activeGroupsWithResponseName_le abstract compatible.abstractLawful schema
        traversal variableValues runtimeType responseName availableGroups)
    have htail := tail_ih runtimeType ref
      (groupsWithoutResponseName responseName availableGroups) rfl
      (CollectedGroupsParent_tail hparents)
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
        have hcandidateRest : candidate ∈ flattenCollectedFields rest := by
          change candidate ∈ fields ++ flattenCollectedFields rest at hcandidate
          rcases List.mem_append.mp hcandidate with hhead | hrest
          · have hheadName := hgroupWellFormed.2 candidate hhead
            have hgroupNe : group.responseName ≠ responseName := by
              have hfiltered := (List.mem_filter.mp hgroup).2
              intro heq
              simp [heq] at hfiltered
            exact False.elim
              (hgroupNe (hgroupCover.2.2.1.symm.trans hheadName))
          · exact hrest
        exact ⟨candidate, hcandidateRest, hgroupCover, heq⟩)
    rw [executeQueryAnnotatedCollectedFields,
      summarizeCollectedGroups_partition_responseName abstract
        compatible.abstractLawful schema traversal responseName availableGroups]
    exact compatible.toCompatibilityCore.combineFieldsResult_related _ _ _ _ hhead' htail
  case case3 =>
    intro fuel source responseName runtimeType ref groups _hsource _hparents
      hnonempty _hnames _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    exact False.elim (hnonempty rfl)
  case case4 =>
    intro source responseName field rest runtimeType ref groups _hsource _hparents
      _hnonempty _hnames _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    simpa [executeQueryAnnotatedField, foldAnnotatedResponseFieldsResult] using
      compatible.toCompatibilityCore.empty_related_any
        (summarizeCollectedGroups abstract schema traversal groups)
  case case5 =>
    intro source responseName field rest fuel hlookup runtimeType ref groups
      _hsource _hparents _hnonempty _hnames _hvalid _hgroups _hinherited _hconditions
      _hcover _hrepresent
    simpa [executeQueryAnnotatedField, hlookup,
      foldAnnotatedResponseFieldsResult] using
      compatible.toCompatibilityCore.empty_related_any
        (summarizeCollectedGroups abstract schema traversal groups)
  case case6 =>
    intro source responseName field rest fuel definition hlookup hcoerce
      runtimeType ref groups hsource hparents _hnonempty hnames hvalid hgroups
      hinherited hconditions hcover hrepresent
    subst source
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted :
        compatible.related (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizeCollectedChildren abstract schema traversal groups) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact compatible.toCompatibilityCore.empty_related_any _
    have hmatch :
        groupsRepresentField schema variableValues runtimeType ref groups field :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        groups (field :: rest) field (by simp) (by
          intro candidate hcandidate
          exact (hnames candidate hcandidate).trans (hnames field (by simp)).symm)
        hvalid.1 hconditions hrepresent
    have hsingle := compatible.singleFieldResult_related schema variableValues
      runtimeType ref responseName field rest definition completed groups traversal
      (hparents field (by simp)) hlookup (hvalid.2.2.1 field (by simp)) hgroups
      hinherited hconditions hcover hmatch hcompleted
    simp only [executeQueryAnnotatedField, hlookup]
    rw [hcoerce]
    exact hsingle
  case case7 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      hresolve runtimeType ref groups hsource hparents _hnonempty hnames hvalid hgroups
      hinherited hconditions hcover hrepresent
    subst source
    let completed : Result AnnotatedResponseValue :=
      match definition.outputType with
      | .nonNull _inner => .error 1
      | _ => .ok (.null, 1)
    have hcompleted :
        compatible.related (foldAnnotatedResponseValueResult concrete completed)
          (foldChildSummaryForValueResult abstract
            (summarizeCollectedChildren abstract schema traversal groups) completed) := by
      cases htype : definition.outputType <;>
        simp [completed, htype, foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren, foldChildSummaryForValueResult,
          foldChildSummaryForValue] <;>
        exact compatible.toCompatibilityCore.empty_related_any _
    have hmatch :
        groupsRepresentField schema variableValues runtimeType ref groups field :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        groups (field :: rest) field (by simp) (by
          intro candidate hcandidate
          exact (hnames candidate hcandidate).trans (hnames field (by simp)).symm)
        hvalid.1 hconditions hrepresent
    have hsingle := compatible.singleFieldResult_related schema variableValues
      runtimeType ref responseName field rest definition completed groups traversal
      (hparents field (by simp)) hlookup (hvalid.2.2.1 field (by simp)) hgroups
      hinherited hconditions hcover hmatch hcompleted
    simp only [executeQueryAnnotatedField, hlookup, hcoerce]
    rw [hresolve]
    exact hsingle
  case case8 =>
    intro source responseName field rest fuel definition hlookup coercedArguments hcoerce
      resolved hresolve
      complete_ih runtimeType ref groups hsource hparents hnonempty hnames hvalid hgroups
      hinherited hconditions hcover hrepresent
    subst source
    have hcompleted := complete_ih runtimeType ref responseName field.fieldName
      definition groups rfl
      (by simpa [hparents field (by simp)] using hlookup)
      ⟨field, by simp, rfl⟩
      hparents hnonempty hnames hvalid hgroups hinherited hconditions hcover hrepresent
    have hmatch :
        groupsRepresentField schema variableValues runtimeType ref groups field :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        groups (field :: rest) field (by simp) (by
          intro candidate hcandidate
          exact (hnames candidate hcandidate).trans (hnames field (by simp)).symm)
        hvalid.1 hconditions hrepresent
    have hsingle := compatible.singleFieldResult_related schema variableValues
      runtimeType ref responseName field rest definition
      (completeAnnotatedResponseValue schema resolvers variableValues fuel
        definition.outputType (field :: rest) resolved)
      groups traversal (hparents field (by simp)) hlookup
      (hvalid.2.2.1 field (by simp)) hgroups hinherited hconditions hcover hmatch
      hcompleted
    simpa [executeQueryAnnotatedField, hlookup, hcoerce, hresolve] using hsingle
  case case9 =>
    intro fieldType fields value runtimeType ref responseName fieldName definition
      groups _hnamed _hlookup _hwitness _hparents _hnonempty _hnames _hvalid _hgroups
      _hinherited _hconditions _hcover _hrepresent
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      compatible.empty_related
  case case10 =>
    intro fuel inner fields value hfuel complete_ih runtimeType ref responseName
      fieldName definition groups hnamed hlookup hwitness hparents hnonempty hnames
      hvalid hgroups hinherited hconditions hcover hrepresent
    have hinner := complete_ih runtimeType ref responseName fieldName definition groups
      (by simpa [TypeRef.namedType] using hnamed) hlookup hwitness hparents hnonempty hnames
      hvalid hgroups hinherited hconditions hcover hrepresent
    simpa [completeAnnotatedResponseValue, hfuel] using
      compatible.toCompatibilityCore.completeNonNullResult_related
        (completeAnnotatedResponseValue schema resolvers variableValues fuel inner fields
          value)
        (summarizeCollectedChildren abstract schema traversal groups) hinner
  case case11 =>
    intro fuel fieldType fields hnotNonNull runtimeType ref responseName fieldName
      definition groups _hnamed _hlookup _hwitness _hparents _hnonempty _hnames
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    simpa [completeAnnotatedResponseValue, hnotNonNull,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      compatible.empty_related
  case case12 =>
    intro fuel typeName fields value hcomposite runtimeType ref responseName fieldName
      definition groups _hnamed _hlookup _hwitness _hparents _hnonempty _hnames
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      compatible.empty_related
  case case13 =>
    intro fuel typeName fields value hnotComposite runtimeType ref responseName
      fieldName definition groups _hnamed _hlookup _hwitness _hparents _hnonempty
      _hnames _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    have hcomposite : (TypeRef.named typeName).isCompositeBool schema = false := by
      cases hvalue : (TypeRef.named typeName).isCompositeBool schema with
      | false => rfl
      | true => exact False.elim (hnotComposite hvalue)
    simpa [completeAnnotatedResponseValue, hcomposite,
      foldAnnotatedResponseValueResult, foldAnnotatedResponseValueChildren,
      foldChildSummaryForValueResult, foldChildSummaryForValue] using
      compatible.empty_related
  case case14 =>
    intro fuel childParentType fields childRuntimeType childRef hinclude childGroups
      child_ih runtimeType ref responseName fieldName definition groups hnamed hlookup
      hwitness hparents hnonempty hnames hvalid hgroups hinherited hconditions hcover
      hrepresent
    have hchildParent :
        childParentType = definition.outputType.namedType := by
      simpa [TypeRef.namedType] using hnamed
    subst childParentType
    let childAvailable :=
      candidateChildGroupsFor schema definition.outputType.namedType childRuntimeType
        traversal groups
    have hchildParents : CollectedGroupsParent childRuntimeType childGroups := by
      simpa [childGroups,
        NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
        collectFields_parent schema variableValues childRuntimeType
          (.object childRuntimeType childRef)
          (Execution.mergedFieldSelectionSet fields)
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
        schema.lookupField first.parentType first.fieldName = some definition := by
      rw [hparents first hfirst, hfirstName]
      exact hlookup
    rcases hvalid.2.1 first definition childRuntimeType hfirst hlookupFirst hinclude with
      ⟨hchildObject, hchildReady, hchildMerge⟩
    have hchildArguments : selectionSetArgumentsNodup
        (Execution.mergedFieldSelectionSet fields) :=
      selectionSetArgumentsNodup_mergedFieldSelectionSet fields hvalid.2.2.2
    have hchildValid : ExecutableGroupsValid schema childGroups := by
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
          (flattenCollectedFields childGroups) := by
      exact candidateChildGroupsFor_cover_subfields schema variableValues runtimeType
        runtimeType ref definition.outputType.namedType childRuntimeType responseName
        childRef groups fields traversal htraversal hinclude hinherited hnames hcover
    have hchildRepresent :
        groupsRepresentFields schema variableValues childRuntimeType childRuntimeType
          (.object childRuntimeType childRef) childAvailable
          (flattenCollectedFields childGroups) := by
      have hpossible :
          (schema.getPossibleTypes definition.outputType.namedType).contains
              childRuntimeType
            = true := by
        simpa [Schema.typeIncludesObjectBool] using hinclude
      simpa [childGroups] using
        candidateChildGroupsFor_represent_subfields schema variableValues runtimeType ref
          definition.outputType.namedType childRuntimeType childRef groups fields traversal
          (by rw [htraversalRuntime]; exact hsummaryValues) hpossible hinherited hconditions
          hrepresent
    have hchild := child_ih childRuntimeType childRef childAvailable rfl
      hchildParents hchildWellFormed hchildNodup hchildValid hchildInherited hchildCover
      hchildRepresent
    have hmatch :
        groupsRepresentField schema variableValues runtimeType ref groups first :=
      groupsRepresentField_of_represent_and_compatible schema variableValues runtimeType ref
        groups fields first hfirst (by
          intro candidate hcandidate
          exact (hnames candidate hcandidate).trans (hnames first hfirst).symm)
        hvalid.1 hconditions hrepresent
    have hcandidatesLe :=
      candidateChildGroupsFor_le_summarizeCollectedChildren abstract
        compatible.abstractLawful schema definition.outputType.namedType childRuntimeType
        variableValues summaryVariableValues traversal hsummaryValues htraversalRuntime groups
        (List.contains_iff_mem.mp (by
          simpa [Schema.typeIncludesObjectBool] using hinclude))
        (by
          intro group hgroup
          exact lookupField_childParentType_mem_of_condition_allows schema
            variableValues runtimeType group fieldName definition
            (hconditions group hgroup) (by
              rw [← hfirstName]
              exact fieldName_mem_of_groupsRepresentField schema variableValues runtimeType
                ref groups first hmatch group hgroup)
            hlookup)
    have hchild' := compatible.related_mono _ _ _ hchild hcandidatesLe
    cases hresult :
        executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
          (.object childRuntimeType childRef) childGroups with
    | error errors =>
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                (.object childRuntimeType childRef)
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
          foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          compatible.empty_related
    | ok completed =>
        rcases completed with ⟨childFields, errors⟩
        rw [hresult] at hchild'
        have hresult' :
            executeQueryAnnotatedCollectedFields schema resolvers variableValues fuel
                (.object childRuntimeType childRef)
                (collectFields schema variableValues childRuntimeType
                  (.object childRuntimeType childRef)
                  (Execution.mergedFieldSelectionSet fields))
              = .ok (childFields, errors) := by
          simpa [childGroups,
            NormalForm.collectSubfields_eq_collectFields_mergedFieldSelectionSet] using
            hresult
        have hchildFields :
            compatible.related (foldAnnotatedResponseFields concrete childFields)
              (summarizeCollectedChildren abstract schema traversal groups) := by
          simpa [foldAnnotatedResponseFieldsResult] using hchild'
        simpa [completeAnnotatedResponseValue, hinclude, hresult',
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue,
          compatible.abstractLawful.combine_empty] using hchildFields
  case case15 =>
    intro fuel parentType fields childRuntimeType childRef hnotInclude runtimeType ref
      responseName fieldName definition groups _hnamed _hlookup _hwitness _hparents
      _hnonempty _hnames _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    have hinclude : schema.typeIncludesObjectBool parentType childRuntimeType = false := by
      cases hvalue : schema.typeIncludesObjectBool parentType childRuntimeType with
      | false => rfl
      | true => exact False.elim (hnotInclude hvalue)
    simpa [completeAnnotatedResponseValue, hinclude,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      compatible.empty_related
  case case16 =>
    intro fuel inner fields values list_ih runtimeType ref responseName fieldName
      definition groups hnamed hlookup hwitness hparents hnonempty hnames hvalid hgroups
      hinherited hconditions hcover hrepresent
    have hlist := list_ih runtimeType ref responseName fieldName definition groups
      (by simpa [TypeRef.namedType] using hnamed) hlookup hwitness hparents hnonempty hnames
      hvalid hgroups hinherited hconditions hcover hrepresent
    cases hresult :
        completeAnnotatedResponseValueList schema resolvers variableValues fuel inner
          fields values with
    | error errors =>
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using
          compatible.empty_related
    | ok completed =>
        rcases completed with ⟨completedValues, errors⟩
        rw [hresult] at hlist
        have hvalues :
            compatible.related (foldAnnotatedResponseValues concrete completedValues)
              (foldChildSummaryForValues abstract
                (summarizeCollectedChildren abstract schema traversal groups)
                completedValues) := by
          simpa [foldAnnotatedResponseValuesResult,
            foldChildSummaryForValuesResult] using hlist
        simpa [completeAnnotatedResponseValue, hresult,
          catchAnnotatedResponseBubbleAsNull,
          foldAnnotatedResponseValueResult,
          foldAnnotatedResponseValueChildren,
          foldChildSummaryForValueResult, foldChildSummaryForValue] using hvalues
  case case17 =>
    intro fuel typeName fields values runtimeType ref responseName fieldName definition
      groups _hnamed _hlookup _hwitness _hparents _hnonempty _hnames _hvalid _hgroups
      _hinherited _hconditions _hcover _hrepresent
    simpa [completeAnnotatedResponseValue, foldAnnotatedResponseValueResult,
      foldChildSummaryForValueResult] using
      compatible.empty_related
  case case18 =>
    intro fuel inner fields value hnotNull hnotList runtimeType ref responseName
      fieldName definition groups _hnamed _hlookup _hwitness _hparents _hnonempty _hnames
      _hvalid _hgroups _hinherited _hconditions _hcover _hrepresent
    simpa [completeAnnotatedResponseValue, hnotNull, hnotList,
      foldAnnotatedResponseValueResult, foldChildSummaryForValueResult] using
      compatible.empty_related
  case case19 =>
    intro fuel itemType fields runtimeType ref responseName fieldName definition
      groups _hnamed _hlookup _hwitness _hparents _hnonempty _hnames _hvalid _hgroups
      _hinherited _hconditions _hcover _hrepresent
    simpa [completeAnnotatedResponseValueList,
      foldAnnotatedResponseValuesResult, foldAnnotatedResponseValues,
      foldChildSummaryForValuesResult, foldChildSummaryForValues] using
      compatible.empty_related
  case case20 =>
    intro fuel itemType fields value values head_ih tail_ih runtimeType ref
      responseName fieldName definition groups hnamed hlookup hwitness hparents hnonempty
      hnames hvalid hgroups hinherited hconditions hcover hrepresent
    have hhead := head_ih runtimeType ref responseName fieldName definition groups
      hnamed hlookup hwitness hparents hnonempty hnames hvalid hgroups hinherited hconditions
      hcover hrepresent
    have htail := tail_ih runtimeType ref responseName fieldName definition groups
      hnamed hlookup hwitness hparents hnonempty hnames hvalid hgroups hinherited hconditions
      hcover hrepresent
    simpa [completeAnnotatedResponseValueList] using
      compatible.toCompatibilityCore.combineValuesResult_related
        (completeAnnotatedResponseValue schema resolvers variableValues fuel itemType
          fields value)
        (completeAnnotatedResponseValueList schema resolvers variableValues fuel itemType
          fields values)
        (summarizeCollectedChildren abstract schema traversal groups) hhead htail

-- Generic execution soundness with a Boolean environment already known to the abstract
-- traversal. The environment must agree with concrete execution wherever it supplies a
-- Boolean value.
theorem Compatible.executeQueryAnnotatedWithFuel_relatedUsingVariables
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
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    : compatible.related
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
        foldAnnotatedResponseValueChildren] using
        compatible.toCompatibilityCore.empty_related_any
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
      have hparents :
          CollectedGroupsParent (operation.rootType schema) executionGroups := by
        exact collectFields_parent schema coercedVariableValues (operation.rootType schema)
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
      have hvalid : ExecutableGroupsValid schema executionGroups := by
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
            compatible.abstractLawful schema (operation.rootType schema) []
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
          compatible.abstractLawful.le
            (summarizeCollectedGroups abstract schema traversal availableGroups)
            (summarizeSelectionSet abstract schema (operation.rootType schema) []
              operation.selectionSet summaryVariableValues) := by
        rw [hsummary]
        subst traversal
        unfold summarizeSelectionSet summarizeConditionTree
        simpa [tree, booleanConditionValues] using
          summarizeTreeAtRuntimeType_le abstract
            compatible.abstractLawful schema (operation.rootType schema) [] tree
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
            availableGroups (flattenCollectedFields executionGroups) := by
        exact htraversal (operation.rootType schema) [] operation.selectionSet
          (operation.rootType schema) (operation.rootType schema) ref rfl
          hpossible
      have hrepresent :
          groupsRepresentFields schema coercedVariableValues
            (operation.rootType schema) (operation.rootType schema)
            (.object (operation.rootType schema) ref) availableGroups
            (flattenCollectedFields executionGroups) := by
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
      have hrelated :=
        (annotatedResponseExecution_related_all schema hschema resolvers
          coercedVariableValues summaryVariableValues hsummaryValues
          compatible traversal htraversal htraversalRuntime).1 fuel
          (.object (operation.rootType schema) ref) executionGroups
          (operation.rootType schema) ref availableGroups rfl hparents hwellFormed hnodup
          hvalid hinherited hcover hrepresent
      have hrelated' := compatible.related_mono _ _ _ hrelated hsummaryLe
      cases hresult
            : executeQueryAnnotatedCollectedFields schema resolvers coercedVariableValues
                fuel (.object (operation.rootType schema) ref) executionGroups with
      | error errors =>
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValueChildren,
            foldAnnotatedResponseFieldsResult] using hrelated'
      | ok completed =>
          rcases completed with ⟨fields, errors⟩
          rw [hresult] at hrelated'
          simpa [executeQueryAnnotatedWithFuel, hroot, coercedVariableValues,
            executionGroups, hresult, foldAnnotatedResponse,
            foldAnnotatedResponseValueChildren,
            foldAnnotatedResponseFieldsResult] using hrelated'

-- Unknown-variable specialization of the resolved Boolean-environment theorem.
theorem Compatible.executeQueryAnnotatedWithFuel_related
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    (schema : Schema) (operation : Operation)
    (resolvers : Resolvers ObjectRef) (variableValues : VariableValues)
    (fuel : Nat) (source : ResolverValue ObjectRef)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hoperation : Validation.operationDefinitionValid schema operation)
    (compatible
      : Compatible concrete abstract schema
          (coerceVariableValues operation variableValues))
    : compatible.related
        (foldAnnotatedResponse concrete
          (executeQueryAnnotatedWithFuel schema resolvers variableValues operation fuel
            source))
        (summarizeOperation abstract schema operation) := by
  simpa [summarizeOperation] using
    Compatible.executeQueryAnnotatedWithFuel_relatedUsingVariables schema operation
      resolvers variableValues []
      (booleanValuesMatchRuntime_empty
        (coerceVariableValues operation variableValues))
      fuel source hschema hoperation compatible

theorem operationWithVariablesSoundWithFuel
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v})
    {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationWithVariablesSoundWithFuel algebraFor compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  have hrelated :=
    Compatible.executeQueryAnnotatedWithFuel_relatedUsingVariables schema operation
      resolvers variableValues coercedVariableValues
      (booleanValuesMatchRuntime_self coercedVariableValues) fuel source hschema hoperation
      (compatibleFor coercedVariableValues)
  simpa [summarizeOperationWithVariables, coercedVariableValues] using hrelated

theorem operationWithVariablesSound
    {concrete : ConcreteAlgebra.{u}}
    (algebraFor : VariableValues -> Algebra.{v})
    {schema : Schema}
    (compatibleFor : ∀ values, Compatible concrete (algebraFor values) schema values)
    (operation : Operation)
    : OperationWithVariablesSound algebraFor compatibleFor operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  have hsound := operationWithVariablesSoundWithFuel algebraFor compatibleFor
    operation hschema hoperation ObjectRef resolvers variableValues
    (executeQueryFuelBound schema operation) source
  simpa [executeQueryAnnotated] using hsound

theorem analysisWithVariablesSound
    (algebraFor : VariableValues -> Algebra.{v}) (schema : Schema)
    (operation : Operation)
    : AnalysisWithVariablesSound algebraFor schema operation := by
  intro concrete compatibleFor
  exact operationWithVariablesSound algebraFor compatibleFor operation

-- Generic witness for direct fuel-parameterized syntactic soundness. The compatibility
-- provider supplies the local field-group obligation after operation variables are
-- coerced; no comparison with the exact-case summary is used.
theorem operationSoundWithFuel
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    {schema : Schema} {operation : Operation}
    (compatible : ∀ variableValues, Compatible concrete abstract schema variableValues)
    : OperationSoundWithFuel (concrete := concrete) (abstract := abstract)
        compatible operation := by
  intro hschema hoperation ObjectRef resolvers variableValues fuel source
  let coercedVariableValues := coerceVariableValues operation variableValues
  exact
    Compatible.executeQueryAnnotatedWithFuel_related
      schema operation resolvers variableValues fuel source hschema hoperation
      (compatible coercedVariableValues)

-- Generic witness for direct default-executor syntactic soundness.
theorem operationSound
    {concrete : ConcreteAlgebra.{u}} {abstract : Algebra.{v}}
    {schema : Schema} {operation : Operation}
    (compatible : ∀ variableValues, Compatible concrete abstract schema variableValues)
    : OperationSound (concrete := concrete) (abstract := abstract)
        compatible operation := by
  intro hschema hoperation ObjectRef resolvers variableValues source
  have hsound :=
    operationSoundWithFuel compatible hschema hoperation ObjectRef resolvers
      variableValues (executeQueryFuelBound schema operation) source
  simpa [executeQueryAnnotated] using hsound

-- Generic witness for the public syntactic analysis soundness statement.
theorem analysisSound (abstract : Algebra.{v}) (schema : Schema) (operation : Operation)
    : AnalysisSound abstract schema operation := by
  intro concrete compatible
  exact operationSound compatible

end Syntactic
end TreeSummary
end GraphQL
