import Proofs.GraphQL.Theories.NormalForm.Shared.Execution
import Proofs.GraphQL.Theories.NormalForm.Shared.DirectiveFree
import Proofs.GraphQL.Execution.FieldCollection
import Proofs.GraphQL.Theories.NormalForm.Shared.ResponseNameFree
import Proofs.GraphQL.Validation.FieldMerge

/-!
Field-collection helper lemmas for directive-free ground-type normalization.

This module separates execution-facing collection facts from the structural normal-form
proofs in `GraphQL.NormalForm.GroundTypeNormalization`.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

variable {ObjectRef : Type}

def executableFieldScoped? (schema : Schema) (field : Execution.ExecutableField)
    : Option FieldMerge.ScopedField := do
  let fieldDefinition <- schema.lookupField field.parentType field.fieldName
  some
    {
      parentType := field.parentType,
      responseName := field.responseName,
      fieldName := field.fieldName,
      arguments := field.arguments,
      outputType := fieldDefinition.outputType,
      selectionSet := field.selectionSet
    }

theorem executableFieldScoped?_some
    {schema : Schema} {field : Execution.ExecutableField}
    {scopedField : FieldMerge.ScopedField}
    : executableFieldScoped? schema field = some scopedField
      -> ∃ fieldDefinition,
          schema.lookupField field.parentType field.fieldName = some fieldDefinition
          ∧ scopedField
            = {
              parentType := field.parentType,
              responseName := field.responseName,
              fieldName := field.fieldName,
              arguments := field.arguments,
              outputType := fieldDefinition.outputType,
              selectionSet := field.selectionSet
            } := by
  intro hscoped
  unfold executableFieldScoped? at hscoped
  cases hlookup : schema.lookupField field.parentType field.fieldName with
  | none =>
      simp [hlookup] at hscoped
  | some fieldDefinition =>
      simp [hlookup] at hscoped
      subst scopedField
      exact ⟨fieldDefinition, rfl, rfl⟩

theorem executableFieldScoped?_sameSelection
    {schema : Schema} {field : Execution.ExecutableField}
    {scopedField : FieldMerge.ScopedField}
    : executableFieldScoped? schema field = some scopedField
      -> scopedField.parentType = field.parentType
          ∧ scopedField.responseName = field.responseName
          ∧ scopedField.fieldName = field.fieldName
          ∧ scopedField.arguments = field.arguments
          ∧ scopedField.selectionSet = field.selectionSet := by
  intro hscoped
  rcases executableFieldScoped?_some hscoped with
    ⟨_fieldDefinition, _hlookup, hshape⟩
  subst scopedField
  simp

theorem executableGroupWellFormed_field_responseName
    {group : Name × List Execution.ExecutableField}
    {field : Execution.ExecutableField}
    : executableGroupWellFormed group
      -> field ∈ group.snd
      -> field.responseName = group.fst := by
  intro hgroup hfield
  exact hgroup.2 field hfield

theorem executableFields_same_parent_identity_of_scoped_merge
    {schema : Schema}
    {left right : Execution.ExecutableField}
    {leftScoped rightScoped : FieldMerge.ScopedField}
    : executableFieldScoped? schema left = some leftScoped
      -> executableFieldScoped? schema right = some rightScoped
      -> FieldMerge.fieldsForNameCanMerge schema leftScoped rightScoped
      -> left.parentType = right.parentType
      -> left.fieldName = right.fieldName
          ∧ Argument.argumentsEquivalent left.arguments right.arguments := by
  intro hleftScoped hrightScoped hmerge hparent
  have hleftShape :=
    executableFieldScoped?_sameSelection hleftScoped
  have hrightShape :=
    executableFieldScoped?_sameSelection hrightScoped
  have hscopedParent :
      leftScoped.parentType = rightScoped.parentType := by
    exact hleftShape.1.trans (hparent.trans hrightShape.1.symm)
  have hidentity :=
    FieldMerge.fieldsForNameCanMerge_same_parent_identity hmerge
      hscopedParent
  exact ⟨
    hleftShape.2.2.1.symm.trans
      (hidentity.1.trans hrightShape.2.2.1),
    by
      simpa [hleftShape.2.2.2.1, hrightShape.2.2.2.1]
        using hidentity.2⟩

theorem lookupType_name_eq_for_collection
    (schema : Schema) {typeName : Name}
    {typeDefinition : TypeDefinition}
    : schema.lookupType typeName = some typeDefinition
      -> typeDefinition.name = typeName := by
  intro hlookup
  have hmatch := List.find?_some hlookup
  simpa [Schema.lookupType] using hmatch

theorem typeIncludesObjectBool_eq_of_objectTypeNameBool_true_for_collection
    (schema : Schema) {typeName runtimeType : Name}
    : objectTypeNameBool schema typeName = true
      -> schema.typeIncludesObjectBool typeName runtimeType = true
      -> runtimeType = typeName := by
  intro hobject hinclude
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType typeName with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = typeName :=
            lookupType_name_eq_for_collection schema hlookup
          simp [Schema.typeIncludesObjectBool, Schema.getPossibleTypes,
            hlookup, hname] at hinclude
          exact hinclude
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
    (schema : Schema) {parentType typeCondition : Name}
    {source : Execution.ResolverValue ObjectRef}
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> Execution.doesFragmentTypeApplyBool schema parentType source typeCondition
          = schema.typesOverlapBool parentType typeCondition := by
  intro hobject hsource
  rcases hsource with ⟨runtimeType, ref, hsourceEq, hparent⟩
  subst source
  have hruntime :
      runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true_for_collection
      schema hobject hparent
  subst runtimeType
  unfold objectTypeNameBool at hobject
  cases hlookup : schema.lookupType parentType with
  | none =>
      simp [hlookup] at hobject
  | some typeDefinition =>
      cases typeDefinition with
      | object objectType =>
          have hname : objectType.name = parentType :=
            lookupType_name_eq_for_collection schema hlookup
          unfold Schema.typesOverlapBool
          simp [Execution.doesFragmentTypeApplyBool,
            Execution.runtimeObjectType?, Schema.getPossibleTypes, hlookup,
            hname]
      | builtinScalar scalar => simp [hlookup] at hobject
      | customScalar scalar => simp [hlookup] at hobject
      | interface interfaceType => simp [hlookup] at hobject
      | union unionType => simp [hlookup] at hobject
      | enum enumType => simp [hlookup] at hobject
      | inputObject inputObjectType => simp [hlookup] at hobject

theorem collectedResponseSelectionSet_eq_nil_of_key_absent (responseName : Name)
    : ∀ groups,
        responseName ∉ groups.map Prod.fst
        -> collectedResponseSelectionSet responseName groups = []
  | [], _habsent => by
      simp [collectedResponseSelectionSet]
  | group :: rest, habsent => by
      rcases group with ⟨groupResponseName, fields⟩
      have hheadNe : groupResponseName ≠ responseName := by
        intro heq
        exact habsent (by simp [heq])
      have hheadFalse : (groupResponseName == responseName) = false := by
        cases hmatch : groupResponseName == responseName
        · rfl
        · exact False.elim (hheadNe (beq_iff_eq.mp hmatch))
      have hrestAbsent : responseName ∉ rest.map Prod.fst := by
        intro hmem
        exact habsent (by simp [hmem])
      simp [collectedResponseSelectionSet, hheadFalse,
        collectedResponseSelectionSet_eq_nil_of_key_absent responseName rest
          hrestAbsent]

theorem collectedResponseSelectionSet_addExecutableGroup
    (responseName : Name) (group : Name × List Execution.ExecutableField)
    : ∀ groups,
        collectedResponseSelectionSet responseName
          (Execution.addExecutableGroup group groups)
        = collectedResponseSelectionSet responseName groups
          ++  if group.fst == responseName then
                Execution.mergedFieldSelectionSet group.snd
              else
                []
  | [] => by
      rcases group with ⟨groupResponseName, fields⟩
      by_cases hresponse : (groupResponseName == responseName) = true
      · simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
          hresponse]
      · have hfalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
          hfalse]
  | current :: rest => by
      rcases group with ⟨groupResponseName, groupFields⟩
      rcases current with ⟨currentName, currentFields⟩
      by_cases hcurrentGroup : (currentName == groupResponseName) = true
      · have hcurrentEq : currentName = groupResponseName :=
          beq_iff_eq.mp hcurrentGroup
        subst currentName
        by_cases hresponse : (groupResponseName == responseName) = true
        · simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hresponse, Execution.mergedFieldSelectionSet_append]
        · have hresponseFalse : (groupResponseName == responseName) = false := by
            cases hmatch : groupResponseName == responseName
            · rfl
            · contradiction
          simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hresponseFalse]
      · have hcurrentGroupFalse :
            (currentName == groupResponseName) = false := by
          cases hmatch : currentName == groupResponseName
          · rfl
          · contradiction
        by_cases hcurrentResponse : (currentName == responseName) = true
        · have hgroupResponseFalse :
              (groupResponseName == responseName) = false := by
            cases hmatch : groupResponseName == responseName
            · rfl
            · have hcr : currentName = responseName :=
                beq_iff_eq.mp hcurrentResponse
              have hgr : groupResponseName = responseName :=
                beq_iff_eq.mp hmatch
              subst currentName
              subst groupResponseName
              simp at hcurrentGroupFalse
          simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hcurrentGroupFalse, hcurrentResponse, hgroupResponseFalse]
        · have hcurrentResponseFalse :
              (currentName == responseName) = false := by
            cases hmatch : currentName == responseName
            · rfl
            · contradiction
          simp [Execution.addExecutableGroup, collectedResponseSelectionSet,
            hcurrentGroupFalse, hcurrentResponseFalse,
            collectedResponseSelectionSet_addExecutableGroup responseName
              (groupResponseName, groupFields) rest]

theorem collectedResponseSelectionSet_mergeExecutableGroups (responseName : Name)
    : ∀ left right,
        executableGroupNamesNodup right
        -> collectedResponseSelectionSet responseName
              (Execution.mergeExecutableGroups left right)
            = collectedResponseSelectionSet responseName left
              ++ collectedResponseSelectionSet responseName right
  | left, [], _hnodup => by
      simp [Execution.mergeExecutableGroups, collectedResponseSelectionSet]
  | left, group :: rest, hnodup => by
      rcases group with ⟨groupResponseName, fields⟩
      have hrestNodup : executableGroupNamesNodup rest := hnodup.2
      have hrestMerge :=
        collectedResponseSelectionSet_mergeExecutableGroups responseName
          (Execution.addExecutableGroup (groupResponseName, fields) left)
          rest hrestNodup
      by_cases hresponse : (groupResponseName == responseName) = true
      · have hresponseEq : groupResponseName = responseName :=
          beq_iff_eq.mp hresponse
        subst groupResponseName
        have hrestSelection :
            collectedResponseSelectionSet responseName rest = [] :=
          collectedResponseSelectionSet_eq_nil_of_key_absent responseName rest
            hnodup.1
        simp [Execution.mergeExecutableGroups] at hrestMerge ⊢
        rw [hrestMerge,
          collectedResponseSelectionSet_addExecutableGroup responseName
            (responseName, fields) left]
        simp [collectedResponseSelectionSet, hrestSelection]
      · have hresponseFalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        simp [Execution.mergeExecutableGroups] at hrestMerge ⊢
        rw [hrestMerge,
          collectedResponseSelectionSet_addExecutableGroup responseName
            (groupResponseName, fields) left]
        simp [collectedResponseSelectionSet, hresponseFalse]

theorem executableGroupWellFormed_singleton_field (field : Execution.ExecutableField)
    : executableGroupWellFormed (field.responseName, [field]) := by
  constructor
  · simp
  · intro candidate hcandidate
    simp at hcandidate
    subst candidate
    rfl

theorem executableGroupsWellFormed_nil : executableGroupsWellFormed [] := by
  intro group hgroup
  simp at hgroup

theorem executableGroupsWellFormed_tail
    {group : Name × List Execution.ExecutableField}
    {groups : List (Name × List Execution.ExecutableField)}
    : executableGroupsWellFormed (group :: groups)
      -> executableGroupsWellFormed groups := by
  intro hgroups candidate hcandidate
  exact hgroups candidate (by simp [hcandidate])

theorem addExecutableGroup_wellFormed
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : executableGroupWellFormed group
      -> executableGroupsWellFormed groups
      -> executableGroupsWellFormed (Execution.addExecutableGroup group groups) := by
  intro hgroup hgroups
  induction groups with
  | nil =>
      intro candidate hcandidate
      simp [Execution.addExecutableGroup] at hcandidate
      subst candidate
      exact hgroup
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == group.fst) = true
      · have hcurrentName : currentName = group.fst := beq_iff_eq.mp hname
        intro candidate hcandidate
        simp [Execution.addExecutableGroup, hname] at hcandidate
        rcases hcandidate with hhead | htail
        · subst candidate
          have hcurrent :
              executableGroupWellFormed (currentName, currentFields) :=
            hgroups (currentName, currentFields) (by simp)
          constructor
          · intro hnil
            simp at hnil
            exact hcurrent.1 hnil.1
          · intro field hfield
            rcases List.mem_append.mp hfield with hfieldCurrent | hfieldGroup
            · exact hcurrent.2 field hfieldCurrent
            · exact (hgroup.2 field hfieldGroup).trans hcurrentName.symm
        · exact hgroups candidate (by simp [htail])
      · have hfalse : (currentName == group.fst) = false := by
          cases hmatch : currentName == group.fst
          · rfl
          · contradiction
        intro candidate hcandidate
        simp [Execution.addExecutableGroup, hfalse] at hcandidate
        rcases hcandidate with hhead | htail
        · subst candidate
          exact hgroups (currentName, currentFields) (by simp)
        · exact ih (executableGroupsWellFormed_tail hgroups) candidate
            htail

theorem mergeExecutableGroups_wellFormed
    (left right : List (Name × List Execution.ExecutableField))
    : executableGroupsWellFormed left
      -> executableGroupsWellFormed right
      -> executableGroupsWellFormed (Execution.mergeExecutableGroups left right) := by
  intro hleft hright
  induction right generalizing left with
  | nil =>
      simpa [Execution.mergeExecutableGroups] using hleft
  | cons group rest ih =>
      simp [Execution.mergeExecutableGroups]
      exact ih (Execution.addExecutableGroup group left)
        (addExecutableGroup_wellFormed group left
          (hright group (by simp)) hleft)
        (executableGroupsWellFormed_tail hright)

theorem mergeExecutableGroups_mem_responseName
    (left right : List (Name × List Execution.ExecutableField))
    (responseName : Name)
    : responseName ∈ (Execution.mergeExecutableGroups left right).map Prod.fst
      ↔ responseName ∈ left.map Prod.fst ∨ responseName ∈ right.map Prod.fst := by
  induction right generalizing left with
  | nil =>
      simp [Execution.mergeExecutableGroups]
  | cons group rest ih =>
      change
        responseName ∈
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup group left) rest).map Prod.fst
          ↔ responseName ∈ left.map Prod.fst
            ∨ responseName ∈ (group :: rest).map Prod.fst
      rw [ih (Execution.addExecutableGroup group left)]
      rw [addExecutableGroup_mem_responseName group left responseName]
      rcases group with ⟨groupResponseName, fields⟩
      simp [or_assoc, or_left_comm, or_comm]

theorem withoutExecutableGroupsWithResponseName_addExecutableGroup
    (responseName : Name)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    : withoutExecutableGroupsWithResponseName responseName
        (Execution.addExecutableGroup group groups)
      = if group.fst == responseName then
          withoutExecutableGroupsWithResponseName responseName groups
        else
          Execution.addExecutableGroup group
            (withoutExecutableGroupsWithResponseName responseName groups) := by
  induction groups with
  | nil =>
      rcases group with ⟨groupResponseName, groupFields⟩
      by_cases hresponse : (groupResponseName == responseName) = true
      · simp [withoutExecutableGroupsWithResponseName,
          Execution.addExecutableGroup, hresponse]
      · have hfalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        simp [withoutExecutableGroupsWithResponseName,
          Execution.addExecutableGroup, hfalse]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      rcases group with ⟨groupResponseName, groupFields⟩
      by_cases hcurrent : (currentName == groupResponseName) = true
      · have hcurrentEq : currentName = groupResponseName :=
          beq_iff_eq.mp hcurrent
        subst currentName
        by_cases hresponse : (groupResponseName == responseName) = true
        · simp [withoutExecutableGroupsWithResponseName,
            Execution.addExecutableGroup, hresponse]
        · have hresponseFalse :
              (groupResponseName == responseName) = false := by
            cases hmatch : groupResponseName == responseName
            · rfl
            · contradiction
          simp [withoutExecutableGroupsWithResponseName,
            Execution.addExecutableGroup, hresponseFalse]
      · have hcurrentFalse :
            (currentName == groupResponseName) = false := by
          cases hmatch : currentName == groupResponseName
          · rfl
          · contradiction
        by_cases hcurrentResponse : (currentName == responseName) = true
        · have hgroupResponseFalse :
              (groupResponseName == responseName) = false := by
            cases hmatch : groupResponseName == responseName
            · rfl
            · have hcurrentEq : currentName = responseName :=
                beq_iff_eq.mp hcurrentResponse
              have hgroupEq : groupResponseName = responseName :=
                beq_iff_eq.mp hmatch
              subst currentName
              subst groupResponseName
              simp at hcurrentFalse
          simpa [withoutExecutableGroupsWithResponseName,
            Execution.addExecutableGroup, hcurrentFalse, hcurrentResponse,
            hgroupResponseFalse] using ih
        · have hcurrentResponseFalse :
              (currentName == responseName) = false := by
            cases hmatch : currentName == responseName
            · rfl
            · contradiction
          by_cases hgroupResponse : (groupResponseName == responseName) = true
          · simpa [withoutExecutableGroupsWithResponseName,
              Execution.addExecutableGroup, hcurrentFalse,
              hcurrentResponseFalse, hgroupResponse] using ih
          · have hgroupResponseFalse :
                (groupResponseName == responseName) = false := by
              cases hmatch : groupResponseName == responseName
              · rfl
              · contradiction
            simp [withoutExecutableGroupsWithResponseName,
              Execution.addExecutableGroup, hcurrentFalse,
              hcurrentResponseFalse, hgroupResponseFalse]
            exact by
              simpa [withoutExecutableGroupsWithResponseName,
                hgroupResponseFalse] using ih

theorem withoutExecutableGroupsWithResponseName_mergeExecutableGroups
    (responseName : Name)
    (left right : List (Name × List Execution.ExecutableField))
    : withoutExecutableGroupsWithResponseName responseName
        (Execution.mergeExecutableGroups left right)
      = Execution.mergeExecutableGroups
          (withoutExecutableGroupsWithResponseName responseName left)
          (withoutExecutableGroupsWithResponseName responseName right) := by
  induction right generalizing left with
  | nil =>
      simp [Execution.mergeExecutableGroups,
        withoutExecutableGroupsWithResponseName]
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, groupFields⟩
      by_cases hresponse : (groupResponseName == responseName) = true
      · change
          withoutExecutableGroupsWithResponseName responseName
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup
                (groupResponseName, groupFields) left) rest)
          =
          Execution.mergeExecutableGroups
            (withoutExecutableGroupsWithResponseName responseName left)
            (withoutExecutableGroupsWithResponseName responseName
              ((groupResponseName, groupFields) :: rest))
        rw [ih (Execution.addExecutableGroup
          (groupResponseName, groupFields) left)]
        rw [withoutExecutableGroupsWithResponseName_addExecutableGroup]
        simp [withoutExecutableGroupsWithResponseName,
          Execution.mergeExecutableGroups, hresponse]
      · have hfalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        change
          withoutExecutableGroupsWithResponseName responseName
            (Execution.mergeExecutableGroups
              (Execution.addExecutableGroup
                (groupResponseName, groupFields) left) rest)
          =
          Execution.mergeExecutableGroups
            (withoutExecutableGroupsWithResponseName responseName left)
            (withoutExecutableGroupsWithResponseName responseName
              ((groupResponseName, groupFields) :: rest))
        rw [ih (Execution.addExecutableGroup
          (groupResponseName, groupFields) left)]
        rw [withoutExecutableGroupsWithResponseName_addExecutableGroup]
        simp [withoutExecutableGroupsWithResponseName,
          Execution.mergeExecutableGroups, hfalse]

theorem withoutExecutableGroupsWithResponseName_eq_self_of_not_mem (responseName : Name)
    : ∀ groups : List (Name × List Execution.ExecutableField),
        responseName ∉ groups.map Prod.fst
        -> withoutExecutableGroupsWithResponseName responseName groups = groups
  | groups, hnotin => by
      unfold withoutExecutableGroupsWithResponseName
      apply List.filter_eq_self.mpr
      intro group hgroup
      rcases group with ⟨groupResponseName, groupFields⟩
      have hne : groupResponseName ≠ responseName := by
        intro heq
        exact hnotin
          (List.mem_map.mpr
            ⟨(groupResponseName, groupFields), hgroup, heq⟩)
      have hfalse : (groupResponseName == responseName) = false := by
        cases hmatch : groupResponseName == responseName
        · rfl
        · exact False.elim (hne (beq_iff_eq.mp hmatch))
      simp [hfalse]

theorem withoutExecutableGroupsWithResponseName_cons_self_of_namesNodup
    (responseName : Name) (fields : List Execution.ExecutableField)
    (rest : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup ((responseName, fields) :: rest)
      -> withoutExecutableGroupsWithResponseName responseName
            ((responseName, fields) :: rest)
          = rest := by
  intro hnodup
  have htrue : (responseName == responseName) = true := by simp
  unfold withoutExecutableGroupsWithResponseName
  simp
  intro groupResponseName groupFields hmem heq
  subst groupResponseName
  exact hnodup.1
    (List.mem_map.mpr ⟨(responseName, groupFields), hmem, rfl⟩)

theorem mergeExecutableGroups_preserves_head
    (responseName : Name) (currentFields : List Execution.ExecutableField)
    (headRest right : List (Name × List Execution.ExecutableField))
    : ∃ appendedFields mergedRest,
        Execution.mergeExecutableGroups ((responseName, currentFields) :: headRest) right
        = (responseName, currentFields ++ appendedFields) :: mergedRest := by
  induction right generalizing currentFields headRest with
  | nil =>
      exact ⟨[], headRest, by simp [Execution.mergeExecutableGroups]⟩
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, groupFields⟩
      by_cases hresponse : (responseName == groupResponseName) = true
      · have hresponseEq : responseName = groupResponseName :=
          beq_iff_eq.mp hresponse
        subst groupResponseName
        rcases ih (currentFields ++ groupFields) headRest with
          ⟨appendedFields, mergedRest, hmerge⟩
        refine ⟨groupFields ++ appendedFields, mergedRest, ?_⟩
        simpa [Execution.mergeExecutableGroups, Execution.addExecutableGroup,
          List.append_assoc] using hmerge
      · have hfalse : (responseName == groupResponseName) = false := by
          cases hmatch : responseName == groupResponseName
          · rfl
          · contradiction
        have hreverseFalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · have hgr : groupResponseName = responseName :=
              beq_iff_eq.mp hmatch
            subst groupResponseName
            simp at hfalse
        rcases ih currentFields
            (Execution.addExecutableGroup (groupResponseName, groupFields)
              headRest) with
          ⟨appendedFields, mergedRest, hmerge⟩
        refine ⟨appendedFields, mergedRest, ?_⟩
        have hne : responseName ≠ groupResponseName := by
          intro heq
          subst responseName
          simp at hfalse
        simpa [Execution.mergeExecutableGroups, Execution.addExecutableGroup,
          hne] using hmerge

theorem withoutExecutableGroupsWithResponseName_namesNodup
    (responseName : Name)
    (groups : List (Name × List Execution.ExecutableField))
    : executableGroupNamesNodup groups
      -> executableGroupNamesNodup
          (withoutExecutableGroupsWithResponseName responseName groups) := by
  induction groups with
  | nil =>
      simp [withoutExecutableGroupsWithResponseName,
        executableGroupNamesNodup]
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, fields⟩
      intro hnodup
      by_cases hresponse : (groupResponseName == responseName) = true
      · simp [withoutExecutableGroupsWithResponseName, hresponse]
        exact ih hnodup.2
      · have hfalse : (groupResponseName == responseName) = false := by
          cases hmatch : groupResponseName == responseName
          · rfl
          · contradiction
        simp [withoutExecutableGroupsWithResponseName, hfalse,
          executableGroupNamesNodup]
        constructor
        · intro fields hmem
          exact False.elim
            (hnodup.1
              (List.mem_map.mpr
                ⟨(groupResponseName, fields), hmem, rfl⟩))
        · exact ih hnodup.2

theorem collectFields_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    : Execution.collectFields schema variableValues parentType source [] = [] := by
  rfl

theorem collectFields_cons
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selection : Selection) (rest : List Selection)
    : Execution.collectFields schema variableValues parentType source (selection :: rest)
      = Execution.mergeExecutableGroups
          (Execution.collectSelection schema variableValues parentType source selection)
          (Execution.collectFields schema variableValues parentType source rest) := by
  rfl

theorem collectFields_field_noDirectives
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet rest : List Selection)
    : Execution.collectFields schema variableValues parentType source
        (Selection.field responseName fieldName arguments [] selectionSet :: rest)
      = Execution.mergeExecutableGroups
          [(
            responseName,
            [{
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }]
          )]
          (Execution.collectFields schema variableValues parentType source rest) := by
  simp [collectFields_cons, collectSelection_field_noDirectives]

theorem collectFields_inlineFragment_none_directiveFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment none [] selectionSet :: rest)
      = Execution.mergeExecutableGroups
          (Execution.collectFields schema variableValues parentType source selectionSet)
          (Execution.collectFields schema variableValues parentType source rest) := by
  simp [collectFields_cons, collectSelection_inlineFragment_none_noDirectives]

theorem collectFields_inlineFragment_some_directiveFree_apply
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
          = Execution.mergeExecutableGroups
              (Execution.collectFields schema variableValues parentType source
                selectionSet)
              (Execution.collectFields schema variableValues parentType source rest) := by
  intro happly
  simp [collectFields_cons, collectSelection_inlineFragment_some_noDirectives,
    happly]

theorem collectFields_inlineFragment_some_directiveFree_skip
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
          = Execution.mergeExecutableGroups []
              (Execution.collectFields schema variableValues parentType source rest) := by
  intro hskip
  simp [collectFields_cons, collectSelection_inlineFragment_some_noDirectives,
    hskip]

mutual
  theorem collectSelection_wellFormed
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name)
      (source : Execution.ResolverValue ObjectRef)
      (selection : Selection)
      : executableGroupsWellFormed
          (Execution.collectSelection schema variableValues parentType source
            selection) := by
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            Execution.selectionDirectivesAllowBool variableValues directives = true
        · simp [Execution.collectSelection, hallows]
          intro group hgroup
          simp at hgroup
          subst group
          exact executableGroupWellFormed_singleton_field {
            parentType := parentType,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }
        · have hfalse :
              Execution.selectionDirectivesAllowBool variableValues directives =
                false := by
            cases hmatch :
                Execution.selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [Execution.collectSelection, hfalse,
            executableGroupsWellFormed_nil]
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · simp [Execution.collectSelection, hallows]
              exact collectFields_wellFormed schema variableValues parentType
                source selectionSet
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupsWellFormed_nil]
        | some typeCondition =>
            by_cases hallows :
                Execution.selectionDirectivesAllowBool variableValues directives =
                  true
            · by_cases happly :
                Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition = true
              · simp [Execution.collectSelection, hallows, happly]
                exact collectFields_wellFormed schema variableValues parentType
                  source selectionSet
              · have hfalse :
                    Execution.doesFragmentTypeApplyBool schema parentType source
                      typeCondition = false := by
                  cases hmatch :
                      Execution.doesFragmentTypeApplyBool schema parentType
                        source typeCondition
                  · rfl
                  · contradiction
                simp [Execution.collectSelection, hallows, hfalse,
                  executableGroupsWellFormed_nil]
            · have hfalse :
                  Execution.selectionDirectivesAllowBool variableValues
                    directives = false := by
                cases hmatch :
                    Execution.selectionDirectivesAllowBool variableValues
                      directives
                · rfl
                · contradiction
              simp [Execution.collectSelection, hfalse,
                executableGroupsWellFormed_nil]

  theorem collectFields_wellFormed
      (schema : Schema) (variableValues : Execution.VariableValues)
      (parentType : Name)
      (source : Execution.ResolverValue ObjectRef)
      (selectionSet : List Selection)
      : executableGroupsWellFormed
          (Execution.collectFields schema variableValues parentType source
            selectionSet) := by
    cases selectionSet with
    | nil =>
        simp [Execution.collectFields, executableGroupsWellFormed_nil]
    | cons selection rest =>
        simp [Execution.collectFields]
        exact mergeExecutableGroups_wellFormed
          (Execution.collectSelection schema variableValues parentType source
            selection)
          (Execution.collectFields schema variableValues parentType source rest)
          (collectSelection_wellFormed schema variableValues parentType source
            selection)
          (collectFields_wellFormed schema variableValues parentType source
            rest)
end

theorem collectFields_inlineFragment_none_directiveFree_flatten
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.collectFields schema variableValues parentType source
        (Selection.inlineFragment none [] selectionSet :: rest)
      = Execution.collectFields schema variableValues parentType source
          (selectionSet ++ rest) := by
  rw [collectFields_inlineFragment_none_directiveFree]
  rw [collectFields_append]

theorem collectFields_inlineFragment_some_directiveFree_apply_flatten
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = true
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
          = Execution.collectFields schema variableValues parentType source
              (selectionSet ++ rest) := by
  intro happly
  rw [collectFields_inlineFragment_some_directiveFree_apply]
  · rw [collectFields_append]
  · exact happly

theorem collectFields_responseName_not_mem_of_responseNameFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName : Name)
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> ∀ selectionSet,
          selectionSetDirectiveFree selectionSet
          -> selectionSetResponseNameFree schema parentType responseName selectionSet
          -> responseName
              ∉ (Execution.collectFields schema variableValues parentType
                  source selectionSet).map
                  Prod.fst
  | hobject, hsource, [], _hfree, _hresponseFree => by
      simp [Execution.collectFields]
  | hobject, hsource,
      Selection.field fieldResponseName fieldName arguments directives
        selectionSet :: rest,
      hfree, hresponseFree => by
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailResponseFree := selectionSetResponseNameFree_tail hresponseFree
      have hfieldNe : fieldResponseName ≠ responseName := by
        have hheadResponseFree :=
          selectionSetResponseNameFree_head hresponseFree
        simpa [selectionResponseNameFree] using hheadResponseFree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      rw [collectFields_field_noDirectives]
      intro hmem
      have hcases :=
        (mergeExecutableGroups_mem_responseName
          [(fieldResponseName, [{
            parentType := parentType,
            responseName := fieldResponseName,
            fieldName := fieldName,
            arguments := arguments,
            selectionSet := selectionSet
          }])]
          (Execution.collectFields schema variableValues parentType source
            rest)
          responseName).mp hmem
      cases hcases with
      | inl hhead =>
          simp at hhead
          exact hfieldNe hhead.symm
      | inr htail =>
          exact
            collectFields_responseName_not_mem_of_responseNameFree schema
              variableValues parentType source responseName hobject hsource
              rest htailFree htailResponseFree htail
  | hobject, hsource,
      Selection.inlineFragment none directives selectionSet :: rest,
      hfree, hresponseFree => by
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailResponseFree := selectionSetResponseNameFree_tail hresponseFree
      have hheadResponseFree := selectionSetResponseNameFree_head hresponseFree
      have hselectionResponseFree :
          selectionSetResponseNameFree schema parentType responseName
            selectionSet := by
        simpa [selectionResponseNameFree] using hheadResponseFree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      have hselectionFree : selectionSetDirectiveFree selectionSet := by
        simpa [selectionDirectiveFree, hdirectives] using hheadFree.2
      subst directives
      rw [collectFields_inlineFragment_none_directiveFree]
      intro hmem
      have hcases :=
        (mergeExecutableGroups_mem_responseName
          (Execution.collectFields schema variableValues parentType source
            selectionSet)
          (Execution.collectFields schema variableValues parentType source
            rest)
          responseName).mp hmem
      cases hcases with
      | inl hselection =>
          exact
            collectFields_responseName_not_mem_of_responseNameFree schema
              variableValues parentType source responseName hobject hsource
              selectionSet hselectionFree hselectionResponseFree hselection
      | inr htail =>
          exact
            collectFields_responseName_not_mem_of_responseNameFree schema
              variableValues parentType source responseName hobject hsource
              rest htailFree htailResponseFree htail
  | hobject, hsource,
      Selection.inlineFragment (some typeCondition) directives selectionSet
        :: rest,
      hfree, hresponseFree => by
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailResponseFree := selectionSetResponseNameFree_tail hresponseFree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      have hselectionFree : selectionSetDirectiveFree selectionSet := by
        simpa [selectionDirectiveFree, hdirectives] using hheadFree.2
      subst directives
      cases happly :
          Execution.doesFragmentTypeApplyBool schema parentType source
            typeCondition
      · rw [collectFields_inlineFragment_some_directiveFree_skip]
        · intro hmem
          have hcases :=
            (mergeExecutableGroups_mem_responseName []
              (Execution.collectFields schema variableValues parentType source
                rest)
              responseName).mp hmem
          cases hcases with
          | inl hnil =>
              simp at hnil
          | inr htail =>
              exact collectFields_responseName_not_mem_of_responseNameFree
                schema variableValues parentType source responseName hobject
                hsource rest htailFree htailResponseFree htail
        · exact happly
      · have hoverlap :
            schema.typesOverlapBool parentType typeCondition = true := by
          rw [← doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
            schema hobject hsource]
          exact happly
        have hheadResponseFree := selectionSetResponseNameFree_head hresponseFree
        have hselectionResponseFree :
            selectionSetResponseNameFree schema parentType responseName
              selectionSet := by
          simpa [selectionResponseNameFree, hoverlap] using hheadResponseFree
        rw [collectFields_inlineFragment_some_directiveFree_apply]
        · intro hmem
          have hcases :=
            (mergeExecutableGroups_mem_responseName
              (Execution.collectFields schema variableValues parentType source
                selectionSet)
              (Execution.collectFields schema variableValues parentType source
                rest)
              responseName).mp hmem
          cases hcases with
          | inl hselection =>
              exact
                collectFields_responseName_not_mem_of_responseNameFree schema
                  variableValues parentType source responseName hobject
                  hsource selectionSet hselectionFree hselectionResponseFree
                  hselection
          | inr htail =>
              exact
                collectFields_responseName_not_mem_of_responseNameFree schema
                  variableValues parentType source responseName hobject
                  hsource rest htailFree htailResponseFree htail
        · exact happly

theorem collectFields_field_noDirectives_cons_of_responseName_not_mem
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet rest : List Selection)
    : responseName
        ∉ (Execution.collectFields schema variableValues parentType source rest).map
            Prod.fst
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments [] selectionSet :: rest)
          = (
              responseName,
              [{
                parentType := parentType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }]
            )
            :: Execution.collectFields schema variableValues parentType source rest := by
  intro hnotin
  rw [collectFields_field_noDirectives]
  rw [mergeExecutableGroups_eq_append_of_namesDisjoint]
  · simp
  · intro name hleft hright
    simp at hleft
    subst name
    exact hnotin hright
  · exact collectFields_namesNodup schema variableValues parentType source rest

theorem collectFields_field_head_exists
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (selectionSet rest : List Selection)
    : ∃ sourceFields sourceRest,
        Execution.collectFields schema variableValues parentType source
          (Selection.field responseName fieldName arguments [] selectionSet :: rest)
        = (
            responseName,
            {
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }
            :: sourceFields
          )
          :: sourceRest := by
  let sourceField : Execution.ExecutableField :=
    {
      parentType := parentType,
      responseName := responseName,
      fieldName := fieldName,
      arguments := arguments,
      selectionSet := selectionSet
    }
  let restGroups :=
    Execution.collectFields schema variableValues parentType source rest
  rcases mergeExecutableGroups_preserves_head responseName [sourceField]
      [] restGroups with
    ⟨appendedFields, sourceRest, hmerge⟩
  refine ⟨appendedFields, sourceRest, ?_⟩
  rw [collectFields_field_noDirectives]
  simpa [sourceField, restGroups] using hmerge

theorem collectFields_withoutFieldSelectionsWithResponseName_directiveFree
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName : Name)
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> ∀ selectionSet,
          selectionSetDirectiveFree selectionSet
          -> Execution.collectFields schema variableValues parentType source
                (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
              = withoutExecutableGroupsWithResponseName responseName
                  (Execution.collectFields schema variableValues parentType
                    source selectionSet)
  | hobject, hsource, [], _hfree => by
      simp [Execution.collectFields, withoutFieldSelectionsWithResponseName,
        withoutExecutableGroupsWithResponseName]
  | hobject, hsource,
      Selection.field fieldResponseName fieldName arguments directives
        selectionSet :: rest,
      hfree => by
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      by_cases hresponse : (fieldResponseName == responseName) = true
      · rw [withoutFieldSelectionsWithResponseName]
        simp [hresponse]
        rw [collectFields_field_noDirectives]
        rw [withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
        have hsingleton :
            withoutExecutableGroupsWithResponseName responseName
              [(fieldResponseName, [{
                parentType := parentType,
                responseName := fieldResponseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }])]
            = [] := by
          simp [withoutExecutableGroupsWithResponseName, hresponse]
        rw [hsingleton]
        have hrest :=
          collectFields_withoutFieldSelectionsWithResponseName_directiveFree schema
            variableValues parentType source responseName hobject hsource
            rest htailFree
        rw [hrest]
        exact (mergeExecutableGroups_nil_left_of_namesNodup
          (withoutExecutableGroupsWithResponseName responseName
            (Execution.collectFields schema variableValues parentType source
              rest))
          (withoutExecutableGroupsWithResponseName_namesNodup responseName
            (Execution.collectFields schema variableValues parentType source
              rest)
            (collectFields_namesNodup schema variableValues parentType
              source rest))).symm
      · have hfalse : (fieldResponseName == responseName) = false := by
          cases hmatch : fieldResponseName == responseName
          · rfl
          · contradiction
        rw [withoutFieldSelectionsWithResponseName]
        simp [hfalse]
        rw [collectFields_field_noDirectives]
        rw [collectFields_field_noDirectives]
        rw [withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
        have hsingleton :
            withoutExecutableGroupsWithResponseName responseName
              [(fieldResponseName, [{
                parentType := parentType,
                responseName := fieldResponseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }])]
            =
            [(fieldResponseName, [{
              parentType := parentType,
              responseName := fieldResponseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := selectionSet
            }])] := by
          simp [withoutExecutableGroupsWithResponseName, hfalse]
        rw [hsingleton]
        rw [collectFields_withoutFieldSelectionsWithResponseName_directiveFree schema
          variableValues parentType source responseName hobject hsource rest
          htailFree]
  | hobject, hsource,
      Selection.inlineFragment none directives selectionSet :: rest,
      hfree => by
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      have hselectionFree : selectionSetDirectiveFree selectionSet := by
        simpa [selectionDirectiveFree, hdirectives] using hheadFree.2
      subst directives
      rw [withoutFieldSelectionsWithResponseName]
      rw [collectFields_inlineFragment_none_directiveFree]
      rw [collectFields_inlineFragment_none_directiveFree]
      rw [withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
      rw [collectFields_withoutFieldSelectionsWithResponseName_directiveFree schema
        variableValues parentType source responseName hobject hsource
        selectionSet hselectionFree]
      rw [collectFields_withoutFieldSelectionsWithResponseName_directiveFree schema
        variableValues parentType source responseName hobject hsource rest
        htailFree]
  | hobject, hsource,
      Selection.inlineFragment (some typeCondition) directives selectionSet
        :: rest,
      hfree => by
      have hheadFree := selectionSetDirectiveFree_head hfree
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      have hselectionFree : selectionSetDirectiveFree selectionSet := by
        simpa [selectionDirectiveFree, hdirectives] using hheadFree.2
      subst directives
      cases happly :
          Execution.doesFragmentTypeApplyBool schema parentType source
            typeCondition
      · have hoverlapFalse :
            schema.typesOverlapBool parentType typeCondition = false := by
          rw [← doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
            schema hobject hsource]
          exact happly
        simp [withoutFieldSelectionsWithResponseName]
        rw [collectFields_inlineFragment_some_directiveFree_skip]
        · rw [collectFields_inlineFragment_some_directiveFree_skip]
          · rw [mergeExecutableGroups_nil_left_of_namesNodup
              (Execution.collectFields schema variableValues parentType source
                rest)
              (collectFields_namesNodup schema variableValues parentType
                source rest)]
            rw [mergeExecutableGroups_nil_left_of_namesNodup
              (Execution.collectFields schema variableValues parentType source
                (withoutFieldSelectionsWithResponseName schema responseName rest))
              (collectFields_namesNodup schema variableValues parentType
                source (withoutFieldSelectionsWithResponseName schema responseName
                  rest))]
            exact collectFields_withoutFieldSelectionsWithResponseName_directiveFree
              schema variableValues parentType source responseName hobject
              hsource rest htailFree
          · exact happly
        · exact happly
      · have hoverlap :
            schema.typesOverlapBool parentType typeCondition = true := by
          rw [← doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
            schema hobject hsource]
          exact happly
        simp [withoutFieldSelectionsWithResponseName]
        rw [collectFields_inlineFragment_some_directiveFree_apply]
        · rw [collectFields_inlineFragment_some_directiveFree_apply]
          · rw [withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
            rw [collectFields_withoutFieldSelectionsWithResponseName_directiveFree
              schema variableValues parentType source responseName hobject
              hsource selectionSet hselectionFree]
            rw [collectFields_withoutFieldSelectionsWithResponseName_directiveFree
              schema variableValues parentType source responseName hobject
              hsource rest htailFree]
          · exact happly
        · exact happly

theorem collectFields_withoutFieldSelectionsWithResponseName_eq_sourceRest_of_cons
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName : Name) (fields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    (selectionSet : List Selection)
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree selectionSet
      -> Execution.collectFields schema variableValues parentType source selectionSet
          = (responseName, fields) :: sourceRest
      -> Execution.collectFields schema variableValues parentType source
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
          = sourceRest := by
  intro hobject hsource hfree hcollect
  have hfilter :=
    collectFields_withoutFieldSelectionsWithResponseName_directiveFree schema
      variableValues parentType source responseName hobject hsource
      selectionSet hfree
  have hnodup :
      executableGroupNamesNodup ((responseName, fields) :: sourceRest) := by
    simpa [hcollect] using
      collectFields_namesNodup schema variableValues parentType source
        selectionSet
  rw [hcollect] at hfilter
  exact hfilter.trans
    (withoutExecutableGroupsWithResponseName_cons_self_of_namesNodup
      responseName fields sourceRest hnodup)

theorem collectFields_withoutFieldSelectionsWithResponseName_fieldHead_rest_eq_sourceRest
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (responseName fieldName : Name)
    (arguments : List Argument) (subselections rest : List Selection)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    : let sourceField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := subselections
        }
      objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree
          (Selection.field responseName fieldName arguments [] subselections :: rest)
      -> Execution.collectFields schema variableValues parentType source
            (Selection.field responseName fieldName arguments [] subselections :: rest)
          = (responseName, sourceField :: sourceFields) :: sourceRest
      -> Execution.collectFields schema variableValues parentType source
            (withoutFieldSelectionsWithResponseName schema responseName rest)
          = sourceRest := by
  intro sourceField hobject hsource hfree hcollect
  have hrestFree := selectionSetDirectiveFree_tail hfree
  have hsourceCollect :
      Execution.collectFields schema variableValues parentType source
        (Selection.field responseName fieldName arguments [] subselections
          :: rest)
      =
      (responseName, sourceField :: sourceFields) :: sourceRest := by
    simpa [sourceField] using hcollect
  have hfilteredAll :=
    collectFields_withoutFieldSelectionsWithResponseName_eq_sourceRest_of_cons schema
      variableValues parentType source responseName
      (sourceField :: sourceFields) sourceRest
      (Selection.field responseName fieldName arguments [] subselections
        :: rest)
      hobject hsource hfree hsourceCollect
  simpa [withoutFieldSelectionsWithResponseName] using hfilteredAll

theorem mergeSelectionSets_append (left right : List Selection)
    : mergeSelectionSets (left ++ right)
      = mergeSelectionSets left ++ mergeSelectionSets right := by
  induction left with
  | nil =>
      simp [mergeSelectionSets]
  | cons selection rest ih =>
      simp [mergeSelectionSets, ih, List.append_assoc]

theorem collectFields_fieldSelectionsWithResponseNameInScope_responseSelection
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (responseName : Name) (selectionSet : List Selection)
    : objectTypeNameBool schema parentType = true
      -> (∃ runtimeType ref,
            source = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true)
      -> selectionSetDirectiveFree selectionSet
      -> collectedResponseSelectionSet responseName
            (Execution.collectFields schema variableValues parentType source selectionSet)
          = mergeSelectionSets
              (fieldSelectionsWithResponseNameInScope schema parentType responseName
                selectionSet) := by
  intro hobject hsource hfree
  induction selectionSet
    using fieldSelectionsWithResponseNameInScope.induct schema parentType
            responseName with
  | case1 =>
      simp [Execution.collectFields, fieldSelectionsWithResponseNameInScope,
        collectedResponseSelectionSet, mergeSelectionSets]
  | case2 rest selectionResponseName fieldName arguments directives
      fieldSelectionSet hname hrest =>
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have hrestProjection := hrest hrestFree
      have hsingleton :
          collectedResponseSelectionSet responseName
            [(selectionResponseName, [{
              parentType := parentType,
              responseName := selectionResponseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := fieldSelectionSet
            }])]
          =
          fieldSelectionSet := by
        have hresponse : selectionResponseName = responseName :=
          beq_iff_eq.mp hname
        subst selectionResponseName
        simp [collectedResponseSelectionSet,
          Execution.mergedFieldSelectionSet]
      rw [collectFields_field_noDirectives]
      rw [collectedResponseSelectionSet_mergeExecutableGroups]
      · simp [fieldSelectionsWithResponseNameInScope, hname, mergeSelectionSets,
          Selection.subselections, hsingleton, hrestProjection]
      · exact collectFields_namesNodup schema variableValues parentType source
          rest
  | case3 rest selectionResponseName fieldName arguments directives
      fieldSelectionSet hname hrest =>
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have hrestProjection := hrest hrestFree
      have hsingleton :
          collectedResponseSelectionSet responseName
            [(selectionResponseName, [{
              parentType := parentType,
              responseName := selectionResponseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := fieldSelectionSet
            }])]
          =
          [] := by
        have hresponseFalse : (selectionResponseName == responseName) = false := by
          cases hmatch : selectionResponseName == responseName
          · rfl
          · exact False.elim (hname hmatch)
        simp [collectedResponseSelectionSet, hresponseFalse]
      rw [collectFields_field_noDirectives]
      rw [collectedResponseSelectionSet_mergeExecutableGroups]
      · simp [fieldSelectionsWithResponseNameInScope, hname, hsingleton,
          hrestProjection]
      · exact collectFields_namesNodup schema variableValues parentType source
          rest
  | case4 rest directives fragmentSelectionSet hfragment hrest =>
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      have hfragmentFree : selectionSetDirectiveFree fragmentSelectionSet := by
        simpa [selectionDirectiveFree, hdirectives] using hheadFree.2
      subst directives
      have hfragmentProjection := hfragment hfragmentFree
      have hrestProjection := hrest hrestFree
      rw [collectFields_inlineFragment_none_directiveFree]
      rw [collectedResponseSelectionSet_mergeExecutableGroups]
      · simp [fieldSelectionsWithResponseNameInScope, mergeSelectionSets_append,
          hfragmentProjection, hrestProjection]
      · exact collectFields_namesNodup schema variableValues parentType source
          rest
  | case5 rest typeCondition directives fragmentSelectionSet hoverlap hrest
      hfragment =>
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      have hfragmentFree : selectionSetDirectiveFree fragmentSelectionSet := by
        simpa [selectionDirectiveFree, hdirectives] using hheadFree.2
      subst directives
      have happly :
          Execution.doesFragmentTypeApplyBool schema parentType source
            typeCondition = true := by
        rw [doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
          schema hobject hsource]
        exact hoverlap
      have hfragmentProjection := hfragment hfragmentFree
      have hrestProjection := hrest hrestFree
      rw [collectFields_inlineFragment_some_directiveFree_apply]
      · rw [collectedResponseSelectionSet_mergeExecutableGroups]
        · simp [fieldSelectionsWithResponseNameInScope, hoverlap,
            mergeSelectionSets_append, hfragmentProjection, hrestProjection]
        · exact collectFields_namesNodup schema variableValues parentType source
            rest
      · exact happly
  | case6 rest typeCondition directives fragmentSelectionSet hoverlap hrest =>
      have hrestFree := selectionSetDirectiveFree_tail hfree
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have hfalse : schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · exact False.elim (hoverlap hmatch)
      have hskip :
          Execution.doesFragmentTypeApplyBool schema parentType source
            typeCondition = false := by
        rw [doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
          schema hobject hsource]
        exact hfalse
      have hrestProjection := hrest hrestFree
      rw [collectFields_inlineFragment_some_directiveFree_skip]
      · rw [mergeExecutableGroups_nil_left_of_namesNodup
          (Execution.collectFields schema variableValues parentType source rest)
          (collectFields_namesNodup schema variableValues parentType source
            rest)]
        simp [fieldSelectionsWithResponseNameInScope, hfalse, hrestProjection]
      · exact hskip

theorem mergeExecutableGroups_nil_left_collectFields
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : executableGroupNamesNodup
        (Execution.mergeExecutableGroups []
          (Execution.collectFields schema variableValues parentType source
            selectionSet)) := by
  exact mergeExecutableGroups_namesNodup []
    (Execution.collectFields schema variableValues parentType source selectionSet)
    (by simp [executableGroupNamesNodup])

theorem mergeExecutableGroups_nil_left_collectFields_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    : Execution.mergeExecutableGroups []
        (Execution.collectFields schema variableValues parentType source selectionSet)
      = Execution.collectFields schema variableValues parentType source selectionSet := by
  exact mergeExecutableGroups_nil_left_of_namesNodup
    (Execution.collectFields schema variableValues parentType source selectionSet)
    (collectFields_namesNodup schema variableValues parentType source
      selectionSet)

theorem collectFields_inlineFragment_some_directiveFree_skip_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType typeCondition : Name)
    (source : Execution.ResolverValue ObjectRef)
    (selectionSet rest : List Selection)
    : Execution.doesFragmentTypeApplyBool schema parentType source typeCondition = false
      -> Execution.collectFields schema variableValues parentType source
            (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest)
          = Execution.collectFields schema variableValues parentType source rest := by
  intro hskip
  rw [collectFields_inlineFragment_some_directiveFree_skip schema
    variableValues parentType typeCondition source selectionSet rest hskip]
  exact mergeExecutableGroups_nil_left_collectFields_eq schema variableValues
    parentType source rest

end GroundTypeNormalization

end NormalForm

end GraphQL
