import GraphQL.Theories.QueryInclusion
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.SelectionConditions
import Proofs.GraphQL.Theories.QueryInclusion.Support.Algorithms.ExecutionUngrouped.Equivalence.Core
import Proofs.GraphQL.Theories.QueryInclusion.Support.SchemaWellFormedness.PossibleTypes
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.LookupValidity
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.RuntimeTypes
import Proofs.GraphQL.Theories.QueryInclusion.Support.Theories.NormalForm.Shared.SemanticReadiness.Readiness
import Proofs.GraphQL.Theories.QueryInclusion.Support.Validation.FieldMerge

/-! Supporting lemmas extracted from commit `7797374fd` for the talk exercises. -/

namespace GraphQL.Algorithms.ExecutionUngroupedUncached.Eager

open GraphQL.Execution

def collectedExecutableFields : List (Name × List ExecutableField) -> List ExecutableField
  | [] => []
  | (_responseName, fields) :: rest =>
      fields ++ collectedExecutableFields rest

def collectedExecutableEntries
    : List (Name × List ExecutableField) -> List (Name × ExecutableField)
  | [] => []
  | (responseName, fields) :: rest =>
      fields.map (fun field => (responseName, field)) ++ collectedExecutableEntries rest

def ExecutableEntriesRuntimeScopedBy
    (schema : Schema) (runtimeType : Name)
    (scopedFields : List FieldMerge.ScopedField)
    (entries : List (Name × ExecutableField))
    : Prop :=
  ∀ entry,
    entry ∈ entries
    -> ∃ scopedField,
        scopedField ∈ scopedFields
        ∧ scopedField.responseName = entry.1
        ∧ ScopedFieldMatchesExecutableIdentity scopedField entry.2
        ∧ ScopedFieldRuntimeApplies schema runtimeType scopedField

theorem collectedExecutableFields_mem_of_group_mem
    {groups : List (Name × List ExecutableField)}
    {responseName : Name} {fields : List ExecutableField}
    {field : ExecutableField}
    : (responseName, fields) ∈ groups
      -> field ∈ fields
      -> field ∈ collectedExecutableFields groups := by
  intro hgroup hfield
  induction groups with
  | nil =>
      simp at hgroup
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, groupFields⟩
      simp [collectedExecutableFields] at hgroup ⊢
      rcases hgroup with hhead | htail
      · rcases hhead with ⟨_hresponseName, hfields⟩
        cases hfields
        exact Or.inl hfield
      · exact Or.inr (ih htail)

theorem collectedExecutableEntries_mem_of_group_mem
    {groups : List (Name × List ExecutableField)}
    {responseName : Name} {fields : List ExecutableField}
    {field : ExecutableField}
    : (responseName, fields) ∈ groups
      -> field ∈ fields
      -> (responseName, field) ∈ collectedExecutableEntries groups := by
  intro hgroup hfield
  induction groups with
  | nil => simp at hgroup
  | cons group rest ih =>
      rcases group with ⟨groupResponseName, groupFields⟩
      rcases List.mem_cons.mp hgroup with hhead | htail
      · cases hhead
        simp [collectedExecutableEntries, hfield]
      · simp [collectedExecutableEntries, ih htail]

theorem collectedExecutableFields_mem_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (field : ExecutableField)
    : field
        ∈ collectedExecutableFields (GraphQL.Execution.addExecutableGroup group groups)
      ↔ field ∈ group.snd ∨ field ∈ collectedExecutableFields groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hname, List.mem_append]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hgroupOrRest
          · exact Or.inr (Or.inl hcurrent)
          · rcases hgroupOrRest with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (Or.inr hrest)
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (Or.inl hgroup)
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (Or.inr hrest)
      · have hfalse : (currentName == groupName) = false := by
          cases hmatch : currentName == groupName
          · rfl
          · contradiction
        simp [collectedExecutableFields, GraphQL.Execution.addExecutableGroup,
          hfalse, List.mem_append]
        constructor
        · intro hmem
          rcases hmem with hcurrent | hadded
          · exact Or.inr (Or.inl hcurrent)
          · rcases ih.mp hadded with hgroup | hrest
            · exact Or.inl hgroup
            · exact Or.inr (Or.inr hrest)
        · intro hmem
          rcases hmem with hgroup | hcurrentOrRest
          · exact Or.inr (ih.mpr (Or.inl hgroup))
          · rcases hcurrentOrRest with hcurrent | hrest
            · exact Or.inl hcurrent
            · exact Or.inr (ih.mpr (Or.inr hrest))

theorem collectedExecutableFields_mem_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    (field : ExecutableField)
    : field
        ∈ collectedExecutableFields (GraphQL.Execution.mergeExecutableGroups left right)
      ↔ field ∈ collectedExecutableFields left
        ∨ field ∈ collectedExecutableFields right := by
  induction right generalizing left with
  | nil =>
      simp [collectedExecutableFields, GraphQL.Execution.mergeExecutableGroups]
  | cons group rest ih =>
      rcases group with ⟨responseName, fields⟩
      change
        field ∈
            collectedExecutableFields
              (GraphQL.Execution.mergeExecutableGroups
                (GraphQL.Execution.addExecutableGroup (responseName, fields)
                  left) rest)
          ↔
        field ∈ collectedExecutableFields left
          ∨ field ∈ collectedExecutableFields ((responseName, fields) :: rest)
      constructor
      · intro hmem
        rcases
            (ih
              (GraphQL.Execution.addExecutableGroup (responseName, fields)
                left)).mp hmem with hadded | hrest
        · rcases
            (collectedExecutableFields_mem_addExecutableGroup
              (responseName, fields) left field).mp hadded with
            hfield | hleft
          · exact Or.inr (by simp [collectedExecutableFields, hfield])
          · exact Or.inl hleft
        · exact Or.inr (by simp [collectedExecutableFields, hrest])
      · intro hmem
        rcases hmem with hleft | hright
        · exact (ih
                  (GraphQL.Execution.addExecutableGroup (responseName, fields) left)).mpr
                  (Or.inl
                    ((collectedExecutableFields_mem_addExecutableGroup
                        (responseName, fields) left field).mpr
                      (Or.inr hleft)))
        · have hfieldsOrRest :
              field ∈ fields ∨ field ∈ collectedExecutableFields rest := by
            simpa [collectedExecutableFields, List.mem_append] using hright
          rcases hfieldsOrRest with hfield | hrest
          · exact (ih
                    (GraphQL.Execution.addExecutableGroup (responseName, fields)
                      left)).mpr
                    (Or.inl
                      ((collectedExecutableFields_mem_addExecutableGroup
                          (responseName, fields) left field).mpr
                        (Or.inl hfield)))
          · exact (ih
                    (GraphQL.Execution.addExecutableGroup (responseName, fields)
                      left)).mpr
                    (Or.inr hrest)

theorem collectedExecutableEntries_mem_addExecutableGroup
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (entry : Name × ExecutableField)
    : entry
        ∈ collectedExecutableEntries (GraphQL.Execution.addExecutableGroup group groups)
      ↔ entry ∈ group.2.map (fun field => (group.1, field))
        ∨ entry ∈ collectedExecutableEntries groups := by
  rcases group with ⟨groupName, groupFields⟩
  induction groups with
  | nil => simp [collectedExecutableEntries, GraphQL.Execution.addExecutableGroup]
  | cons current rest ih =>
      rcases current with ⟨currentName, currentFields⟩
      by_cases hname : (currentName == groupName) = true
      · have heq : currentName = groupName := beq_iff_eq.mp hname
        subst groupName
        simp only [GraphQL.Execution.addExecutableGroup, hname, ite_true,
          collectedExecutableEntries, List.map_append, List.mem_append,
          List.mem_map]
        constructor
        · rintro ((hcurrent | hgroup) | hrest)
          · exact Or.inr (Or.inl hcurrent)
          · exact Or.inl hgroup
          · exact Or.inr (Or.inr hrest)
        · rintro (hgroup | hcurrent | hrest)
          · exact Or.inl (Or.inr hgroup)
          · exact Or.inl (Or.inl hcurrent)
          · exact Or.inr hrest
      · have hfalse : (currentName == groupName) = false := by
          cases hvalue : currentName == groupName
          · rfl
          · contradiction
        simp only [GraphQL.Execution.addExecutableGroup, hfalse,
          Bool.false_eq_true, ite_false, collectedExecutableEntries,
          List.mem_append]
        rw [ih]
        constructor
        · rintro (hcurrent | hgroup | hrest)
          · exact Or.inr (Or.inl hcurrent)
          · exact Or.inl hgroup
          · exact Or.inr (Or.inr hrest)
        · rintro (hgroup | hcurrent | hrest)
          · exact Or.inr (Or.inl hgroup)
          · exact Or.inl hcurrent
          · exact Or.inr (Or.inr hrest)

theorem collectedExecutableEntries_mem_mergeExecutableGroups
    (left right : List (Name × List ExecutableField))
    (entry : Name × ExecutableField)
    : entry
        ∈ collectedExecutableEntries (GraphQL.Execution.mergeExecutableGroups left right)
      ↔ entry ∈ collectedExecutableEntries left
        ∨ entry ∈ collectedExecutableEntries right := by
  induction right generalizing left with
  | nil => simp [GraphQL.Execution.mergeExecutableGroups,
      collectedExecutableEntries]
  | cons group rest ih =>
      change entry ∈ collectedExecutableEntries
          (GraphQL.Execution.mergeExecutableGroups
            (GraphQL.Execution.addExecutableGroup group left) rest)
        ↔ entry ∈ collectedExecutableEntries left
          ∨ entry ∈ collectedExecutableEntries (group :: rest)
      rw [ih, collectedExecutableEntries_mem_addExecutableGroup]
      simp [collectedExecutableEntries, or_assoc, or_left_comm]

mutual
  theorem collectSelection_entriesRuntimeScopedBy_of_selectionLookupValid
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity) (selection : Selection)
      : ScopedParentRuntimeApplies schema runtimeType scopedParent
        -> NormalForm.selectionLookupValid schema scopedParent selection
        -> ExecutableEntriesRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema scopedParent [selection])
            (collectedExecutableEntries
              (GraphQL.Execution.collectSelection schema variableValues collectParent
                (.object runtimeType identity) selection)) := by
    intro hparentRuntime hlookupValid entry hentry
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldLookup : ∃ fieldDefinition,
            schema.lookupField scopedParent fieldName = some fieldDefinition := by
          simpa [NormalForm.selectionLookupValid] using hlookupValid
        rcases hfieldLookup with ⟨fieldDefinition, hlookup⟩
        by_cases hallows : selectionDirectivesAllowBool variableValues directives = true
        · have hentryEq : entry =
              (responseName, {
                fieldName := fieldName
                arguments := arguments
                selectionSet := selectionSet
              }) := by
            simpa [GraphQL.Execution.collectSelection, collectedExecutableEntries,
              hallows]
              using hentry
          subst entry
          refine ⟨{
              parentType := scopedParent
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              outputType := fieldDefinition.outputType
              selectionSet := selectionSet
            }, ?_, rfl, ?_, ?_⟩
          · simp [FieldMerge.collectFields, hlookup]
          · exact ⟨rfl, rfl, rfl⟩
          · simpa [ScopedFieldRuntimeApplies, ScopedParentRuntimeApplies]
              using hparentRuntime
        · have hfalse : selectionDirectivesAllowBool variableValues directives = false := by
            cases hvalue : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableEntries,
            hfalse] at hentry
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            have hchildren : NormalForm.selectionSetLookupValid schema scopedParent
                selectionSet := by
              simpa [NormalForm.selectionLookupValid] using hlookupValid
            by_cases hallows :
              selectionDirectivesAllowBool variableValues directives = true
            · have hrecursive :=
                collectFields_entriesRuntimeScopedBy_of_selectionSetLookupValid schema
                  variableValues collectParent scopedParent runtimeType identity
                  selectionSet hparentRuntime hchildren
              simp [GraphQL.Execution.collectSelection, hallows] at hentry
              rcases hrecursive entry hentry with
                ⟨scopedField, hmem, hname, hmatch, hruntime⟩
              exact ⟨scopedField, by simpa [FieldMerge.collectFields] using hmem,
                hname, hmatch, hruntime⟩
            · have hfalse : selectionDirectivesAllowBool variableValues directives = false := by
                cases hvalue : selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, collectedExecutableEntries,
                hfalse] at hentry
        | some typeCondition =>
            have hchildren : NormalForm.selectionSetLookupValid schema typeCondition
                selectionSet := by
              simpa [NormalForm.selectionLookupValid] using hlookupValid
            by_cases hallows :
              selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly : doesFragmentTypeApplyBool schema collectParent
                  (.object runtimeType identity) typeCondition = true
              · have htypeRuntime :
                    ScopedParentRuntimeApplies schema runtimeType typeCondition := by
                  simpa [ScopedParentRuntimeApplies, doesFragmentTypeApplyBool,
                    runtimeObjectType?]
                    using happly
                have hrecursive :=
                  collectFields_entriesRuntimeScopedBy_of_selectionSetLookupValid schema
                    variableValues collectParent typeCondition runtimeType identity
                    selectionSet htypeRuntime hchildren
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hentry
                rcases hrecursive entry hentry with
                  ⟨scopedField, hmem, hname, hmatch, hruntime⟩
                exact ⟨
                  scopedField,
                  by simpa [FieldMerge.collectFields] using hmem,
                  hname,
                  hmatch,
                  hruntime
                ⟩
              · have hfalse : doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition = false := by
                  cases hvalue : doesFragmentTypeApplyBool schema collectParent
                    (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, collectedExecutableEntries,
                  hallows, hfalse] at hentry
            · have hfalse : selectionDirectivesAllowBool variableValues directives = false := by
                cases hvalue : selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, collectedExecutableEntries,
                hfalse] at hentry

  theorem collectFields_entriesRuntimeScopedBy_of_selectionSetLookupValid
      {ObjectIdentity : Type}
      (schema : Schema) (variableValues : VariableValues)
      (collectParent scopedParent runtimeType : Name)
      (identity : ObjectIdentity) (selectionSet : List Selection)
      : ScopedParentRuntimeApplies schema runtimeType scopedParent
        -> NormalForm.selectionSetLookupValid schema scopedParent selectionSet
        -> ExecutableEntriesRuntimeScopedBy schema runtimeType
            (FieldMerge.collectFields schema scopedParent selectionSet)
            (collectedExecutableEntries
              (GraphQL.Execution.collectFields schema variableValues collectParent
                (.object runtimeType identity) selectionSet)) := by
    intro hparentRuntime hlookupValid entry hentry
    cases selectionSet with
    | nil => simp [GraphQL.Execution.collectFields, collectedExecutableEntries] at hentry
    | cons selection rest =>
        have hlookupValid' : ∀ candidate, candidate ∈ selection :: rest ->
            NormalForm.selectionLookupValid schema scopedParent candidate := by
          simpa [NormalForm.selectionSetLookupValid] using hlookupValid
        have hhead := hlookupValid' selection (by simp)
        have htail : NormalForm.selectionSetLookupValid schema scopedParent rest := by
          simp only [NormalForm.selectionSetLookupValid]
          intro candidate hcandidate
          exact hlookupValid' candidate (by simp [hcandidate])
        have hleft := collectSelection_entriesRuntimeScopedBy_of_selectionLookupValid
          schema variableValues collectParent scopedParent runtimeType identity selection
          hparentRuntime hhead
        have hright := collectFields_entriesRuntimeScopedBy_of_selectionSetLookupValid
          schema variableValues collectParent scopedParent runtimeType identity rest
          hparentRuntime htail
        rcases (collectedExecutableEntries_mem_mergeExecutableGroups
          (GraphQL.Execution.collectSelection schema variableValues collectParent
            (.object runtimeType identity) selection)
          (GraphQL.Execution.collectFields schema variableValues collectParent
            (.object runtimeType identity) rest) entry).mp
            (by simpa [GraphQL.Execution.collectFields] using hentry) with
          hselection | hrest
        · rcases hleft entry hselection with
            ⟨scopedField, hmem, hname, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hname, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl,
            FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inl hmem)
        · rcases hright entry hrest with
            ⟨scopedField, hmem, hname, hmatch, hruntime⟩
          refine ⟨scopedField, ?_, hname, hmatch, hruntime⟩
          rw [show selection :: rest = [selection] ++ rest by rfl,
            FieldMerge.collectFields_append]
          exact List.mem_append.mpr (Or.inr hmem)
end

mutual
  theorem collectSelection_lookupValid_of_selectionSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSemanticsReady schema parentType selection
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType (.object runtimeType identity) selection)
            -> ∃ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition := by
    intro hobject hparentRuntime hready field hfield
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        have hfieldReady :
            ∃ fieldDefinition,
              schema.lookupField parentType fieldName = some fieldDefinition
                ∧ ∀ runtimeType,
                  schema.typeIncludesObjectBool
                      fieldDefinition.outputType.namedType runtimeType =
                    true ->
                  NormalForm.selectionSetSemanticsReady schema runtimeType
                    selectionSet := by
          simpa [NormalForm.selectionSemanticsReady] using hready
        rcases hfieldReady with ⟨fieldDefinition, hlookup, _hchildReady⟩
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          subst field
          exact ⟨fieldDefinition, hlookup⟩
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hbodyReady :
                  NormalForm.selectionSetSemanticsReady schema parentType
                    selectionSet := by
                simpa [NormalForm.selectionSemanticsReady] using hready
              have hrecursive :=
                collectFields_lookupValid_of_selectionSetSemanticsReady_object
                  schema variableValues parentType runtimeType identity
                  selectionSet hobject hparentRuntime hbodyReady
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              exact hrecursive field hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
                hfalse] at hfield
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType
                    (.object runtimeType identity) typeCondition = true
              · have hbodyReady :
                    NormalForm.selectionSetSemanticsReady schema parentType
                      selectionSet := by
                  have hreadyPair :
                      NormalForm.selectionSetLookupValid schema typeCondition
                          selectionSet
                        ∧
                        (schema.typesOverlapBool parentType typeCondition =
                          true ->
                          NormalForm.selectionSetSemanticsReady schema
                            parentType selectionSet) := by
                    simpa [NormalForm.selectionSemanticsReady] using hready
                  have hruntimeEq : runtimeType = parentType :=
                    object_typeIncludesObjectBool_eq_self schema hobject
                      hparentRuntime
                  have htypeIncludes :
                      schema.typeIncludesObjectBool typeCondition parentType =
                        true := by
                    simpa [doesFragmentTypeApplyBool, runtimeObjectType?, hruntimeEq]
                      using happly
                  have hparentIncludes :
                      schema.typeIncludesObjectBool parentType parentType =
                        true :=
                    NormalForm.object_typeIncludesObjectBool_self schema hobject
                  have hoverlap :
                      schema.typesOverlapBool parentType typeCondition =
                        true := by
                    unfold Schema.typesOverlapBool
                    exact List.any_eq_true.mpr
                      ⟨parentType, List.contains_iff_mem.mp hparentIncludes,
                        htypeIncludes⟩
                  exact hreadyPair.2 hoverlap
                have hrecursive :=
                  collectFields_lookupValid_of_selectionSetSemanticsReady_object
                    schema variableValues parentType runtimeType identity
                    selectionSet hobject hparentRuntime hbodyReady
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                exact hrecursive field hfield
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
                  hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
                hfalse] at hfield

  theorem collectFields_lookupValid_of_selectionSetSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType (.object runtimeType identity) selectionSet)
            -> ∃ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition := by
    intro hobject hparentRuntime hready field hfield
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hheadReady :
            NormalForm.selectionSemanticsReady schema parentType selection := by
          unfold NormalForm.selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            NormalForm.selectionSetSemanticsReady schema parentType rest :=
          NormalForm.selectionSetSemanticsReady_tail hready
        have hleft :=
          collectSelection_lookupValid_of_selectionSemanticsReady_object
            schema variableValues parentType runtimeType identity selection
            hobject hparentRuntime hheadReady
        have hright :=
          collectFields_lookupValid_of_selectionSetSemanticsReady_object
            schema variableValues parentType runtimeType identity rest hobject
            hparentRuntime htailReady
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · exact hleft field hselection
        · exact hright field hrest
end

mutual
  theorem collectSelection_childSemanticsReady_of_selectionSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selection : Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSemanticsReady schema parentType selection
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectSelection schema variableValues
                    parentType (.object runtimeType identity) selection)
            -> ∀ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition
                -> ∀ childRuntime,
                    schema.typeIncludesObjectBool
                        fieldDefinition.outputType.namedType childRuntime
                      = true
                    -> NormalForm.selectionSetSemanticsReady schema childRuntime
                        field.selectionSet := by
    intro hobject hparentRuntime hready field hfield fieldDefinition hlookup
      childRuntime hinclude
    cases selection with
    | field responseName fieldName arguments directives selectionSet =>
        by_cases hallows :
            selectionDirectivesAllowBool variableValues directives = true
        · simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hallows] at hfield
          subst field
          have hfieldReady :
              ∃ readyDefinition,
                schema.lookupField parentType fieldName = some readyDefinition
                  ∧ ∀ runtimeType,
                    schema.typeIncludesObjectBool
                        readyDefinition.outputType.namedType runtimeType =
                      true ->
                    NormalForm.selectionSetSemanticsReady schema runtimeType
                      selectionSet := by
            simpa [NormalForm.selectionSemanticsReady] using hready
          rcases hfieldReady with
            ⟨readyDefinition, hreadyLookup, hchildReady⟩
          rw [hlookup] at hreadyLookup
          cases hreadyLookup
          exact hchildReady childRuntime hinclude
        · have hfalse :
              selectionDirectivesAllowBool variableValues directives = false := by
            cases hmatch : selectionDirectivesAllowBool variableValues directives
            · rfl
            · contradiction
          simp [GraphQL.Execution.collectSelection, collectedExecutableFields,
            hfalse] at hfield
    | inlineFragment typeCondition directives selectionSet =>
        cases typeCondition with
        | none =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · have hbodyReady :
                  NormalForm.selectionSetSemanticsReady schema parentType
                    selectionSet := by
                simpa [NormalForm.selectionSemanticsReady] using hready
              have hrecursive :=
                collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
                  schema variableValues parentType runtimeType identity
                  selectionSet hobject hparentRuntime hbodyReady
              simp [GraphQL.Execution.collectSelection, hallows] at hfield
              exact hrecursive field hfield fieldDefinition hlookup
                childRuntime hinclude
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield
        | some typeCondition =>
            by_cases hallows :
                selectionDirectivesAllowBool variableValues directives = true
            · by_cases happly :
                  doesFragmentTypeApplyBool schema parentType
                    (.object runtimeType identity) typeCondition = true
              · have hbodyReady :
                    NormalForm.selectionSetSemanticsReady schema parentType
                      selectionSet := by
                  have hreadyPair :
                      NormalForm.selectionSetLookupValid schema typeCondition
                          selectionSet
                        ∧
                        (schema.typesOverlapBool parentType typeCondition =
                          true ->
                          NormalForm.selectionSetSemanticsReady schema
                            parentType selectionSet) := by
                    simpa [NormalForm.selectionSemanticsReady] using hready
                  have hruntimeEq : runtimeType = parentType :=
                    object_typeIncludesObjectBool_eq_self schema hobject
                      hparentRuntime
                  have htypeIncludes :
                      schema.typeIncludesObjectBool typeCondition parentType =
                        true := by
                    simpa [doesFragmentTypeApplyBool, runtimeObjectType?, hruntimeEq]
                      using happly
                  have hparentIncludes :
                      schema.typeIncludesObjectBool parentType parentType =
                        true :=
                    NormalForm.object_typeIncludesObjectBool_self schema hobject
                  have hoverlap :
                      schema.typesOverlapBool parentType typeCondition =
                        true := by
                    unfold Schema.typesOverlapBool
                    exact List.any_eq_true.mpr
                      ⟨parentType, List.contains_iff_mem.mp hparentIncludes,
                        htypeIncludes⟩
                  exact hreadyPair.2 hoverlap
                have hrecursive :=
                  collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
                    schema variableValues parentType runtimeType identity
                    selectionSet hobject hparentRuntime hbodyReady
                simp [GraphQL.Execution.collectSelection, hallows, happly] at hfield
                exact hrecursive field hfield fieldDefinition hlookup
                  childRuntime hinclude
              · have hfalse :
                    doesFragmentTypeApplyBool schema parentType
                      (.object runtimeType identity) typeCondition = false := by
                  cases hmatch :
                      doesFragmentTypeApplyBool schema parentType
                        (.object runtimeType identity) typeCondition
                  · rfl
                  · contradiction
                simp [GraphQL.Execution.collectSelection,
                  collectedExecutableFields, hallows, hfalse] at hfield
            · have hfalse :
                  selectionDirectivesAllowBool variableValues directives =
                    false := by
                cases hmatch :
                    selectionDirectivesAllowBool variableValues directives
                · rfl
                · contradiction
              simp [GraphQL.Execution.collectSelection,
                collectedExecutableFields, hfalse] at hfield

  theorem collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
      {ObjectIdentity : Type}
      (schema : Schema)
      (variableValues : VariableValues)
      (parentType runtimeType : Name)
      (identity : ObjectIdentity)
      (selectionSet : List Selection)
      : schema.objectType parentType
        -> ScopedParentRuntimeApplies schema runtimeType parentType
        -> NormalForm.selectionSetSemanticsReady schema parentType selectionSet
        -> ∀ field,
            field
              ∈ collectedExecutableFields
                  (GraphQL.Execution.collectFields schema variableValues
                    parentType (.object runtimeType identity) selectionSet)
            -> ∀ fieldDefinition,
                schema.lookupField parentType field.fieldName = some fieldDefinition
                -> ∀ childRuntime,
                    schema.typeIncludesObjectBool
                        fieldDefinition.outputType.namedType childRuntime
                      = true
                    -> NormalForm.selectionSetSemanticsReady schema childRuntime
                        field.selectionSet := by
    intro hobject hparentRuntime hready field hfield fieldDefinition hlookup
      childRuntime hinclude
    cases selectionSet with
    | nil =>
        simp [GraphQL.Execution.collectFields, collectedExecutableFields] at hfield
    | cons selection rest =>
        have hheadReady :
            NormalForm.selectionSemanticsReady schema parentType selection := by
          unfold NormalForm.selectionSetSemanticsReady at hready
          exact hready selection (by simp)
        have htailReady :
            NormalForm.selectionSetSemanticsReady schema parentType rest :=
          NormalForm.selectionSetSemanticsReady_tail hready
        have hleft :=
          collectSelection_childSemanticsReady_of_selectionSemanticsReady_object
            schema variableValues parentType runtimeType identity selection
            hobject hparentRuntime hheadReady
        have hright :=
          collectFields_childSemanticsReady_of_selectionSetSemanticsReady_object
            schema variableValues parentType runtimeType identity rest hobject
            hparentRuntime htailReady
        simp [GraphQL.Execution.collectFields] at hfield
        rcases
            (collectedExecutableFields_mem_mergeExecutableGroups
              (GraphQL.Execution.collectSelection schema variableValues
                parentType (.object runtimeType identity) selection)
              (GraphQL.Execution.collectFields schema variableValues parentType
                (.object runtimeType identity) rest)
              field).mp hfield with hselection | hrest
        · exact hleft field hselection fieldDefinition hlookup childRuntime
            hinclude
        · exact hright field hrest fieldDefinition hlookup childRuntime
            hinclude
end

end GraphQL.Algorithms.ExecutionUngroupedUncached.Eager
