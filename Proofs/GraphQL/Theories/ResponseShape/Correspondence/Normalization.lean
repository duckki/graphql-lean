import Proofs.GraphQL.Theories.ResponseShape.Footprint
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.FilterExecution
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.StaticFieldGroups
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Validity.Branches.Filter
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.SelectionSetSemantics

/-!
Collection-level footprint transport through Boolean filtering and ground
normalization.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization

variable {ObjectRef : Type}

/-- Membership of an executable field in some collected response-name group. -/
private def executableFieldMember
    (field : Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) : Prop :=
  ∃ group, group ∈ groups ∧ field ∈ group.snd

private theorem executableFieldMember_cons_iff
    (field : Execution.ExecutableField)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField)) :
    executableFieldMember field (group :: groups)
      ↔ field ∈ group.snd ∨ executableFieldMember field groups := by
  constructor
  · rintro ⟨candidate, hcandidate, hfield⟩
    rcases List.mem_cons.mp hcandidate with hhead | htail
    · subst candidate
      exact Or.inl hfield
    · exact Or.inr ⟨candidate, htail, hfield⟩
  · rintro (hfield | ⟨candidate, hcandidate, hfield⟩)
    · exact ⟨group, by simp, hfield⟩
    · exact ⟨candidate, List.mem_cons_of_mem group hcandidate, hfield⟩

private theorem executableFieldMember_addExecutableGroup_iff
    (field : Execution.ExecutableField)
    (group : Name × List Execution.ExecutableField) :
    ∀ groups,
      executableFieldMember field
          (Execution.addExecutableGroup group groups)
        ↔ executableFieldMember field groups ∨ field ∈ group.snd
  | [] => by
      rcases group with ⟨responseName, fields⟩
      simp [executableFieldMember, Execution.addExecutableGroup]
  | current :: rest => by
      rcases group with ⟨responseName, fields⟩
      rcases current with ⟨currentName, currentFields⟩
      cases hresponse : currentName == responseName
      · rw [Execution.addExecutableGroup]
        simp only [hresponse, Bool.false_eq_true, ↓reduceIte]
        rw [executableFieldMember_cons_iff,
          executableFieldMember_cons_iff,
          executableFieldMember_addExecutableGroup_iff field
            (responseName, fields) rest]
        constructor
        · rintro (hcurrent | hrest | hfields)
          · exact Or.inl (Or.inl hcurrent)
          · exact Or.inl (Or.inr hrest)
          · exact Or.inr hfields
        · rintro ((hcurrent | hrest) | hfields)
          · exact Or.inl hcurrent
          · exact Or.inr (Or.inl hrest)
          · exact Or.inr (Or.inr hfields)
      · rw [Execution.addExecutableGroup]
        simp only [hresponse, ↓reduceIte]
        rw [executableFieldMember_cons_iff,
          executableFieldMember_cons_iff, List.mem_append]
        constructor
        · rintro ((hcurrent | hfields) | hrest)
          · exact Or.inl (Or.inl hcurrent)
          · exact Or.inr hfields
          · exact Or.inl (Or.inr hrest)
        · rintro ((hcurrent | hrest) | hfields)
          · exact Or.inl (Or.inl hcurrent)
          · exact Or.inr hrest
          · exact Or.inl (Or.inr hfields)

private theorem executableFieldMember_mergeExecutableGroups_iff
    (field : Execution.ExecutableField) :
    ∀ left right,
      executableFieldMember field
          (Execution.mergeExecutableGroups left right)
        ↔ executableFieldMember field left ∨ executableFieldMember field right
  | left, [] => by
      simp [Execution.mergeExecutableGroups, executableFieldMember]
  | left, group :: rest => by
      rw [show Execution.mergeExecutableGroups left (group :: rest) =
          Execution.mergeExecutableGroups
            (Execution.addExecutableGroup group left) rest by rfl]
      rw [executableFieldMember_mergeExecutableGroups_iff field
        (Execution.addExecutableGroup group left) rest]
      rw [executableFieldMember_addExecutableGroup_iff]
      constructor
      · rintro ((hleft | hgroup) | hrest)
        · exact Or.inl hleft
        · exact Or.inr
            ((executableFieldMember_cons_iff field group rest).mpr
              (Or.inl hgroup))
        · exact Or.inr
            ((executableFieldMember_cons_iff field group rest).mpr
              (Or.inr hrest))
      · rintro (hleft | hright)
        · exact Or.inl (Or.inl hleft)
        · rcases hright with ⟨candidate, hcandidate, hfield⟩
          rcases List.mem_cons.mp hcandidate with hhead | htail
          · subst candidate
            exact Or.inl (Or.inr hfield)
          · exact Or.inr ⟨candidate, htail, hfield⟩

/--
Validation-side source data for one field reached by runtime collection.  The
parent alternative is exactly the premise needed to compare a collected field
with the concrete-object representative of its response-name group.
-/
private structure RuntimeCollectedFieldSource
    (schema : Schema) (runtimeType validationParent : Name)
    (selectionSet : List Selection) (source : FieldMerge.ScopedField)
    (field : Execution.ExecutableField) : Prop where
  sourceMem : source ∈ FieldMerge.collectFields schema validationParent selectionSet
  parentCondition : source.parentType = runtimeType ∨ ¬ schema.objectType source.parentType
  responseName : source.responseName = field.responseName
  fieldName : source.fieldName = field.fieldName
  arguments : source.arguments = field.arguments
  selectionSet : source.selectionSet = field.selectionSet

private theorem executableFieldMember_collectFields_runtime_source
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (hruntimeObject : schema.objectType runtimeType) :
    ∀ validationParent selectionSet field,
      schema.typeIncludesObjectBool validationParent runtimeType = true
      → selectionSetLookupValid schema validationParent selectionSet
      → executableFieldMember field
          (Execution.collectFields schema variableValues runtimeType
            (.object runtimeType ref) selectionSet)
      → ∃ source,
          RuntimeCollectedFieldSource schema runtimeType validationParent
            selectionSet source field
  | validationParent, [], field, _hincludes, _hlookup, hfield => by
      simp [Execution.collectFields, executableFieldMember] at hfield
  | validationParent,
      Selection.field responseName fieldName arguments directives subselections
        :: rest,
      field, hincludes, hlookupValid, hfield => by
      have hheadLookup :
          selectionLookupValid schema validationParent
            (Selection.field responseName fieldName arguments directives
              subselections) :=
        selectionSetLookupValid_head hlookupValid
      have htailLookup : selectionSetLookupValid schema validationParent rest :=
        selectionSetLookupValid_tail hlookupValid
      simp [selectionLookupValid] at hheadLookup
      rcases hheadLookup with ⟨fieldDefinition, hlookup⟩
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues directives
      · have hcollect :
            Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref)
                (Selection.field responseName fieldName arguments directives
                    subselections :: rest)
              = Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType ref) rest := by
          exact collectFields_field_directives_skipped_eq schema variableValues
            runtimeType (.object runtimeType ref) responseName fieldName
            arguments directives subselections rest hallow
        rw [hcollect] at hfield
        rcases executableFieldMember_collectFields_runtime_source schema
            variableValues runtimeType ref hruntimeObject validationParent rest
            field hincludes htailLookup hfield with
          ⟨source, hsource⟩
        refine ⟨source, ?_, hsource.parentCondition,
          hsource.responseName, hsource.fieldName, hsource.arguments,
          hsource.selectionSet⟩
        simpa [FieldMerge.collectFields, hlookup] using
          Or.inr hsource.sourceMem
      · have hmember :
            executableFieldMember field
                [(responseName, [{
                  parentType := runtimeType,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := subselections
                }])]
              ∨ executableFieldMember field
                  (Execution.collectFields schema variableValues runtimeType
                    (.object runtimeType ref) rest) := by
          apply
            (executableFieldMember_mergeExecutableGroups_iff field
              [(responseName, [{
                parentType := runtimeType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := subselections
              }])]
              (Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) rest)).mp
          simpa [Execution.collectFields, Execution.collectSelection, hallow]
            using hfield
        rcases hmember with hhead | htail
        · have hfieldEq :
              field = {
                parentType := runtimeType,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := subselections
              } := by
            rcases hhead with ⟨group, hgroup, hfieldMem⟩
            simp at hgroup
            subst group
            simpa using hfieldMem
          subst field
          let source : FieldMerge.ScopedField := {
            parentType := validationParent,
            responseName := responseName,
            fieldName := fieldName,
            arguments := arguments,
            outputType := fieldDefinition.outputType,
            selectionSet := subselections
          }
          refine ⟨source, ?_, ?_, rfl, rfl, rfl, rfl⟩
          · simp [source, FieldMerge.collectFields, hlookup]
          · by_cases hparentObject : schema.objectType validationParent
            · exact Or.inl (by
                have heq := object_typeIncludesObjectBool_eq_self schema
                  hparentObject hincludes
                simpa [source] using heq.symm)
            · exact Or.inr (by simpa [source] using hparentObject)
        · rcases
            executableFieldMember_collectFields_runtime_source schema
              variableValues runtimeType ref hruntimeObject validationParent rest
              field hincludes htailLookup htail with
            ⟨source, hsource⟩
          refine ⟨source, ?_, hsource.parentCondition,
            hsource.responseName, hsource.fieldName, hsource.arguments,
            hsource.selectionSet⟩
          simpa [FieldMerge.collectFields, hlookup] using Or.inr hsource.sourceMem
  | validationParent,
      Selection.inlineFragment none directives subselections :: rest,
      field, hincludes, hlookupValid, hfield => by
      have hheadLookup :
          selectionLookupValid schema validationParent
            (Selection.inlineFragment none directives subselections) :=
        selectionSetLookupValid_head hlookupValid
      have hbodyLookup : selectionSetLookupValid schema validationParent subselections :=
        by simpa [selectionLookupValid] using hheadLookup
      have htailLookup : selectionSetLookupValid schema validationParent rest :=
        selectionSetLookupValid_tail hlookupValid
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues directives
      · have hcollect :
            Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref)
                (Selection.inlineFragment none directives subselections :: rest)
              = Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType ref) rest := by
          exact collectFields_inlineFragment_none_directives_skipped_eq schema
            variableValues runtimeType (.object runtimeType ref) directives
            subselections rest hallow
        rw [hcollect] at hfield
        rcases executableFieldMember_collectFields_runtime_source schema
            variableValues runtimeType ref hruntimeObject validationParent rest
            field hincludes htailLookup hfield with
          ⟨source, hsource⟩
        refine ⟨source, ?_, hsource.parentCondition,
          hsource.responseName, hsource.fieldName, hsource.arguments,
          hsource.selectionSet⟩
        simpa [FieldMerge.collectFields] using Or.inr hsource.sourceMem
      · have hmember :=
          (executableFieldMember_mergeExecutableGroups_iff field
            (Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ref) subselections)
            (Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ref) rest)).mp
            (by simpa [Execution.collectFields, Execution.collectSelection,
                hallow] using hfield)
        rcases hmember with hbody | htail
        · rcases executableFieldMember_collectFields_runtime_source schema
              variableValues runtimeType ref hruntimeObject validationParent
              subselections field hincludes hbodyLookup hbody with
            ⟨source, hsource⟩
          refine ⟨source, ?_, hsource.parentCondition,
            hsource.responseName, hsource.fieldName, hsource.arguments,
            hsource.selectionSet⟩
          simp [FieldMerge.collectFields, hsource.sourceMem]
        · rcases executableFieldMember_collectFields_runtime_source schema
              variableValues runtimeType ref hruntimeObject validationParent rest
              field hincludes htailLookup htail with
            ⟨source, hsource⟩
          refine ⟨source, ?_, hsource.parentCondition,
            hsource.responseName, hsource.fieldName, hsource.arguments,
            hsource.selectionSet⟩
          simp [FieldMerge.collectFields, hsource.sourceMem]
  | validationParent,
      Selection.inlineFragment (some typeCondition) directives subselections
        :: rest,
      field, hincludes, hlookupValid, hfield => by
      have hheadLookup :
          selectionLookupValid schema validationParent
            (Selection.inlineFragment (some typeCondition) directives
              subselections) :=
        selectionSetLookupValid_head hlookupValid
      have hbodyLookup : selectionSetLookupValid schema typeCondition subselections :=
        by simpa [selectionLookupValid] using hheadLookup
      have htailLookup : selectionSetLookupValid schema validationParent rest :=
        selectionSetLookupValid_tail hlookupValid
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues directives
      · have hcollect :
            Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref)
                (Selection.inlineFragment (some typeCondition) directives
                    subselections :: rest)
              = Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType ref) rest := by
          apply collectFields_inlineFragment_some_directives_skipped_eq_object
          simp [hallow]
        rw [hcollect] at hfield
        rcases executableFieldMember_collectFields_runtime_source schema
            variableValues runtimeType ref hruntimeObject validationParent rest
            field hincludes htailLookup hfield with
          ⟨source, hsource⟩
        refine ⟨source, ?_, hsource.parentCondition,
          hsource.responseName, hsource.fieldName, hsource.arguments,
          hsource.selectionSet⟩
        simpa [FieldMerge.collectFields] using Or.inr hsource.sourceMem
      · cases happly :
            Execution.doesFragmentTypeApplyBool schema runtimeType
              (.object runtimeType ref) typeCondition
        · have hcollect :
              Execution.collectFields schema variableValues runtimeType
                  (.object runtimeType ref)
                  (Selection.inlineFragment (some typeCondition) directives
                      subselections :: rest)
                = Execution.collectFields schema variableValues runtimeType
                    (.object runtimeType ref) rest := by
            apply collectFields_inlineFragment_some_directives_skipped_eq_object
            simpa [hallow, Execution.doesFragmentTypeApplyBool,
              Execution.runtimeObjectType?] using happly
          rw [hcollect] at hfield
          rcases executableFieldMember_collectFields_runtime_source schema
              variableValues runtimeType ref hruntimeObject validationParent rest
              field hincludes htailLookup hfield with
            ⟨source, hsource⟩
          refine ⟨source, ?_, hsource.parentCondition,
            hsource.responseName, hsource.fieldName, hsource.arguments,
            hsource.selectionSet⟩
          simpa [FieldMerge.collectFields] using Or.inr hsource.sourceMem
        · have htypeIncludes :
              schema.typeIncludesObjectBool typeCondition runtimeType = true := by
            simpa [Execution.doesFragmentTypeApplyBool,
              Execution.runtimeObjectType?] using happly
          have hmember :=
            (executableFieldMember_mergeExecutableGroups_iff field
              (Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) subselections)
              (Execution.collectFields schema variableValues runtimeType
                (.object runtimeType ref) rest)).mp
              (by simpa [Execution.collectFields, Execution.collectSelection,
                  hallow, happly] using hfield)
          rcases hmember with hbody | htail
          · rcases executableFieldMember_collectFields_runtime_source schema
                variableValues runtimeType ref hruntimeObject typeCondition
                subselections field htypeIncludes hbodyLookup hbody with
              ⟨source, hsource⟩
            refine ⟨source, ?_, hsource.parentCondition,
              hsource.responseName, hsource.fieldName, hsource.arguments,
              hsource.selectionSet⟩
            simp [FieldMerge.collectFields, hsource.sourceMem]
          · rcases executableFieldMember_collectFields_runtime_source schema
                variableValues runtimeType ref hruntimeObject validationParent
                rest field hincludes htailLookup htail with
              ⟨source, hsource⟩
            refine ⟨source, ?_, hsource.parentCondition,
              hsource.responseName, hsource.fieldName, hsource.arguments,
              hsource.selectionSet⟩
            simp [FieldMerge.collectFields, hsource.sourceMem]

private theorem argumentsEquivalent_trans
    {left middle right : List Argument}
    (hleft : Argument.argumentsEquivalent left middle)
    (hright : Argument.argumentsEquivalent middle right) :
    Argument.argumentsEquivalent left right :=
  Argument.argumentsEquivalent_trans hleft hright

/-- Every matching member of a valid collected response-name group can be
replaced by the source field at that group's normalization head. -/
private theorem executableGroupMatchesPathStep_iff_head
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (ref : ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (subselections rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    (step : PathStep)
    (hobject : schema.objectType parentType)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hlookupValid : selectionSetLookupValid schema parentType
      (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hmerge : FieldMerge.fieldsInSetCanMerge schema parentType
      (Selection.field responseName fieldName arguments [] subselections :: rest))
    (hcollect :
      Execution.collectFields schema variableValues parentType
          (.object parentType ref)
          (Selection.field responseName fieldName arguments [] subselections :: rest)
        = (responseName, {
              parentType := parentType,
              responseName := responseName,
              fieldName := fieldName,
              arguments := arguments,
              selectionSet := subselections
            } :: sourceFields) :: sourceRest) :
    (∃ field,
      field ∈ ({
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      } : Execution.ExecutableField) :: sourceFields
      ∧ executableFieldMatchesPathStep schema field step)
      ↔
    executableFieldMatchesPathStep schema
      {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
      step := by
  let headField : Execution.ExecutableField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    selectionSet := subselections
  }
  let headScoped : FieldMerge.ScopedField := {
    parentType := parentType,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    outputType := fieldDefinition.outputType,
    selectionSet := subselections
  }
  have hheadScoped :
      headScoped ∈ FieldMerge.collectFields schema parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest) := by
    simp [headScoped, FieldMerge.collectFields, hlookup]
  constructor
  · rintro ⟨field, hfield, hmatch⟩
    have hfieldMember : executableFieldMember field
        (Execution.collectFields schema variableValues parentType
          (.object parentType ref)
          (Selection.field responseName fieldName arguments [] subselections
            :: rest)) := by
      refine ⟨(responseName, headField :: sourceFields), ?_, ?_⟩
      · rw [hcollect]
        simp [headField]
      · simpa [headField] using hfield
    rcases executableFieldMember_collectFields_runtime_source schema
        variableValues parentType ref hobject parentType
        (Selection.field responseName fieldName arguments [] subselections
          :: rest)
        field
        (GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
          schema
          (GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
            schema hobject))
        hlookupValid hfieldMember with
      ⟨source, hsource⟩
    have hwellFormed : executableGroupsWellFormed
        ((responseName, headField :: sourceFields) :: sourceRest) := by
      rw [← hcollect]
      exact GroundTypeNormalization.collectFields_wellFormed schema
        variableValues parentType (.object parentType ref)
        (Selection.field responseName fieldName arguments [] subselections
          :: rest)
    have hgroupWellFormed : executableGroupWellFormed
        (responseName, headField :: sourceFields) :=
      hwellFormed _ (by simp)
    have hfieldResponse : field.responseName = responseName :=
      GroundTypeNormalization.executableGroupWellFormed_field_responseName
        hgroupWellFormed (by simpa [headField] using hfield)
    have hresponse : headScoped.responseName = source.responseName := by
      rw [hsource.responseName, hfieldResponse]
    have hfieldMerge :
        FieldMerge.fieldsForNameCanMerge schema headScoped source :=
      FieldMerge.fieldsInSetCanMerge_pair hmerge hheadScoped
        hsource.sourceMem hresponse
    have hparents :
        headScoped.parentType = source.parentType
          ∨ ¬ schema.objectType headScoped.parentType
          ∨ ¬ schema.objectType source.parentType := by
      rcases hsource.parentCondition with hparent | hnotObject
      · exact Or.inl (by simpa [headScoped] using hparent.symm)
      · exact Or.inr (Or.inr hnotObject)
    rcases FieldMerge.fieldsForNameCanMerge_identity hfieldMerge hparents with
      ⟨hfieldName, harguments⟩
    rcases hmatch with
      ⟨hmatchResponse, hmatchFieldName, hmatchArguments,
        matchDefinition, hmatchLookup, hmatchOutput⟩
    refine ⟨?_, ?_, ?_, matchDefinition, hmatchLookup, hmatchOutput⟩
    · exact hfieldResponse.symm.trans hmatchResponse
    · exact (by
        simpa [headScoped] using
          hfieldName.trans (hsource.fieldName.trans hmatchFieldName))
    · exact argumentsEquivalent_trans
        (by simpa [headScoped, hsource.arguments] using harguments)
        hmatchArguments
  · intro hmatch
    exact ⟨headField, by simp [headField], by simpa [headField] using hmatch⟩

/-- At a concrete runtime object, the abstract-return wrapper collects exactly
the normalization branch for that object. -/
private theorem collectFields_possibleTypeNormalizations_runtime_branch_eq
    (schema : Schema) (variableValues : Execution.VariableValues)
    (runtimeType : Name) (ref : ObjectRef)
    (possibleTypes : List Name) (selectionSet : List Selection)
    (hobjects : ∀ objectType,
      objectType ∈ possibleTypes
        → objectTypeNameBool schema objectType = true)
    (hnodup : possibleTypes.Nodup)
    (hmem : runtimeType ∈ possibleTypes) :
    Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ref)
        (GroundTypeNormalization.possibleTypeNormalizations schema
          possibleTypes selectionSet)
      =
    Execution.collectFields schema variableValues runtimeType
      (.object runtimeType ref)
      (normalizeSelectionSet schema runtimeType selectionSet) := by
  induction possibleTypes with
  | nil => simp at hmem
  | cons objectType rest ih =>
      have hobject : objectTypeNameBool schema objectType = true :=
        hobjects objectType (by simp)
      have hrestObjects : ∀ candidate,
          candidate ∈ rest → objectTypeNameBool schema candidate = true := by
        intro candidate hcandidate
        exact hobjects candidate (List.mem_cons_of_mem objectType hcandidate)
      have hrestNodup : rest.Nodup := hnodup.tail
      cases hnormalized :
          normalizeSelectionSet schema objectType selectionSet with
      | nil =>
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            rw [show
              GroundTypeNormalization.possibleTypeNormalizations schema
                  (runtimeType :: rest) selectionSet
                = GroundTypeNormalization.possibleTypeNormalizations schema rest
                    selectionSet by
                simp [GroundTypeNormalization.possibleTypeNormalizations,
                  hnormalized]]
            rw [GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
              schema variableValues runtimeType (ref := ref) rest selectionSet
              hrestObjects hrestNotin]
            simp [Execution.collectFields, hnormalized]
          · have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            simpa [GroundTypeNormalization.possibleTypeNormalizations,
              hnormalized] using
              ih hrestObjects hrestNodup hrestMem
      | cons selection restNormalized =>
          rw [show
            GroundTypeNormalization.possibleTypeNormalizations schema
                (objectType :: rest) selectionSet
              = Selection.inlineFragment (some objectType) []
                  (selection :: restNormalized)
                  :: GroundTypeNormalization.possibleTypeNormalizations schema
                    rest selectionSet by
              simp [GroundTypeNormalization.possibleTypeNormalizations,
                hnormalized]]
          by_cases heq : objectType = runtimeType
          · subst objectType
            have hrestNotin : runtimeType ∉ rest :=
              (List.nodup_cons.mp hnodup).1
            have happly :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (.object runtimeType ref) runtimeType = true :=
              GroundTypeNormalization.doesFragmentTypeApplyBool_object_self
                schema (ref := ref) hobject
            rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_apply_flatten
              schema variableValues runtimeType runtimeType
              (.object runtimeType ref) (selection :: restNormalized)
              (GroundTypeNormalization.possibleTypeNormalizations schema rest
                selectionSet) happly]
            rw [collectFields_append]
            rw [GroundTypeNormalization.collectFields_possibleTypeNormalizations_not_mem_eq_nil
              schema variableValues runtimeType (ref := ref) rest selectionSet
              hrestObjects hrestNotin]
            simp [hnormalized, Execution.mergeExecutableGroups_nil_right]
          · have hskip :
                Execution.doesFragmentTypeApplyBool schema runtimeType
                  (.object runtimeType ref) objectType = false :=
              GroundTypeNormalization.doesFragmentTypeApplyBool_object_other_false
                schema (ref := ref) hobject heq
            rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
              schema variableValues runtimeType objectType
              (.object runtimeType ref) (selection :: restNormalized)
              (GroundTypeNormalization.possibleTypeNormalizations schema rest
                selectionSet) hskip]
            have hrestMem : runtimeType ∈ rest := by
              rcases List.mem_cons.mp hmem with hhead | htail
              · exact False.elim (heq hhead.symm)
              · exact htail
            exact ih hrestObjects hrestNodup hrestMem

/-- Collected-path selection splits over the leading group and the remaining
group list. -/
private theorem collectedFieldsSelectPath_cons_groups_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (group : Name × List Execution.ExecutableField)
    (groups : List (Name × List Execution.ExecutableField))
    (path : List PathStep) :
    collectedFieldsSelectPath schema variableValues (group :: groups) path
      ↔ collectedFieldsSelectPath schema variableValues [group] path
        ∨ collectedFieldsSelectPath schema variableValues groups path := by
  cases path with
  | nil => simp
  | cons step rest =>
      cases rest with
      | nil =>
          rw [collectedFieldsSelectPath_singleton,
            collectedFieldsSelectPath_singleton,
            collectedFieldsSelectPath_singleton]
          constructor
          · rintro ⟨fields, hgroup, hmatch⟩
            rcases List.mem_cons.mp hgroup with hhead | htail
            · exact Or.inl ⟨fields, by simp [hhead], hmatch⟩
            · exact Or.inr ⟨fields, htail, hmatch⟩
          · rintro (⟨fields, hgroup, hmatch⟩ | ⟨fields, hgroup, hmatch⟩)
            · exact ⟨fields, by simp at hgroup ⊢; simp [hgroup], hmatch⟩
            · exact ⟨fields, List.mem_cons_of_mem group hgroup, hmatch⟩
      | cons next rest =>
          rw [collectedFieldsSelectPath_cons_cons,
            collectedFieldsSelectPath_cons_cons,
            collectedFieldsSelectPath_cons_cons]
          constructor
          · rintro ⟨fields, hgroup, hmatch, hincludes, hpath⟩
            rcases List.mem_cons.mp hgroup with hhead | htail
            · exact Or.inl ⟨fields, by simp [hhead], hmatch,
                hincludes, hpath⟩
            · exact Or.inr ⟨fields, htail, hmatch, hincludes, hpath⟩
          · rintro (⟨fields, hgroup, hmatch, hincludes, hpath⟩ |
              ⟨fields, hgroup, hmatch, hincludes, hpath⟩)
            · exact ⟨fields, by simp at hgroup ⊢; simp [hgroup],
                hmatch, hincludes, hpath⟩
            · exact ⟨fields, List.mem_cons_of_mem group hgroup,
                hmatch, hincludes, hpath⟩

/-- A normalized singleton representative and its complete source group select
the same paths when current-step matching and merged-child collection agree. -/
private theorem collectedFieldsSelectPath_singleton_group_transport
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType responseName : Name)
    (normalizedField : Execution.ExecutableField)
    (sourceFields : List Execution.ExecutableField)
    (hmatch : ∀ step,
      executableFieldMatchesPathStep schema normalizedField step
        ↔ ∃ sourceField,
          sourceField ∈ sourceFields
          ∧ executableFieldMatchesPathStep schema sourceField step)
    (hchildren : ∀ (step next : PathStep) (rest : List PathStep),
      step.parentObject = parentType
        → executableFieldMatchesPathStep schema normalizedField step
        → schema.typeIncludesObject
          step.field.outputType.namedType next.parentObject
        →
      (collectedFieldsSelectPath schema variableValues
          (Execution.collectSubfields schema variableValues next.parentObject
            (.object next.parentObject ()) [normalizedField])
          (next :: rest)
        ↔
      collectedFieldsSelectPath schema variableValues
          (Execution.collectSubfields schema variableValues next.parentObject
            (.object next.parentObject ()) sourceFields)
          (next :: rest))) :
  ∀ path,
      (∀ step rest, path = step :: rest → step.parentObject = parentType)
      →
      (collectedFieldsSelectPath schema variableValues
          [(responseName, [normalizedField])] path
        ↔
      collectedFieldsSelectPath schema variableValues
          [(responseName, sourceFields)] path)
  | [], _hparent => by simp
  | [step], _hparent => by
      rw [collectedFieldsSelectPath_singleton,
        collectedFieldsSelectPath_singleton]
      constructor
      · rintro ⟨fields, hgroup, field, hfield, hfieldMatch⟩
        have hgroupEq :
            (step.responseName, fields) =
              (responseName, [normalizedField]) := by
          simpa only [List.mem_singleton] using hgroup
        have hresponse : step.responseName = responseName :=
          congrArg Prod.fst hgroupEq
        have hfields : fields = [normalizedField] :=
          congrArg Prod.snd hgroupEq
        subst fields
        have hfieldEq : field = normalizedField := by simpa using hfield
        subst field
        have hnormalizedMatch :
            executableFieldMatchesPathStep schema normalizedField step := by
          exact hfieldMatch
        rcases (hmatch step).mp hnormalizedMatch with
          ⟨sourceField, hsourceField, hsourceMatch⟩
        refine ⟨sourceFields, ?_, sourceField, hsourceField, hsourceMatch⟩
        simp [hresponse]
      · rintro ⟨fields, hgroup, field, hfield, hfieldMatch⟩
        have hgroupEq :
            (step.responseName, fields) = (responseName, sourceFields) := by
          simpa only [List.mem_singleton] using hgroup
        have hresponse : step.responseName = responseName :=
          congrArg Prod.fst hgroupEq
        have hfields : fields = sourceFields := congrArg Prod.snd hgroupEq
        subst fields
        have hnormalizedMatch :=
          (hmatch step).mpr ⟨field, hfield, hfieldMatch⟩
        refine ⟨[normalizedField], ?_, normalizedField, by simp,
          hnormalizedMatch⟩
        simp [hresponse]
  | step :: next :: rest, hparent => by
      rw [collectedFieldsSelectPath_cons_cons,
        collectedFieldsSelectPath_cons_cons]
      constructor
      · rintro ⟨fields, hgroup, ⟨field, hfield, hfieldMatch⟩,
          hincludes, hpath⟩
        have hgroupEq :
            (step.responseName, fields) =
              (responseName, [normalizedField]) := by
          simpa only [List.mem_singleton] using hgroup
        have hresponse : step.responseName = responseName :=
          congrArg Prod.fst hgroupEq
        have hfields : fields = [normalizedField] :=
          congrArg Prod.snd hgroupEq
        subst fields
        have hfieldEq : field = normalizedField := by simpa using hfield
        subst field
        have hnormalizedMatch :
            executableFieldMatchesPathStep schema normalizedField step := by
          exact hfieldMatch
        rcases (hmatch step).mp hnormalizedMatch with
          ⟨sourceField, hsourceField, hsourceMatch⟩
        have hstepParent : step.parentObject = parentType :=
          hparent step (next :: rest) rfl
        refine ⟨sourceFields, ?_,
          ⟨sourceField, hsourceField, hsourceMatch⟩, hincludes, ?_⟩
        · simp [hresponse]
        · exact
            (hchildren step next rest hstepParent hnormalizedMatch hincludes).mp
              hpath
      · rintro ⟨fields, hgroup, ⟨field, hfield, hfieldMatch⟩,
          hincludes, hpath⟩
        have hgroupEq :
            (step.responseName, fields) = (responseName, sourceFields) := by
          simpa only [List.mem_singleton] using hgroup
        have hresponse : step.responseName = responseName :=
          congrArg Prod.fst hgroupEq
        have hfields : fields = sourceFields := congrArg Prod.snd hgroupEq
        subst fields
        have hnormalizedMatch :=
          (hmatch step).mpr ⟨field, hfield, hfieldMatch⟩
        have hstepParent : step.parentObject = parentType :=
          hparent step (next :: rest) rfl
        refine ⟨[normalizedField], ?_,
          ⟨normalizedField, by simp, hnormalizedMatch⟩, hincludes, ?_⟩
        · simp [hresponse]
        · exact
            (hchildren step next rest hstepParent hnormalizedMatch hincludes).mpr
              hpath

/-- Ground normalization preserves the exact collected-field path footprint.
The source group may contain several fields; its normalized representative uses
their complete merged child selection set. -/
private theorem collectedFieldsSelectPath_normalizeSelectionSet_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema) :
    ∀ parentType selectionSet path,
      (∀ step rest, path = step :: rest → step.parentObject = parentType)
      →
      objectTypeNameBool schema parentType = true
      → selectionSetDirectiveFree selectionSet
      → selectionSetSemanticsReady schema parentType selectionSet
      → FieldMerge.fieldsInSetCanMerge schema parentType selectionSet
      →
      (collectedFieldsSelectPath schema variableValues
          (Execution.collectFields schema variableValues parentType
            (.object parentType ())
            (normalizeSelectionSet schema parentType selectionSet)) path
        ↔
       collectedFieldsSelectPath schema variableValues
          (Execution.collectFields schema variableValues parentType
            (.object parentType ()) selectionSet) path) := by
  intro parentType selectionSet
  induction parentType, selectionSet using normalizeSelectionSet.induct schema
    with
  | case1 parentType =>
      intro path _hparent _hobject _hfree _hready _hmerge
      simp [normalizeSelectionSet, Execution.collectFields]
  | case2 parentType rest responseName fieldName arguments directives
      subselections hlookup _hrest =>
      intro path _hparent _hobject _hfree hready _hmerge
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments directives
              subselections :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments directives
            subselections :: rest)
          hready
      exact False.elim
        (selectionSetLookupValid_field_head_lookup_none_false hlookupValid
          hlookup)
  | case3 parentType rest responseName fieldName arguments directives
      subselections fieldDefinition hlookup matching mergedSubselections
      returnType htailIH hobjectIH hpossibleIH =>
      intro path hpathParent hobject hfree hready hmerge
      have hheadFree :
          selectionDirectiveFree
            (Selection.field responseName fieldName arguments directives
              subselections) :=
        selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      let matching :=
        fieldSelectionsWithResponseNameInScope schema parentType responseName rest
      let mergedSubselections :=
        subselections ++ mergeSelectionSets matching
      let returnType := fieldDefinition.outputType.namedType
      let normalizedSubselections :=
        if objectTypeNameBool schema returnType then
          normalizeSelectionSet schema returnType mergedSubselections
        else
          GroundTypeNormalization.possibleTypeNormalizations schema
            (schema.getPossibleTypes returnType) mergedSubselections
      let filteredRest :=
        withoutFieldSelectionsWithResponseName schema responseName rest
      let normalizedRest :=
        normalizeSelectionSet schema parentType filteredRest
      let sourceField : Execution.ExecutableField := {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := subselections
      }
      let normalizedField : Execution.ExecutableField := {
        parentType := parentType,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := normalizedSubselections
      }
      have hparentObject : schema.objectType parentType :=
        objectType_of_objectTypeNameBool_eq_true schema hobject
      have hsourceValue :
          ∃ runtimeType ref,
            (Execution.ResolverValue.object parentType () :
                Execution.ResolverValue Unit)
              = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true :=
        ⟨parentType, (), rfl,
          GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
            schema hobject⟩
      have hlookupValid :
          selectionSetLookupValid schema parentType
            (Selection.field responseName fieldName arguments [] subselections
              :: rest) :=
        selectionSetLookupValid_of_selectionSetSemanticsReady
          (Selection.field responseName fieldName arguments [] subselections
            :: rest)
          hready
      have htailFree : selectionSetDirectiveFree rest :=
        selectionSetDirectiveFree_tail hfree
      have htailReady : selectionSetSemanticsReady schema parentType rest :=
        selectionSetSemanticsReady_tail hready
      have htailMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType rest :=
        fieldsInSetCanMerge_tail schema parentType
          (Selection.field responseName fieldName arguments [] subselections)
          rest hmerge
      have hfilteredFree : selectionSetDirectiveFree filteredRest := by
        exact withoutFieldSelectionsWithResponseName_directiveFree schema
          responseName rest htailFree
      have hfilteredReady :
          selectionSetSemanticsReady schema parentType filteredRest := by
        exact selectionSetSemanticsReady_withoutFieldSelectionsWithResponseName
          schema responseName parentType rest htailReady
      have hfilteredMerge :
          FieldMerge.fieldsInSetCanMerge schema parentType filteredRest := by
        exact fieldsInSetCanMerge_withoutFieldSelectionsWithResponseName schema
          responseName parentType rest htailMerge
      have htailFootprint :
          collectedFieldsSelectPath schema variableValues
              (Execution.collectFields schema variableValues parentType
                (.object parentType ()) normalizedRest) path
            ↔
          collectedFieldsSelectPath schema variableValues
              (Execution.collectFields schema variableValues parentType
                (.object parentType ()) filteredRest) path := by
        exact htailIH path hpathParent hobject hfilteredFree
          hfilteredReady hfilteredMerge
      rcases GroundTypeNormalization.collectFields_field_head_exists schema
          variableValues parentType (.object parentType ()) responseName
          fieldName arguments subselections rest with
        ⟨sourceFields, sourceRest, hsourceCollect⟩
      have hsourceRest :
          Execution.collectFields schema variableValues parentType
              (.object parentType ()) filteredRest
            = sourceRest := by
        exact
          GroundTypeNormalization.collectFields_withoutFieldSelectionsWithResponseName_fieldHead_rest_eq_sourceRest
            schema variableValues parentType (.object parentType ()) responseName
            fieldName arguments subselections rest sourceFields sourceRest
            hobject hsourceValue hfree
            (by simpa [sourceField] using hsourceCollect)
      have hnormalizedRestNotin :
          responseName ∉
            (Execution.collectFields schema variableValues parentType
              (.object parentType ()) normalizedRest).map Prod.fst := by
        exact
          GroundTypeNormalization.collectFields_responseName_not_mem_of_responseNameFree
            schema variableValues parentType (.object parentType ())
            responseName hobject hsourceValue normalizedRest
            (by
              exact GroundTypeNormalization.normalizeSelectionSet_directiveFree
                schema parentType
                filteredRest hfilteredFree)
            (by
              exact
                GroundTypeNormalization.normalizeSelectionSet_responseNameFree
                  schema parentType responseName filteredRest
                (withoutFieldSelectionsWithResponseName_responseNameFree schema
                  parentType responseName rest))
      have hnormalize :
          normalizeSelectionSet schema parentType
              (Selection.field responseName fieldName arguments [] subselections
                :: rest)
            = Selection.field responseName fieldName arguments []
                normalizedSubselections
              :: normalizedRest := by
        rw [normalizeSelectionSet.eq_2, hlookup]
        simp [matching, mergedSubselections, returnType,
          normalizedSubselections, filteredRest, normalizedRest,
          NormalForm.normalizedField,
          GroundTypeNormalization.possibleTypeNormalizations]
        rfl
      have hnormalizedCollect :
          Execution.collectFields schema variableValues parentType
              (.object parentType ())
              (normalizeSelectionSet schema parentType
                (Selection.field responseName fieldName arguments []
                  subselections :: rest))
            = (responseName, [normalizedField])
                :: Execution.collectFields schema variableValues parentType
                  (.object parentType ()) normalizedRest := by
        rw [hnormalize]
        simpa [normalizedField] using
          GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
            schema variableValues parentType (.object parentType ())
            responseName fieldName arguments normalizedSubselections
            normalizedRest hnormalizedRestNotin
      have hmerged :
          Execution.mergedFieldSelectionSet (sourceField :: sourceFields)
            = mergedSubselections := by
        have hprojection :=
          GroundTypeNormalization.collectFields_fieldSelectionsWithResponseNameInScope_responseSelection
            schema variableValues parentType (.object parentType ())
            responseName
            (Selection.field responseName fieldName arguments [] subselections
              :: rest)
            hobject hsourceValue hfree
        simp [collectedResponseSelectionSet, hsourceCollect,
          fieldSelectionsWithResponseNameInScope, mergeSelectionSets,
          Selection.subselections] at hprojection
        simpa [sourceField, matching, mergedSubselections] using hprojection
      have hmergedFree : selectionSetDirectiveFree mergedSubselections := by
        simpa [mergedSubselections, matching] using
          selectionSetDirectiveFree_fieldHead_merged schema parentType
            responseName fieldName arguments subselections rest hfree
      have hcurrent :
          collectedFieldsSelectPath schema variableValues
              [(responseName, [normalizedField])] path
            ↔
          collectedFieldsSelectPath schema variableValues
              [(responseName, sourceField :: sourceFields)] path := by
        refine collectedFieldsSelectPath_singleton_group_transport schema
          variableValues parentType responseName normalizedField
          (sourceField :: sourceFields) ?_ ?_ path hpathParent
        · intro step
          have hgroupMatch :=
            executableGroupMatchesPathStep_iff_head schema variableValues
              parentType () responseName fieldName arguments subselections rest
              fieldDefinition sourceFields sourceRest step hparentObject hlookup
              hlookupValid hmerge
              (by simpa [sourceField] using hsourceCollect)
          simpa [normalizedField, sourceField,
            executableFieldMatchesPathStep] using hgroupMatch.symm
        · intro step next childRest hstepParent hstepMatch hincludes
          rcases hstepMatch with
            ⟨_stepResponse, hstepFieldName, _stepArguments,
              stepFieldDefinition, hstepLookup, hstepOutput⟩
          have hstepFieldNameEq : step.field.fieldName = fieldName := by
            simpa [normalizedField] using hstepFieldName.symm
          rw [hstepParent, hstepFieldNameEq] at hstepLookup
          have hstepDefinitionEq : stepFieldDefinition = fieldDefinition :=
            Option.some.inj (hstepLookup.symm.trans hlookup)
          subst stepFieldDefinition
          have hstepOutputEq :
              step.field.outputType = fieldDefinition.outputType :=
            hstepOutput.symm
          rw [collectSubfields_eq_collectFields_mergedFieldSelectionSet,
            collectSubfields_eq_collectFields_mergedFieldSelectionSet]
          simp only [Execution.mergedFieldSelectionSet_cons,
            Execution.mergedFieldSelectionSet_nil, List.append_nil]
          change
            collectedFieldsSelectPath schema variableValues
                (Execution.collectFields schema variableValues next.parentObject
                  (.object next.parentObject ()) normalizedSubselections)
                (next :: childRest)
              ↔
            collectedFieldsSelectPath schema variableValues
                (Execution.collectFields schema variableValues next.parentObject
                  (.object next.parentObject ())
                  (Execution.mergedFieldSelectionSet
                    (sourceField :: sourceFields)))
                (next :: childRest)
          rw [hmerged]
          have hincludeReturn :
              schema.typeIncludesObjectBool returnType next.parentObject = true :=
            List.contains_iff_mem.mpr (by
              simpa [Schema.typeIncludesObject, returnType, hstepOutputEq]
                using hincludes)
          have hmergedReady :
              selectionSetSemanticsReady schema next.parentObject
                mergedSubselections := by
            simpa [mergedSubselections, matching] using
              selectionSetSemanticsReady_fieldHead_merged_of_child_object schema
                parentType responseName fieldName next.parentObject arguments
                subselections rest fieldDefinition hparentObject hready
                hlookupValid hmerge hlookup hincludeReturn
          have hmergedCanMerge :
              FieldMerge.fieldsInSetCanMerge schema next.parentObject
                mergedSubselections := by
            simpa [mergedSubselections, matching] using
              fieldsInSetCanMerge_fieldHead_merged_of_canMerge_object_lookupValid
                schema parentType responseName fieldName next.parentObject
                arguments subselections rest fieldDefinition hparentObject
                hlookupValid hmerge hlookup
          by_cases hreturnObject :
              objectTypeNameBool schema returnType = true
          · have hruntimeEq : next.parentObject = returnType :=
              GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
                schema hreturnObject hincludeReturn
            rw [hruntimeEq] at hmergedReady hmergedCanMerge ⊢
            simp [normalizedSubselections, hreturnObject]
            exact hobjectIH (next :: childRest)
              (by
                intro childStep tail hpath
                cases hpath
                exact hruntimeEq)
              hreturnObject hmergedFree hmergedReady hmergedCanMerge
          · have hreturnObjectFalse :
                objectTypeNameBool schema returnType = false := by
              cases hmatch : objectTypeNameBool schema returnType
              · rfl
              · contradiction
            have hpossible :
                next.parentObject ∈ schema.getPossibleTypes returnType :=
              List.contains_iff_mem.mp hincludeReturn
            have hobjects : ∀ objectType,
                objectType ∈ schema.getPossibleTypes returnType
                  → objectTypeNameBool schema objectType = true := by
              intro objectType hobjectType
              exact
                GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
                  schema
                  (SchemaWellFormedness.schemaWellFormed_possibleTypesAreObjects
                    hschema returnType objectType hobjectType)
            rw [show normalizedSubselections =
                GroundTypeNormalization.possibleTypeNormalizations schema
                  (schema.getPossibleTypes returnType) mergedSubselections by
              simp [normalizedSubselections, hreturnObjectFalse]]
            rw [collectFields_possibleTypeNormalizations_runtime_branch_eq
              schema variableValues next.parentObject ()
              (schema.getPossibleTypes returnType) mergedSubselections hobjects
              (SchemaWellFormedness.schemaWellFormed_possibleTypesNodup hschema
                returnType)
              hpossible]
            exact hpossibleIH next.parentObject (next :: childRest)
              (by
                intro childStep tail hpath
                cases hpath
                rfl)
              (hobjects next.parentObject hpossible) hmergedFree
              hmergedReady hmergedCanMerge
      have htailFinal :
          collectedFieldsSelectPath schema variableValues
              (Execution.collectFields schema variableValues parentType
                (.object parentType ()) normalizedRest) path
            ↔
          collectedFieldsSelectPath schema variableValues sourceRest path := by
        simpa [normalizedRest, filteredRest, hsourceRest] using
          htailFootprint
      rw [hnormalizedCollect, hsourceCollect]
      rw [collectedFieldsSelectPath_cons_groups_iff schema variableValues
        (responseName, [normalizedField])
        (Execution.collectFields schema variableValues parentType
          (.object parentType ()) normalizedRest) path]
      rw [collectedFieldsSelectPath_cons_groups_iff schema variableValues
        (responseName, sourceField :: sourceFields) sourceRest path]
      rw [hcurrent, htailFinal]
  | case4 parentType rest directives subselections happend =>
      intro path hpathParent hobject hfree hready hmerge
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hselectionFree : selectionSetDirectiveFree subselections := by
        simpa [selectionDirectiveFree] using hheadFree.2
      have happendFree : selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree htailFree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment none [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hselectionReady :
          selectionSetSemanticsReady schema parentType subselections := by
        simpa [selectionSemanticsReady] using hheadReady
      have htailReady := selectionSetSemanticsReady_tail hready
      have happendReady :=
        selectionSetSemanticsReady_append hselectionReady htailReady
      have happendMerge :=
        fieldsInSetCanMerge_inlineFragment_none_flatten schema parentType
          subselections rest hmerge
      rw [show normalizeSelectionSet schema parentType
            (Selection.inlineFragment none [] subselections :: rest)
          = normalizeSelectionSet schema parentType (subselections ++ rest) by
        simp [normalizeSelectionSet]]
      rw [GroundTypeNormalization.collectFields_inlineFragment_none_directiveFree_flatten]
      exact happend path hpathParent hobject happendFree happendReady
        happendMerge
  | case5 parentType rest typeCondition directives subselections hoverlap
      _hrest happend =>
      intro path hpathParent hobject hfree hready hmerge
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have htailFree := selectionSetDirectiveFree_tail hfree
      have hselectionFree : selectionSetDirectiveFree subselections := by
        simpa [selectionDirectiveFree] using hheadFree.2
      have happendFree : selectionSetDirectiveFree (subselections ++ rest) :=
        selectionSetDirectiveFree_append hselectionFree htailFree
      have hheadReady :
          selectionSemanticsReady schema parentType
            (Selection.inlineFragment (some typeCondition) [] subselections) := by
        unfold selectionSetSemanticsReady at hready
        exact hready _ (by simp)
      have hheadReadyPair :
          selectionSetLookupValid schema typeCondition subselections
            ∧ (schema.typesOverlapBool parentType typeCondition = true →
              selectionSetSemanticsReady schema parentType subselections) := by
        simpa [selectionSemanticsReady] using hheadReady
      have hselectionReady := hheadReadyPair.2 hoverlap
      have htailReady := selectionSetSemanticsReady_tail hready
      have happendReady :=
        selectionSetSemanticsReady_append hselectionReady htailReady
      have hselectionParentLookup :=
        selectionSetLookupValid_of_selectionSetSemanticsReady subselections
          hselectionReady
      have htailLookup :=
        selectionSetLookupValid_of_selectionSetSemanticsReady rest htailReady
      have hparentObject :=
        objectType_of_objectTypeNameBool_eq_true schema hobject
      have happendMerge :=
        fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object schema
          parentType typeCondition subselections rest hschema hparentObject
          hoverlap hselectionParentLookup hheadReadyPair.1 htailLookup hmerge
      have hsourceValue :
          ∃ runtimeType ref,
            (Execution.ResolverValue.object parentType () :
                Execution.ResolverValue Unit)
              = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true :=
        ⟨parentType, (), rfl,
          GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
            schema hobject⟩
      have happly :
          Execution.doesFragmentTypeApplyBool schema parentType
            (.object parentType ()) typeCondition = true := by
        rw [GroundTypeNormalization.doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
          schema hobject hsourceValue]
        exact hoverlap
      rw [show normalizeSelectionSet schema parentType
            (Selection.inlineFragment (some typeCondition) [] subselections
              :: rest)
          = normalizeSelectionSet schema parentType (subselections ++ rest) by
        simp [normalizeSelectionSet, hoverlap]]
      rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_apply_flatten
        schema variableValues parentType typeCondition (.object parentType ())
        subselections rest happly]
      exact happend path hpathParent hobject happendFree happendReady
        happendMerge
  | case6 parentType rest typeCondition directives subselections hoverlap
      hrest =>
      intro path hpathParent hobject hfree hready hmerge
      have hheadFree := selectionSetDirectiveFree_head hfree
      have hdirectives : directives = [] := by
        simpa [selectionDirectiveFree] using hheadFree.1
      subst directives
      have htailFree := selectionSetDirectiveFree_tail hfree
      have htailReady := selectionSetSemanticsReady_tail hready
      have htailMerge := fieldsInSetCanMerge_tail schema parentType
        (Selection.inlineFragment (some typeCondition) [] subselections)
        rest hmerge
      have hoverlapFalse :
          schema.typesOverlapBool parentType typeCondition = false := by
        cases hmatch : schema.typesOverlapBool parentType typeCondition
        · rfl
        · exact False.elim (hoverlap hmatch)
      have hsourceValue :
          ∃ runtimeType ref,
            (Execution.ResolverValue.object parentType () :
                Execution.ResolverValue Unit)
              = .object runtimeType ref
            ∧ schema.typeIncludesObjectBool parentType runtimeType = true :=
        ⟨parentType, (), rfl,
          GroundTypeNormalization.typeIncludesObjectBool_self_of_objectTypeNameBool
            schema hobject⟩
      have hskip :
          Execution.doesFragmentTypeApplyBool schema parentType
            (.object parentType ()) typeCondition = false := by
        rw [GroundTypeNormalization.doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
          schema hobject hsourceValue]
        exact hoverlapFalse
      rw [show normalizeSelectionSet schema parentType
            (Selection.inlineFragment (some typeCondition) [] subselections
              :: rest)
          = normalizeSelectionSet schema parentType rest by
        simp [normalizeSelectionSet, hoverlapFalse]]
      rw [GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
        schema variableValues parentType typeCondition (.object parentType ())
        subselections rest hskip]
      exact hrest path hpathParent hobject htailFree htailReady htailMerge

private theorem executableFieldMatchesPathStep_filterExecutableFieldBoolCase_iff
    (schema : Schema) (boolCase : BoolCase)
    (field : Execution.ExecutableField) (step : PathStep) :
    executableFieldMatchesPathStep schema
        (filterExecutableFieldBoolCase boolCase field) step
      ↔ executableFieldMatchesPathStep schema field step := by
  rfl

private theorem filterExecutableGroupsBoolCase_group_mem_iff
    (boolCase : BoolCase)
    (groups : List (Name × List Execution.ExecutableField))
    (responseName : Name) (filteredFields : List Execution.ExecutableField) :
    (responseName, filteredFields)
        ∈ filterExecutableGroupsBoolCase boolCase groups
      ↔ ∃ fields,
          (responseName, fields) ∈ groups
          ∧ filteredFields = fields.map (filterExecutableFieldBoolCase boolCase) := by
  constructor
  · intro hmem
    rcases List.mem_map.mp hmem with ⟨group, hgroup, hgroupEq⟩
    rcases group with ⟨groupName, fields⟩
    simp [filterExecutableGroupBoolCase] at hgroupEq
    rcases hgroupEq with ⟨hname, hfields⟩
    subst groupName
    subst filteredFields
    exact ⟨fields, hgroup, rfl⟩
  · rintro ⟨fields, hmem, rfl⟩
    exact List.mem_map.mpr
      ⟨(responseName, fields), hmem, by
        simp [filterExecutableGroupBoolCase]⟩

private theorem collectSubfields_map_filterExecutableFieldBoolCase
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation) (boolCase : BoolCase)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation))
    (parentType : Name) (source : Execution.ResolverValue ObjectRef) :
    ∀ fields,
      executableFieldsSelectionVarsInOperation operation fields
      → Execution.collectSubfields schema variableValues parentType source
          (fields.map (filterExecutableFieldBoolCase boolCase))
        = filterExecutableGroupsBoolCase boolCase
            (Execution.collectSubfields schema variableValues parentType source
              fields)
  | [], _hvars => by
      simp [Execution.collectSubfields, Execution.collectFields,
        filterExecutableGroupsBoolCase]
  | field :: rest, hvars => by
      have hfieldVars :
          ∀ varName,
            varName ∈ selectionSetBooleanVariables field.selectionSet
            → varName ∈ selectionSetBooleanVariables operation.selectionSet :=
        hvars field (by simp)
      have hrestVars :
          executableFieldsSelectionVarsInOperation operation rest := by
        intro candidate hcandidate
        exact hvars candidate (by simp [hcandidate])
      have hhead :=
        collectFields_filterSelectionSetBoolCase schema variableValues
          operation boolCase hagrees parentType source field.selectionSet
          hfieldVars
      have htail :=
        collectSubfields_map_filterExecutableFieldBoolCase schema variableValues
          operation boolCase hagrees parentType source rest hrestVars
      simp only [List.map, Execution.collectSubfields]
      change
        Execution.mergeExecutableGroups
            (Execution.collectFields schema variableValues parentType source
              (filterSelectionSetBoolCase boolCase field.selectionSet))
            (Execution.collectSubfields schema variableValues parentType source
              (rest.map (filterExecutableFieldBoolCase boolCase)))
          = filterExecutableGroupsBoolCase boolCase
              (Execution.mergeExecutableGroups
                (Execution.collectFields schema variableValues parentType source
                  field.selectionSet)
                (Execution.collectSubfields schema variableValues parentType source
                  rest))
      rw [hhead, htail]
      exact
        (filterExecutableGroupsBoolCase_mergeExecutableGroups boolCase
          (Execution.collectFields schema variableValues parentType source
            field.selectionSet)
          (Execution.collectSubfields schema variableValues parentType source
            rest)).symm

private theorem collectedFieldsSelectPath_filterExecutableGroupsBoolCase_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation) (boolCase : BoolCase)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation))
    (groups : List (Name × List Execution.ExecutableField))
    (hvars : executableGroupsSelectionVarsInOperation operation groups) :
    ∀ path,
      collectedFieldsSelectPath schema variableValues
          (filterExecutableGroupsBoolCase boolCase groups) path
        ↔ collectedFieldsSelectPath schema variableValues groups path
  | [] => by simp
  | [step] => by
      rw [collectedFieldsSelectPath_singleton,
        collectedFieldsSelectPath_singleton]
      constructor
      · rintro ⟨filteredFields, hgroup, filteredField, hfield, hmatch⟩
        rcases
            (filterExecutableGroupsBoolCase_group_mem_iff boolCase groups
              step.responseName filteredFields).mp hgroup with
          ⟨fields, hsourceGroup, rfl⟩
        rcases List.mem_map.mp hfield with
          ⟨field, hsourceField, hfieldEq⟩
        subst filteredField
        exact ⟨fields, hsourceGroup, field, hsourceField,
          (executableFieldMatchesPathStep_filterExecutableFieldBoolCase_iff
            schema boolCase field step).mp hmatch⟩
      · rintro ⟨fields, hgroup, field, hfield, hmatch⟩
        refine ⟨fields.map (filterExecutableFieldBoolCase boolCase), ?_,
          filterExecutableFieldBoolCase boolCase field,
          List.mem_map.mpr ⟨field, hfield, rfl⟩, ?_⟩
        · exact
            (filterExecutableGroupsBoolCase_group_mem_iff boolCase groups
              step.responseName
              (fields.map (filterExecutableFieldBoolCase boolCase))).mpr
              ⟨fields, hgroup, rfl⟩
        · exact
            (executableFieldMatchesPathStep_filterExecutableFieldBoolCase_iff
              schema boolCase field step).mpr hmatch
  | step :: next :: rest => by
      rw [collectedFieldsSelectPath_cons_cons,
        collectedFieldsSelectPath_cons_cons]
      constructor
      · rintro ⟨filteredFields, hgroup,
          ⟨filteredField, hfield, hmatch⟩, hincludes, hpath⟩
        rcases
            (filterExecutableGroupsBoolCase_group_mem_iff boolCase groups
              step.responseName filteredFields).mp hgroup with
          ⟨fields, hsourceGroup, rfl⟩
        rcases List.mem_map.mp hfield with
          ⟨field, hsourceField, hfieldEq⟩
        subst filteredField
        have hfieldVars :
            executableFieldsSelectionVarsInOperation operation fields :=
          hvars (step.responseName, fields) hsourceGroup
        rw [collectSubfields_map_filterExecutableFieldBoolCase schema
          variableValues operation boolCase hagrees next.parentObject
          (.object next.parentObject ()) fields hfieldVars] at hpath
        exact ⟨fields, hsourceGroup, ⟨field, hsourceField,
          (executableFieldMatchesPathStep_filterExecutableFieldBoolCase_iff
            schema boolCase field step).mp hmatch⟩,
          hincludes,
          (collectedFieldsSelectPath_filterExecutableGroupsBoolCase_iff
            schema variableValues operation boolCase hagrees
            (Execution.collectSubfields schema variableValues next.parentObject
              (.object next.parentObject ()) fields)
            (by
              rw [collectSubfields_eq_collectFields_mergedFieldSelectionSet]
              exact collectFields_executableGroupsSelectionVarsInOperation
                schema variableValues operation next.parentObject
                (.object next.parentObject ())
                (Execution.mergedFieldSelectionSet fields)
                (executableFieldsSelectionVarsInOperation_merged operation
                  fields hfieldVars))
            (next :: rest)).mp hpath⟩
      · rintro ⟨fields, hgroup, ⟨field, hfield, hmatch⟩,
          hincludes, hpath⟩
        have hfieldVars :
            executableFieldsSelectionVarsInOperation operation fields :=
          hvars (step.responseName, fields) hgroup
        refine ⟨fields.map (filterExecutableFieldBoolCase boolCase), ?_,
          ⟨filterExecutableFieldBoolCase boolCase field,
          List.mem_map.mpr ⟨field, hfield, rfl⟩,
          (executableFieldMatchesPathStep_filterExecutableFieldBoolCase_iff
            schema boolCase field step).mpr hmatch⟩,
          hincludes, ?_⟩
        · exact
            (filterExecutableGroupsBoolCase_group_mem_iff boolCase groups
              step.responseName
              (fields.map (filterExecutableFieldBoolCase boolCase))).mpr
              ⟨fields, hgroup, rfl⟩
        · rw [collectSubfields_map_filterExecutableFieldBoolCase schema
            variableValues operation boolCase hagrees next.parentObject
            (.object next.parentObject ()) fields hfieldVars]
          exact
            (collectedFieldsSelectPath_filterExecutableGroupsBoolCase_iff
              schema variableValues operation boolCase hagrees
              (Execution.collectSubfields schema variableValues next.parentObject
                (.object next.parentObject ()) fields)
              (by
                rw [collectSubfields_eq_collectFields_mergedFieldSelectionSet]
                exact collectFields_executableGroupsSelectionVarsInOperation
                  schema variableValues operation next.parentObject
                  (.object next.parentObject ())
                  (Execution.mergedFieldSelectionSet fields)
                  (executableFieldsSelectionVarsInOperation_merged operation
                    fields hfieldVars))
              (next :: rest)).mpr hpath

theorem collectedFieldsSelectPath_filterSelectionSetBoolCase_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (operation : Operation) (boolCase : BoolCase)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation))
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (selectionSet : List Selection)
    (hvars : ∀ varName,
      varName ∈ selectionSetBooleanVariables selectionSet
      → varName ∈ selectionSetBooleanVariables operation.selectionSet)
    (path : List PathStep) :
    collectedFieldsSelectPath schema variableValues
        (Execution.collectFields schema variableValues parentType source
          (filterSelectionSetBoolCase boolCase selectionSet)) path
      ↔
    collectedFieldsSelectPath schema variableValues
        (Execution.collectFields schema variableValues parentType source selectionSet)
        path := by
  rw [collectFields_filterSelectionSetBoolCase schema variableValues operation
    boolCase hagrees parentType source selectionSet hvars]
  exact collectedFieldsSelectPath_filterExecutableGroupsBoolCase_iff
    schema variableValues operation boolCase hagrees
    (Execution.collectFields schema variableValues parentType source selectionSet)
    (collectFields_executableGroupsSelectionVarsInOperation schema
      variableValues operation parentType source selectionSet hvars)
    path

/-- When execution values agree with a Boolean case, filtering followed by
ground normalization preserves the source operation's collected footprint at
every admissible concrete root object. -/
theorem collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
    (schema : Schema) (operation : Operation) (boolCase : BoolCase)
    (variableValues : Execution.VariableValues)
    (step : PathStep) (rest : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hagrees : variableValuesAgreeWithCase variableValues boolCase
      (operationBoolVars operation))
    (hincludes : schema.typeIncludesObject
      (operation.rootType schema) step.parentObject) :
    collectedFieldsSelectPath schema variableValues
        (Execution.collectFields schema variableValues
          (operation.rootType schema) (.object step.parentObject ())
          (normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase boolCase operation.selectionSet)))
        (step :: rest)
      ↔
    collectedFieldsSelectPath schema variableValues
        (Execution.collectFields schema variableValues
          (operation.rootType schema) (.object step.parentObject ())
          operation.selectionSet)
        (step :: rest) := by
  have hrootObject : schema.objectType (operation.rootType schema) := by
    have hrootEq := Validation.operationDefinitionValid_rootType_eq hvalid
    rw [hrootEq]
    exact hschema.2.1
  have hobject :
      objectTypeNameBool schema (operation.rootType schema) = true :=
    GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType schema
      hrootObject
  have hruntimeEq : step.parentObject = operation.rootType schema :=
    GroundTypeNormalization.typeIncludesObjectBool_eq_of_objectTypeNameBool_true
      schema hobject (List.contains_iff_mem.mpr hincludes)
  have hready :
      selectionSetSemanticsReady schema (operation.rootType schema)
        operation.selectionSet :=
    selectionSetSemanticsReady_of_selectionSetValid_object schema
      operation.variableDefinitions (operation.rootType schema) hschema
      hrootObject operation.selectionSet
      (Validation.operationDefinitionValid_selectionSetValid hvalid)
  have hmerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        operation.selectionSet :=
    Validation.operationDefinitionValid_fieldsInSetCanMerge hvalid
  have hfilteredFree :
      selectionSetDirectiveFree
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    filterSelectionSetBoolCase_directiveFree schema boolCase
      operation.selectionSet
  have hfilteredReady :
      selectionSetSemanticsReady schema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    selectionSetSemanticsReady_filterSelectionSetBoolCase schema boolCase
      (operation.rootType schema) operation.selectionSet hready
  have hfilteredMerge :
      FieldMerge.fieldsInSetCanMerge schema (operation.rootType schema)
        (filterSelectionSetBoolCase boolCase operation.selectionSet) :=
    fieldsInSetCanMerge_filterSelectionSetBoolCase_forSemantics schema
      boolCase hmerge
  have hground :=
    collectedFieldsSelectPath_normalizeSelectionSet_iff schema
      variableValues hschema
      (operation.rootType schema)
      (filterSelectionSetBoolCase boolCase operation.selectionSet)
      (step :: rest)
      (by
        intro current tail hpath
        cases hpath
        exact hruntimeEq)
      hobject hfilteredFree hfilteredReady hfilteredMerge
  have hfilter :=
    collectedFieldsSelectPath_filterSelectionSetBoolCase_iff schema
      variableValues operation boolCase hagrees
      (operation.rootType schema) (.object (ObjectRef := Unit) step.parentObject ())
      operation.selectionSet (by
        intro varName hvar
        exact hvar)
      (step :: rest)
  rw [hruntimeEq] at hfilter ⊢
  exact hground.trans hfilter

/-- For a valid operation and complete Boolean assignment, filtering followed
by ground normalization preserves the source operation's collected footprint at
every admissible concrete root object. -/
theorem collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_iff
    (schema : Schema) (operation : Operation) (assignment : BoolCase)
    (step : PathStep) (rest : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete : completeNormalBoolCase (operationBoolVars operation) assignment)
    (hincludes : schema.typeIncludesObject
      (operation.rootType schema) step.parentObject) :
    collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
        (Execution.collectFields schema (boolCaseVariableValues assignment)
          (operation.rootType schema) (.object step.parentObject ())
          (normalizeSelectionSet schema (operation.rootType schema)
            (filterSelectionSetBoolCase assignment operation.selectionSet)))
        (step :: rest)
      ↔
    collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
        (Execution.collectFields schema (boolCaseVariableValues assignment)
          (operation.rootType schema) (.object step.parentObject ())
          operation.selectionSet)
        (step :: rest) := by
  have hagrees :
      variableValuesAgreeWithCase (boolCaseVariableValues assignment)
        assignment (operationBoolVars operation) :=
    variableValuesAgreeWithCase_boolCaseVariableValues [] hcomplete
  exact
    collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
      schema operation assignment (boolCaseVariableValues assignment)
      step rest hschema hvalid hagrees hincludes

/-- Operation-level public wrapper: replacing the source selection set by the
active filtered ground-normalized case preserves exactly the selected paths. -/
theorem operationSelectsPath_normalize_filterSelectionSetBoolCase_iff
    (schema : Schema) (operation : Operation) (assignment : BoolCase)
    (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete : completeNormalBoolCase (operationBoolVars operation) assignment) :
    operationSelectsPath schema
        { operation with
          selectionSet :=
            normalizeSelectionSet schema (operation.rootType schema)
              (filterSelectionSetBoolCase assignment operation.selectionSet) }
        assignment path
      ↔
    operationSelectsPath schema operation assignment path := by
  cases path with
  | nil => simp
  | cons step rest =>
      rw [operationSelectsPath_cons_iff, operationSelectsPath_cons_iff]
      change
        (schema.typeIncludesObject (operation.rootType schema) step.parentObject
          ∧ collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
            (Execution.collectFields schema (boolCaseVariableValues assignment)
              (operation.rootType schema) (.object step.parentObject ())
              (normalizeSelectionSet schema (operation.rootType schema)
                (filterSelectionSetBoolCase assignment operation.selectionSet)))
            (step :: rest))
        ↔
        (schema.typeIncludesObject (operation.rootType schema) step.parentObject
          ∧ collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
            (Execution.collectFields schema (boolCaseVariableValues assignment)
              (operation.rootType schema) (.object step.parentObject ())
              operation.selectionSet)
            (step :: rest))
      constructor
      · rintro ⟨hincludes, hpath⟩
        exact ⟨hincludes,
          (collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_iff
            schema operation assignment step rest hschema hvalid hcomplete
            hincludes).mp hpath⟩
      · rintro ⟨hincludes, hpath⟩
        exact ⟨hincludes,
          (collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_iff
            schema operation assignment step rest hschema hvalid hcomplete
            hincludes).mpr hpath⟩

end ResponseShape

end GraphQL
