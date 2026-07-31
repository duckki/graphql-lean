import Proofs.GraphQL.Argument
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.RootFilterSemantics
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.ReorderingSoundness
import Proofs.GraphQL.Theories.NormalForm.SelectionReordering
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Normalization

/-!
Selected-path footprint transport across complete-normal equality up to
reordering.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization
open NormalForm.GroundTypeNormalization
open NormalForm.GroundTypeNormalization.ReorderingSoundness

private def fieldGroupOfSelection (parentType : Name)
    : Selection → Name × List Execution.ExecutableField
  | .field responseName fieldName arguments _directives childSelectionSet =>
      (
        responseName,
        [{
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := childSelectionSet
        }]
      )
  | .inlineFragment _typeCondition _directives _childSelectionSet => ("", [])

private theorem collectFields_normal_object_eq_map
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name)
    : ∀ selectionSet : List Selection,
        selectionSetDirectiveFree selectionSet
        → selectionSetNormal schema parentType selectionSet
        → objectTypeNameBool schema parentType = true
        → Execution.collectFields schema variableValues parentType
            (.object parentType ()) selectionSet
          = selectionSet.map (fieldGroupOfSelection parentType)
  | [], _hfree, _hnormal, _hobject => by
      simp [Execution.collectFields]
  | selection :: rest, hfree, hnormal, hobject => by
      have hallFields : selectionsAllFields (selection :: rest) :=
        selectionSetNormal_allFields_of_object hnormal hobject
      have hselectionField : Selection.isField selection :=
        hallFields selection (by simp)
      cases selection with
      | inlineFragment typeCondition directives childSelectionSet =>
          simp [Selection.isField] at hselectionField
      | field responseName fieldName arguments directives childSelectionSet =>
          have hdirectives : directives = [] :=
            (selectionSetDirectiveFree_head hfree).1
          subst directives
          have hcollect :=
            NormalForm.GroundTypeNormalization.ExecutionKeys.collectFields_normal_object_field_head
                schema variableValues
                parentType (.object parentType ()) responseName fieldName
                arguments childSelectionSet rest hfree hnormal hobject
          rw [hcollect]
          rw [collectFields_normal_object_eq_map schema variableValues
            parentType rest (selectionSetDirectiveFree_tail hfree)
            (selectionSetNormal_tail hnormal) hobject]
          rfl

private theorem field_of_fieldGroup_mem
    (parentType responseName : Name)
    (selectionSet : List Selection)
    (hfree : selectionSetDirectiveFree selectionSet)
    (hallFields : selectionsAllFields selectionSet)
    (fields : List Execution.ExecutableField)
    (hgroup
      : (responseName, fields) ∈ selectionSet.map (fieldGroupOfSelection parentType))
    : ∃ fieldName arguments childSelectionSet,
        Selection.field responseName fieldName arguments [] childSelectionSet
          ∈ selectionSet
        ∧ fields
          = [{
              parentType := parentType
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := childSelectionSet
            }] := by
  rcases List.mem_map.mp hgroup with
    ⟨selection, hselection, hgroupEq⟩
  have hfield : Selection.isField selection :=
    hallFields selection hselection
  cases selection with
  | inlineFragment typeCondition directives childSelectionSet =>
      simp [Selection.isField] at hfield
  | field selectedResponseName fieldName arguments directives childSelectionSet =>
      have hdirectives : directives = [] :=
        selectionSetDirectiveFree_field_directives_nil_of_mem hfree hselection
      subst directives
      simp [fieldGroupOfSelection] at hgroupEq
      rcases hgroupEq with ⟨hresponseName, hfields⟩
      subst selectedResponseName
      exact ⟨fieldName, arguments, childSelectionSet, hselection, hfields.symm⟩

private theorem matching_field_of_reordering
    {left right : List Selection}
    {responseName fieldName : Name}
    {leftArguments : List Argument} {leftChild : List Selection}
    (hequal : SelectionSetEqualUpToReordering left right)
    (hleft : Selection.field responseName fieldName leftArguments [] leftChild ∈ left)
    : ∃ rightArguments rightChild,
        Selection.field responseName fieldName rightArguments [] rightChild ∈ right
        ∧ Argument.argumentsEquivalent leftArguments rightArguments
        ∧ SelectionSetEqualUpToReordering leftChild rightChild := by
  rcases selectionSetEqualUpToReordering_left_mem hequal hleft with
    ⟨rightSelection, hright, hrelation⟩
  cases hrelation with
  | field _ _ _ harguments hchildren =>
      exact ⟨_, _, hright, harguments, hchildren⟩

private theorem collectFields_normal_abstract_eq_matched_body
    (schema : Schema) (variableValues : Execution.VariableValues)
    (normalParentType runtimeType : Name)
    (selectionSet childSelectionSet : List Selection)
    (hnonObject : objectTypeNameBool schema normalParentType = false)
    (hruntimeObject : objectTypeNameBool schema runtimeType = true)
    (hfree : selectionSetDirectiveFree selectionSet)
    (hnormal : selectionSetNormal schema normalParentType selectionSet)
    (hmem
      : Selection.inlineFragment (some runtimeType) [] childSelectionSet ∈ selectionSet)
    : Execution.collectFields schema variableValues runtimeType
        (.object runtimeType ()) selectionSet
      = Execution.collectFields schema variableValues runtimeType
          (.object runtimeType ()) childSelectionSet := by
  rcases List.mem_iff_append.mp hmem with
    ⟨pref, suffix, hselectionSet⟩
  subst selectionSet
  let matched := Selection.inlineFragment (some runtimeType) [] childSelectionSet
  have hprefixFree : selectionSetDirectiveFree pref :=
    NormalForm.selectionSetDirectiveFree_append_left hfree
  have htailFree : selectionSetDirectiveFree (matched :: suffix) :=
    NormalForm.selectionSetDirectiveFree_append_right (left := pref) hfree
  have hsuffixFree : selectionSetDirectiveFree suffix :=
    selectionSetDirectiveFree_tail htailFree
  have hnodup : inlineFragmentTypeConditionsNodup
      (pref ++ matched :: suffix) :=
    selectionSetNormal_inlineFragmentTypeConditionsNodup hnormal
  have hnotOther :
      runtimeType ∉ (pref ++ suffix).filterMap inlineFragmentTypeCondition? :=
    inlineFragmentTypeCondition_not_mem_remove_middle_inlineFragment
      (pref := pref) (suffix := suffix) (typeCondition := runtimeType)
      (directives := []) (childSelectionSet := childSelectionSet) hnodup
  have hother : ∀ selection, selection ∈ pref ++ suffix →
      ∃ typeCondition body,
        selection = Selection.inlineFragment (some typeCondition) [] body
        ∧ objectTypeNameBool schema typeCondition = true
        ∧ typeCondition ≠ runtimeType := by
    intro selection hselection
    have hselectionOriginal : selection ∈ pref ++ matched :: suffix := by
      rcases List.mem_append.mp hselection with hprefix | hsuffix
      · exact List.mem_append_left _ hprefix
      · exact List.mem_append_right _ (List.mem_cons_of_mem matched hsuffix)
    rcases selectionSetNormal_inlineFragment_some_of_nonObject_mem hnormal
        hnonObject hselectionOriginal with
      ⟨typeCondition, directives, body, hselectionEq⟩
    subst selection
    have hdirectives : directives = [] :=
      selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem hfree
        hselectionOriginal
    subst directives
    rcases selectionSetNormal_inlineFragment_child_of_mem hnormal
        hselectionOriginal with ⟨htypeObject, _hbodyNormal⟩
    have htypeObjectBool : objectTypeNameBool schema typeCondition = true :=
      objectTypeNameBool_eq_true_of_objectType_forNormality schema htypeObject
    have hne : typeCondition ≠ runtimeType := by
      intro heq
      subst typeCondition
      exact hnotOther (List.mem_filterMap.mpr
        ⟨Selection.inlineFragment (some runtimeType) [] body, hselection,
          by simp [inlineFragmentTypeCondition?]⟩)
    exact ⟨typeCondition, body, rfl, htypeObjectBool, hne⟩
  have hprefixCollect :
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType ()) pref = [] :=
    collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
      schema variableValues (executionParentType := runtimeType)
      (runtimeType := runtimeType) () hprefixFree (by
        intro selection hselection
        exact hother selection (List.mem_append_left suffix hselection))
  have hsuffixCollect :
      Execution.collectFields schema variableValues runtimeType
          (.object runtimeType ()) suffix = [] :=
    collectFields_other_object_inlineFragments_eq_nil_at_runtime_parent
      schema variableValues (executionParentType := runtimeType)
      (runtimeType := runtimeType) () hsuffixFree (by
        intro selection hselection
        exact hother selection (List.mem_append_right pref hselection))
  have happly :
      Execution.doesFragmentTypeApplyBool schema runtimeType
          (.object runtimeType ()) runtimeType = true :=
    doesFragmentTypeApplyBool_object_self schema (ref := ()) hruntimeObject
  rw [collectFields_append schema variableValues runtimeType
    (.object runtimeType ()) pref (matched :: suffix)]
  rw [hprefixCollect]
  rw [mergeExecutableGroups_nil_left_collectFields_eq schema variableValues
    runtimeType (.object runtimeType ()) (matched :: suffix)]
  rw [collectFields_inlineFragment_some_directiveFree_apply schema
    variableValues runtimeType runtimeType (.object runtimeType ())
    childSelectionSet suffix happly]
  rw [hsuffixCollect]
  exact Execution.mergeExecutableGroups_nil_right _

private theorem normalSelectionSets_project_at_runtime
    (schema : Schema) (variableValues : Execution.VariableValues)
    (normalParentType runtimeType : Name)
    (left right : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hincludes : schema.typeIncludesObject normalParentType runtimeType)
    (hleftNormal : selectionSetNormal schema normalParentType left)
    (hrightNormal : selectionSetNormal schema normalParentType right)
    (hleftFree : selectionSetDirectiveFree left)
    (hrightFree : selectionSetDirectiveFree right)
    (hequal : SelectionSetEqualUpToReordering left right)
    : ∃ leftActive rightActive,
        selectionSetNormal schema runtimeType leftActive
        ∧ selectionSetNormal schema runtimeType rightActive
        ∧ selectionSetDirectiveFree leftActive
        ∧ selectionSetDirectiveFree rightActive
        ∧ SelectionSetEqualUpToReordering leftActive rightActive
        ∧ Execution.collectFields schema variableValues runtimeType
            (.object runtimeType ()) left
          = Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ()) leftActive
        ∧ Execution.collectFields schema variableValues runtimeType
            (.object runtimeType ()) right
          = Execution.collectFields schema variableValues runtimeType
              (.object runtimeType ()) rightActive := by
  have hincludeBool :
      schema.typeIncludesObjectBool normalParentType runtimeType = true :=
    List.contains_iff_mem.mpr hincludes
  have hruntimeObject : objectTypeNameBool schema runtimeType = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hincludeBool
  by_cases hparentObject :
      objectTypeNameBool schema normalParentType = true
  · have hruntimeEq : runtimeType = normalParentType :=
      typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema
        hparentObject hincludeBool
    subst runtimeType
    exact ⟨left, right, hleftNormal, hrightNormal, hleftFree, hrightFree,
      hequal, rfl, rfl⟩
  · have hparentAbstract :
        objectTypeNameBool schema normalParentType = false := by
      cases hvalue : objectTypeNameBool schema normalParentType
      · rfl
      · exact False.elim (hparentObject hvalue)
    by_cases hleftRuntime :
        runtimeType ∈ left.filterMap inlineFragmentTypeCondition?
    · rcases List.mem_filterMap.mp hleftRuntime with
        ⟨leftSelection, hleftMem, hleftCondition⟩
      cases leftSelection with
      | field responseName fieldName arguments directives childSelectionSet =>
          simp [inlineFragmentTypeCondition?] at hleftCondition
      | inlineFragment maybeTypeCondition leftDirectives leftBody =>
          cases maybeTypeCondition with
          | none =>
              simp [inlineFragmentTypeCondition?] at hleftCondition
          | some matchedTypeCondition =>
              simp [inlineFragmentTypeCondition?] at hleftCondition
              subst matchedTypeCondition
              have hleftDirectives : leftDirectives = [] :=
                selectionSetDirectiveFree_inlineFragment_directives_nil_of_mem
                  hleftFree hleftMem
              subst leftDirectives
              rcases selectionSetEqualUpToReordering_left_mem hequal hleftMem with
                ⟨rightSelection, hrightMem, hrelation⟩
              cases hrelation with
              | inlineFragment _ _ hchildren =>
                  rename_i rightBody
                  have hrightDirectives :
                      selectionSetDirectiveFree rightBody :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hrightFree hrightMem
                  have hleftBodyFree :
                      selectionSetDirectiveFree leftBody :=
                    selectionSetDirectiveFree_inlineFragment_child_of_mem
                      hleftFree hleftMem
                  rcases selectionSetNormal_inlineFragment_child_of_mem
                      hleftNormal hleftMem with
                    ⟨_hleftRuntimeObject, hleftBodyNormal⟩
                  rcases selectionSetNormal_inlineFragment_child_of_mem
                      hrightNormal hrightMem with
                    ⟨_hrightRuntimeObject, hrightBodyNormal⟩
                  have hleftCollect :=
                    collectFields_normal_abstract_eq_matched_body schema
                      variableValues normalParentType runtimeType left leftBody
                      hparentAbstract hruntimeObject hleftFree hleftNormal hleftMem
                  have hrightCollect :=
                    collectFields_normal_abstract_eq_matched_body schema
                      variableValues normalParentType runtimeType right rightBody
                      hparentAbstract hruntimeObject hrightFree hrightNormal hrightMem
                  exact ⟨leftBody, rightBody, hleftBodyNormal,
                    hrightBodyNormal, hleftBodyFree, hrightDirectives, hchildren,
                    hleftCollect, hrightCollect⟩
    · have hrightRuntime :
          runtimeType ∉ right.filterMap inlineFragmentTypeCondition? := by
        intro hmem
        exact hleftRuntime
          ((inlineFragmentTypeCondition_mem_iff_of_equalUpToReordering hequal).2
            hmem)
      have hleftCollect :=
        collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
          schema variableValues (normalParentType := normalParentType)
          (executionParentType := runtimeType) (runtimeType := runtimeType) ()
          hparentAbstract hleftFree hleftNormal hleftRuntime
      have hrightCollect :=
        collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
          schema variableValues (normalParentType := normalParentType)
          (executionParentType := runtimeType) (runtimeType := runtimeType) ()
          hparentAbstract hrightFree hrightNormal hrightRuntime
      have hemptyNormal : selectionSetNormal schema runtimeType [] := by
        simp [selectionSetNormal, selectionSetGroundTyped,
          selectionSetNonRedundant, responseNamesNodup,
          inlineFragmentTypeConditionsNodup, selectionsAllFields, hruntimeObject]
      refine ⟨[], [], hemptyNormal, hemptyNormal, selectionSetDirectiveFree_nil,
        selectionSetDirectiveFree_nil, selectionSetEqualUpToReordering_refl [],
        ?_, ?_⟩
      · simpa [Execution.collectFields] using hleftCollect
      · simpa [Execution.collectFields] using hrightCollect

private theorem normalSelectionSets_reordering_collectedFieldsSelectPath_singleton
    (schema : Schema) (variableValues : Execution.VariableValues)
    (step : PathStep) (normalParentType : Name)
    (left right : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hincludes : schema.typeIncludesObject normalParentType step.parentObject)
    (hleftNormal : selectionSetNormal schema normalParentType left)
    (hrightNormal : selectionSetNormal schema normalParentType right)
    (hleftFree : selectionSetDirectiveFree left)
    (hrightFree : selectionSetDirectiveFree right)
    (hequal : SelectionSetEqualUpToReordering left right)
    (hpath
      : collectedFieldsSelectPath schema variableValues
          (Execution.collectFields schema variableValues step.parentObject
            (.object step.parentObject ()) left) [step])
    : collectedFieldsSelectPath schema variableValues
        (Execution.collectFields schema variableValues step.parentObject
          (.object step.parentObject ()) right) [step] := by
  rcases normalSelectionSets_project_at_runtime schema variableValues
      normalParentType step.parentObject left right hschema hincludes
      hleftNormal hrightNormal hleftFree hrightFree hequal with
    ⟨leftActive, rightActive, hleftActiveNormal, hrightActiveNormal,
      hleftActiveFree, hrightActiveFree, hactiveEqual,
      hleftCollect, hrightCollect⟩
  rw [hleftCollect] at hpath
  rw [hrightCollect]
  have hincludeBool :
      schema.typeIncludesObjectBool normalParentType step.parentObject = true :=
    List.contains_iff_mem.mpr hincludes
  have hobject : objectTypeNameBool schema step.parentObject = true :=
    objectTypeNameBool_of_typeIncludesObjectBool hschema hincludeBool
  have hleftMap := collectFields_normal_object_eq_map schema variableValues
    step.parentObject leftActive hleftActiveFree hleftActiveNormal hobject
  have hrightMap := collectFields_normal_object_eq_map schema variableValues
    step.parentObject rightActive hrightActiveFree hrightActiveNormal hobject
  rw [hleftMap, collectedFieldsSelectPath_singleton] at hpath
  rw [hrightMap, collectedFieldsSelectPath_singleton]
  rcases hpath with ⟨fields, hgroup, field, hfield, hmatch⟩
  rcases field_of_fieldGroup_mem step.parentObject step.responseName
      leftActive hleftActiveFree
      (selectionSetNormal_allFields_of_object hleftActiveNormal hobject)
      fields hgroup with
    ⟨fieldName, leftArguments, leftChild, hleftSelection, hfields⟩
  subst fields
  simp only [List.mem_singleton] at hfield
  subst field
  rcases matching_field_of_reordering hactiveEqual hleftSelection with
    ⟨rightArguments, rightChild, hrightSelection, harguments, hchildren⟩
  let rightField : Execution.ExecutableField :=
    {
      parentType := step.parentObject
      responseName := step.responseName
      fieldName := fieldName
      arguments := rightArguments
      selectionSet := rightChild
    }
  have hrightGroup :
      (step.responseName, [rightField]) ∈
        rightActive.map (fieldGroupOfSelection step.parentObject) :=
    List.mem_map.mpr ⟨_, hrightSelection, by
      simp [fieldGroupOfSelection, rightField]⟩
  have hrightMatch : executableFieldMatchesPathStep schema rightField step := by
    rcases hmatch with
      ⟨hresponseName, hfieldName, hleftArguments, fieldDefinition,
        hlookup, houtput⟩
    exact ⟨hresponseName, hfieldName,
      Argument.argumentsEquivalent_trans
        (Argument.argumentsEquivalent_symm harguments) hleftArguments,
      fieldDefinition, hlookup, houtput⟩
  exact ⟨[rightField], hrightGroup, rightField, by simp, hrightMatch⟩

private theorem normalSelectionSets_reordering_collectedFieldsSelectPath
    (schema : Schema) (variableValues : Execution.VariableValues)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    : ∀ rest : List PathStep,
      ∀ (step : PathStep) (normalParentType : Name) (left right : List Selection),
        schema.typeIncludesObject normalParentType step.parentObject
        → selectionSetNormal schema normalParentType left
        → selectionSetNormal schema normalParentType right
        → selectionSetDirectiveFree left
        → selectionSetDirectiveFree right
        → SelectionSetEqualUpToReordering left right
        → collectedFieldsSelectPath schema variableValues
            (Execution.collectFields schema variableValues step.parentObject
              (.object step.parentObject ()) left) (step :: rest)
        → collectedFieldsSelectPath schema variableValues
            (Execution.collectFields schema variableValues step.parentObject
              (.object step.parentObject ()) right) (step :: rest) := by
  intro rest
  induction rest with
  | nil =>
      intro step normalParentType left right hincludes hleftNormal
        hrightNormal hleftFree hrightFree hequal hpath
      exact
        normalSelectionSets_reordering_collectedFieldsSelectPath_singleton
          schema variableValues step normalParentType left right hschema
          hincludes hleftNormal hrightNormal hleftFree hrightFree hequal hpath
  | cons next tail ih =>
      intro step normalParentType left right hincludes hleftNormal
        hrightNormal hleftFree hrightFree hequal hpath
      rcases normalSelectionSets_project_at_runtime schema variableValues
          normalParentType step.parentObject left right hschema hincludes
          hleftNormal hrightNormal hleftFree hrightFree hequal with
        ⟨leftActive, rightActive, hleftActiveNormal, hrightActiveNormal,
          hleftActiveFree, hrightActiveFree, hactiveEqual,
          hleftCollect, hrightCollect⟩
      rw [hleftCollect] at hpath
      rw [hrightCollect]
      have hincludeBool :
          schema.typeIncludesObjectBool normalParentType
            step.parentObject = true :=
        List.contains_iff_mem.mpr hincludes
      have hobject : objectTypeNameBool schema step.parentObject = true :=
        objectTypeNameBool_of_typeIncludesObjectBool hschema hincludeBool
      have hleftMap := collectFields_normal_object_eq_map schema variableValues
        step.parentObject leftActive hleftActiveFree hleftActiveNormal hobject
      have hrightMap := collectFields_normal_object_eq_map schema variableValues
        step.parentObject rightActive hrightActiveFree hrightActiveNormal hobject
      rw [hleftMap, collectedFieldsSelectPath_cons_cons] at hpath
      rw [hrightMap, collectedFieldsSelectPath_cons_cons]
      rcases hpath with
        ⟨fields, hgroup, ⟨field, hfield, hmatch⟩,
          hnextIncludes, hchildPath⟩
      rcases field_of_fieldGroup_mem step.parentObject step.responseName
          leftActive hleftActiveFree
          (selectionSetNormal_allFields_of_object hleftActiveNormal hobject)
          fields hgroup with
        ⟨fieldName, leftArguments, leftChild, hleftSelection, hfields⟩
      subst fields
      simp only [List.mem_singleton] at hfield
      subst field
      rcases matching_field_of_reordering hactiveEqual hleftSelection with
        ⟨rightArguments, rightChild, hrightSelection, harguments, hchildren⟩
      rcases selectionSetNormal_field_child_of_mem_with_returnType
          hleftActiveNormal hleftSelection with
        ⟨leftReturnType, hleftReturnType, hleftChildNormal⟩
      rcases selectionSetNormal_field_child_of_mem_with_returnType
          hrightActiveNormal hrightSelection with
        ⟨rightReturnType, hrightReturnType, hrightChildNormal'⟩
      have hreturnTypes : rightReturnType = leftReturnType := by
        rw [hleftReturnType] at hrightReturnType
        exact (Option.some.inj hrightReturnType).symm
      subst rightReturnType
      have hleftChildFree : selectionSetDirectiveFree leftChild :=
        selectionSetDirectiveFree_field_child_of_mem hleftActiveFree
          hleftSelection
      have hrightChildFree : selectionSetDirectiveFree rightChild :=
        selectionSetDirectiveFree_field_child_of_mem hrightActiveFree
          hrightSelection
      have hleftChildPath :
          collectedFieldsSelectPath schema variableValues
            (Execution.collectFields schema variableValues next.parentObject
              (.object next.parentObject ()) leftChild) (next :: tail) := by
        simpa [Execution.collectSubfields, Execution.mergeExecutableGroups]
          using hchildPath
      rcases hmatch with
        ⟨hresponseName, hfieldName, hleftArguments, fieldDefinition,
          hlookup, houtput⟩
      have hreturnTypeAtStep :
          schema.fieldReturnType? step.parentObject step.field.fieldName =
            some leftReturnType := by
        rw [← hfieldName]
        exact hleftReturnType
      have hdefinitionReturn :
          fieldDefinition.outputType.namedType = leftReturnType :=
        fieldDefinition_namedType_eq_of_fieldReturnType? hlookup
          hreturnTypeAtStep
      have houtputNamed :
          fieldDefinition.outputType.namedType = step.field.outputType.namedType :=
        congrArg (fun outputType : TypeRef => outputType.namedType) houtput
      have hreturnTypeEq :
          leftReturnType = step.field.outputType.namedType :=
        hdefinitionReturn.symm.trans houtputNamed
      have hchildIncludes :
          schema.typeIncludesObject leftReturnType next.parentObject := by
        simpa [hreturnTypeEq] using hnextIncludes
      have hrightChildPath := ih next leftReturnType leftChild rightChild
        hchildIncludes hleftChildNormal hrightChildNormal' hleftChildFree
        hrightChildFree hchildren hleftChildPath
      let rightField : Execution.ExecutableField :=
        {
          parentType := step.parentObject
          responseName := step.responseName
          fieldName := fieldName
          arguments := rightArguments
          selectionSet := rightChild
        }
      have hrightGroup :
          (step.responseName, [rightField]) ∈
            rightActive.map (fieldGroupOfSelection step.parentObject) :=
        List.mem_map.mpr ⟨_, hrightSelection, by
          simp [fieldGroupOfSelection, rightField]⟩
      have hrightMatch :
          executableFieldMatchesPathStep schema rightField step :=
        ⟨hresponseName, hfieldName,
          Argument.argumentsEquivalent_trans
            (Argument.argumentsEquivalent_symm harguments) hleftArguments,
          fieldDefinition, hlookup, houtput⟩
      refine ⟨[rightField], hrightGroup, ?_, hnextIncludes, ?_⟩
      · exact ⟨rightField, by simp, hrightMatch⟩
      · simpa [Execution.collectSubfields, Execution.mergeExecutableGroups]
          using hrightChildPath

private theorem normalSelectionSets_reordering_collectedFieldsSelectPath_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (step : PathStep) (rest : List PathStep) (normalParentType : Name)
    (left right : List Selection)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hincludes : schema.typeIncludesObject normalParentType step.parentObject)
    (hleftNormal : selectionSetNormal schema normalParentType left)
    (hrightNormal : selectionSetNormal schema normalParentType right)
    (hleftFree : selectionSetDirectiveFree left)
    (hrightFree : selectionSetDirectiveFree right)
    (hequal : SelectionSetEqualUpToReordering left right)
    : collectedFieldsSelectPath schema variableValues
        (Execution.collectFields schema variableValues step.parentObject
          (.object step.parentObject ()) left) (step :: rest)
      ↔ collectedFieldsSelectPath schema variableValues
          (Execution.collectFields schema variableValues step.parentObject
            (.object step.parentObject ()) right) (step :: rest) := by
  constructor
  · exact normalSelectionSets_reordering_collectedFieldsSelectPath
      schema variableValues hschema rest step normalParentType left right
      hincludes hleftNormal hrightNormal hleftFree hrightFree hequal
  · exact normalSelectionSets_reordering_collectedFieldsSelectPath
      schema variableValues hschema rest step normalParentType right left
      hincludes hrightNormal hleftNormal hrightFree hleftFree
      (NormalForm.SelectionSetEqualUpToReordering.symm hequal)

private theorem completeNormalizeOperation_boolVarsEquivalent_of_nonempty
    (schema : Schema) (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hnonempty : (completeNormalizeOperation schema operation).selectionSet ≠ [])
    : operationBoolVarsEquivalent operation
        (completeNormalizeOperation schema operation) := by
  have hrootObject : objectTypeNameBool schema (operation.rootType schema) = true :=
    operation_root_objectTypeNameBool_of_wf_valid hschema hvalid
  intro candidate
  cases hvariables : operationBoolVars operation with
  | nil =>
      have hnormal :
          completeNormalSelectionSet schema [] (operation.rootType schema)
            (completeNormalizeRootSelectionSet schema []
              (operation.rootType schema) operation.selectionSet) :=
        completeNormalizeRootSelectionSet_normal_nil schema hschema
          (operation.rootType schema) operation.selectionSet
          (completeNormalizeRootSelectionSet schema []
            (operation.rootType schema) operation.selectionSet)
          hrootObject rfl
      have hnormalizedFree :
          selectionSetDirectiveFree
            (completeNormalizeRootSelectionSet schema []
              (operation.rootType schema) operation.selectionSet) :=
        hnormal.2.2
      have hnormalizedVariables :
          operationBoolVars (completeNormalizeOperation schema operation) = [] := by
        unfold operationBoolVars
        rw [completeNormalizeOperation_selectionSet, hvariables]
        rw [selectionSetDirectiveFree_booleanVariables_nil _ hnormalizedFree]
        rfl
      simp [hnormalizedVariables]
  | cons varName variables =>
      have hvariablesNodup : (varName :: variables).Nodup := by
        simpa [hvariables] using operationBoolVars_nodup operation
      have hnormal :
          completeNormalSelectionSet schema (varName :: variables)
            (operation.rootType schema)
            (completeNormalizeRootSelectionSet schema (varName :: variables)
              (operation.rootType schema) operation.selectionSet) :=
        completeNormalizeRootSelectionSet_normal_cons schema hschema varName
          variables hvariablesNodup (operation.rootType schema)
          operation.selectionSet
          (completeNormalizeRootSelectionSet schema (varName :: variables)
            (operation.rootType schema) operation.selectionSet)
          hrootObject rfl
      have hnormalizedNonempty :
          completeNormalizeRootSelectionSet schema (varName :: variables)
            (operation.rootType schema) operation.selectionSet ≠ [] := by
        simpa [completeNormalizeOperation, hvariables] using hnonempty
      have hnormalizedIff :=
        operationBoolVars_mem_iff_of_completeNormalSelectionSet_cons hnormal
          hnormalizedNonempty candidate
      have hnormalizedOperationIff :
          candidate ∈ operationBoolVars
              (completeNormalizeOperation schema operation) ↔
            candidate ∈ varName :: variables := by
        unfold operationBoolVars
        rw [completeNormalizeOperation_selectionSet, hvariables]
        exact hnormalizedIff
      simpa [hvariables] using hnormalizedOperationIff.symm

private theorem completeNormalSelection_body_normal_free
    {schema : Schema} {leftVar : BoolVar} {variables : List BoolVar}
    {parentType : Name} {selectionSet : List Selection}
    (hnormal
      : completeNormalSelectionSet schema (leftVar :: variables) parentType selectionSet)
    {selection : Selection} {boolCase : BoolCase} {body : List Selection}
    (hmem : selection ∈ selectionSet)
    (hcase : completeNormalBoolCase (leftVar :: variables) boolCase)
    (hstem : completeNormalBooleanStem boolCase selection body)
    : selectionSetNormal schema parentType body ∧ selectionSetDirectiveFree body := by
  rcases hnormal with
    ⟨_hvariablesNodup, _hselectionSetNodup, hbranches, _hunique⟩
  rcases hbranches selection hmem with
    ⟨normalCase, normalBody, hnormalCase, hnormalStem,
      hbodyNormal, hbodyFree⟩
  have heq := completeNormalBooleanStem_case_body_eq hcase hnormalCase
    (by simp) hstem hnormalStem
  cases heq.1
  cases heq.2
  exact ⟨hbodyNormal, hbodyFree⟩

private theorem completeNormalOperations_reordering_collectedFieldsSelectPath_iff
    (schema : Schema) (left right : Operation) (assignment : BoolCase)
    (step : PathStep) (rest : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrootObject : objectTypeNameBool schema (left.rootType schema) = true)
    (hincludes : schema.typeIncludesObject (left.rootType schema) step.parentObject)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hequal : completeNormalOperationsEqualUpToReordering left right)
    (hcomplete
      : operationBoolVars left ≠ []
        → completeNormalBoolCase (operationBoolVars left) assignment)
    : collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
        (Execution.collectFields schema (boolCaseVariableValues assignment)
          (left.rootType schema) (.object step.parentObject ())
          left.selectionSet) (step :: rest)
      ↔ collectedFieldsSelectPath schema (boolCaseVariableValues assignment)
          (Execution.collectFields schema (boolCaseVariableValues assignment)
            (right.rootType schema) (.object step.parentObject ())
            right.selectionSet) (step :: rest) := by
  have hvariables :=
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReordering
      hequal
  rcases hequal with ⟨hoperationType, hselectionEqual⟩
  have hroot : left.rootType schema = right.rootType schema := by
    exact congrArg (fun operationType => operationType.rootType schema)
      hoperationType
  have hincludeBool :
      schema.typeIncludesObjectBool (left.rootType schema)
        step.parentObject = true :=
    List.contains_iff_mem.mpr hincludes
  have hstepParent : step.parentObject = left.rootType schema :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hrootObject
      hincludeBool
  cases hleftVars : operationBoolVars left with
  | nil =>
      have hrightVars : operationBoolVars right = [] :=
        operationBoolVars_eq_nil_of_equivalent_left_nil hvariables hleftVars
      have hleftShape := hleftNormal
      have hrightShape := hrightNormal
      simp [completeNormalOperation, completeNormalSelectionSet, hleftVars]
        at hleftShape
      simp [completeNormalOperation, completeNormalSelectionSet, hrightVars]
        at hrightShape
      have hrightNormalAtLeft :
          selectionSetNormal schema (left.rootType schema) right.selectionSet := by
        simpa [hroot] using hrightShape.1
      have hselectionGround :
          SelectionSetEqualUpToReordering left.selectionSet right.selectionSet := by
        simpa [hleftVars] using hselectionEqual
      have hiff :=
        normalSelectionSets_reordering_collectedFieldsSelectPath_iff schema
          (boolCaseVariableValues assignment) step rest (left.rootType schema)
          left.selectionSet right.selectionSet hschema hincludes hleftShape.1
          hrightNormalAtLeft hleftShape.2 hrightShape.2 hselectionGround
      simpa [hstepParent, hroot] using hiff
  | cons leftVar leftVariables =>
      cases hrightVars : operationBoolVars right with
      | nil =>
          have hleftHead : leftVar ∈ operationBoolVars left := by
            simp [hleftVars]
          have hrightHead : leftVar ∈ operationBoolVars right :=
            (hvariables leftVar).1 hleftHead
          simp [hrightVars] at hrightHead
      | cons rightVar rightVariables =>
          have hvariables' : ∀ varName,
              varName ∈ leftVar :: leftVariables ↔
                varName ∈ rightVar :: rightVariables := by
            intro varName
            simpa [hleftVars, hrightVars] using hvariables varName
          have hruntimeLeft :
              completeNormalBoolCase (leftVar :: leftVariables) assignment := by
            simpa [hleftVars] using hcomplete (by simp [hleftVars])
          have hruntimeRight :
              completeNormalBoolCase (rightVar :: rightVariables) assignment :=
            completeNormalBoolCase_of_variable_mem_iff hruntimeLeft
              (by simpa [hrightVars] using operationBoolVars_nodup right)
              (fun varName =>
                (hruntimeLeft.2.2 varName).trans (hvariables' varName))
          have hleftNormal' :
              completeNormalSelectionSet schema (leftVar :: leftVariables)
                (left.rootType schema) left.selectionSet := by
            simpa [completeNormalOperation, hleftVars] using hleftNormal
          have hrightNormal' :
              completeNormalSelectionSet schema (rightVar :: rightVariables)
                (right.rootType schema) right.selectionSet := by
            simpa [completeNormalOperation, hrightVars] using hrightNormal
          have hcompleteEqual :
              CompleteNormalSelectionSetEqualUpToReordering
                (leftVar :: leftVariables) (rightVar :: rightVariables)
                left.selectionSet right.selectionSet := by
            simpa [hleftVars, hrightVars] using hselectionEqual
          rcases hcompleteEqual with
            ⟨pairs, hpairsLeft, hpairsRight, hpairsEqual⟩
          by_cases hmatch : ∃ pair leftCase rightCase leftBody rightBody,
              pair ∈ pairs
              ∧ completeNormalBoolCase (leftVar :: leftVariables) leftCase
              ∧ completeNormalBoolCase (rightVar :: rightVariables) rightCase
              ∧ completeNormalBooleanStem leftCase pair.1 leftBody
              ∧ completeNormalBooleanStem rightCase pair.2 rightBody
              ∧ completeNormalBoolCasesEquivalent leftCase rightCase
              ∧ SelectionSetEqualUpToReordering leftBody rightBody
              ∧ completeNormalBoolCasesEquivalent assignment leftCase
          · rcases hmatch with
              ⟨pair, leftCase, rightCase, leftBody, rightBody, hpair,
                hleftCase, hrightCase, hleftStem, hrightStem, hcasesEqual,
                hbodiesEqual, hruntimeEqual⟩
            have hleftPairMem : pair.1 ∈ pairs.map Prod.fst :=
              List.mem_map.mpr ⟨pair, hpair, rfl⟩
            have hrightPairMem : pair.2 ∈ pairs.map Prod.snd :=
              List.mem_map.mpr ⟨pair, hpair, rfl⟩
            have hleftMem : pair.1 ∈ left.selectionSet :=
              hpairsLeft.mem_iff.mp hleftPairMem
            have hrightMem : pair.2 ∈ right.selectionSet :=
              hpairsRight.mem_iff.mp hrightPairMem
            have hleftBody := completeNormalSelection_body_normal_free
              hleftNormal' hleftMem hleftCase hleftStem
            have hrightBody := completeNormalSelection_body_normal_free
              hrightNormal' hrightMem hrightCase hrightStem
            have hrightRuntimeEqual :
                completeNormalBoolCasesEquivalent assignment rightCase :=
              completeNormalBoolCasesEquivalent_trans hruntimeEqual hcasesEqual
            have hleftCollect :=
              collectFields_completeNormalSelectionSet_eq_body_of_equivalent
                schema [] (left.rootType schema) (.object step.parentObject ())
                hleftNormal' hleftMem hruntimeLeft hleftCase hruntimeEqual
                hleftStem hleftBody.2
            have hrightCollect :=
              collectFields_completeNormalSelectionSet_eq_body_of_equivalent
                schema [] (right.rootType schema) (.object step.parentObject ())
                hrightNormal' hrightMem hruntimeRight hrightCase
                hrightRuntimeEqual hrightStem hrightBody.2
            rw [hleftCollect, hrightCollect]
            have hrightBodyNormalAtLeft :
                selectionSetNormal schema (left.rootType schema) rightBody := by
              simpa [hroot] using hrightBody.1
            have hiff :=
              normalSelectionSets_reordering_collectedFieldsSelectPath_iff
                schema (boolCaseVariableValues assignment) step rest
                (left.rootType schema) leftBody rightBody hschema hincludes
                hleftBody.1 hrightBodyNormalAtLeft hleftBody.2 hrightBody.2
                hbodiesEqual
            simpa [hstepParent, hroot] using hiff
          · have hnoneLeft : ¬ ∃ selection candidate body,
                selection ∈ left.selectionSet
                ∧ completeNormalBoolCase (leftVar :: leftVariables) candidate
                ∧ completeNormalBooleanStem candidate selection body
                ∧ completeNormalBoolCasesEquivalent assignment candidate := by
              rintro ⟨selection, candidate, body, hselection, hcandidate,
                hstem, hequivalent⟩
              have hselectionPair : selection ∈ pairs.map Prod.fst :=
                hpairsLeft.mem_iff.mpr hselection
              rcases List.mem_map.mp hselectionPair with
                ⟨pair, hpair, hpairLeft⟩
              rcases hpairsEqual pair hpair with
                ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
                  hrightCase, hleftStem, hrightStem, hcasesEqual,
                  hbodiesEqual⟩
              have hcandidateStemAtPair :
                  completeNormalBooleanStem candidate pair.1 body := by
                simpa [hpairLeft] using hstem
              have hcaseBodyEq := completeNormalBooleanStem_case_body_eq
                hcandidate hleftCase (by simp) hcandidateStemAtPair hleftStem
              have hcandidateCasesEqual :
                  completeNormalBoolCasesEquivalent candidate rightCase := by
                simpa [hcaseBodyEq.1] using hcasesEqual
              have hcandidateBodiesEqual :
                  SelectionSetEqualUpToReordering body rightBody := by
                simpa [hcaseBodyEq.2] using hbodiesEqual
              exact hmatch ⟨pair, candidate, rightCase, body, rightBody,
                hpair, hcandidate, hrightCase, hcandidateStemAtPair,
                hrightStem, hcandidateCasesEqual, hcandidateBodiesEqual,
                hequivalent⟩
            have hnoneRight : ¬ ∃ selection candidate body,
                selection ∈ right.selectionSet
                ∧ completeNormalBoolCase (rightVar :: rightVariables) candidate
                ∧ completeNormalBooleanStem candidate selection body
                ∧ completeNormalBoolCasesEquivalent assignment candidate := by
              rintro ⟨selection, candidate, body, hselection, hcandidate,
                hstem, hequivalent⟩
              have hselectionPair : selection ∈ pairs.map Prod.snd :=
                hpairsRight.mem_iff.mpr hselection
              rcases List.mem_map.mp hselectionPair with
                ⟨pair, hpair, hpairRight⟩
              rcases hpairsEqual pair hpair with
                ⟨leftCase, rightCase, leftBody, rightBody, hleftCase,
                  hrightCase, hleftStem, hrightStem, hcasesEqual,
                  hbodiesEqual⟩
              have hcandidateStemAtPair :
                  completeNormalBooleanStem candidate pair.2 body := by
                simpa [hpairRight] using hstem
              have hcaseBodyEq := completeNormalBooleanStem_case_body_eq
                hcandidate hrightCase (by simp) hcandidateStemAtPair hrightStem
              have hleftCandidateCasesEqual :
                  completeNormalBoolCasesEquivalent leftCase candidate := by
                simpa [hcaseBodyEq.1] using hcasesEqual
              have hleftCandidateBodiesEqual :
                  SelectionSetEqualUpToReordering leftBody body := by
                simpa [hcaseBodyEq.2] using hbodiesEqual
              have hruntimeLeftCase := completeNormalBoolCasesEquivalent_trans
                hequivalent
                (completeNormalBoolCasesEquivalent_symm
                  hleftCandidateCasesEqual)
              exact hmatch ⟨pair, leftCase, candidate, leftBody, body,
                hpair, hleftCase, hcandidate, hleftStem,
                hcandidateStemAtPair, hleftCandidateCasesEqual,
                hleftCandidateBodiesEqual, hruntimeLeftCase⟩
            have hleftCollect :=
              collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent
                schema [] (left.rootType schema) (.object step.parentObject ())
                hleftNormal' hruntimeLeft hnoneLeft
            have hrightCollect :=
              collectFields_completeNormalSelectionSet_eq_nil_of_no_equivalent
                schema [] (right.rootType schema) (.object step.parentObject ())
                hrightNormal' hruntimeRight hnoneRight
            rw [hleftCollect, hrightCollect]

private theorem completeNormalOperations_reordering_operationSelectsPath_iff
    (schema : Schema) (left right : Operation) (assignment : BoolCase)
    (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hrootObject : objectTypeNameBool schema (left.rootType schema) = true)
    (hleftNormal : completeNormalOperation schema left)
    (hrightNormal : completeNormalOperation schema right)
    (hequal : completeNormalOperationsEqualUpToReordering left right)
    (hcomplete
      : operationBoolVars left ≠ []
        → completeNormalBoolCase (operationBoolVars left) assignment)
    : operationSelectsPath schema left assignment path
      ↔ operationSelectsPath schema right assignment path := by
  cases path with
  | nil => simp
  | cons step rest =>
      rw [operationSelectsPath_cons_iff, operationSelectsPath_cons_iff]
      have hroot : left.rootType schema = right.rootType schema :=
        congrArg (fun operationType => operationType.rootType schema) hequal.1
      constructor
      · rintro ⟨hincludes, hpath⟩
        have hrightIncludes :
            schema.typeIncludesObject (right.rootType schema)
              step.parentObject := by
          simpa [← hroot] using hincludes
        exact ⟨hrightIncludes,
          (completeNormalOperations_reordering_collectedFieldsSelectPath_iff
            schema left right assignment step rest hschema hrootObject
            hincludes hleftNormal hrightNormal hequal hcomplete).1 hpath⟩
      · rintro ⟨hrightIncludes, hpath⟩
        have hleftIncludes :
            schema.typeIncludesObject (left.rootType schema)
              step.parentObject := by
          simpa [hroot] using hrightIncludes
        exact ⟨hleftIncludes,
          (completeNormalOperations_reordering_collectedFieldsSelectPath_iff
            schema left right assignment step rest hschema hrootObject
            hleftIncludes hleftNormal hrightNormal hequal hcomplete).2 hpath⟩

private theorem completeNormalizeOperation_operationSelectsPath_iff
    (schema : Schema) (operation : Operation) (assignment : BoolCase)
    (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hvalid : Validation.operationDefinitionValid schema operation)
    (hcomplete : completeNormalBoolCase (operationBoolVars operation) assignment)
    : operationSelectsPath schema (completeNormalizeOperation schema operation)
        assignment path
      ↔ operationSelectsPath schema operation assignment path := by
  cases path with
  | nil => simp
  | cons step rest =>
      rw [operationSelectsPath_cons_iff, operationSelectsPath_cons_iff]
      rw [completeNormalizeOperation_rootType,
        completeNormalizeOperation_selectionSet]
      have hvaluesComplete :
          boolVarsComplete (operationBoolVars operation)
            (boolCaseVariableValues assignment) :=
        boolVarsComplete_boolCaseVariableValues [] hcomplete
      rcases allBoolCases_complete_for_variableValues
          (boolCaseVariableValues assignment) (operationBoolVars operation)
          hvaluesComplete with
        ⟨runtimeCase, hruntimeCase, hagrees⟩
      constructor
      · rintro ⟨hincludes, hpath⟩
        refine ⟨hincludes, ?_⟩
        have hfullCollect :
            Execution.collectFields schema (boolCaseVariableValues assignment)
                (operation.rootType schema) (.object step.parentObject ())
                (completeNormalizeRootSelectionSet schema
                  (operationBoolVars operation) (operation.rootType schema)
                  operation.selectionSet) =
              Execution.collectFields schema (boolCaseVariableValues assignment)
                (operation.rootType schema) (.object step.parentObject ())
                (normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)) := by
          calc
            _ = Execution.collectFields schema
                  (boolCaseVariableValues assignment)
                  (operation.rootType schema) (.object step.parentObject ())
                  (List.flatten
                    ((allBoolCases (operationBoolVars operation)).map
                      (fun boolCase =>
                        wrapWithBoolCase boolCase
                          (normalizeSelectionSet schema (operation.rootType schema)
                            (filterSelectionSetBoolCase boolCase
                              operation.selectionSet))))) :=
                collectFields_completeNormalizeRootSelectionSet_eq_wrapped
                  schema (boolCaseVariableValues assignment)
                  (operationBoolVars operation) (operation.rootType schema)
                  (.object step.parentObject ()) operation.selectionSet
            _ = _ := collectFields_flatten_boolCaseWrappers_runtime schema
              (boolCaseVariableValues assignment) operation
              (operation.rootType schema) (.object step.parentObject ())
              runtimeCase
              (fun boolCase =>
                normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase boolCase operation.selectionSet))
              hruntimeCase hagrees
        rw [hfullCollect] at hpath
        exact
          (collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation runtimeCase (boolCaseVariableValues assignment)
            step rest hschema hvalid hagrees hincludes).1 hpath
      · rintro ⟨hincludes, hpath⟩
        refine ⟨hincludes, ?_⟩
        have hnormalizedPath :=
          (collectedFieldsSelectPath_normalize_filterSelectionSetBoolCase_for_agreeing_values_iff
            schema operation runtimeCase (boolCaseVariableValues assignment)
            step rest hschema hvalid hagrees hincludes).2 hpath
        have hfullCollect :
            Execution.collectFields schema (boolCaseVariableValues assignment)
                (operation.rootType schema) (.object step.parentObject ())
                (completeNormalizeRootSelectionSet schema
                  (operationBoolVars operation) (operation.rootType schema)
                  operation.selectionSet) =
              Execution.collectFields schema (boolCaseVariableValues assignment)
                (operation.rootType schema) (.object step.parentObject ())
                (normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase runtimeCase
                    operation.selectionSet)) := by
          calc
            _ = Execution.collectFields schema
                  (boolCaseVariableValues assignment)
                  (operation.rootType schema) (.object step.parentObject ())
                  (List.flatten
                    ((allBoolCases (operationBoolVars operation)).map
                      (fun boolCase =>
                        wrapWithBoolCase boolCase
                          (normalizeSelectionSet schema (operation.rootType schema)
                            (filterSelectionSetBoolCase boolCase
                              operation.selectionSet))))) :=
                collectFields_completeNormalizeRootSelectionSet_eq_wrapped
                  schema (boolCaseVariableValues assignment)
                  (operationBoolVars operation) (operation.rootType schema)
                  (.object step.parentObject ()) operation.selectionSet
            _ = _ := collectFields_flatten_boolCaseWrappers_runtime schema
              (boolCaseVariableValues assignment) operation
              (operation.rootType schema) (.object step.parentObject ())
              runtimeCase
              (fun boolCase =>
                normalizeSelectionSet schema (operation.rootType schema)
                  (filterSelectionSetBoolCase boolCase operation.selectionSet))
              hruntimeCase hagrees
        rwa [hfullCollect]

/-- Complete-normal equality up to reordering preserves the selected-path
footprint of the source operations under every complete Boolean assignment. -/
theorem completeNormalize_equalUpToReordering_operationSelectsPath_iff
    (schema : Schema) (left right : Operation)
    (assignment : BoolCase) (path : List PathStep)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hleftValid : Validation.operationDefinitionValid schema left)
    (hrightValid : Validation.operationDefinitionValid schema right)
    (hsupport : operationBoolVarsEquivalent left right)
    (heq
      : completeNormalOperationsEqualUpToReordering
          (completeNormalizeOperation schema left)
          (completeNormalizeOperation schema right))
    (hcomplete : completeNormalBoolCase (operationBoolVars left) assignment)
    : operationSelectsPath schema left assignment path
      ↔ operationSelectsPath schema right assignment path := by
  let normalizedLeft := completeNormalizeOperation schema left
  let normalizedRight := completeNormalizeOperation schema right
  have hrightComplete :
      completeNormalBoolCase (operationBoolVars right) assignment :=
    completeNormalBoolCase_of_variable_mem_iff hcomplete
      (operationBoolVars_nodup right) (fun varName =>
        (hcomplete.2.2 varName).trans (hsupport varName))
  have hleftNormal : completeNormalOperation schema normalizedLeft := by
    simpa [normalizedLeft] using
      completeNormalizeOperation_normal schema left hschema hleftValid
  have hrightNormal : completeNormalOperation schema normalizedRight := by
    simpa [normalizedRight] using
      completeNormalizeOperation_normal schema right hschema hrightValid
  have hnormalizedComplete : operationBoolVars normalizedLeft ≠ [] →
      completeNormalBoolCase (operationBoolVars normalizedLeft) assignment := by
    intro hvariablesNonempty
    have hselectionNonempty : normalizedLeft.selectionSet ≠ [] := by
      intro hselectionEmpty
      apply hvariablesNonempty
      simp [operationBoolVars, hselectionEmpty, selectionSetBooleanVariables,
        dedupBoolVars]
    have hnormalizedSupport :
        operationBoolVarsEquivalent left normalizedLeft := by
      simpa [normalizedLeft] using
        completeNormalizeOperation_boolVarsEquivalent_of_nonempty schema left
          hschema hleftValid (by simpa [normalizedLeft] using hselectionNonempty)
    exact completeNormalBoolCase_of_variable_mem_iff hcomplete
      (operationBoolVars_nodup normalizedLeft) (fun varName =>
        (hcomplete.2.2 varName).trans (hnormalizedSupport varName))
  have hrootObject :
      objectTypeNameBool schema (normalizedLeft.rootType schema) = true := by
    simpa [normalizedLeft, completeNormalizeOperation_rootType] using
      operation_root_objectTypeNameBool_of_wf_valid hschema hleftValid
  have hnormalizedIff :
      operationSelectsPath schema normalizedLeft assignment path ↔
        operationSelectsPath schema normalizedRight assignment path := by
    exact completeNormalOperations_reordering_operationSelectsPath_iff
      schema normalizedLeft normalizedRight assignment path hschema hrootObject
      hleftNormal hrightNormal (by simpa [normalizedLeft, normalizedRight] using heq)
      hnormalizedComplete
  have hleftNormalization :
      operationSelectsPath schema normalizedLeft assignment path ↔
        operationSelectsPath schema left assignment path := by
    simpa [normalizedLeft] using
      completeNormalizeOperation_operationSelectsPath_iff schema left
        assignment path hschema hleftValid hcomplete
  have hrightNormalization :
      operationSelectsPath schema normalizedRight assignment path ↔
        operationSelectsPath schema right assignment path := by
    simpa [normalizedRight] using
      completeNormalizeOperation_operationSelectsPath_iff schema right
        assignment path hschema hrightValid hrightComplete
  exact hleftNormalization.symm.trans
    (hnormalizedIff.trans hrightNormalization)

end ResponseShape

end GraphQL
