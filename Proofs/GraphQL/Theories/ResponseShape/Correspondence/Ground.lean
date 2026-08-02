import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.FieldCollection
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Validity.Support.Basics
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.Readiness
import Proofs.GraphQL.Theories.ResponseShape.Compute.Ground
import Proofs.GraphQL.Theories.ResponseShape.Compute.GroundInvariant
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Equivalence
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Merge
import Proofs.GraphQL.Theories.ResponseShape.Denotation
import Proofs.GraphQL.Theories.ResponseShape.Footprint

/-!
Path correspondence for one directive-free ground selection set and its
decoded response shape.
-/

namespace GraphQL

namespace ResponseShape

/-- Exact denotation supplies the corresponding semantic-path witness. -/
theorem ResponseShape.DenotesEquivalentPath.of_denotes
    {schema : Schema} {assignment : NormalForm.BoolCase}
    {parentType : Name} {shape : ResponseShape} {path : List PathStep}
    (hdenotes : shape.DenotesPath schema assignment parentType path) :
    shape.DenotesEquivalentPath schema assignment parentType path := by
  exact ⟨path, hdenotes, pathsSemanticallyEquivalent_refl path⟩

private theorem ResponseShape.denotesPath_reparent_object_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType objectType : Name) (shape : ResponseShape)
    (hobject : schema.objectType objectType)
    (hincludes : schema.typeIncludesObjectBool parentType objectType = true)
    (hkeys : ShapeObjectTypesIn [objectType] shape)
    (path : List PathStep) :
    shape.DenotesPath schema assignment parentType path ↔
      shape.DenotesPath schema assignment objectType path := by
  have hself : schema.typeIncludesObject objectType objectType :=
    List.contains_iff_mem.mp
      (NormalForm.object_typeIncludesObjectBool_self schema hobject)
  have hparent : schema.typeIncludesObject parentType objectType :=
    List.contains_iff_mem.mp hincludes
  constructor
  · intro hdenotes
    cases hdenotes with
    | @field _ positions position possible definition runtimeObject
        _runtimePossible positionMem possibleMem runtimeMem definitionMem
        clauseHolds =>
        have hruntime : runtimeObject = objectType := by
          simpa using hkeys position positionMem possible possibleMem
            runtimeObject runtimeMem
        subst runtimeObject
        exact .field hself positionMem possibleMem runtimeMem definitionMem
          clauseHolds
    | @child _ positions position possible definition runtimeObject childShape
        childPath _runtimePossible positionMem possibleMem runtimeMem
        definitionMem clauseHolds subshapeEq childDenotes =>
        have hruntime : runtimeObject = objectType := by
          simpa using hkeys position positionMem possible possibleMem
            runtimeObject runtimeMem
        subst runtimeObject
        exact .child hself positionMem possibleMem runtimeMem definitionMem
          clauseHolds subshapeEq childDenotes
  · intro hdenotes
    cases hdenotes with
    | @field _ positions position possible definition runtimeObject
        _runtimePossible positionMem possibleMem runtimeMem definitionMem
        clauseHolds =>
        have hruntime : runtimeObject = objectType := by
          simpa using hkeys position positionMem possible possibleMem
            runtimeObject runtimeMem
        subst runtimeObject
        exact .field hparent positionMem possibleMem runtimeMem definitionMem
          clauseHolds
    | @child _ positions position possible definition runtimeObject childShape
        childPath _runtimePossible positionMem possibleMem runtimeMem
        definitionMem clauseHolds subshapeEq childDenotes =>
        have hruntime : runtimeObject = objectType := by
          simpa using hkeys position positionMem possible possibleMem
            runtimeObject runtimeMem
        subst runtimeObject
        exact .child hparent positionMem possibleMem runtimeMem definitionMem
          clauseHolds subshapeEq childDenotes

private theorem ResponseShape.denotesEquivalentPath_reparent_object_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType objectType : Name) (shape : ResponseShape)
    (hobject : schema.objectType objectType)
    (hincludes : schema.typeIncludesObjectBool parentType objectType = true)
    (hkeys : ShapeObjectTypesIn [objectType] shape)
    (path : List PathStep) :
    shape.DenotesEquivalentPath schema assignment parentType path ↔
      shape.DenotesEquivalentPath schema assignment objectType path := by
  unfold ResponseShape.DenotesEquivalentPath
  constructor
  · rintro ⟨denotedPath, hdenotes, hequivalent⟩
    exact ⟨denotedPath,
      (ResponseShape.denotesPath_reparent_object_iff schema assignment
        parentType objectType shape hobject hincludes hkeys denotedPath).mp
          hdenotes,
      hequivalent⟩
  · rintro ⟨denotedPath, hdenotes, hequivalent⟩
    exact ⟨denotedPath,
      (ResponseShape.denotesPath_reparent_object_iff schema assignment
        parentType objectType shape hobject hincludes hkeys denotedPath).mpr
          hdenotes,
      hequivalent⟩

/-- Semantic-path denotation distributes exactly across shape merge. -/
theorem mergeResponseShapes_denotesEquivalentPath_iff
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (parentType : Name) (left right : ResponseShape)
    (path : List PathStep) :
    (mergeResponseShapes left right).DenotesEquivalentPath
        schema assignment parentType path
      ↔ left.DenotesEquivalentPath schema assignment parentType path
        ∨ right.DenotesEquivalentPath schema assignment parentType path := by
  unfold ResponseShape.DenotesEquivalentPath
  constructor
  · rintro ⟨denotedPath, hdenotes, hequivalent⟩
    rw [mergeResponseShapes_denotesPath_iff] at hdenotes
    exact hdenotes.elim
      (fun hleft => Or.inl ⟨denotedPath, hleft, hequivalent⟩)
      (fun hright => Or.inr ⟨denotedPath, hright, hequivalent⟩)
  · rintro (⟨denotedPath, hdenotes, hequivalent⟩ |
      ⟨denotedPath, hdenotes, hequivalent⟩)
    · exact ⟨denotedPath,
        mergeResponseShapes_denotesPath_left schema assignment parentType
          left right denotedPath hdenotes,
        hequivalent⟩
    · exact ⟨denotedPath,
        mergeResponseShapes_denotesPath_right schema assignment parentType
          left right denotedPath hdenotes,
        hequivalent⟩

/-- The execution field-collection footprint of a selection set in one nominal
scope. The first path step supplies the concrete object used for fragment
applicability. -/
def selectionSetSelectsPath
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (selectionSet : List Selection) :
    List PathStep -> Prop
  | [] => False
  | step :: rest =>
      schema.typeIncludesObject parentType step.parentObject
      ∧ collectedFieldsSelectPath schema variableValues
          (Execution.collectFields schema variableValues step.parentObject
            (.object step.parentObject ()) selectionSet)
          (step :: rest)

@[simp] theorem selectionSetSelectsPath_nil
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (selectionSet : List Selection) :
    selectionSetSelectsPath schema variableValues parentType selectionSet []
      ↔ False := by
  rfl

theorem selectionSetSelectsPath_cons_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType : Name) (selectionSet : List Selection)
    (step : PathStep) (rest : List PathStep) :
    selectionSetSelectsPath schema variableValues parentType selectionSet
        (step :: rest)
      ↔ schema.typeIncludesObject parentType step.parentObject
        ∧ collectedFieldsSelectPath schema variableValues
          (Execution.collectFields schema variableValues step.parentObject
            (.object step.parentObject ()) selectionSet)
          (step :: rest) := by
  rfl

private theorem emptyShape_denotesEquivalentPath_iff_emptySelectionSet
    (schema : Schema) (assignment : NormalForm.BoolCase)
    (variableValues : Execution.VariableValues) (parentType : Name)
    (path : List PathStep) :
    (ResponseShape.object []).DenotesEquivalentPath
        schema assignment parentType path
      ↔ selectionSetSelectsPath schema variableValues parentType [] path := by
  constructor
  · rintro ⟨denotedPath, hdenotes, _hequivalent⟩
    cases hdenotes <;> simp_all
  · intro hselects
    cases path with
    | nil => exact False.elim hselects
    | cons step rest =>
        rw [selectionSetSelectsPath_cons_iff] at hselects
        rcases hselects with ⟨_outer, hcollected⟩
        simp [NormalForm.GroundTypeNormalization.collectFields_nil] at hcollected
        cases rest with
        | nil =>
            rw [collectedFieldsSelectPath_singleton] at hcollected
            simp at hcollected
        | cons next tail =>
            rw [collectedFieldsSelectPath_cons_cons] at hcollected
            simp at hcollected

/-- Splits a footprint across the leading executable group and the remaining
groups. -/
theorem collectedFieldsSelectPath_cons_iff
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
            simp only [List.mem_cons] at hgroup
            cases hgroup with
            | inl hhead =>
                exact Or.inl ⟨fields, by simp [hhead], hmatch⟩
            | inr htail =>
                exact Or.inr ⟨fields, htail, hmatch⟩
          · rintro (⟨fields, hgroup, hmatch⟩ | ⟨fields, hgroup, hmatch⟩)
            · exact ⟨fields, by simp at hgroup ⊢; simp [hgroup], hmatch⟩
            · exact ⟨fields, by simp [hgroup], hmatch⟩
      | cons next rest =>
          rw [collectedFieldsSelectPath_cons_cons,
            collectedFieldsSelectPath_cons_cons,
            collectedFieldsSelectPath_cons_cons]
          constructor
          · rintro ⟨fields, hgroup, hmatch, hincludes, hpath⟩
            simp only [List.mem_cons] at hgroup
            cases hgroup with
            | inl hhead =>
                exact Or.inl ⟨fields, by simp [hhead], hmatch,
                  hincludes, hpath⟩
            | inr htail =>
                exact Or.inr ⟨fields, htail, hmatch, hincludes, hpath⟩
          · rintro (⟨fields, hgroup, hmatch, hincludes, hpath⟩ |
              ⟨fields, hgroup, hmatch, hincludes, hpath⟩)
            · exact ⟨fields, by simp at hgroup ⊢; simp [hgroup],
                hmatch, hincludes, hpath⟩
            · exact ⟨fields, by simp [hgroup], hmatch, hincludes, hpath⟩

private theorem objectFieldCons_selectsPath_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet rest : List Selection)
    (hobject : schema.objectType parentType)
    (hresponseName :
      responseName ∉ rest.filterMap Selection.responseName?)
    (hnormal : NormalForm.selectionSetNormal schema parentType
      (.field responseName fieldName arguments [] selectionSet :: rest))
    (hfree : NormalForm.selectionSetDirectiveFree
      (.field responseName fieldName arguments [] selectionSet :: rest))
    (path : List PathStep) :
    selectionSetSelectsPath schema variableValues parentType
        (.field responseName fieldName arguments [] selectionSet :: rest) path
      ↔ selectionSetSelectsPath schema variableValues parentType
          [.field responseName fieldName arguments [] selectionSet] path
        ∨ selectionSetSelectsPath schema variableValues parentType rest path := by
  cases path with
  | nil => simp
  | cons step pathRest =>
      have hparentEq (hinclude :
          schema.typeIncludesObject parentType step.parentObject) :
          step.parentObject = parentType :=
        object_typeIncludesObjectBool_eq_self schema hobject
          (List.contains_iff_mem.mpr hinclude)
      constructor
      · intro hselects
        rw [selectionSetSelectsPath_cons_iff] at hselects
        rcases hselects with ⟨hinclude, hcollected⟩
        have heq := hparentEq hinclude
        have hrestNormal :=
          NormalForm.GroundTypeNormalization.selectionSetNormal_tail hnormal
        have hrestFree :=
          NormalForm.selectionSetDirectiveFree_tail hfree
        have hobjectBool :
            NormalForm.objectTypeNameBool schema parentType = true :=
          NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
            schema hobject
        have hkeys :=
          NormalForm.GroundTypeNormalization.ExecutionKeys.collectFields_normal_object_keys_eq_responseNames
              schema variableValues parentType (.object parentType ()) rest
              hrestFree hrestNormal hobjectBool
        have hnotin :
            responseName ∉
              (Execution.collectFields schema variableValues parentType
                (.object parentType ()) rest).map Prod.fst := by
          rw [hkeys]
          exact hresponseName
        have hcollect :=
          NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
              schema variableValues parentType (.object parentType ())
              responseName fieldName arguments selectionSet rest hnotin
        have hcollectHead :=
          NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
              schema variableValues parentType (.object parentType ())
              responseName fieldName arguments selectionSet [] (by
                rw [NormalForm.GroundTypeNormalization.collectFields_nil]
                simp)
        rw [heq] at hcollected
        rw [hcollect, collectedFieldsSelectPath_cons_iff] at hcollected
        cases hcollected with
        | inl hhead =>
            left
            rw [selectionSetSelectsPath_cons_iff]
            refine ⟨by simpa [heq] using hinclude, ?_⟩
            rw [heq, hcollectHead]
            exact hhead
        | inr htail =>
            right
            rw [selectionSetSelectsPath_cons_iff]
            refine ⟨hinclude, ?_⟩
            simpa [heq] using htail
      · intro hselects
        rcases hselects with hhead | htail
        · rw [selectionSetSelectsPath_cons_iff] at hhead
          rcases hhead with ⟨hinclude, hcollected⟩
          have heq := hparentEq hinclude
          have hrestNormal :=
            NormalForm.GroundTypeNormalization.selectionSetNormal_tail hnormal
          have hrestFree :=
            NormalForm.selectionSetDirectiveFree_tail hfree
          have hobjectBool :
              NormalForm.objectTypeNameBool schema parentType = true :=
            NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
              schema hobject
          have hkeys :=
            NormalForm.GroundTypeNormalization.ExecutionKeys.collectFields_normal_object_keys_eq_responseNames
                schema variableValues parentType (.object parentType ()) rest
                hrestFree hrestNormal hobjectBool
          have hnotin :
              responseName ∉
                (Execution.collectFields schema variableValues parentType
                  (.object parentType ()) rest).map Prod.fst := by
            rw [hkeys]
            exact hresponseName
          have hcollect :=
            NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
                schema variableValues parentType (.object parentType ())
                responseName fieldName arguments selectionSet rest hnotin
          have hcollectHead :=
            NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
                schema variableValues parentType (.object parentType ())
                responseName fieldName arguments selectionSet [] (by
                  rw [NormalForm.GroundTypeNormalization.collectFields_nil]
                  simp)
          rw [heq, hcollectHead] at hcollected
          rw [selectionSetSelectsPath_cons_iff, heq, hcollect,
            collectedFieldsSelectPath_cons_iff]
          exact ⟨by simpa [heq] using hinclude,
            Or.inl hcollected⟩
        · rw [selectionSetSelectsPath_cons_iff] at htail
          rcases htail with ⟨hinclude, hcollected⟩
          have heq := hparentEq hinclude
          have hrestNormal :=
            NormalForm.GroundTypeNormalization.selectionSetNormal_tail hnormal
          have hrestFree :=
            NormalForm.selectionSetDirectiveFree_tail hfree
          have hobjectBool :
              NormalForm.objectTypeNameBool schema parentType = true :=
            NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
              schema hobject
          have hkeys :=
            NormalForm.GroundTypeNormalization.ExecutionKeys.collectFields_normal_object_keys_eq_responseNames
                schema variableValues parentType (.object parentType ()) rest
                hrestFree hrestNormal hobjectBool
          have hnotin :
              responseName ∉
                (Execution.collectFields schema variableValues parentType
                  (.object parentType ()) rest).map Prod.fst := by
            rw [hkeys]
            exact hresponseName
          have hcollect :=
            NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
                schema variableValues parentType (.object parentType ())
                responseName fieldName arguments selectionSet rest hnotin
          rw [heq] at hcollected
          rw [selectionSetSelectsPath_cons_iff, heq, hcollect,
            collectedFieldsSelectPath_cons_iff]
          exact ⟨by simpa [heq] using hinclude, Or.inr hcollected⟩

private theorem abstractType_objectTypeNameBool_false
    (schema : Schema) {parentType : Name}
    (habstract : AbstractType schema parentType) :
    NormalForm.objectTypeNameBool schema parentType = false := by
  rcases habstract with ⟨interfaceType, hlookup⟩ |
    ⟨unionType, hlookup⟩
  · simp [NormalForm.objectTypeNameBool, hlookup]
  · simp [NormalForm.objectTypeNameBool, hlookup]

private theorem abstractFragmentCons_selectsPath_iff
    (schema : Schema) (variableValues : Execution.VariableValues)
    (parentType objectType : Name) (selection rest : List Selection)
    (habstract : AbstractType schema parentType)
    (hobject : schema.objectType objectType)
    (hincludes : schema.typeIncludesObjectBool parentType objectType = true)
    (htypeCondition : objectType ∉
      rest.filterMap NormalForm.inlineFragmentTypeCondition?)
    (hnormal : NormalForm.selectionSetNormal schema parentType
      (.inlineFragment (some objectType) [] selection :: rest))
    (hfree : NormalForm.selectionSetDirectiveFree
      (.inlineFragment (some objectType) [] selection :: rest))
    (path : List PathStep) :
    selectionSetSelectsPath schema variableValues parentType
        (.inlineFragment (some objectType) [] selection :: rest) path
      ↔ selectionSetSelectsPath schema variableValues objectType selection path
        ∨ selectionSetSelectsPath schema variableValues parentType rest path := by
  cases path with
  | nil => simp
  | cons step pathRest =>
      have habstractBool :=
        abstractType_objectTypeNameBool_false schema habstract
      have hobjectBool :
          NormalForm.objectTypeNameBool schema objectType = true :=
        NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
          schema hobject
      have hrestNormal :=
        NormalForm.GroundTypeNormalization.selectionSetNormal_tail hnormal
      have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
      by_cases heq : step.parentObject = objectType
      · have hrestEmpty :
            Execution.collectFields schema variableValues objectType
                (.object objectType ()) rest = [] :=
          NormalForm.GroundTypeNormalization.collectFields_inlineFragments_without_typeCondition_eq_nil_at_runtime_parent
              schema variableValues (normalParentType := parentType)
              (executionParentType := objectType) (runtimeType := objectType) ()
              habstractBool hrestFree hrestNormal htypeCondition
        have hcollect :
            Execution.collectFields schema variableValues step.parentObject
                (.object step.parentObject ())
                (.inlineFragment (some objectType) [] selection :: rest)
              = Execution.collectFields schema variableValues objectType
                  (.object objectType ()) selection := by
          rw [heq,
            NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_apply]
          · rw [hrestEmpty]
            simp [Execution.mergeExecutableGroups]
          · simp [Execution.doesFragmentTypeApplyBool,
              Execution.runtimeObjectType?,
              NormalForm.object_typeIncludesObjectBool_self schema hobject]
        constructor
        · intro hselects
          rw [selectionSetSelectsPath_cons_iff, hcollect] at hselects
          rcases hselects with ⟨_outer, hcollected⟩
          left
          rw [selectionSetSelectsPath_cons_iff]
          rw [heq]
          exact ⟨List.contains_iff_mem.mp
              (NormalForm.object_typeIncludesObjectBool_self schema hobject),
            hcollected⟩
        · intro hselects
          rcases hselects with hselection | hrest
          · rw [selectionSetSelectsPath_cons_iff] at hselection
            rcases hselection with ⟨_outer, hcollected⟩
            rw [heq] at hcollected
            rw [selectionSetSelectsPath_cons_iff, hcollect]
            exact ⟨by simpa [heq, Schema.typeIncludesObject] using
                List.contains_iff_mem.mp hincludes,
              hcollected⟩
          · rw [selectionSetSelectsPath_cons_iff] at hrest
            rcases hrest with ⟨_outer, hcollected⟩
            rw [heq, hrestEmpty] at hcollected
            cases pathRest with
            | nil =>
                rw [collectedFieldsSelectPath_singleton] at hcollected
                simp at hcollected
            | cons next tail =>
                rw [collectedFieldsSelectPath_cons_cons] at hcollected
                simp at hcollected
      · have hskip :
            Execution.doesFragmentTypeApplyBool schema step.parentObject
              (.object step.parentObject ()) objectType = false :=
          NormalForm.GroundTypeNormalization.doesFragmentTypeApplyBool_object_condition_other_false
              schema () hobjectBool (by exact Ne.symm heq)
        have hcollect :
            Execution.collectFields schema variableValues step.parentObject
                (.object step.parentObject ())
                (.inlineFragment (some objectType) [] selection :: rest)
              = Execution.collectFields schema variableValues step.parentObject
                  (.object step.parentObject ()) rest :=
          NormalForm.GroundTypeNormalization.collectFields_inlineFragment_some_directiveFree_skip_eq
              schema variableValues step.parentObject objectType
              (.object step.parentObject ()) selection rest hskip
        constructor
        · intro hselects
          rw [selectionSetSelectsPath_cons_iff, hcollect] at hselects
          exact Or.inr hselects
        · intro hselects
          rcases hselects with hselection | hrest
          · rw [selectionSetSelectsPath_cons_iff] at hselection
            rcases hselection with ⟨hinclude, _hcollected⟩
            have hsame := object_typeIncludesObjectBool_eq_self schema hobject
              (List.contains_iff_mem.mpr hinclude)
            exact False.elim (heq hsame)
          · rw [selectionSetSelectsPath_cons_iff, hcollect]
            exact hrest

private theorem executableFieldMatchesPathStep_refl
    (schema : Schema) (parentType responseName fieldName : Name)
    (arguments : List Argument) (selectionSet : List Selection)
    (fieldDefinition : FieldDefinition)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition) :
    executableFieldMatchesPathStep schema
        {
          parentType := parentType
          responseName := responseName
          fieldName := fieldName
          arguments := arguments
          selectionSet := selectionSet
        }
        {
          parentObject := parentType
          responseName := responseName
          field := {
            fieldName := fieldName
            arguments := arguments
            outputType := fieldDefinition.outputType
          }
        } := by
  refine ⟨rfl, rfl,
    NormalForm.GroundTypeNormalization.argumentsEquivalent_refl arguments,
    fieldDefinition, hlookup, rfl⟩

private theorem singletonLeaf_denotesEquivalentPath_iff
    (schema : Schema) (clause : Clause)
    (assignment : NormalForm.BoolCase)
    (variableValues : Execution.VariableValues)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (fieldDefinition : FieldDefinition)
    (hobject : schema.objectType parentType)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hholds : clause.HoldsIn assignment)
    (path : List PathStep) :
    (singletonDefinitionShape parentType responseName
        (.mk clause
          { fieldName := fieldName
            arguments := arguments
            outputType := fieldDefinition.outputType }
          none)).DenotesEquivalentPath schema assignment parentType path
      ↔ selectionSetSelectsPath schema variableValues parentType
          [.field responseName fieldName arguments [] []] path := by
  cases path with
  | nil =>
      constructor
      · rintro ⟨denotedPath, hdenotes, hequivalent⟩
        cases denotedPath with
        | nil => exact hdenotes.nonempty rfl
        | cons step rest =>
            simp [PathsSemanticallyEquivalent] at hequivalent
      · intro hselects
        exact False.elim hselects
  | cons step rest =>
      cases rest with
      | nil =>
          have hcollect :
              Execution.collectFields schema variableValues step.parentObject
                  (.object step.parentObject ())
                  [.field responseName fieldName arguments [] []]
                = [(responseName, [{
                    parentType := step.parentObject
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := []
                  }])] :=
            NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
                schema variableValues step.parentObject (.object step.parentObject ())
                responseName fieldName arguments [] [] (by
                  rw [NormalForm.GroundTypeNormalization.collectFields_nil]
                  simp)
          constructor
          · rintro ⟨denotedPath, hdenotes, hequivalent⟩
            rw [singletonDefinitionShape_denotesPath_iff] at hdenotes
            rcases hdenotes with
              ⟨hruntime, _hactive, hfield | hchild⟩
            · subst denotedPath
              simp only [PathsSemanticallyEquivalent,
                PathStep.SemanticallyEquivalent] at hequivalent
              rcases hequivalent with
                ⟨⟨hparent, hresponse, hfieldName, harguments, houtput⟩,
                  _hempty⟩
              rw [selectionSetSelectsPath_cons_iff,
                hcollect,
                collectedFieldsSelectPath_singleton]
              refine ⟨?_, ?_⟩
              · simpa [hparent] using hruntime
              · refine ⟨[{
                    parentType := step.parentObject
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := []
                  }], ?_, ?_⟩
                · simp [hresponse]
                · refine ⟨{
                    parentType := step.parentObject
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := []
                  }, by simp, ?_⟩
                  unfold executableFieldMatchesPathStep
                  refine ⟨hresponse, hfieldName, harguments, ?_⟩
                  refine ⟨fieldDefinition, ?_, houtput⟩
                  rw [← hparent, ← hfieldName]
                  exact hlookup
            · rcases hchild with
                ⟨childShape, childPath, hnone, _hchildDenotes, _hpath⟩
              unfold ShapeDefinition.subshape at hnone
              contradiction
          · intro hselects
            rw [selectionSetSelectsPath_cons_iff,
              hcollect,
              collectedFieldsSelectPath_singleton] at hselects
            rcases hselects with
              ⟨hruntime, fields, hgroup, field, hfieldMem, hmatch⟩
            simp only [List.mem_singleton] at hgroup
            have hfields := congrArg Prod.snd hgroup
            change fields = [{
              parentType := step.parentObject
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := []
            }] at hfields
            subst fields
            simp at hfieldMem
            subst field
            rcases hmatch with
              ⟨hresponse, hfieldName, harguments,
                candidate, hcandidate, houtput⟩
            have hparent : step.parentObject = parentType :=
              object_typeIncludesObjectBool_eq_self schema hobject
                (List.contains_iff_mem.mpr hruntime)
            have hcandidateEq : candidate = fieldDefinition := by
              rw [hparent, ← hfieldName, hlookup] at hcandidate
              exact Option.some.inj hcandidate.symm
            subst candidate
            let denotedStep : PathStep := {
              parentObject := parentType
              responseName := responseName
              field := {
                fieldName := fieldName
                arguments := arguments
                outputType := fieldDefinition.outputType
              }
            }
            refine ⟨[denotedStep], ?_, ?_⟩
            · exact singletonDefinitionShape_denotesPath_field
                schema assignment parentType parentType responseName
                (.mk clause
                  { fieldName := fieldName
                    arguments := arguments
                    outputType := fieldDefinition.outputType }
                  none)
                (List.contains_iff_mem.mp
                  (NormalForm.object_typeIncludesObjectBool_self schema hobject))
                hholds
            · simp only [PathsSemanticallyEquivalent]
              refine ⟨?_, trivial⟩
              unfold PathStep.SemanticallyEquivalent denotedStep
              exact ⟨hparent.symm, hresponse, hfieldName, harguments,
                houtput⟩
      | cons next tail =>
          have hcollect :
              Execution.collectFields schema variableValues step.parentObject
                  (.object step.parentObject ())
                  [.field responseName fieldName arguments [] []]
                = [(responseName, [{
                    parentType := step.parentObject
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := []
                  }])] :=
            NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
                schema variableValues step.parentObject (.object step.parentObject ())
                responseName fieldName arguments [] [] (by
                  rw [NormalForm.GroundTypeNormalization.collectFields_nil]
                  simp)
          constructor
          · rintro ⟨denotedPath, hdenotes, hequivalent⟩
            rw [singletonDefinitionShape_denotesPath_iff] at hdenotes
            rcases hdenotes with ⟨_runtime, _active, hfield | hchild⟩
            · subst denotedPath
              simp [PathsSemanticallyEquivalent] at hequivalent
            · rcases hchild with
                ⟨_childShape, _childPath, hnone, _childDenotes, _hpath⟩
              unfold ShapeDefinition.subshape at hnone
              contradiction
          · intro hselects
            rw [selectionSetSelectsPath_cons_iff,
              hcollect,
              collectedFieldsSelectPath_cons_cons] at hselects
            rcases hselects with
              ⟨_runtime, fields, hgroup, _hmatch, _hincludes, hchild⟩
            simp only [List.mem_singleton] at hgroup
            have hfields := congrArg Prod.snd hgroup
            change fields = [{
              parentType := step.parentObject
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := []
            }] at hfields
            subst fields
            simp [Execution.collectSubfields, Execution.mergeExecutableGroups,
              Execution.collectFields] at hchild
            cases tail with
            | nil =>
                rw [collectedFieldsSelectPath_singleton] at hchild
                simp at hchild
            | cons third tail =>
                rw [collectedFieldsSelectPath_cons_cons] at hchild
                simp at hchild

private theorem singletonComposite_denotesEquivalentPath_iff
    (schema : Schema) (clause : Clause)
    (assignment : NormalForm.BoolCase)
    (variableValues : Execution.VariableValues)
    (parentType responseName fieldName : Name)
    (arguments : List Argument) (fieldDefinition : FieldDefinition)
    (selectionSet : List Selection) (childShape : ResponseShape)
    (hobject : schema.objectType parentType)
    (hlookup : schema.lookupField parentType fieldName = some fieldDefinition)
    (hholds : clause.HoldsIn assignment)
    (hchild : ∀ childPath,
      childShape.DenotesEquivalentPath schema assignment
          fieldDefinition.outputType.namedType childPath
        ↔ selectionSetSelectsPath schema variableValues
            fieldDefinition.outputType.namedType selectionSet childPath)
    (path : List PathStep) :
    (singletonDefinitionShape parentType responseName
        (.mk clause
          { fieldName := fieldName
            arguments := arguments
            outputType := fieldDefinition.outputType }
          (some childShape))).DenotesEquivalentPath
            schema assignment parentType path
      ↔ selectionSetSelectsPath schema variableValues parentType
          [.field responseName fieldName arguments [] selectionSet] path := by
  cases path with
  | nil =>
      constructor
      · rintro ⟨denotedPath, hdenotes, hequivalent⟩
        cases denotedPath with
        | nil => exact hdenotes.nonempty rfl
        | cons step rest =>
            simp [PathsSemanticallyEquivalent] at hequivalent
      · intro hselects
        exact False.elim hselects
  | cons step rest =>
      have hcollect :
          Execution.collectFields schema variableValues step.parentObject
              (.object step.parentObject ())
              [.field responseName fieldName arguments [] selectionSet]
            = [(responseName, [{
                parentType := step.parentObject
                responseName := responseName
                fieldName := fieldName
                arguments := arguments
                selectionSet := selectionSet
              }])] :=
        NormalForm.GroundTypeNormalization.collectFields_field_noDirectives_cons_of_responseName_not_mem
          schema variableValues step.parentObject (.object step.parentObject ())
          responseName fieldName arguments selectionSet [] (by
            rw [NormalForm.GroundTypeNormalization.collectFields_nil]
            simp)
      cases rest with
      | nil =>
          constructor
          · rintro ⟨denotedPath, hdenotes, hequivalent⟩
            rw [singletonDefinitionShape_denotesPath_iff] at hdenotes
            rcases hdenotes with
              ⟨hruntime, _hactive, hfield | hchildPath⟩
            · subst denotedPath
              simp only [PathsSemanticallyEquivalent,
                PathStep.SemanticallyEquivalent] at hequivalent
              rcases hequivalent with
                ⟨⟨hparent, hresponse, hfieldName, harguments, houtput⟩,
                  _hempty⟩
              rw [selectionSetSelectsPath_cons_iff, hcollect,
                collectedFieldsSelectPath_singleton]
              refine ⟨by simpa [hparent] using hruntime, ?_⟩
              refine ⟨[{
                  parentType := step.parentObject
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }], by simp [hresponse], ?_⟩
              refine ⟨{
                  parentType := step.parentObject
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }, by simp, ?_⟩
              unfold executableFieldMatchesPathStep
              refine ⟨hresponse, hfieldName, harguments,
                fieldDefinition, ?_, houtput⟩
              rw [← hparent, ← hfieldName]
              exact hlookup
            · rcases hchildPath with
                ⟨storedChild, childPath, hsome, childDenotes, hpath⟩
              injection hsome with hstored
              subst storedChild
              subst denotedPath
              cases childPath with
              | nil => exact False.elim (childDenotes.nonempty rfl)
              | cons childStep childRest =>
                  simp [PathsSemanticallyEquivalent] at hequivalent
          · intro hselects
            rw [selectionSetSelectsPath_cons_iff, hcollect,
              collectedFieldsSelectPath_singleton] at hselects
            rcases hselects with
              ⟨hruntime, fields, hgroup, field, hfieldMem, hmatch⟩
            simp only [List.mem_singleton] at hgroup
            have hfields := congrArg Prod.snd hgroup
            change fields = [{
              parentType := step.parentObject
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := selectionSet
            }] at hfields
            subst fields
            simp at hfieldMem
            subst field
            rcases hmatch with
              ⟨hresponse, hfieldName, harguments,
                candidate, hcandidate, houtput⟩
            have hparent : step.parentObject = parentType :=
              object_typeIncludesObjectBool_eq_self schema hobject
                (List.contains_iff_mem.mpr hruntime)
            have hcandidateEq : candidate = fieldDefinition := by
              rw [hparent, ← hfieldName, hlookup] at hcandidate
              exact Option.some.inj hcandidate.symm
            subst candidate
            let denotedStep : PathStep := {
              parentObject := parentType
              responseName := responseName
              field := {
                fieldName := fieldName
                arguments := arguments
                outputType := fieldDefinition.outputType
              }
            }
            refine ⟨[denotedStep], ?_, ?_⟩
            · exact singletonDefinitionShape_denotesPath_field
                schema assignment parentType parentType responseName
                (.mk clause
                  { fieldName := fieldName
                    arguments := arguments
                    outputType := fieldDefinition.outputType }
                  (some childShape))
                (List.contains_iff_mem.mp
                  (NormalForm.object_typeIncludesObjectBool_self schema hobject))
                hholds
            · simp only [PathsSemanticallyEquivalent]
              refine ⟨?_, trivial⟩
              unfold PathStep.SemanticallyEquivalent denotedStep
              exact ⟨hparent.symm, hresponse, hfieldName, harguments,
                houtput⟩
      | cons next tail =>
          constructor
          · rintro ⟨denotedPath, hdenotes, hequivalent⟩
            rw [singletonDefinitionShape_denotesPath_iff] at hdenotes
            rcases hdenotes with
              ⟨hruntime, _hactive, hfield | hchildPath⟩
            · subst denotedPath
              simp [PathsSemanticallyEquivalent] at hequivalent
            · rcases hchildPath with
                ⟨storedChild, childPath, hsome, childDenotes, hpath⟩
              injection hsome with hstored
              subst storedChild
              subst denotedPath
              simp only [PathsSemanticallyEquivalent,
                PathStep.SemanticallyEquivalent] at hequivalent
              rcases hequivalent with
                ⟨⟨hparent, hresponse, hfieldName, harguments, houtput⟩,
                  hchildEquivalent⟩
              have hchildEnvelope :
                  childShape.DenotesEquivalentPath schema assignment
                    fieldDefinition.outputType.namedType (next :: tail) :=
                ⟨childPath, childDenotes, hchildEquivalent⟩
              have hchildSelects := (hchild (next :: tail)).mp hchildEnvelope
              rw [selectionSetSelectsPath_cons_iff] at hchildSelects
              rcases hchildSelects with
                ⟨hchildIncludes, hchildCollected⟩
              rw [selectionSetSelectsPath_cons_iff, hcollect,
                collectedFieldsSelectPath_cons_cons]
              refine ⟨by simpa [hparent] using hruntime, ?_⟩
              refine ⟨[{
                  parentType := step.parentObject
                  responseName := responseName
                  fieldName := fieldName
                  arguments := arguments
                  selectionSet := selectionSet
                }], by simp [hresponse], ?_, ?_, ?_⟩
              · refine ⟨{
                    parentType := step.parentObject
                    responseName := responseName
                    fieldName := fieldName
                    arguments := arguments
                    selectionSet := selectionSet
                  }, by simp, ?_⟩
                unfold executableFieldMatchesPathStep
                refine ⟨hresponse, hfieldName, harguments,
                  fieldDefinition, ?_, houtput⟩
                rw [← hparent, ← hfieldName]
                exact hlookup
              · change fieldDefinition.outputType = step.field.outputType at houtput
                rw [← houtput]
                exact hchildIncludes
              · simpa [Execution.collectSubfields,
                  Execution.mergeExecutableGroups] using hchildCollected
          · intro hselects
            rw [selectionSetSelectsPath_cons_iff, hcollect,
              collectedFieldsSelectPath_cons_cons] at hselects
            rcases hselects with
              ⟨hruntime, fields, hgroup, hmatch, hnextIncludes,
                hchildCollected⟩
            simp only [List.mem_singleton] at hgroup
            have hfields := congrArg Prod.snd hgroup
            change fields = [{
              parentType := step.parentObject
              responseName := responseName
              fieldName := fieldName
              arguments := arguments
              selectionSet := selectionSet
            }] at hfields
            subst fields
            rcases hmatch with ⟨field, hfieldMem, hmatch⟩
            simp at hfieldMem
            subst field
            rcases hmatch with
              ⟨hresponse, hfieldName, harguments,
                candidate, hcandidate, houtput⟩
            have hparent : step.parentObject = parentType :=
              object_typeIncludesObjectBool_eq_self schema hobject
                (List.contains_iff_mem.mpr hruntime)
            have hcandidateEq : candidate = fieldDefinition := by
              rw [hparent, ← hfieldName, hlookup] at hcandidate
              exact Option.some.inj hcandidate.symm
            subst candidate
            have hchildCollected' :
                collectedFieldsSelectPath schema variableValues
                  (Execution.collectFields schema variableValues
                    next.parentObject (.object next.parentObject ()) selectionSet)
                  (next :: tail) := by
              simpa [Execution.collectSubfields,
                Execution.mergeExecutableGroups] using hchildCollected
            have hchildSelects :
                selectionSetSelectsPath schema variableValues
                  fieldDefinition.outputType.namedType selectionSet
                  (next :: tail) := by
              rw [selectionSetSelectsPath_cons_iff]
              exact ⟨by simpa [houtput] using hnextIncludes,
                hchildCollected'⟩
            rcases (hchild (next :: tail)).mpr hchildSelects with
              ⟨denotedChildPath, hchildDenotes, hchildEquivalent⟩
            let denotedStep : PathStep := {
              parentObject := parentType
              responseName := responseName
              field := {
                fieldName := fieldName
                arguments := arguments
                outputType := fieldDefinition.outputType
              }
            }
            refine ⟨denotedStep :: denotedChildPath, ?_, ?_⟩
            · exact singletonDefinitionShape_denotesPath_child
                schema assignment parentType parentType responseName
                (.mk clause
                  { fieldName := fieldName
                    arguments := arguments
                    outputType := fieldDefinition.outputType }
                  (some childShape))
                childShape denotedChildPath
                (List.contains_iff_mem.mp
                  (NormalForm.object_typeIncludesObjectBool_self schema hobject))
                hholds rfl hchildDenotes
            · simp only [PathsSemanticallyEquivalent]
              refine ⟨?_, hchildEquivalent⟩
              unfold PathStep.SemanticallyEquivalent denotedStep
              exact ⟨hparent.symm, hresponse, hfieldName, harguments,
                houtput⟩

mutual
  /-- The ground decoder and execution field collection represent the same
  semantic paths on normalizer output. -/
  theorem foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
      (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
      (hvalid : clause.Valid support)
      (hcomplete : clause.CompleteMinterm support)
      (assignment : NormalForm.BoolCase)
      (variableValues : Execution.VariableValues) :
      ∀ {parentType selectionSet shape},
        GroundSelectionSetImage schema parentType selectionSet ->
        NormalForm.selectionSetNormal schema parentType selectionSet ->
        NormalForm.selectionSetDirectiveFree selectionSet ->
        foldGroundSelectionSet schema clause parentType selectionSet = .ok shape ->
        clause.HoldsIn assignment ->
        ∀ path,
          shape.DenotesEquivalentPath schema assignment parentType path
            ↔ selectionSetSelectsPath schema variableValues parentType
                selectionSet path
    | _parentType, [], shape, .objectNil hobject,
        _hnormal, _hfree, hfold, _hholds, path => by
        rcases hobject with ⟨objectType, hlookup⟩
        have hshape : shape = .object [] := by
          unfold foldGroundSelectionSet at hfold
          simp [NormalForm.objectTypeNameBool, hlookup] at hfold
          exact hfold.symm
        subst shape
        exact emptyShape_denotesEquivalentPath_iff_emptySelectionSet
          schema assignment variableValues _ path
    | parentType,
        .field responseName fieldName arguments [] selectionSet :: rest,
        shape,
        @GroundSelectionSetImage.objectField _ _ _ _ _ fieldDefinition _ _
          hobject hlookup hresponseName hchild hrest,
        hnormal, hfree, hfold, hholds, path => by
        have hchildNormal :
            NormalForm.selectionSetNormal schema
              fieldDefinition.outputType.namedType selectionSet :=
          NormalForm.GroundTypeNormalization.selectionSetNormal_field_child_of_mem_lookup
            hnormal
            (show Selection.field responseName fieldName arguments [] selectionSet
                ∈ Selection.field responseName fieldName arguments [] selectionSet
                  :: rest by simp)
            hlookup
        have hchildFree :
            NormalForm.selectionSetDirectiveFree selectionSet :=
          NormalForm.GroundTypeNormalization.selectionSetDirectiveFree_field_child_of_mem
            hfree
            (show Selection.field responseName fieldName arguments [] selectionSet
                ∈ Selection.field responseName fieldName arguments [] selectionSet
                  :: rest by simp)
        have hrestNormal :=
          NormalForm.GroundTypeNormalization.selectionSetNormal_tail hnormal
        have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
        rcases foldGroundFieldChild_success schema clause fieldName hchild with
          ⟨subshape, hsubshape⟩
        rcases foldGroundSelectionSet_success_of_image schema clause hrest with
          ⟨restShape, hrestShape⟩
        have hobjectBool :
            NormalForm.objectTypeNameBool schema parentType = true :=
          NormalForm.GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType_forNormality
            schema hobject
        unfold foldGroundSelectionSet at hfold
        simp only [hobjectBool, if_true, List.isEmpty_nil, Bool.not_true,
          Bool.false_eq_true, if_false] at hfold
        split at hfold
        · simp at hfold
        · simp [Bind.bind, Except.bind, hlookup, hrestShape] at hfold
          have hshape :
              shape = mergeResponseShapes
                (singletonDefinitionShape parentType responseName
                  (.mk clause
                    { fieldName := fieldName
                      arguments := arguments
                      outputType := fieldDefinition.outputType }
                    subshape))
                restShape := by
            cases hcomposite :
                fieldDefinition.outputType.isCompositeBool schema with
            | false =>
                cases hleaf : NormalForm.leafTypeNameBool schema
                    fieldDefinition.outputType.namedType with
                | false => simp [hcomposite, hleaf] at hsubshape
                | true =>
                    cases selectionSet with
                    | nil =>
                        simp [hcomposite, hleaf] at hsubshape hfold
                        subst subshape
                        exact hfold.symm
                    | cons childHead childRest =>
                        simp [hcomposite, hleaf] at hsubshape
            | true =>
                cases hchildFold : foldGroundSelectionSet schema clause
                    fieldDefinition.outputType.namedType selectionSet with
                | error error =>
                    simp [hcomposite, hchildFold] at hsubshape
                | ok childShape =>
                    simp [hcomposite, hchildFold] at hsubshape hfold
                    subst subshape
                    exact hfold.symm
          subst shape
          rw [mergeResponseShapes_denotesEquivalentPath_iff,
            objectFieldCons_selectsPath_iff schema variableValues parentType
              responseName fieldName arguments selectionSet rest hobject
              hresponseName hnormal hfree path]
          cases subshape with
          | none =>
              have hchildEmpty :=
                foldGroundFieldChild_correspondence schema support clause
                  hvalid hcomplete assignment variableValues fieldName hchild
                  hsubshape hchildNormal hchildFree hholds
              subst selectionSet
              rw [singletonLeaf_denotesEquivalentPath_iff schema clause
                assignment variableValues parentType responseName fieldName
                arguments fieldDefinition hobject hlookup hholds path]
              exact or_congr Iff.rfl
                (foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
                  schema support clause hvalid hcomplete assignment
                  variableValues hrest hrestNormal hrestFree hrestShape
                  hholds path)
          | some childShape =>
              have hchildCorrespondence :=
                foldGroundFieldChild_correspondence schema support clause
                  hvalid hcomplete assignment variableValues fieldName hchild
                  hsubshape hchildNormal hchildFree hholds
              rw [singletonComposite_denotesEquivalentPath_iff schema clause
                assignment variableValues parentType responseName fieldName
                arguments fieldDefinition selectionSet childShape hobject
                hlookup hholds hchildCorrespondence path]
              exact or_congr Iff.rfl
                (foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
                  schema support clause hvalid hcomplete assignment
                  variableValues hrest hrestNormal hrestFree hrestShape
                  hholds path)
    | _parentType, [], shape, .abstractNil habstract,
        _hnormal, _hfree, hfold, _hholds, path => by
        rcases habstract with ⟨interfaceType, hlookup⟩ |
          ⟨unionType, hlookup⟩
        · have hshape : shape = .object [] := by
            unfold foldGroundSelectionSet at hfold
            simp [NormalForm.objectTypeNameBool, abstractTypeNameBool,
              hlookup] at hfold
            exact hfold.symm
          subst shape
          exact emptyShape_denotesEquivalentPath_iff_emptySelectionSet
            schema assignment variableValues _ path
        · have hshape : shape = .object [] := by
            unfold foldGroundSelectionSet at hfold
            simp [NormalForm.objectTypeNameBool, abstractTypeNameBool,
              hlookup] at hfold
            exact hfold.symm
          subst shape
          exact emptyShape_denotesEquivalentPath_iff_emptySelectionSet
            schema assignment variableValues _ path
    | parentType,
        .inlineFragment (some objectType) [] selection :: rest,
        shape,
        .abstractFragment habstract hobject hincludes hnonempty
          htypeCondition hselection hrest,
        hnormal, hfree, hfold, hholds, path => by
        have hselectionNormal :
            NormalForm.selectionSetNormal schema objectType selection :=
          (NormalForm.GroundTypeNormalization.selectionSetNormal_inlineFragment_child_of_mem
            hnormal
            (show Selection.inlineFragment (some objectType) [] selection
                ∈ Selection.inlineFragment (some objectType) [] selection :: rest
              by simp)).2
        have hselectionFree :
            NormalForm.selectionSetDirectiveFree selection :=
          NormalForm.GroundTypeNormalization.selectionSetDirectiveFree_inlineFragment_child_of_mem
            hfree
            (show Selection.inlineFragment (some objectType) [] selection
                ∈ Selection.inlineFragment (some objectType) [] selection :: rest
              by simp)
        have hrestNormal :=
          NormalForm.GroundTypeNormalization.selectionSetNormal_tail hnormal
        have hrestFree := NormalForm.selectionSetDirectiveFree_tail hfree
        rcases foldGroundSelectionSet_success_of_image schema clause hselection with
          ⟨selectionShape, hselectionShape⟩
        rcases foldGroundSelectionSet_success_of_image schema clause hrest with
          ⟨restShape, hrestShape⟩
        rcases hobject with ⟨objectDefinition, hobjectLookup⟩
        have hlookupObject :
            schema.lookupObject objectType = some objectDefinition := by
          simp [Schema.lookupObject, hobjectLookup]
        unfold foldGroundSelectionSet at hfold
        have habstractBool : abstractTypeNameBool schema parentType = true := by
          rcases habstract with ⟨interfaceType, hparentLookup⟩ |
            ⟨unionType, hparentLookup⟩
          · simp [abstractTypeNameBool, hparentLookup]
          · simp [abstractTypeNameBool, hparentLookup]
        have hnonObject :
            NormalForm.objectTypeNameBool schema parentType = false :=
          abstractType_objectTypeNameBool_false schema habstract
        have hselectionEmpty : selection.isEmpty = false := by
          cases selection with
          | nil => exact False.elim (hnonempty rfl)
          | cons head tail => rfl
        simp only [hnonObject, Bool.false_eq_true, if_false,
          habstractBool, if_true, List.isEmpty_nil, Bool.not_true,
          hselectionEmpty] at hfold
        simp only [Bind.bind, Except.bind] at hfold
        split at hfold
        · simp at hfold
        · simp [hlookupObject, hincludes, hselectionShape, hrestShape] at hfold
          subst shape
          rw [mergeResponseShapes_denotesEquivalentPath_iff,
            abstractFragmentCons_selectsPath_iff schema variableValues
              parentType objectType selection rest habstract
              ⟨objectDefinition, hobjectLookup⟩ hincludes htypeCondition
              hnormal hfree path]
          exact or_congr
            ((ResponseShape.denotesEquivalentPath_reparent_object_iff
                schema assignment parentType objectType selectionShape
                ⟨objectDefinition, hobjectLookup⟩ hincludes
                (by
                  rcases foldGroundSelectionSet_success_of_image_with_invariant
                      schema support clause hvalid hcomplete hselection with
                    ⟨invariantShape, hinvariantFold, _hinvariant,
                      _hclauses, hobjectMetadata, _habstractMetadata⟩
                  have hshapeEq : invariantShape = selectionShape :=
                    Except.ok.inj (hinvariantFold.symm.trans hselectionShape)
                  subst invariantShape
                  exact (hobjectMetadata
                    ⟨objectDefinition, hobjectLookup⟩).2)
                path).trans
              (foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
                schema support clause hvalid hcomplete assignment variableValues
                hselection hselectionNormal hselectionFree hselectionShape
                hholds path))
            (foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
              schema support clause hvalid hcomplete assignment variableValues
              hrest hrestNormal hrestFree hrestShape hholds path)

  theorem foldGroundFieldChild_correspondence
      (schema : Schema) (support : List NormalForm.BoolVar) (clause : Clause)
      (hvalid : clause.Valid support)
      (hcomplete : clause.CompleteMinterm support)
      (assignment : NormalForm.BoolCase)
      (variableValues : Execution.VariableValues) (fieldName : Name) :
      ∀ {fieldDefinition selectionSet subshape},
        GroundFieldChildImage schema fieldDefinition selectionSet ->
        (if fieldDefinition.outputType.isCompositeBool schema then
            match foldGroundSelectionSet schema clause
                fieldDefinition.outputType.namedType selectionSet with
            | .ok child => .ok (some child)
            | .error error => .error error
          else if NormalForm.leafTypeNameBool schema
              fieldDefinition.outputType.namedType then
            if selectionSet.isEmpty then .ok none
            else .error (.leafFieldHasSubselections fieldName)
          else
            .error (.invalidFieldOutputType fieldName
              fieldDefinition.outputType.namedType)) =
          (.ok subshape : Except ShapeBuildError (Option ResponseShape)) ->
        NormalForm.selectionSetNormal schema
          fieldDefinition.outputType.namedType selectionSet ->
        NormalForm.selectionSetDirectiveFree selectionSet ->
        clause.HoldsIn assignment ->
        match subshape with
        | none => selectionSet = []
        | some childShape => ∀ path,
            childShape.DenotesEquivalentPath schema assignment
                fieldDefinition.outputType.namedType path
              ↔ selectionSetSelectsPath schema variableValues
                  fieldDefinition.outputType.namedType selectionSet path
    | fieldDefinition, selectionSet, subshape,
        .composite hcomposite hselection,
        hfold, hnormal, hfree, hholds => by
        cases hselectionFold : foldGroundSelectionSet schema clause
            fieldDefinition.outputType.namedType selectionSet with
        | error error => simp [hcomposite, hselectionFold] at hfold
        | ok childShape =>
            simp [hcomposite, hselectionFold] at hfold
            subst subshape
            exact fun path =>
              foldGroundSelectionSet_denotesEquivalentPath_iff_selectionSetSelectsPath
                schema support clause hvalid hcomplete assignment variableValues
                hselection hnormal hfree hselectionFold hholds path
    | fieldDefinition, [], subshape, .leaf hleaf,
        hfold, _hnormal, _hfree, _hholds => by
        have hcomposite :=
          isCompositeBool_eq_false_of_leafTypeNameBool schema hleaf
        simp [hcomposite, hleaf] at hfold
        subst subshape
        rfl
end

end ResponseShape

end GraphQL
