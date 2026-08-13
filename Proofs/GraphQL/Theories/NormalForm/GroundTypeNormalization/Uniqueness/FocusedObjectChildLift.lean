import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.RuntimeDataDiffWitness

/-!
Focused object-child lift for contextual runtime witnesses.

This module lifts a contextual child witness through its shared parent field.
The support predicate is local to the split context: only sibling child
selection sets for the same field head and equivalent arguments must be
executable under the shared child object.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def focusedSelectionSetTargetChildrenSupported
    (targetField : Name) (leftArguments rightArguments : List Argument)
    (selectionSet : List Selection) (support : List Selection -> Prop)
    : Prop :=
  ∀ responseName arguments directives childSelectionSet,
    Selection.field responseName targetField arguments directives childSelectionSet
      ∈ selectionSet
    -> (Argument.argumentsEquivalent arguments leftArguments
        ∨ Argument.argumentsEquivalent arguments rightArguments)
    -> support childSelectionSet

noncomputable def focusedSelectionSetTargetChildSelectionSets
    (targetField : Name) (leftArguments rightArguments : List Argument)
    : List Selection -> List (List Selection)
  | [] => []
  | Selection.field _responseName fieldName arguments _directives
      childSelectionSet :: rest => by
      classical
      exact
        if fieldName = targetField
          ∧ (Argument.argumentsEquivalent arguments leftArguments
            ∨ Argument.argumentsEquivalent arguments rightArguments) then
          childSelectionSet ::
            focusedSelectionSetTargetChildSelectionSets targetField
              leftArguments rightArguments rest
        else
          focusedSelectionSetTargetChildSelectionSets targetField
            leftArguments rightArguments rest
  | _selection :: rest =>
      focusedSelectionSetTargetChildSelectionSets targetField leftArguments
        rightArguments rest

theorem focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
    {targetField : Name} {leftArguments rightArguments : List Argument}
    {selectionSet : List Selection}
    : focusedSelectionSetTargetChildrenSupported targetField leftArguments
        rightArguments selectionSet
        (fun childSelectionSet =>
          childSelectionSet
          ∈ focusedSelectionSetTargetChildSelectionSets targetField
              leftArguments rightArguments selectionSet) := by
  intro responseName arguments directives childSelectionSet hmem harguments
  induction selectionSet with
  | nil =>
      simp at hmem
  | cons selection rest ih =>
      cases selection with
      | field headResponseName fieldName headArguments headDirectives
          headChildSelectionSet =>
          simp only [List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
            simp [focusedSelectionSetTargetChildSelectionSets, harguments]
          · by_cases htarget :
              fieldName = targetField
                ∧ (Argument.argumentsEquivalent headArguments leftArguments
                  ∨ Argument.argumentsEquivalent headArguments rightArguments)
            · simp [focusedSelectionSetTargetChildSelectionSets, htarget,
                ih htail]
            · simpa [focusedSelectionSetTargetChildSelectionSets, htarget]
                using ih htail
      | inlineFragment typeCondition headDirectives headSelectionSet =>
          simp only [List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
          · simpa [focusedSelectionSetTargetChildSelectionSets] using ih htail

noncomputable def focusedSplitTargetChildSelectionSets
    (targetField : Name) (leftArguments rightArguments : List Argument)
    (leftPref rightPref leftSuffix rightSuffix : List Selection)
    : List (List Selection) :=
  focusedSelectionSetTargetChildSelectionSets targetField leftArguments
    rightArguments leftPref
  ++ focusedSelectionSetTargetChildSelectionSets targetField leftArguments
      rightArguments rightPref
  ++ focusedSelectionSetTargetChildSelectionSets targetField leftArguments
      rightArguments leftSuffix
  ++ focusedSelectionSetTargetChildSelectionSets targetField leftArguments
      rightArguments rightSuffix

noncomputable def focusedSupportTargetChildSelectionSets
    (targetField : Name) (leftArguments rightArguments : List Argument)
    : List (List Selection) -> List (List Selection)
  | [] => []
  | selectionSet :: rest =>
      focusedSelectionSetTargetChildSelectionSets targetField leftArguments
        rightArguments selectionSet
      ++ focusedSupportTargetChildSelectionSets targetField leftArguments
          rightArguments rest

noncomputable def focusedObjectChildSupportSelectionSets
    (targetField : Name) (leftArguments rightArguments : List Argument)
    (leftPref rightPref leftSuffix rightSuffix : List Selection)
    (supportSelectionSets : List (List Selection))
    : List (List Selection) :=
  focusedSplitTargetChildSelectionSets targetField leftArguments
    rightArguments leftPref rightPref leftSuffix rightSuffix
  ++ focusedSupportTargetChildSelectionSets targetField leftArguments
      rightArguments supportSelectionSets

theorem
    focusedSelectionSetTargetChildSelectionSets_subset_supportTargetChildSelectionSets_of_mem
    {targetField : Name} {leftArguments rightArguments : List Argument}
    {supportSelectionSets : List (List Selection)}
    {selectionSet childSelectionSet : List Selection}
    : selectionSet ∈ supportSelectionSets
      -> childSelectionSet
          ∈ focusedSelectionSetTargetChildSelectionSets targetField
              leftArguments rightArguments selectionSet
      -> childSelectionSet
          ∈ focusedSupportTargetChildSelectionSets targetField leftArguments
              rightArguments supportSelectionSets := by
  intro hselection hchild
  induction supportSelectionSets with
  | nil =>
      simp at hselection
  | cons head rest ih =>
      simp at hselection
      rcases hselection with hhead | htail
      · subst selectionSet
        simp [focusedSupportTargetChildSelectionSets, hchild]
      · have hrest := ih htail
        simp [focusedSupportTargetChildSelectionSets, hrest]

theorem focusedSelectionSetTargetChildrenSupported_supportTargetChildSelectionSets
    {targetField : Name} {leftArguments rightArguments : List Argument}
    {supportSelectionSets : List (List Selection)}
    {selectionSet : List Selection}
    : selectionSet ∈ supportSelectionSets
      -> focusedSelectionSetTargetChildrenSupported targetField leftArguments
          rightArguments selectionSet
          (fun childSelectionSet =>
            childSelectionSet
            ∈ focusedSupportTargetChildSelectionSets targetField leftArguments
                rightArguments supportSelectionSets) := by
  intro hselection responseName arguments directives childSelectionSet hmem
    harguments
  have htarget :=
    focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
      (targetField := targetField) (leftArguments := leftArguments)
      (rightArguments := rightArguments) (selectionSet := selectionSet)
      responseName arguments directives childSelectionSet hmem harguments
  exact
    focusedSelectionSetTargetChildSelectionSets_subset_supportTargetChildSelectionSets_of_mem
      (targetField := targetField) (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (supportSelectionSets := supportSelectionSets)
      hselection htarget

theorem focusedSelectionSetTargetChildSelectionSets_mem
    {targetField : Name} {leftArguments rightArguments : List Argument}
    {selectionSet : List Selection} {childSelectionSet : List Selection}
    : childSelectionSet
        ∈ focusedSelectionSetTargetChildSelectionSets targetField leftArguments
            rightArguments selectionSet
      -> ∃ responseName arguments directives,
          Selection.field responseName targetField arguments directives childSelectionSet
            ∈ selectionSet
          ∧ (Argument.argumentsEquivalent arguments leftArguments
              ∨ Argument.argumentsEquivalent arguments rightArguments) := by
  intro hmem
  induction selectionSet with
  | nil =>
      simp [focusedSelectionSetTargetChildSelectionSets] at hmem
  | cons selection rest ih =>
      cases selection with
      | field responseName fieldName arguments directives headChildSelectionSet =>
          by_cases htarget :
              fieldName = targetField
                ∧ (Argument.argumentsEquivalent arguments leftArguments
                  ∨ Argument.argumentsEquivalent arguments rightArguments)
          · simp [focusedSelectionSetTargetChildSelectionSets, htarget] at hmem
            rcases hmem with hhead | htail
            · subst childSelectionSet
              refine ⟨responseName, arguments, directives, ?_, htarget.2⟩
              simp [htarget.1]
            · rcases ih htail with
                ⟨tailResponseName, tailArguments, tailDirectives,
                  htailMem, htailArguments⟩
              exact
                ⟨tailResponseName, tailArguments, tailDirectives,
                  List.mem_cons_of_mem _ htailMem, htailArguments⟩
          · simp [focusedSelectionSetTargetChildSelectionSets, htarget] at hmem
            rcases ih hmem with
              ⟨tailResponseName, tailArguments, tailDirectives, htailMem,
                htailArguments⟩
            exact
              ⟨tailResponseName, tailArguments, tailDirectives,
                List.mem_cons_of_mem _ htailMem, htailArguments⟩
      | inlineFragment typeCondition directives inlineSelectionSet =>
          simp [focusedSelectionSetTargetChildSelectionSets] at hmem
          rcases ih hmem with
            ⟨tailResponseName, tailArguments, tailDirectives, htailMem,
              htailArguments⟩
          exact
            ⟨tailResponseName, tailArguments, tailDirectives,
              List.mem_cons_of_mem _ htailMem, htailArguments⟩

theorem focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType targetField returnType : Name}
    {leftArguments rightArguments : List Argument}
    {selectionSet childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema variableDefinitions parentType selectionSet
      -> selectionSetDirectiveFree selectionSet
      -> selectionSetNormal schema parentType selectionSet
      -> schema.lookupField parentType targetField = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> childSelectionSet
          ∈ focusedSelectionSetTargetChildSelectionSets targetField leftArguments
              rightArguments selectionSet
      -> Validation.selectionSetValid schema variableDefinitions returnType
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema returnType childSelectionSet := by
  intro hvalid hfree hnormal hlookup hreturnType hcomposite hmem
  rcases focusedSelectionSetTargetChildSelectionSets_mem hmem with
    ⟨responseName, arguments, directives, hfieldMem, _harguments⟩
  rcases selectionSetValid_field_lookup_of_mem hvalid hfieldMem with
    ⟨candidateFieldDefinition, hcandidateLookup, _hargs,
      hfieldSelectionValid⟩
  have hcandidateEq : candidateFieldDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateFieldDefinition
  rcases fieldSelectionSetValid_child_of_composite hfieldSelectionValid
      hcomposite with
    ⟨_hchildNonempty, hchildValid⟩
  have hchildFree :
      selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hfree hfieldMem
  rcases selectionSetNormal_field_child_of_mem_with_returnType hnormal
      hfieldMem with
    ⟨candidateReturnType, hcandidateReturnType, hchildNormal⟩
  have hcandidateReturnEq : candidateReturnType = returnType := by
    simp [Schema.fieldReturnType?, hlookup, hreturnType] at hcandidateReturnType
    exact hcandidateReturnType.symm
  subst candidateReturnType
  have hchildValidReturn :
      Validation.selectionSetValid schema variableDefinitions returnType
        childSelectionSet := by
    simpa [hreturnType] using hchildValid
  exact ⟨hchildValidReturn, hchildFree, hchildNormal⟩

theorem
    focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal_of_field_subset
    {schema : Schema} {variableDefinitions : List VariableDefinition}
    {parentType targetField returnType : Name}
    {leftArguments rightArguments : List Argument}
    {whole selectionSet childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : (∀ responseName arguments directives childSelectionSet,
        Selection.field responseName targetField arguments directives childSelectionSet
          ∈ selectionSet
        -> Selection.field responseName targetField arguments directives childSelectionSet
            ∈ whole)
      -> Validation.selectionSetValid schema variableDefinitions parentType whole
      -> selectionSetDirectiveFree whole
      -> selectionSetNormal schema parentType whole
      -> schema.lookupField parentType targetField = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> childSelectionSet
          ∈ focusedSelectionSetTargetChildSelectionSets targetField leftArguments
              rightArguments selectionSet
      -> Validation.selectionSetValid schema variableDefinitions returnType
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema returnType childSelectionSet := by
  intro hfieldSubset hvalid hfree hnormal hlookup hreturnType hcomposite
    hmem
  rcases focusedSelectionSetTargetChildSelectionSets_mem hmem with
    ⟨responseName, arguments, directives, hfieldMem, _harguments⟩
  have hwholeMem :
      Selection.field responseName targetField arguments directives
        childSelectionSet ∈ whole :=
    hfieldSubset responseName arguments directives childSelectionSet
      hfieldMem
  rcases selectionSetValid_field_lookup_of_mem hvalid hwholeMem with
    ⟨candidateFieldDefinition, hcandidateLookup, _hargs,
      hfieldSelectionValid⟩
  have hcandidateEq : candidateFieldDefinition = fieldDefinition := by
    rw [hlookup] at hcandidateLookup
    exact Option.some.inj hcandidateLookup.symm
  subst candidateFieldDefinition
  rcases fieldSelectionSetValid_child_of_composite hfieldSelectionValid
      hcomposite with
    ⟨_hchildNonempty, hchildValid⟩
  have hchildFree :
      selectionSetDirectiveFree childSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hfree hwholeMem
  rcases selectionSetNormal_field_child_of_mem_with_returnType hnormal
      hwholeMem with
    ⟨candidateReturnType, hcandidateReturnType, hchildNormal⟩
  have hcandidateReturnEq : candidateReturnType = returnType := by
    simp [Schema.fieldReturnType?, hlookup, hreturnType] at hcandidateReturnType
    exact hcandidateReturnType.symm
  subst candidateReturnType
  have hchildValidReturn :
      Validation.selectionSetValid schema variableDefinitions returnType
        childSelectionSet := by
    simpa [hreturnType] using hchildValid
  exact ⟨hchildValidReturn, hchildFree, hchildNormal⟩

theorem focusedSupportTargetChildSelectionSets_child_exists_valid_free_normal
    {schema : Schema}
    {parentType returnType fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {supportSelectionSets : List (List Selection)}
    {childSelectionSet : List Selection}
    {fieldDefinition : FieldDefinition}
    : (∀ supportSelectionSet,
        supportSelectionSet ∈ supportSelectionSets
        -> ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions parentType
              supportSelectionSet
            ∧ selectionSetDirectiveFree supportSelectionSet
            ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> childSelectionSet
          ∈ focusedSupportTargetChildSelectionSets fieldName leftArguments
              rightArguments supportSelectionSets
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions returnType
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema returnType childSelectionSet := by
  intro hsupportValid hlookup hreturnType hcomposite hmem
  induction supportSelectionSets with
  | nil =>
      simp [focusedSupportTargetChildSelectionSets] at hmem
  | cons head rest ih =>
      simp [focusedSupportTargetChildSelectionSets] at hmem
      rcases hmem with hhead | htail
      · rcases hsupportValid head (by simp) with
          ⟨variableDefinitions, hvalid, hfree, hnormal⟩
        rcases
            focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal
              (schema := schema)
              (variableDefinitions := variableDefinitions)
              (parentType := parentType) (targetField := fieldName)
              (returnType := returnType) (leftArguments := leftArguments)
              (rightArguments := rightArguments)
              (selectionSet := head)
              (childSelectionSet := childSelectionSet)
              (fieldDefinition := fieldDefinition)
              hvalid hfree hnormal hlookup hreturnType hcomposite hhead with
          ⟨hchildValid, hchildFree, hchildNormal⟩
        exact ⟨variableDefinitions, hchildValid, hchildFree, hchildNormal⟩
      · have hrestValid :
            ∀ supportSelectionSet,
              supportSelectionSet ∈ rest ->
                ∃ variableDefinitions,
                  Validation.selectionSetValid schema variableDefinitions
                    parentType supportSelectionSet
                  ∧ selectionSetDirectiveFree supportSelectionSet
                  ∧ selectionSetNormal schema parentType supportSelectionSet := by
          intro supportSelectionSet hsupport
          exact hsupportValid supportSelectionSet
            (List.mem_cons_of_mem head hsupport)
        exact ih hrestValid htail

theorem focusedSplitTargetChildSelectionSets_child_exists_valid_free_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix childSelectionSet
      : List Selection}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType
        (leftPref
          ++ Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
              :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> childSelectionSet
          ∈ focusedSplitTargetChildSelectionSets fieldName leftArguments
              rightArguments leftPref rightPref leftSuffix rightSuffix
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions returnType
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema returnType childSelectionSet := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hlookup hreturnType hcomposite hmem
  simp [focusedSplitTargetChildSelectionSets] at hmem
  rcases hmem with hleftPref | hrightPref | hleftSuffix | hrightSuffix
  · rcases
        focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal_of_field_subset
          (schema := schema)
          (variableDefinitions := leftVariableDefinitions)
          (parentType := parentType) (targetField := fieldName)
          (returnType := returnType) (leftArguments := leftArguments)
          (rightArguments := rightArguments)
          (whole :=
            leftPref ++ Selection.field responseName fieldName leftArguments []
              leftChildSelectionSet :: leftSuffix)
          (selectionSet := leftPref)
          (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition)
          (by
            intro currentResponseName arguments directives currentChild
              hcurrent
            exact List.mem_append_left _ hcurrent)
          hleftValid hleftFree hleftNormal hlookup hreturnType hcomposite
          hleftPref with
      ⟨hvalid, hfree, hnormal⟩
    exact ⟨leftVariableDefinitions, hvalid, hfree, hnormal⟩
  · rcases
        focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal_of_field_subset
          (schema := schema)
          (variableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (targetField := fieldName)
          (returnType := returnType) (leftArguments := leftArguments)
          (rightArguments := rightArguments)
          (whole :=
            rightPref ++
              Selection.field responseName fieldName rightArguments []
                rightChildSelectionSet :: rightSuffix)
          (selectionSet := rightPref)
          (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition)
          (by
            intro currentResponseName arguments directives currentChild
              hcurrent
            exact List.mem_append_left _ hcurrent)
          hrightValid hrightFree hrightNormal hlookup hreturnType hcomposite
          hrightPref with
      ⟨hvalid, hfree, hnormal⟩
    exact ⟨rightVariableDefinitions, hvalid, hfree, hnormal⟩
  · rcases
        focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal_of_field_subset
          (schema := schema)
          (variableDefinitions := leftVariableDefinitions)
          (parentType := parentType) (targetField := fieldName)
          (returnType := returnType) (leftArguments := leftArguments)
          (rightArguments := rightArguments)
          (whole :=
            leftPref ++ Selection.field responseName fieldName leftArguments []
              leftChildSelectionSet :: leftSuffix)
          (selectionSet := leftSuffix)
          (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition)
          (by
            intro currentResponseName arguments directives currentChild
              hcurrent
            exact
              List.mem_append_right leftPref
                (List.mem_cons_of_mem
                  (Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet) hcurrent))
          hleftValid hleftFree hleftNormal hlookup hreturnType hcomposite
          hleftSuffix with
      ⟨hvalid, hfree, hnormal⟩
    exact ⟨leftVariableDefinitions, hvalid, hfree, hnormal⟩
  · rcases
        focusedSelectionSetTargetChildSelectionSets_child_valid_free_normal_of_field_subset
          (schema := schema)
          (variableDefinitions := rightVariableDefinitions)
          (parentType := parentType) (targetField := fieldName)
          (returnType := returnType) (leftArguments := leftArguments)
          (rightArguments := rightArguments)
          (whole :=
            rightPref ++
              Selection.field responseName fieldName rightArguments []
                rightChildSelectionSet :: rightSuffix)
          (selectionSet := rightSuffix)
          (childSelectionSet := childSelectionSet)
          (fieldDefinition := fieldDefinition)
          (by
            intro currentResponseName arguments directives currentChild
              hcurrent
            exact
              List.mem_append_right rightPref
                (List.mem_cons_of_mem
                  (Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet) hcurrent))
          hrightValid hrightFree hrightNormal hlookup hreturnType hcomposite
          hrightSuffix with
      ⟨hvalid, hfree, hnormal⟩
    exact ⟨rightVariableDefinitions, hvalid, hfree, hnormal⟩

theorem focusedObjectChildSupportSelectionSets_child_exists_valid_free_normal
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix childSelectionSet
      : List Selection}
    {supportSelectionSets : List (List Selection)}
    {fieldDefinition : FieldDefinition}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType
        (leftPref
          ++ Selection.field responseName fieldName leftArguments [] leftChildSelectionSet
              :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> schema.isCompositeType fieldDefinition.outputType.namedType
      -> childSelectionSet
          ∈ focusedObjectChildSupportSelectionSets fieldName leftArguments
              rightArguments leftPref rightPref leftSuffix rightSuffix
              supportSelectionSets
      -> ∃ variableDefinitions,
          Validation.selectionSetValid schema variableDefinitions returnType
            childSelectionSet
          ∧ selectionSetDirectiveFree childSelectionSet
          ∧ selectionSetNormal schema returnType childSelectionSet := by
  intro hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal hsupportValid hlookup hreturnType hcomposite hmem
  simp [focusedObjectChildSupportSelectionSets] at hmem
  rcases hmem with hsplit | hsupport
  · exact
      focusedSplitTargetChildSelectionSets_child_exists_valid_free_normal
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (returnType := returnType)
        (responseName := responseName) (fieldName := fieldName)
        (leftArguments := leftArguments) (rightArguments := rightArguments)
        (leftChildSelectionSet := leftChildSelectionSet)
        (rightChildSelectionSet := rightChildSelectionSet)
        (leftPref := leftPref) (rightPref := rightPref)
        (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition)
        hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal hlookup hreturnType hcomposite hsplit
  · exact
      focusedSupportTargetChildSelectionSets_child_exists_valid_free_normal
        (schema := schema) (parentType := parentType)
        (returnType := returnType) (fieldName := fieldName)
        (leftArguments := leftArguments) (rightArguments := rightArguments)
        (supportSelectionSets := supportSelectionSets)
        (childSelectionSet := childSelectionSet)
        (fieldDefinition := fieldDefinition)
        hsupportValid hlookup hreturnType hcomposite hsupport

theorem
    not_selectionSetsDataEquivalent_of_object_child_contextualRuntimeDiff_fieldCases_withFuelGe_focused
    {schema : Schema} (rootSelectionSet : List Selection)
    {parentType returnType responseName fieldName runtimeType : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition} {support : List Selection -> Prop} {minFuel : Nat}
    : schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments leftPref support
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments rightPref support
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments leftSuffix support
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments rightSuffix support
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> minFuel ≤ fuel
            ->  let resolvers :=
                  fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments rightArguments
                let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
                let parentSource :=
                  projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef))
                ∀ otherResponseName otherFieldName arguments directives childSelectionSet,
                  Selection.field otherResponseName otherFieldName arguments directives
                      childSelectionSet
                    ∈ leftPref
                  -> ¬ fieldPairProjectionTarget parentType fieldName fieldName
                        leftArguments rightArguments parentType otherFieldName
                        arguments
                  -> ∃ responseValue fieldErrors,
                      Execution.executeField schema resolvers variableValues parentFuel
                        parentSource otherResponseName
                        [{
                          parentType := parentType,
                          responseName := otherResponseName,
                          fieldName := otherFieldName,
                          arguments := arguments,
                          selectionSet := childSelectionSet
                        }]
                      = .ok ([(otherResponseName, responseValue)], fieldErrors))
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> minFuel ≤ fuel
            ->  let resolvers :=
                  fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments rightArguments
                let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
                let parentSource :=
                  projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef))
                ∀ otherResponseName otherFieldName arguments directives childSelectionSet,
                  Selection.field otherResponseName otherFieldName arguments directives
                      childSelectionSet
                    ∈ rightPref
                  -> ¬ fieldPairProjectionTarget parentType fieldName fieldName
                        leftArguments rightArguments parentType otherFieldName
                        arguments
                  -> ∃ responseValue fieldErrors,
                      Execution.executeField schema resolvers variableValues parentFuel
                        parentSource otherResponseName
                        [{
                          parentType := parentType,
                          responseName := otherResponseName,
                          fieldName := otherFieldName,
                          arguments := arguments,
                          selectionSet := childSelectionSet
                        }]
                      = .ok ([(otherResponseName, responseValue)], fieldErrors))
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> minFuel ≤ fuel
            ->  let resolvers :=
                  fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments rightArguments
                let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
                let parentSource :=
                  projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef))
                ∀ otherResponseName otherFieldName arguments directives childSelectionSet,
                  Selection.field otherResponseName otherFieldName arguments directives
                      childSelectionSet
                    ∈ leftSuffix
                  -> ¬ fieldPairProjectionTarget parentType fieldName fieldName
                        leftArguments rightArguments parentType otherFieldName
                        arguments
                  -> ∃ responseValue fieldErrors,
                      Execution.executeField schema resolvers variableValues parentFuel
                        parentSource otherResponseName
                        [{
                          parentType := parentType,
                          responseName := otherResponseName,
                          fieldName := otherFieldName,
                          arguments := arguments,
                          selectionSet := childSelectionSet
                        }]
                      = .ok ([(otherResponseName, responseValue)], fieldErrors))
      -> (∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
            schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
                childRuntimeType
              = true
            -> minFuel ≤ fuel
            ->  let resolvers :=
                  fieldPairOrDeepSuccessResolvers schema rootSelectionSet
                    (parentObjectProbeFieldResolvers base parentType fieldName
                      childRuntimeType ref fieldDefinition.outputType)
                    parentType fieldName fieldName leftArguments rightArguments
                let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
                let parentSource :=
                  projectionRootResolverValue
                    (.object parentType (none : Option ObjectRef))
                ∀ otherResponseName otherFieldName arguments directives childSelectionSet,
                  Selection.field otherResponseName otherFieldName arguments directives
                      childSelectionSet
                    ∈ rightSuffix
                  -> ¬ fieldPairProjectionTarget parentType fieldName fieldName
                        leftArguments rightArguments parentType otherFieldName
                        arguments
                  -> ∃ responseValue fieldErrors,
                      Execution.executeField schema resolvers variableValues parentFuel
                        parentSource otherResponseName
                        [{
                          parentType := parentType,
                          responseName := otherResponseName,
                          fieldName := otherFieldName,
                          arguments := arguments,
                          selectionSet := childSelectionSet
                        }]
                      = .ok ([(otherResponseName, responseValue)], fieldErrors))
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema returnType
          runtimeType leftChildSelectionSet rightChildSelectionSet support
          minFuel
      -> ¬ selectionSetsDataEquivalent schema parentType
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro hlookup hreturnType hleftFree hrightFree hleftNormal hrightNormal
    hparentObject hleftPrefSupported hrightPrefSupported
    hleftSuffixSupported hrightSuffixSupported hleftPrefOther
    hrightPrefOther hleftSuffixOther hrightSuffixOther hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, base, variableValues, fuel, ref,
      hfuelGe, hsupportResponse, hchildNot⟩
  have hfieldInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        runtimeType = true := by
    simpa [hreturnType] using hinclude
  have hleftPrefFieldsOk :
      selectionSetFieldsExecuteOk schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (parentObjectProbeFieldResolvers base parentType fieldName
            runtimeType ref fieldDefinition.outputType)
          parentType fieldName fieldName leftArguments rightArguments)
        variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        parentType
        (projectionRootResolverValue
          (.object parentType (none : Option ObjectRef)))
        leftPref :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_field_cases
      schema rootSelectionSet base variableValues fuel parentType fieldName
      leftArguments rightArguments fieldDefinition runtimeType ref leftPref
      hlookup hfieldInclude
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hleftPrefSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inl harguments)))
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hleftPrefSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inr harguments)))
      (hleftPrefOther base variableValues fuel runtimeType ref hfieldInclude
        hfuelGe)
  have hrightPrefFieldsOk :
      selectionSetFieldsExecuteOk schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (parentObjectProbeFieldResolvers base parentType fieldName
            runtimeType ref fieldDefinition.outputType)
          parentType fieldName fieldName leftArguments rightArguments)
        variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        parentType
        (projectionRootResolverValue
          (.object parentType (none : Option ObjectRef)))
        rightPref :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_field_cases
      schema rootSelectionSet base variableValues fuel parentType fieldName
      leftArguments rightArguments fieldDefinition runtimeType ref rightPref
      hlookup hfieldInclude
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hrightPrefSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inl harguments)))
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hrightPrefSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inr harguments)))
      (hrightPrefOther base variableValues fuel runtimeType ref hfieldInclude
        hfuelGe)
  have hleftSuffixFieldsOk :
      selectionSetFieldsExecuteOk schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (parentObjectProbeFieldResolvers base parentType fieldName
            runtimeType ref fieldDefinition.outputType)
          parentType fieldName fieldName leftArguments rightArguments)
        variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        parentType
        (projectionRootResolverValue
          (.object parentType (none : Option ObjectRef)))
        leftSuffix :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_field_cases
      schema rootSelectionSet base variableValues fuel parentType fieldName
      leftArguments rightArguments fieldDefinition runtimeType ref leftSuffix
      hlookup hfieldInclude
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hleftSuffixSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inl harguments)))
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hleftSuffixSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inr harguments)))
      (hleftSuffixOther base variableValues fuel runtimeType ref hfieldInclude
        hfuelGe)
  have hrightSuffixFieldsOk :
      selectionSetFieldsExecuteOk schema
        (fieldPairOrDeepSuccessResolvers schema rootSelectionSet
          (parentObjectProbeFieldResolvers base parentType fieldName
            runtimeType ref fieldDefinition.outputType)
          parentType fieldName fieldName leftArguments rightArguments)
        variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        parentType
        (projectionRootResolverValue
          (.object parentType (none : Option ObjectRef)))
        rightSuffix :=
    selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_field_cases
      schema rootSelectionSet base variableValues fuel parentType fieldName
      leftArguments rightArguments fieldDefinition runtimeType ref rightSuffix
      hlookup hfieldInclude
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hrightSuffixSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inl harguments)))
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        exact
          hsupportResponse childSelectionSet
            (hrightSuffixSupported currentResponseName arguments directives
              childSelectionSet hmem (Or.inr harguments)))
      (hrightSuffixOther base variableValues fuel runtimeType ref hfieldInclude
        hfuelGe)
  exact
    not_selectionSetsDataEquivalent_of_object_child_responseData_diff_concrete_fieldsExecuteOk
      rootSelectionSet base variableValues fuel parentType responseName
      fieldName leftArguments rightArguments leftChildSelectionSet
      rightChildSelectionSet leftPref rightPref leftSuffix rightSuffix
      fieldDefinition runtimeType ref hlookup hleftFree hrightFree
      hleftNormal hrightNormal hparentObject hfieldInclude
      ⟨hleftPrefFieldsOk, hrightPrefFieldsOk, hleftSuffixFieldsOk,
        hrightSuffixFieldsOk⟩
      hchildNot

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_child_contextualRuntimeDiff_split_focused
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName runtimeType : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition} {support : List Selection -> Prop}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments leftPref support
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments rightPref support
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments leftSuffix support
      -> focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments rightSuffix support
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema returnType
          runtimeType leftChildSelectionSet rightChildSelectionSet support
          (selectionSetDeepProbeFuel schema parentType
              ((leftPref
                  ++ Selection.field responseName fieldName leftArguments []
                        leftChildSelectionSet
                      :: leftSuffix)
                ++ (rightPref
                    ++ Selection.field responseName fieldName rightArguments []
                          rightChildSelectionSet
                        :: rightSuffix))
            - leafProbeFuel fieldDefinition.outputType)
      -> ¬ selectionSetsDataEquivalent schema parentType
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro hschema hleftValid hrightValid hlookup hreturnType hleftFree
    hrightFree hleftNormal hrightNormal hparentObject hleftPrefSupported
    hrightPrefSupported hleftSuffixSupported hrightSuffixSupported hwitness
  let leftSelectionSet :=
    leftPref ++ Selection.field responseName fieldName leftArguments []
      leftChildSelectionSet :: leftSuffix
  let rightSelectionSet :=
    rightPref ++ Selection.field responseName fieldName rightArguments []
      rightChildSelectionSet :: rightSuffix
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) []
      (leftSelectionSet ++ rightSelectionSet)]
  have hleftOther :
      ∀ (selectionSet : List Selection),
        (∀ otherResponseName otherFieldName arguments directives
            childSelectionSet,
          Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ selectionSet ->
            Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ leftSelectionSet) ->
        ∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
              childRuntimeType = true ->
          (selectionSetDeepProbeFuel schema parentType
            (leftSelectionSet ++ rightSelectionSet)
            - leafProbeFuel fieldDefinition.outputType) ≤ fuel ->
          let resolvers :=
            fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base parentType fieldName
                childRuntimeType ref fieldDefinition.outputType)
              parentType fieldName fieldName leftArguments rightArguments
          let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
          let parentSource :=
            projectionRootResolverValue
              (.object parentType (none : Option ObjectRef))
          ∀ otherResponseName otherFieldName arguments directives
              childSelectionSet,
            Selection.field otherResponseName otherFieldName arguments
                directives childSelectionSet ∈ selectionSet ->
            ¬ fieldPairProjectionTarget parentType fieldName fieldName
                leftArguments rightArguments parentType otherFieldName
                arguments ->
              ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues
                  parentFuel parentSource otherResponseName
                  [{
                    parentType := parentType,
                    responseName := otherResponseName,
                    fieldName := otherFieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                =
                .ok ([(otherResponseName, responseValue)], fieldErrors) := by
    intro selectionSet hsubset ObjectRef base variableValues fuel
      childRuntimeType ref _hinclude hfuelGe
    have hparentFuelGe :
        selectionSetDeepProbeFuel schema parentType
          (leftSelectionSet ++ rightSelectionSet)
          ≤ fuel + leafProbeFuel fieldDefinition.outputType := by
      omega
    exact
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet base variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        parentType fieldName childRuntimeType ref fieldDefinition.outputType
        leftArguments rightArguments selectionSet
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact
            left_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
              (schema := schema) (parentType := parentType)
              (left := leftSelectionSet) (right := rightSelectionSet)
              (leftVariableDefinitions := leftVariableDefinitions)
              (rightVariableDefinitions := rightVariableDefinitions)
              (ProjectionResolverRef.filler :
                ProjectionResolverRef (Option ObjectRef))
              variableValues
              (projectionRootResolverValue
                (.object parentType (none : Option ObjectRef)))
              (fuel + leafProbeFuel fieldDefinition.outputType)
              hschema
              (by simpa [leftSelectionSet] using hleftValid)
              (by simpa [rightSelectionSet] using hrightValid)
              (by simpa [leftSelectionSet] using hleftFree)
              (by simpa [rightSelectionSet] using hrightFree)
              (by simpa [leftSelectionSet] using hleftNormal)
              (by simpa [rightSelectionSet] using hrightNormal)
              hparentObject hparentFuelGe otherResponseName
              otherFieldName arguments directives childSelectionSet
              (hsubset otherResponseName otherFieldName arguments
                directives childSelectionSet hmem))
  have hrightOther :
      ∀ (selectionSet : List Selection),
        (∀ otherResponseName otherFieldName arguments directives
            childSelectionSet,
          Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ selectionSet ->
            Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ rightSelectionSet) ->
        ∀ {ObjectRef : Type} (base : Execution.Resolvers ObjectRef)
            (variableValues : Execution.VariableValues) (fuel : Nat)
            (childRuntimeType : Name) (ref : ObjectRef),
          schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
              childRuntimeType = true ->
          (selectionSetDeepProbeFuel schema parentType
            (leftSelectionSet ++ rightSelectionSet)
            - leafProbeFuel fieldDefinition.outputType) ≤ fuel ->
          let resolvers :=
            fieldPairOrDeepSuccessResolvers schema rootSelectionSet
              (parentObjectProbeFieldResolvers base parentType fieldName
                childRuntimeType ref fieldDefinition.outputType)
              parentType fieldName fieldName leftArguments rightArguments
          let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
          let parentSource :=
            projectionRootResolverValue
              (.object parentType (none : Option ObjectRef))
          ∀ otherResponseName otherFieldName arguments directives
              childSelectionSet,
            Selection.field otherResponseName otherFieldName arguments
                directives childSelectionSet ∈ selectionSet ->
            ¬ fieldPairProjectionTarget parentType fieldName fieldName
                leftArguments rightArguments parentType otherFieldName
                arguments ->
              ∃ responseValue fieldErrors,
                Execution.executeField schema resolvers variableValues
                  parentFuel parentSource otherResponseName
                  [{
                    parentType := parentType,
                    responseName := otherResponseName,
                    fieldName := otherFieldName,
                    arguments := arguments,
                    selectionSet := childSelectionSet
                  }]
                =
                .ok ([(otherResponseName, responseValue)], fieldErrors) := by
    intro selectionSet hsubset ObjectRef base variableValues fuel
      childRuntimeType ref _hinclude hfuelGe
    have hparentFuelGe :
        selectionSetDeepProbeFuel schema parentType
          (leftSelectionSet ++ rightSelectionSet)
          ≤ fuel + leafProbeFuel fieldDefinition.outputType := by
      omega
    exact
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet base variableValues
        (fuel + leafProbeFuel fieldDefinition.outputType + 1)
        parentType fieldName childRuntimeType ref fieldDefinition.outputType
        leftArguments rightArguments selectionSet
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact
            right_selectionSet_deepSuccessFieldOk_append_framed_of_valid_normal_fuel_ge
              (schema := schema) (parentType := parentType)
              (left := leftSelectionSet) (right := rightSelectionSet)
              (leftVariableDefinitions := leftVariableDefinitions)
              (rightVariableDefinitions := rightVariableDefinitions)
              (ProjectionResolverRef.filler :
                ProjectionResolverRef (Option ObjectRef))
              variableValues
              (projectionRootResolverValue
                (.object parentType (none : Option ObjectRef)))
              (fuel + leafProbeFuel fieldDefinition.outputType)
              hschema
              (by simpa [leftSelectionSet] using hleftValid)
              (by simpa [rightSelectionSet] using hrightValid)
              (by simpa [leftSelectionSet] using hleftFree)
              (by simpa [rightSelectionSet] using hrightFree)
              (by simpa [leftSelectionSet] using hleftNormal)
              (by simpa [rightSelectionSet] using hrightNormal)
              hparentObject hparentFuelGe otherResponseName
              otherFieldName arguments directives childSelectionSet
              (hsubset otherResponseName otherFieldName arguments
                directives childSelectionSet hmem))
  exact
    not_selectionSetsDataEquivalent_of_object_child_contextualRuntimeDiff_fieldCases_withFuelGe_focused
      (schema := schema) (parentType := parentType)
      (returnType := returnType) (responseName := responseName)
      (fieldName := fieldName) (runtimeType := runtimeType)
      (leftArguments := leftArguments) (rightArguments := rightArguments)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (leftPref := leftPref) (rightPref := rightPref)
      (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
      (fieldDefinition := fieldDefinition) (support := support)
      (minFuel :=
        selectionSetDeepProbeFuel schema parentType
          (leftSelectionSet ++ rightSelectionSet)
        - leafProbeFuel fieldDefinition.outputType)
      rootSelectionSet hlookup hreturnType
      (by simpa [leftSelectionSet] using hleftFree)
      (by simpa [rightSelectionSet] using hrightFree)
      (by simpa [leftSelectionSet] using hleftNormal)
      (by simpa [rightSelectionSet] using hrightNormal)
      hparentObject hleftPrefSupported hrightPrefSupported
      hleftSuffixSupported hrightSuffixSupported
      (hleftOther leftPref
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact List.mem_append_left _ hmem))
      (hrightOther rightPref
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact List.mem_append_left _ hmem))
      (hleftOther leftSuffix
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact
            List.mem_append_right leftPref
              (List.mem_cons_of_mem
                (Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet) hmem)))
      (hrightOther rightSuffix
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact
            List.mem_append_right rightPref
              (List.mem_cons_of_mem
                (Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet) hmem)))
      (by simpa [leftSelectionSet, rightSelectionSet] using hwitness)

theorem
    not_selectionSetsDataEquivalent_of_valid_normal_object_child_contextualRuntimeDiff_split_targetSupport_focused
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName runtimeType : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {fieldDefinition : FieldDefinition}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema returnType
          runtimeType leftChildSelectionSet rightChildSelectionSet
          (fun childSelectionSet =>
            childSelectionSet
            ∈ focusedSplitTargetChildSelectionSets fieldName leftArguments
                rightArguments leftPref rightPref leftSuffix rightSuffix)
          (selectionSetDeepProbeFuel schema parentType
              ((leftPref
                  ++ Selection.field responseName fieldName leftArguments []
                        leftChildSelectionSet
                      :: leftSuffix)
                ++ (rightPref
                    ++ Selection.field responseName fieldName rightArguments []
                          rightChildSelectionSet
                        :: rightSuffix))
            - leafProbeFuel fieldDefinition.outputType)
      -> ¬ selectionSetsDataEquivalent schema parentType
            (leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix)
            (rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix) := by
  intro hschema hleftValid hrightValid hlookup hreturnType hleftFree
    hrightFree hleftNormal hrightNormal hparentObject hwitness
  exact
    not_selectionSetsDataEquivalent_of_valid_normal_object_child_contextualRuntimeDiff_split_focused
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (returnType := returnType)
      (responseName := responseName) (fieldName := fieldName)
      (runtimeType := runtimeType) (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (leftPref := leftPref) (rightPref := rightPref)
      (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
      (fieldDefinition := fieldDefinition)
      (support := fun childSelectionSet =>
        childSelectionSet ∈
          focusedSplitTargetChildSelectionSets fieldName leftArguments
            rightArguments leftPref rightPref leftSuffix rightSuffix)
      hschema hleftValid hrightValid hlookup hreturnType hleftFree
      hrightFree hleftNormal hrightNormal hparentObject
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        have htarget :=
          focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
            (targetField := fieldName) (leftArguments := leftArguments)
            (rightArguments := rightArguments) (selectionSet := leftPref)
            currentResponseName arguments directives childSelectionSet
            hmem harguments
        simp [focusedSplitTargetChildSelectionSets, htarget])
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        have htarget :=
          focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
            (targetField := fieldName) (leftArguments := leftArguments)
            (rightArguments := rightArguments) (selectionSet := rightPref)
            currentResponseName arguments directives childSelectionSet
            hmem harguments
        simp [focusedSplitTargetChildSelectionSets, htarget])
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        have htarget :=
          focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
            (targetField := fieldName) (leftArguments := leftArguments)
            (rightArguments := rightArguments) (selectionSet := leftSuffix)
            currentResponseName arguments directives childSelectionSet
            hmem harguments
        simp [focusedSplitTargetChildSelectionSets, htarget])
      (by
        intro currentResponseName arguments directives childSelectionSet
          hmem harguments
        have htarget :=
          focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
            (targetField := fieldName) (leftArguments := leftArguments)
            (rightArguments := rightArguments) (selectionSet := rightSuffix)
            currentResponseName arguments directives childSelectionSet
            hmem harguments
        simp [focusedSplitTargetChildSelectionSets, htarget])
      hwitness

theorem
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_of_valid_normal_object_child_contextualRuntimeDiff_split_focusedFiniteSupport
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName runtimeType : Name}
    {leftArguments rightArguments : List Argument}
    {leftChildSelectionSet rightChildSelectionSet
      leftPref rightPref leftSuffix rightSuffix
      : List Selection}
    {supportSelectionSets : List (List Selection)} {fieldDefinition : FieldDefinition}
    {minFuel : Nat}
    : SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> schema.lookupField parentType fieldName = some fieldDefinition
      -> fieldDefinition.outputType.namedType = returnType
      -> selectionSetDirectiveFree
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetDirectiveFree
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> selectionSetNormal schema parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
      -> selectionSetNormal schema parentType
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
      -> objectTypeNameBool schema parentType = true
      -> (∀ supportSelectionSet,
            supportSelectionSet ∈ supportSelectionSets
            -> ∃ variableDefinitions,
                Validation.selectionSetValid schema variableDefinitions parentType
                  supportSelectionSet
                ∧ selectionSetDirectiveFree supportSelectionSet
                ∧ selectionSetNormal schema parentType supportSelectionSet)
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema returnType
          runtimeType leftChildSelectionSet rightChildSelectionSet
          (fun childSelectionSet =>
            childSelectionSet
            ∈ focusedObjectChildSupportSelectionSets fieldName leftArguments
                rightArguments leftPref rightPref leftSuffix rightSuffix
                supportSelectionSets)
          (max
            (selectionSetDeepProbeFuel schema parentType
                (List.flatten
                  ((leftPref
                      ++ Selection.field responseName fieldName leftArguments []
                            leftChildSelectionSet
                          :: leftSuffix)
                    :: (rightPref
                        ++ Selection.field responseName fieldName
                              rightArguments [] rightChildSelectionSet
                            :: rightSuffix)
                    :: supportSelectionSets))
              - leafProbeFuel fieldDefinition.outputType)
            (minFuel - leafProbeFuel fieldDefinition.outputType - 1))
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema
          parentType parentType
          (leftPref
            ++ Selection.field responseName fieldName leftArguments []
                  leftChildSelectionSet
                :: leftSuffix)
          (rightPref
            ++ Selection.field responseName fieldName rightArguments []
                  rightChildSelectionSet
                :: rightSuffix)
          (fun selectionSet => selectionSet ∈ supportSelectionSets)
          minFuel := by
  intro hschema hleftValid hrightValid hlookup hreturnType hleftFree
    hrightFree hleftNormal hrightNormal hparentObject hsupportValid
    hwitness
  let leftSelectionSet :=
    leftPref ++ Selection.field responseName fieldName leftArguments []
      leftChildSelectionSet :: leftSuffix
  let rightSelectionSet :=
    rightPref ++ Selection.field responseName fieldName rightArguments []
      rightChildSelectionSet :: rightSuffix
  let members : List (List Selection) :=
    leftSelectionSet :: rightSelectionSet :: supportSelectionSets
  let rootSelectionSet :=
    [Selection.inlineFragment (some parentType) [] (List.flatten members)]
  let childSupport : List Selection -> Prop :=
    fun childSelectionSet =>
      childSelectionSet ∈
        focusedObjectChildSupportSelectionSets fieldName leftArguments
          rightArguments leftPref rightPref leftSuffix rightSuffix
          supportSelectionSets
  let childMinFuel :=
    max
      (selectionSetDeepProbeFuel schema parentType (List.flatten members)
        - leafProbeFuel fieldDefinition.outputType)
      (minFuel - leafProbeFuel fieldDefinition.outputType - 1)
  have hmembers :
      ∀ memberSelectionSet,
        memberSelectionSet ∈ members ->
          ∃ variableDefinitions,
            Validation.selectionSetValid schema variableDefinitions parentType
              memberSelectionSet
            ∧ selectionSetDirectiveFree memberSelectionSet
            ∧ selectionSetNormal schema parentType memberSelectionSet := by
    intro memberSelectionSet hmember
    simp [members, leftSelectionSet, rightSelectionSet] at hmember
    rcases hmember with hleft | hright | hsupport
    · subst memberSelectionSet
      exact ⟨leftVariableDefinitions, hleftValid, hleftFree, hleftNormal⟩
    · subst memberSelectionSet
      exact ⟨rightVariableDefinitions, hrightValid, hrightFree,
        hrightNormal⟩
    · exact hsupportValid memberSelectionSet hsupport
  have hleftPrefSupported :
      focusedSelectionSetTargetChildrenSupported fieldName leftArguments
        rightArguments leftPref childSupport := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have htarget :=
      focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
        (targetField := fieldName) (leftArguments := leftArguments)
        (rightArguments := rightArguments) (selectionSet := leftPref)
        currentResponseName arguments directives childSelectionSet hmem
        harguments
    simp [childSupport, focusedObjectChildSupportSelectionSets,
      focusedSplitTargetChildSelectionSets, htarget]
  have hrightPrefSupported :
      focusedSelectionSetTargetChildrenSupported fieldName leftArguments
        rightArguments rightPref childSupport := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have htarget :=
      focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
        (targetField := fieldName) (leftArguments := leftArguments)
        (rightArguments := rightArguments) (selectionSet := rightPref)
        currentResponseName arguments directives childSelectionSet hmem
        harguments
    simp [childSupport, focusedObjectChildSupportSelectionSets,
      focusedSplitTargetChildSelectionSets, htarget]
  have hleftSuffixSupported :
      focusedSelectionSetTargetChildrenSupported fieldName leftArguments
        rightArguments leftSuffix childSupport := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have htarget :=
      focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
        (targetField := fieldName) (leftArguments := leftArguments)
        (rightArguments := rightArguments) (selectionSet := leftSuffix)
        currentResponseName arguments directives childSelectionSet hmem
        harguments
    simp [childSupport, focusedObjectChildSupportSelectionSets,
      focusedSplitTargetChildSelectionSets, htarget]
  have hrightSuffixSupported :
      focusedSelectionSetTargetChildrenSupported fieldName leftArguments
        rightArguments rightSuffix childSupport := by
    intro currentResponseName arguments directives childSelectionSet hmem
      harguments
    have htarget :=
      focusedSelectionSetTargetChildrenSupported_targetChildSelectionSets
        (targetField := fieldName) (leftArguments := leftArguments)
        (rightArguments := rightArguments) (selectionSet := rightSuffix)
        currentResponseName arguments directives childSelectionSet hmem
        harguments
    simp [childSupport, focusedObjectChildSupportSelectionSets,
      focusedSplitTargetChildSelectionSets, htarget]
  have hsupportSupported :
      ∀ supportSelectionSet,
        supportSelectionSet ∈ supportSelectionSets ->
          focusedSelectionSetTargetChildrenSupported fieldName leftArguments
            rightArguments supportSelectionSet childSupport := by
    intro supportSelectionSet hsupport currentResponseName arguments
      directives childSelectionSet hmem harguments
    have htarget :=
      focusedSelectionSetTargetChildrenSupported_supportTargetChildSelectionSets
        (targetField := fieldName) (leftArguments := leftArguments)
        (rightArguments := rightArguments)
        (supportSelectionSets := supportSelectionSets)
        (selectionSet := supportSelectionSet)
        hsupport currentResponseName arguments directives childSelectionSet
        hmem harguments
    simp [childSupport, focusedObjectChildSupportSelectionSets, htarget]
  change
    selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema returnType
      runtimeType leftChildSelectionSet rightChildSelectionSet childSupport
      childMinFuel at hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, base, variableValues, fuel, ref, hfuelGe,
      hsupportResponse, hchildNot⟩
  have hfieldInclude :
      schema.typeIncludesObjectBool fieldDefinition.outputType.namedType
        runtimeType = true := by
    simpa [hreturnType] using hinclude
  let parentResolvers :=
    fieldPairOrDeepSuccessResolvers schema rootSelectionSet
      (parentObjectProbeFieldResolvers base parentType fieldName runtimeType
        ref fieldDefinition.outputType)
      parentType fieldName fieldName leftArguments rightArguments
  let parentFuel := fuel + leafProbeFuel fieldDefinition.outputType + 1
  let parentSource : Execution.ResolverValue
      (ProjectionResolverRef (Option ObjectRef)) :=
    projectionRootResolverValue
      (.object parentType (none : Option ObjectRef))
  have hdeepFuel :
      selectionSetDeepProbeFuel schema parentType (List.flatten members) ≤
        fuel + leafProbeFuel fieldDefinition.outputType := by
    have hlocal :
        selectionSetDeepProbeFuel schema parentType (List.flatten members)
          - leafProbeFuel fieldDefinition.outputType ≤ fuel := by
      exact Nat.le_trans (Nat.le_max_left _ _) hfuelGe
    omega
  have hminFuel : minFuel ≤ parentFuel := by
    have hlocal :
        minFuel - leafProbeFuel fieldDefinition.outputType - 1 ≤ fuel := by
      exact Nat.le_trans (Nat.le_max_right _ _) hfuelGe
    dsimp [parentFuel]
    omega
  have hotherOfSubset :
      ∀ (selectionSet wholeSelectionSet : List Selection),
        wholeSelectionSet ∈ members ->
        (∀ (otherResponseName otherFieldName : Name)
            (arguments : List Argument)
            (directives : List DirectiveApplication)
            (childSelectionSet : List Selection),
          Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ selectionSet ->
            Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ wholeSelectionSet) ->
        ∀ (otherResponseName otherFieldName : Name)
            (arguments : List Argument)
            (directives : List DirectiveApplication)
            (childSelectionSet : List Selection),
          Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ selectionSet ->
          ¬ fieldPairProjectionTarget parentType fieldName fieldName
              leftArguments rightArguments parentType otherFieldName
              arguments ->
            ∃ responseValue fieldErrors,
              Execution.executeField schema parentResolvers variableValues
                parentFuel parentSource otherResponseName
                [{
                  parentType := parentType,
                  responseName := otherResponseName,
                  fieldName := otherFieldName,
                  arguments := arguments,
                  selectionSet := childSelectionSet
                }]
              =
              .ok ([(otherResponseName, responseValue)], fieldErrors) := by
    intro selectionSet wholeSelectionSet hmember hsubset
    exact
      selectionSetOtherFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_deepSuccessWithRef_ok
        schema rootSelectionSet base variableValues parentFuel parentType
        fieldName runtimeType ref fieldDefinition.outputType leftArguments
        rightArguments selectionSet
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          simpa [parentFuel, parentSource, rootSelectionSet] using
            selectionSet_deepSuccessFieldOk_framed_of_valid_normal_members
              (schema := schema) (parentType := parentType)
              (members := members) (selectionSet := wholeSelectionSet)
              (ProjectionResolverRef.filler :
                ProjectionResolverRef (Option ObjectRef))
              variableValues parentSource
              (fuel + leafProbeFuel fieldDefinition.outputType)
              hschema hmembers hmember hparentObject hdeepFuel
              otherResponseName otherFieldName arguments directives
              childSelectionSet
              (hsubset otherResponseName otherFieldName arguments
                directives childSelectionSet hmem))
  have hfieldsOkOf
      (selectionSet wholeSelectionSet : List Selection)
      (hmember : wholeSelectionSet ∈ members)
      (hsubset :
        ∀ otherResponseName otherFieldName arguments directives
            childSelectionSet,
          Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ selectionSet ->
            Selection.field otherResponseName otherFieldName arguments
              directives childSelectionSet ∈ wholeSelectionSet)
      (hsupported :
        focusedSelectionSetTargetChildrenSupported fieldName leftArguments
          rightArguments selectionSet childSupport) :
      selectionSetFieldsExecuteOk schema parentResolvers variableValues
        parentFuel parentType parentSource selectionSet := by
    simpa [parentResolvers, parentFuel, parentSource] using
      selectionSetFieldsExecuteOk_fieldPairOrDeepSuccess_parentObjectProbe_of_field_cases
        schema rootSelectionSet base variableValues fuel parentType fieldName
        leftArguments rightArguments fieldDefinition runtimeType ref
        selectionSet hlookup hfieldInclude
        (by
          intro currentResponseName arguments directives childSelectionSet
            hmem harguments
          exact
            hsupportResponse childSelectionSet
              (hsupported currentResponseName arguments directives
                childSelectionSet hmem (Or.inl harguments)))
        (by
          intro currentResponseName arguments directives childSelectionSet
            hmem harguments
          exact
            hsupportResponse childSelectionSet
              (hsupported currentResponseName arguments directives
                childSelectionSet hmem (Or.inr harguments)))
        (by
          simpa [parentResolvers, parentFuel, parentSource] using
            hotherOfSubset selectionSet wholeSelectionSet hmember hsubset)
  have hleftMember : leftSelectionSet ∈ members := by
    simp [members]
  have hrightMember : rightSelectionSet ∈ members := by
    simp [members]
  have hleftPrefFieldsOk :
      selectionSetFieldsExecuteOk schema parentResolvers variableValues
        parentFuel parentType parentSource leftPref :=
    hfieldsOkOf leftPref leftSelectionSet hleftMember
      (by
        intro otherResponseName otherFieldName arguments directives
          childSelectionSet hmem
        exact List.mem_append_left _ hmem)
      hleftPrefSupported
  have hrightPrefFieldsOk :
      selectionSetFieldsExecuteOk schema parentResolvers variableValues
        parentFuel parentType parentSource rightPref :=
    hfieldsOkOf rightPref rightSelectionSet hrightMember
      (by
        intro otherResponseName otherFieldName arguments directives
          childSelectionSet hmem
        exact List.mem_append_left _ hmem)
      hrightPrefSupported
  have hleftSuffixFieldsOk :
      selectionSetFieldsExecuteOk schema parentResolvers variableValues
        parentFuel parentType parentSource leftSuffix :=
    hfieldsOkOf leftSuffix leftSelectionSet hleftMember
      (by
        intro otherResponseName otherFieldName arguments directives
          childSelectionSet hmem
        exact
          List.mem_append_right leftPref
            (List.mem_cons_of_mem
              (Selection.field responseName fieldName leftArguments []
                leftChildSelectionSet) hmem))
      hleftSuffixSupported
  have hrightSuffixFieldsOk :
      selectionSetFieldsExecuteOk schema parentResolvers variableValues
        parentFuel parentType parentSource rightSuffix :=
    hfieldsOkOf rightSuffix rightSelectionSet hrightMember
      (by
        intro otherResponseName otherFieldName arguments directives
          childSelectionSet hmem
        exact
          List.mem_append_right rightPref
            (List.mem_cons_of_mem
              (Selection.field responseName fieldName rightArguments []
                rightChildSelectionSet) hmem))
      hrightSuffixSupported
  have hcontext :=
    object_child_split_context_ok_of_concrete_fieldsExecuteOk
      (schema := schema) rootSelectionSet base variableValues fuel
      (parentType := parentType) (responseName := responseName)
      (fieldName := fieldName) (leftArguments := leftArguments)
      (rightArguments := rightArguments)
      (leftChildSelectionSet := leftChildSelectionSet)
      (rightChildSelectionSet := rightChildSelectionSet)
      (leftPref := leftPref) (rightPref := rightPref)
      (leftSuffix := leftSuffix) (rightSuffix := rightSuffix)
      (fieldDefinition := fieldDefinition) runtimeType ref hleftFree
      hrightFree hleftNormal hrightNormal hparentObject
      (by
        simpa [parentResolvers, parentFuel, parentSource] using
          ⟨hleftPrefFieldsOk, hrightPrefFieldsOk, hleftSuffixFieldsOk,
            hrightSuffixFieldsOk⟩)
  refine
    ⟨typeIncludesObjectBool_self_of_objectTypeNameBool schema hparentObject,
      ProjectionResolverRef (Option ObjectRef), parentResolvers,
      variableValues, parentFuel,
      ProjectionResolverRef.root (none : Option ObjectRef),
      hminFuel, ?_, ?_⟩
  · intro supportSelectionSet hsupport
    rcases hsupportValid supportSelectionSet hsupport with
      ⟨_supportVariableDefinitions, _hsupportValid, hsupportFree,
        hsupportNormal⟩
    have hsupportMember : supportSelectionSet ∈ members := by
      simp [members, hsupport]
    have hsupportFieldsOk :
        selectionSetFieldsExecuteOk schema parentResolvers variableValues
          parentFuel parentType parentSource supportSelectionSet :=
      hfieldsOkOf supportSelectionSet supportSelectionSet hsupportMember
        (by
          intro otherResponseName otherFieldName arguments directives
            childSelectionSet hmem
          exact hmem)
        (hsupportSupported supportSelectionSet hsupport)
    rcases
        ExecutionSuccess.executeSelectionSetAsResponse_object_of_field_ok schema
          parentResolvers variableValues parentFuel parentType parentSource
          supportSelectionSet hsupportFree hsupportNormal hparentObject
          hsupportFieldsOk with
      ⟨supportFields, supportErrors, hsupportResponseParent⟩
    exact ⟨supportFields, supportErrors, by
      simpa [parentSource, projectionRootResolverValue,
        projectionResolverValue] using hsupportResponseParent⟩
  · intro hsemantic
    exact hchildNot
      (responseData_semanticEquivalent_object_child_of_parent_responseData_split_context_ok
        rootSelectionSet base variableValues fuel parentType responseName
        fieldName leftArguments rightArguments leftChildSelectionSet
        rightChildSelectionSet leftPref rightPref leftSuffix rightSuffix
        fieldDefinition runtimeType ref hlookup hleftFree hrightFree
        hleftNormal hrightNormal hparentObject hfieldInclude hcontext
        (by
          simpa [parentResolvers, parentFuel, parentSource,
            projectionRootResolverValue, projectionResolverValue]
            using hsemantic))

end GroundTypeNormalization

end NormalForm

end GraphQL
