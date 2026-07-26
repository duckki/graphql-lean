import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DataSeparation
import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.FocusedTrace

/-!
Focused observable-trace semantic case split.

This module discharges current-object response-name and leaf field-head cases
directly, while leaving composite field-head, composite argument, and recursive
child cases as callbacks. Keeping this split at the observable-trace level
avoids routing the public proof through a collapsed diff trace.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

theorem normalSelectionSetDiffObservableTrace_left_or_right_nonempty
    {schema : Schema} {parentType : Name} {left right : List Selection}
    {responsePath : List Name}
    : NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> left ≠ [] ∨ right ≠ [] := by
  intro htrace
  cases htrace with
  | objectLeftResponseName _hobject hmem _hrightNo =>
      exact Or.inl (List.ne_nil_of_mem hmem)
  | objectRightResponseName _hobject hmem _hleftNo =>
      exact Or.inr (List.ne_nil_of_mem hmem)
  | objectFieldNameLeaf _hobject hleftMem _hrightMem _hleftLookup
      _hrightLookup _hleftLeaf _hrightLeaf _hfieldDiff =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectFieldNameCompositeLeft _hobject hleftMem _hrightMem _hleftLookup
      _hrightLookup _hleftComposite _hpath _hfieldDiff =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectFieldNameCompositeRight _hobject hleftMem _hrightMem _hleftLookup
      _hrightLookup _hrightComposite _hpath _hfieldDiff =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectArgumentsLeaf _hobject hleftMem _hrightMem _hlookup _hleaf
      _hargumentsDiff =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectArgumentsCompositeLeft _hobject hleftMem _hrightMem _hlookup
      _hcomposite _hpath _hargumentsDiff =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | objectChild _hobject _hreturn hleftMem _hrightMem _harguments
      _hchildTrace =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | abstractLeftTypeCondition _hnonObject hleftMem _hrightNo _hpath =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)
  | abstractRightTypeCondition _hnonObject hrightMem _hleftNo _hpath =>
      exact Or.inr (List.ne_nil_of_mem hrightMem)
  | abstractChild _hnonObject hleftMem _hrightMem _hchildTrace =>
      exact Or.inl (List.ne_nil_of_mem hleftMem)

theorem selectionSetValid_field_children_of_observable_trace {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType returnType responseName fieldName : Name}
    {leftArguments rightArguments : List Argument}
    {leftDirectives rightDirectives : List DirectiveApplication}
    {leftChildSelectionSet rightChildSelectionSet left right : List Selection}
    {childPath : List Name}
    : Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> Selection.field responseName fieldName leftArguments leftDirectives
            leftChildSelectionSet
          ∈ left
      -> Selection.field responseName fieldName rightArguments rightDirectives
            rightChildSelectionSet
          ∈ right
      -> schema.fieldReturnType? parentType fieldName = some returnType
      -> NormalSelectionSetDiffObservableTrace schema returnType
          leftChildSelectionSet rightChildSelectionSet childPath
      -> ∃ fieldDefinition,
          schema.lookupField parentType fieldName = some fieldDefinition
          ∧ fieldDefinition.outputType.namedType = returnType
          ∧ Validation.selectionSetValid schema leftVariableDefinitions
              returnType leftChildSelectionSet
          ∧ Validation.selectionSetValid schema rightVariableDefinitions
              returnType rightChildSelectionSet := by
  intro hleftValid hrightValid hleftMem hrightMem hreturnType htrace
  rcases selectionSetValid_field_lookup_of_mem hleftValid hleftMem with
    ⟨fieldDefinition, hlookup, _hleftArguments, hleftFieldValid⟩
  rcases selectionSetValid_field_lookup_of_mem hrightValid hrightMem with
    ⟨rightFieldDefinition, hrightLookup, _hrightArguments,
      hrightFieldValid⟩
  have hrightFieldDefinition : rightFieldDefinition = fieldDefinition := by
    rw [hlookup] at hrightLookup
    exact Option.some.inj hrightLookup.symm
  subst rightFieldDefinition
  have hnamedType :
      fieldDefinition.outputType.namedType = returnType :=
    fieldDefinition_namedType_eq_of_fieldReturnType? hlookup hreturnType
  have hnonempty :=
    normalSelectionSetDiffObservableTrace_left_or_right_nonempty htrace
  have hcomposite :
      schema.isCompositeType fieldDefinition.outputType.namedType := by
    rcases hnonempty with hleftNonempty | hrightNonempty
    · exact
        (fieldSelectionSetValid_child_of_nonempty hleftFieldValid
          hleftNonempty).1
    · exact
        (fieldSelectionSetValid_child_of_nonempty hrightFieldValid
          hrightNonempty).1
  rcases fieldSelectionSetValid_child_of_composite hleftFieldValid
      hcomposite with
    ⟨_hleftNonempty, hleftChildValid⟩
  rcases fieldSelectionSetValid_child_of_composite hrightFieldValid
      hcomposite with
    ⟨_hrightNonempty, hrightChildValid⟩
  refine ⟨fieldDefinition, hlookup, hnamedType, ?_, ?_⟩
  · simpa [hnamedType] using hleftChildValid
  · simpa [hnamedType] using hrightChildValid

theorem object_child_observable_trace_separator_of_split_separator
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection}
    : (∀ {returnType responseName fieldName : Name}
          {leftArguments rightArguments : List Argument}
          {leftChildSelectionSet rightChildSelectionSet
            leftPref rightPref leftSuffix rightSuffix
            : List Selection}
          {fieldDefinition : FieldDefinition} {childPath : List Name},
        schema.lookupField parentType fieldName = some fieldDefinition
        -> fieldDefinition.outputType.namedType = returnType
        -> left
            = leftPref
              ++ Selection.field responseName fieldName leftArguments []
                    leftChildSelectionSet
                  :: leftSuffix
        -> right
            = rightPref
              ++ Selection.field responseName fieldName rightArguments []
                    rightChildSelectionSet
                  :: rightSuffix
        -> Argument.argumentsEquivalent leftArguments rightArguments
        -> Validation.selectionSetValid schema leftVariableDefinitions returnType
            leftChildSelectionSet
        -> Validation.selectionSetValid schema rightVariableDefinitions returnType
            rightChildSelectionSet
        -> selectionSetDirectiveFree leftChildSelectionSet
        -> selectionSetDirectiveFree rightChildSelectionSet
        -> selectionSetNormal schema returnType leftChildSelectionSet
        -> selectionSetNormal schema returnType rightChildSelectionSet
        -> NormalSelectionSetDiffObservableTrace schema returnType
            leftChildSelectionSet rightChildSelectionSet childPath
        -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> ∀ {returnType responseName fieldName : Name}
            {leftArguments rightArguments : List Argument}
            {leftDirectives rightDirectives : List DirectiveApplication}
            {leftChildSelectionSet rightChildSelectionSet : List Selection}
            {childPath : List Name},
          schema.fieldReturnType? parentType fieldName = some returnType
          -> Selection.field responseName fieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
          -> Selection.field responseName fieldName rightArguments rightDirectives
                rightChildSelectionSet
              ∈ right
          -> Argument.argumentsEquivalent leftArguments rightArguments
          -> NormalSelectionSetDiffObservableTrace schema returnType
              leftChildSelectionSet rightChildSelectionSet childPath
          -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hsplit hleftValid hrightValid hleftFree hrightFree hleftNormal
    hrightNormal returnType responseName fieldName leftArguments
    rightArguments leftDirectives rightDirectives leftChildSelectionSet
    rightChildSelectionSet childPath hreturnType hleftMem hrightMem
    harguments htrace
  rcases
      selectionSetValid_field_children_of_observable_trace hleftValid
        hrightValid hleftMem hrightMem hreturnType htrace with
    ⟨fieldDefinition, hlookup, hnamedType, hleftChildValid,
      hrightChildValid⟩
  have hleftDirectives : leftDirectives = [] :=
    selectionSetDirectiveFree_field_directives_nil_of_mem hleftFree
      hleftMem
  have hrightDirectives : rightDirectives = [] :=
    selectionSetDirectiveFree_field_directives_nil_of_mem hrightFree
      hrightMem
  have hleftChildFree :
      selectionSetDirectiveFree leftChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hleftFree hleftMem
  have hrightChildFree :
      selectionSetDirectiveFree rightChildSelectionSet :=
    selectionSetDirectiveFree_field_child_of_mem hrightFree hrightMem
  have hleftChildNormal :
      selectionSetNormal schema returnType leftChildSelectionSet := by
    rcases
        selectionSetNormal_field_child_of_mem_with_returnType hleftNormal
          hleftMem with
      ⟨candidateReturnType, hcandidateReturnType, hcandidateNormal⟩
    have hcandidateEq : candidateReturnType = returnType := by
      rw [hreturnType] at hcandidateReturnType
      exact Option.some.inj hcandidateReturnType.symm
    subst candidateReturnType
    exact hcandidateNormal
  have hrightChildNormal :
      selectionSetNormal schema returnType rightChildSelectionSet := by
    rcases
        selectionSetNormal_field_child_of_mem_with_returnType hrightNormal
          hrightMem with
      ⟨candidateReturnType, hcandidateReturnType, hcandidateNormal⟩
    have hcandidateEq : candidateReturnType = returnType := by
      rw [hreturnType] at hcandidateReturnType
      exact Option.some.inj hcandidateReturnType.symm
    subst candidateReturnType
    exact hcandidateNormal
  rcases List.mem_iff_append.mp hleftMem with
    ⟨leftPref, leftSuffix, hleftEq⟩
  rcases List.mem_iff_append.mp hrightMem with
    ⟨rightPref, rightSuffix, hrightEq⟩
  subst leftDirectives
  subst rightDirectives
  exact
    hsplit hlookup hnamedType hleftEq hrightEq harguments hleftChildValid
      hrightChildValid hleftChildFree hrightChildFree hleftChildNormal
      hrightChildNormal htrace

theorem not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_of_separators
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} {responsePath : List Name}
    : (∀ {responseName leftFieldName rightFieldName : Name}
          {leftArguments rightArguments : List Argument}
          {leftDirectives rightDirectives : List DirectiveApplication}
          {leftChildSelectionSet rightChildSelectionSet : List Selection}
          {leftFieldDefinition rightFieldDefinition : FieldDefinition}
          {childPath : List Name},
        Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
        -> Selection.field responseName rightFieldName rightArguments
              rightDirectives rightChildSelectionSet
            ∈ right
        -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
        -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
        -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
            = true
        -> NormalSelectionSetObservableResponsePath schema
            leftFieldDefinition.outputType.namedType leftChildSelectionSet
            childPath
        -> leftFieldName ≠ rightFieldName
        -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> (∀ {responseName leftFieldName rightFieldName : Name}
              {leftArguments rightArguments : List Argument}
              {leftDirectives rightDirectives : List DirectiveApplication}
              {leftChildSelectionSet rightChildSelectionSet : List Selection}
              {leftFieldDefinition rightFieldDefinition : FieldDefinition}
              {childPath : List Name},
            Selection.field responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
              ∈ left
            -> Selection.field responseName rightFieldName rightArguments
                  rightDirectives rightChildSelectionSet
                ∈ right
            -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
            -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
            -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> NormalSelectionSetObservableResponsePath schema
                rightFieldDefinition.outputType.namedType rightChildSelectionSet
                childPath
            -> leftFieldName ≠ rightFieldName
            -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> (∀ {responseName fieldName : Name}
              {leftArguments rightArguments : List Argument}
              {leftDirectives rightDirectives : List DirectiveApplication}
              {leftChildSelectionSet rightChildSelectionSet : List Selection}
              {fieldDefinition : FieldDefinition} {childPath : List Name},
            Selection.field responseName fieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
            -> Selection.field responseName fieldName rightArguments rightDirectives
                  rightChildSelectionSet
                ∈ right
            -> schema.lookupField parentType fieldName = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
            -> NormalSelectionSetObservableResponsePath schema
                fieldDefinition.outputType.namedType leftChildSelectionSet
                childPath
            -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
            -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> (∀ {returnType responseName fieldName : Name}
              {leftArguments rightArguments : List Argument}
              {leftDirectives rightDirectives : List DirectiveApplication}
              {leftChildSelectionSet rightChildSelectionSet : List Selection}
              {childPath : List Name},
            schema.fieldReturnType? parentType fieldName = some returnType
            -> Selection.field responseName fieldName leftArguments leftDirectives
                  leftChildSelectionSet
                ∈ left
            -> Selection.field responseName fieldName rightArguments rightDirectives
                  rightChildSelectionSet
                ∈ right
            -> Argument.argumentsEquivalent leftArguments rightArguments
            -> NormalSelectionSetDiffObservableTrace schema returnType
                leftChildSelectionSet rightChildSelectionSet childPath
            -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hfieldNameCompositeLeft hfieldNameCompositeRight
    hargumentsCompositeLeft hchild hschema hleftValid hrightValid
    hleftFree hrightFree hleftNormal hrightNormal hobject htrace
  cases htrace with
  | objectLeftResponseName _hobjectDiff hleftMem hrightNoResponseName =>
      exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_left_responseName_diff
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightNoResponseName
  | objectRightResponseName _hobjectDiff hrightMem hleftNoResponseName =>
      exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_right_responseName_diff
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hrightMem hleftNoResponseName
  | objectFieldNameLeaf _hobjectDiff hleftMem hrightMem hleftLookup
      hrightLookup hleftLeaf hrightLeaf hfieldNameDiff =>
      exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_fieldName_diff_leaf
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightMem
          (by
            intro candidate hcandidate
            rw [hleftLookup] at hcandidate
            have hcandidateEq : candidate = _ :=
              Option.some.inj hcandidate.symm
            subst candidate
            exact hleftLeaf)
          (by
            intro candidate hcandidate
            rw [hrightLookup] at hcandidate
            have hcandidateEq : candidate = _ :=
              Option.some.inj hcandidate.symm
            subst candidate
            exact hrightLeaf)
          hfieldNameDiff
  | objectFieldNameCompositeLeft _hobjectDiff hleftMem hrightMem
      hleftLookup hrightLookup hleftComposite hleftObservable
      hfieldNameDiff =>
      exact
        hfieldNameCompositeLeft hleftMem hrightMem hleftLookup hrightLookup
          hleftComposite hleftObservable hfieldNameDiff
  | objectFieldNameCompositeRight _hobjectDiff hleftMem hrightMem
      hleftLookup hrightLookup hrightComposite hrightObservable
      hfieldNameDiff =>
      exact
        hfieldNameCompositeRight hleftMem hrightMem hleftLookup hrightLookup
          hrightComposite hrightObservable hfieldNameDiff
  | objectArgumentsLeaf _hobjectDiff hleftMem hrightMem hlookup hleaf
      hargumentsDiff =>
      exact
        not_selectionSetsDataEquivalent_of_valid_normal_object_arguments_diff_leaf
          hschema hleftValid hrightValid hleftFree hrightFree hleftNormal
          hrightNormal hobject hleftMem hrightMem
          (by
            intro candidate hcandidate
            rw [hlookup] at hcandidate
            have hcandidateEq : candidate = _ :=
              Option.some.inj hcandidate.symm
            subst candidate
            exact hleaf)
          hargumentsDiff
  | objectArgumentsCompositeLeft _hobjectDiff hleftMem hrightMem hlookup
      hcomposite hobservable hargumentsDiff =>
      exact
        hargumentsCompositeLeft hleftMem hrightMem hlookup hcomposite
          hobservable hargumentsDiff
  | objectChild _hobjectDiff hreturnType hleftMem hrightMem harguments
      hchildTrace =>
      exact hchild hreturnType hleftMem hrightMem harguments hchildTrace
  | abstractLeftTypeCondition hnonObject _hleftMem _hrightNoTypeCondition
      _hpath =>
      rw [hobject] at hnonObject
      simp at hnonObject
  | abstractRightTypeCondition hnonObject _hrightMem _hleftNoTypeCondition
      _hpath =>
      rw [hobject] at hnonObject
      simp at hnonObject
  | abstractChild hnonObject _hleftMem _hrightMem _hchildTrace =>
      rw [hobject] at hnonObject
      simp at hnonObject

theorem not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_of_split_child_separators
    {schema : Schema}
    {leftVariableDefinitions rightVariableDefinitions : List VariableDefinition}
    {parentType : Name} {left right : List Selection} {responsePath : List Name}
    : (∀ {responseName leftFieldName rightFieldName : Name}
          {leftArguments rightArguments : List Argument}
          {leftDirectives rightDirectives : List DirectiveApplication}
          {leftChildSelectionSet rightChildSelectionSet : List Selection}
          {leftFieldDefinition rightFieldDefinition : FieldDefinition}
          {childPath : List Name},
        Selection.field responseName leftFieldName leftArguments
            leftDirectives leftChildSelectionSet
          ∈ left
        -> Selection.field responseName rightFieldName rightArguments
              rightDirectives rightChildSelectionSet
            ∈ right
        -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
        -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
        -> (TypeRef.named leftFieldDefinition.outputType.namedType).isCompositeBool schema
            = true
        -> NormalSelectionSetObservableResponsePath schema
            leftFieldDefinition.outputType.namedType leftChildSelectionSet
            childPath
        -> leftFieldName ≠ rightFieldName
        -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> (∀ {responseName leftFieldName rightFieldName : Name}
              {leftArguments rightArguments : List Argument}
              {leftDirectives rightDirectives : List DirectiveApplication}
              {leftChildSelectionSet rightChildSelectionSet : List Selection}
              {leftFieldDefinition rightFieldDefinition : FieldDefinition}
              {childPath : List Name},
            Selection.field responseName leftFieldName leftArguments
                leftDirectives leftChildSelectionSet
              ∈ left
            -> Selection.field responseName rightFieldName rightArguments
                  rightDirectives rightChildSelectionSet
                ∈ right
            -> schema.lookupField parentType leftFieldName = some leftFieldDefinition
            -> schema.lookupField parentType rightFieldName = some rightFieldDefinition
            -> (TypeRef.named rightFieldDefinition.outputType.namedType).isCompositeBool
                  schema
                = true
            -> NormalSelectionSetObservableResponsePath schema
                rightFieldDefinition.outputType.namedType rightChildSelectionSet
                childPath
            -> leftFieldName ≠ rightFieldName
            -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> (∀ {responseName fieldName : Name}
              {leftArguments rightArguments : List Argument}
              {leftDirectives rightDirectives : List DirectiveApplication}
              {leftChildSelectionSet rightChildSelectionSet : List Selection}
              {fieldDefinition : FieldDefinition} {childPath : List Name},
            Selection.field responseName fieldName leftArguments leftDirectives
                leftChildSelectionSet
              ∈ left
            -> Selection.field responseName fieldName rightArguments rightDirectives
                  rightChildSelectionSet
                ∈ right
            -> schema.lookupField parentType fieldName = some fieldDefinition
            -> (TypeRef.named fieldDefinition.outputType.namedType).isCompositeBool schema
                = true
            -> NormalSelectionSetObservableResponsePath schema
                fieldDefinition.outputType.namedType leftChildSelectionSet
                childPath
            -> ¬ Argument.argumentsEquivalent leftArguments rightArguments
            -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> (∀ {returnType responseName fieldName : Name}
              {leftArguments rightArguments : List Argument}
              {leftChildSelectionSet rightChildSelectionSet
                leftPref rightPref leftSuffix rightSuffix
                : List Selection}
              {fieldDefinition : FieldDefinition} {childPath : List Name},
            schema.lookupField parentType fieldName = some fieldDefinition
            -> fieldDefinition.outputType.namedType = returnType
            -> left
                = leftPref
                  ++ Selection.field responseName fieldName leftArguments []
                        leftChildSelectionSet
                      :: leftSuffix
            -> right
                = rightPref
                  ++ Selection.field responseName fieldName rightArguments []
                        rightChildSelectionSet
                      :: rightSuffix
            -> Argument.argumentsEquivalent leftArguments rightArguments
            -> Validation.selectionSetValid schema leftVariableDefinitions returnType
                leftChildSelectionSet
            -> Validation.selectionSetValid schema rightVariableDefinitions returnType
                rightChildSelectionSet
            -> selectionSetDirectiveFree leftChildSelectionSet
            -> selectionSetDirectiveFree rightChildSelectionSet
            -> selectionSetNormal schema returnType leftChildSelectionSet
            -> selectionSetNormal schema returnType rightChildSelectionSet
            -> NormalSelectionSetDiffObservableTrace schema returnType
                leftChildSelectionSet rightChildSelectionSet childPath
            -> ¬ selectionSetsDataEquivalent schema parentType left right)
      -> SchemaWellFormedness.schemaWellFormed schema
      -> Validation.selectionSetValid schema leftVariableDefinitions parentType left
      -> Validation.selectionSetValid schema rightVariableDefinitions parentType right
      -> selectionSetDirectiveFree left
      -> selectionSetDirectiveFree right
      -> selectionSetNormal schema parentType left
      -> selectionSetNormal schema parentType right
      -> objectTypeNameBool schema parentType = true
      -> NormalSelectionSetDiffObservableTrace schema parentType left right responsePath
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hfieldNameCompositeLeft hfieldNameCompositeRight
    hargumentsCompositeLeft hchildSplit hschema hleftValid hrightValid
    hleftFree hrightFree hleftNormal hrightNormal hobject htrace
  apply
    not_selectionSetsDataEquivalent_of_valid_normal_object_diff_observable_trace_of_separators
      (schema := schema)
      (leftVariableDefinitions := leftVariableDefinitions)
      (rightVariableDefinitions := rightVariableDefinitions)
      (parentType := parentType) (left := left) (right := right)
      (responsePath := responsePath)
  · exact hfieldNameCompositeLeft
  · exact hfieldNameCompositeRight
  · exact hargumentsCompositeLeft
  · exact
      object_child_observable_trace_separator_of_split_separator
        (schema := schema)
        (leftVariableDefinitions := leftVariableDefinitions)
        (rightVariableDefinitions := rightVariableDefinitions)
        (parentType := parentType) (left := left) (right := right)
        hchildSplit hleftValid hrightValid hleftFree hrightFree hleftNormal
        hrightNormal
  · exact hschema
  · exact hleftValid
  · exact hrightValid
  · exact hleftFree
  · exact hrightFree
  · exact hleftNormal
  · exact hrightNormal
  · exact hobject
  · exact htrace

end GroundTypeNormalization

end NormalForm

end GraphQL
