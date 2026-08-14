import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.InlineDirectiveExecution

/-!
Static scoped field-group projection facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

variable {ObjectRef : Type}

theorem collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType responseName : Name)
    (boolCase : BoolCase)
    (ref : ObjectRef)
    : ∀ selectionSet,
        variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
        -> (∀ varName,
              varName ∈ selectionSetBooleanVariables selectionSet
              -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
        -> collectedResponseSelectionSet responseName
              (Execution.collectFields schema variableValues lookupParent
                (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
                selectionSet)
            = mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase lookupParent
                    groundType responseName selectionSet))
  | [], _hagrees, _hsourceVars => by
      simp [Execution.collectFields,
        collectedResponseSelectionSet,
        staticScopedFieldsWithResponseName, eraseCompleteScopedSelectionSet,
        mergeSelectionSets]
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest, hagrees, hsourceVars => by
      have hrestVars :
          ∀ varName, varName ∈ selectionSetBooleanVariables rest ->
            varName ∈ selectionSetBooleanVariables operation.selectionSet :=
        sourceSelectionSetVariables_tail operation
          (Selection.field fieldResponseName fieldName arguments directives
            selectionSet)
          rest hsourceVars
      have hrest :=
        collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
          schema variableValues operation lookupParent groundType responseName
          boolCase ref rest hagrees hrestVars
      have hdirectiveEq :=
        directivesAllowInCase_eq_execution_of_field_head
          variableValues boolCase operation fieldResponseName fieldName
          arguments directives selectionSet rest hagrees hsourceVars
      cases hallow :
          directivesAllowIn boolCase directives
      · have hexecSkip :
            Execution.selectionDirectivesAllowBool variableValues directives =
              false := by
          rw [← hdirectiveEq]
          exact hallow
        rw [collectFields_field_directives_skipped_eq schema variableValues
          lookupParent
          (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
          fieldResponseName
          fieldName arguments directives selectionSet rest hexecSkip]
        simpa [staticScopedFieldsWithResponseName, hallow] using hrest
      · have hexecAllow :
            Execution.selectionDirectivesAllowBool variableValues directives =
              true := by
          rw [← hdirectiveEq]
          exact hallow
        rw [GroundTypeNormalization.collectFields_cons]
        simp [Execution.collectSelection, hexecAllow]
        rw [GroundTypeNormalization.collectedResponseSelectionSet_mergeExecutableGroups]
        · cases hresponse : fieldResponseName == responseName <;>
            simp [collectedResponseSelectionSet,
              staticScopedFieldsWithResponseName, hallow, hresponse,
              eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
              mergeSelectionSets, Selection.subselections,
              Execution.mergedFieldSelectionSet, hrest]
        · exact collectFields_namesNodup schema
            variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) rest
  | Selection.inlineFragment none directives selectionSet :: rest,
      hagrees, hsourceVars => by
      have hselectionVars :
          ∀ varName, varName ∈ selectionSetBooleanVariables selectionSet ->
            varName ∈ selectionSetBooleanVariables operation.selectionSet :=
        sourceSelectionSetVariables_inline_child operation none directives
          selectionSet rest hsourceVars
      have hrestVars :
          ∀ varName, varName ∈ selectionSetBooleanVariables rest ->
            varName ∈ selectionSetBooleanVariables operation.selectionSet :=
        sourceSelectionSetVariables_tail operation
          (Selection.inlineFragment none directives selectionSet)
          rest hsourceVars
      have hselection :=
        collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
          schema variableValues operation lookupParent groundType responseName
          boolCase ref selectionSet hagrees hselectionVars
      have hrest :=
        collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
          schema variableValues operation lookupParent groundType responseName
          boolCase ref rest hagrees hrestVars
      have hdirectiveEq :=
        directivesAllowInCase_eq_execution_of_inline_head
          variableValues boolCase operation none directives selectionSet rest
          hagrees hsourceVars
      cases hallow :
          directivesAllowIn boolCase directives
      · have hexecSkip :
            Execution.selectionDirectivesAllowBool variableValues directives =
              false := by
          rw [← hdirectiveEq]
          exact hallow
        rw [collectFields_inlineFragment_none_directives_skipped_eq schema
          variableValues lookupParent
          (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) directives
          selectionSet rest hexecSkip]
        simpa [staticScopedFieldsWithResponseName, hallow] using hrest
      · have hexecAllow :
            Execution.selectionDirectivesAllowBool variableValues directives =
              true := by
          rw [← hdirectiveEq]
          exact hallow
        rw [collectFields_inlineFragment_none_directives_allowed_flatten schema
          variableValues lookupParent
          (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) directives
          selectionSet rest hexecAllow]
        rw [collectFields_append]
        rw [GroundTypeNormalization.collectedResponseSelectionSet_mergeExecutableGroups]
        · simp [staticScopedFieldsWithResponseName, hallow,
            eraseCompleteScopedSelectionSet_append,
            GroundTypeNormalization.mergeSelectionSets_append, hselection,
            hrest]
        · exact collectFields_namesNodup schema
            variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) rest
  | Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest, hagrees, hsourceVars => by
      have hselectionVars :
          ∀ varName, varName ∈ selectionSetBooleanVariables selectionSet ->
            varName ∈ selectionSetBooleanVariables operation.selectionSet :=
        sourceSelectionSetVariables_inline_child operation
          (some typeCondition) directives selectionSet rest hsourceVars
      have hrestVars :
          ∀ varName, varName ∈ selectionSetBooleanVariables rest ->
            varName ∈ selectionSetBooleanVariables operation.selectionSet :=
        sourceSelectionSetVariables_tail operation
          (Selection.inlineFragment (some typeCondition) directives
            selectionSet)
          rest hsourceVars
      have hselection :=
        collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
          schema variableValues operation lookupParent groundType responseName
          boolCase ref selectionSet hagrees hselectionVars
      have hselectionTyped :
          collectedResponseSelectionSet responseName
                (Execution.collectFields schema variableValues lookupParent
                (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
                selectionSet)
            =
          mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                typeCondition groundType responseName selectionSet)) := by
        rw [←
          eraseCompleteScopedSelectionSet_staticScopedFieldsWithResponseName_lookupParent
            schema boolCase lookupParent typeCondition groundType
            responseName selectionSet]
        exact hselection
      have hrest :=
        collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
          schema variableValues operation lookupParent groundType responseName
          boolCase ref rest hagrees hrestVars
      have hbranchEq :=
        inlineSomeBranchAllowInCase_eq_execution_of_inline_head schema
          variableValues boolCase operation groundType typeCondition
          directives selectionSet rest hagrees hsourceVars
      cases hbranch :
          directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType
      · have hexecSkip :
            (Execution.selectionDirectivesAllowBool variableValues directives
              && schema.typeIncludesObjectBool typeCondition groundType) =
              false := by
          rw [← hbranchEq]
          exact hbranch
        rw [collectFields_inlineFragment_some_directives_skipped_eq_object
          schema variableValues lookupParent groundType typeCondition
          ref directives selectionSet rest hexecSkip]
        simpa [staticScopedFieldsWithResponseName, hbranch] using hrest
      · have hexecBranch :
            (Execution.selectionDirectivesAllowBool variableValues directives
              && schema.typeIncludesObjectBool typeCondition groundType) =
              true := by
          rw [← hbranchEq]
          exact hbranch
        have hexecAllow :
            Execution.selectionDirectivesAllowBool variableValues directives =
              true := by
          cases hmatch :
              Execution.selectionDirectivesAllowBool variableValues directives
          · simp [hmatch] at hexecBranch
          · rfl
        have hincludes :
            schema.typeIncludesObjectBool typeCondition groundType = true := by
          cases hmatch :
              schema.typeIncludesObjectBool typeCondition groundType
          · simp [hmatch] at hexecBranch
          · rfl
        rw [collectFields_inlineFragment_some_directives_allowed_flatten_object
          schema variableValues lookupParent groundType typeCondition
          ref directives selectionSet rest hexecAllow hincludes]
        rw [collectFields_append]
        rw [GroundTypeNormalization.collectedResponseSelectionSet_mergeExecutableGroups]
        · simp [staticScopedFieldsWithResponseName, hbranch,
            eraseCompleteScopedSelectionSet_append,
            GroundTypeNormalization.mergeSelectionSets_append, hselectionTyped,
            hrest]
        · exact collectFields_namesNodup schema
            variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) rest

theorem
    collectedResponseSelectionSet_collectFields_completeScopedSelectionSetStaticFieldsWithResponseName
    (schema : Schema) (variableValues : Execution.VariableValues) (operation : Operation)
    (execParent groundType responseName : Name) (boolCase : BoolCase)
    (scopedSelections : List CompleteScopedSelection) (ref : ObjectRef)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet scopedSelections)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> collectedResponseSelectionSet responseName
            (Execution.collectFields schema variableValues execParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (eraseCompleteScopedSelectionSet scopedSelections))
          = mergeSelectionSets
              (eraseCompleteScopedSelectionSet
                (completeScopedSelectionSetStaticFieldsWithResponseName schema
                  boolCase groundType responseName scopedSelections)) := by
  intro hagrees hsourceVars
  have hprojection :
      collectedResponseSelectionSet responseName
          (Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (eraseCompleteScopedSelectionSet scopedSelections))
        =
      mergeSelectionSets
        (eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase execParent
            groundType responseName
            (eraseCompleteScopedSelectionSet scopedSelections))) :=
    collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
      schema variableValues operation execParent groundType responseName
          boolCase ref
      (eraseCompleteScopedSelectionSet scopedSelections) hagrees hsourceVars
  simpa [
    eraseCompleteScopedSelectionSet_completeScopedSelectionSetStaticFieldsWithResponseName
      schema boolCase execParent groundType responseName scopedSelections]
    using hprojection

theorem mergedFieldSelectionSet_source_field_head_eq_staticScopedFields
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (lookupParent groundType : Name)
    (boolCase : BoolCase)
    (ref : ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (sourceFields : List Execution.ExecutableField)
    (sourceTail : List (Name × List Execution.ExecutableField))
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceTail
      -> Execution.mergedFieldSelectionSet
            ({
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields)
          = selectionSet
            ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase lookupParent
                    groundType responseName rest)) := by
  intro hagrees hsourceVars hallow hcollect
  have hprojection :
      collectedResponseSelectionSet responseName
          (Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.field responseName fieldName arguments directives
              selectionSet :: rest))
        =
      mergeSelectionSets
        (eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName
            (Selection.field responseName fieldName arguments directives
              selectionSet :: rest))) :=
    collectedResponseSelectionSet_collectFields_staticScopedFieldsWithResponseName
      schema variableValues operation lookupParent groundType responseName
          boolCase ref
      (Selection.field responseName fieldName arguments directives selectionSet
        :: rest)
      hagrees hsourceVars
  simp [collectedResponseSelectionSet, hcollect,
    staticScopedFieldsWithResponseName, hallow, eraseCompleteScopedSelectionSet,
    eraseCompleteScopedSelection, mergeSelectionSets, Selection.subselections]
    at hprojection
  simpa using hprojection

theorem mergedFieldSelectionSet_source_completeScoped_field_head_eq_staticFields
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (execParent lookupParent groundType : Name)
    (boolCase : BoolCase)
    (ref : ObjectRef)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection) (rest : List CompleteScopedSelection)
    (sourceFields : List Execution.ExecutableField)
    (sourceTail : List (Name × List Execution.ExecutableField))
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    ({
                        lookupParent := lookupParent,
                        selection :=
                          Selection.field responseName fieldName arguments directives
                            selectionSet
                      }
                      :: rest))
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (eraseCompleteScopedSelectionSet
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
                }
                :: rest))
          = (
              responseName,
              {
                parentType := execParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceTail
      -> Execution.mergedFieldSelectionSet
            ({
                parentType := execParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields)
          = selectionSet
            ++ mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (completeScopedSelectionSetStaticFieldsWithResponseName schema
                    boolCase groundType responseName rest)) := by
  intro hagrees hsourceVars hallow hcollect
  have hprojection :
      collectedResponseSelectionSet responseName
          (Execution.collectFields schema variableValues execParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (eraseCompleteScopedSelectionSet
              ({ lookupParent := lookupParent,
                 selection :=
                  Selection.field responseName fieldName arguments directives
                    selectionSet }
                :: rest)))
        =
      mergeSelectionSets
        (eraseCompleteScopedSelectionSet
          (completeScopedSelectionSetStaticFieldsWithResponseName schema
            boolCase groundType responseName
            ({ lookupParent := lookupParent,
               selection :=
                Selection.field responseName fieldName arguments directives
                  selectionSet }
              :: rest))) :=
    collectedResponseSelectionSet_collectFields_completeScopedSelectionSetStaticFieldsWithResponseName
      schema variableValues operation execParent groundType responseName
          boolCase
      ({ lookupParent := lookupParent,
         selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
        :: rest)
      (ref := ref) hagrees hsourceVars
  have hcollectRaw :
      Execution.collectFields schema variableValues execParent
          (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
          (Selection.field responseName fieldName arguments directives
              selectionSet
            :: eraseCompleteScopedSelectionSet rest)
        =
      (responseName, {
        parentType := execParent,
        responseName := responseName,
        fieldName := fieldName,
        arguments := arguments,
        selectionSet := selectionSet
      } :: sourceFields) :: sourceTail := by
    simpa [eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection]
      using hcollect
  simp [collectedResponseSelectionSet, hcollectRaw,
    completeScopedSelectionSetStaticFieldsWithResponseName, hallow,
    eraseCompleteScopedSelectionSet, eraseCompleteScopedSelection,
    mergeSelectionSets, Selection.subselections] at hprojection
  simpa using hprojection

theorem collectFields_withoutFieldSelectionsWithResponseName_directives
    (schema : Schema)
    (variableValues : Execution.VariableValues)
    (parentType : Name) (source : Execution.ResolverValue ObjectRef)
    (responseName : Name)
    : ∀ selectionSet,
        Execution.collectFields schema variableValues parentType source
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
        = withoutExecutableGroupsWithResponseName
            responseName
            (Execution.collectFields schema variableValues parentType source selectionSet)
  | [] => by
      simp [Execution.collectFields, withoutFieldSelectionsWithResponseName,
        withoutExecutableGroupsWithResponseName]
  | Selection.field fieldResponseName fieldName arguments directives
      selectionSet :: rest => by
      have hrest :=
        collectFields_withoutFieldSelectionsWithResponseName_directives schema
          variableValues parentType source responseName rest
      by_cases hresponse : (fieldResponseName == responseName) = true
      · rw [withoutFieldSelectionsWithResponseName]
        simp [hresponse]
        cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
        · rw [collectFields_field_directives_skipped_eq schema variableValues
            parentType source fieldResponseName fieldName arguments
            directives selectionSet rest hallow]
          exact hrest
        · rw [GroundTypeNormalization.collectFields_cons]
          simp [Execution.collectSelection, hallow]
          rw [GroundTypeNormalization.withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
          have hsingleton :
              withoutExecutableGroupsWithResponseName
                responseName
                [(fieldResponseName, [{
                  parentType := parentType,
                  responseName := fieldResponseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                }])]
              = [] := by
            simp [withoutExecutableGroupsWithResponseName,
              hresponse]
          rw [hsingleton]
          rw [mergeExecutableGroups_nil_left_of_namesNodup]
          · exact hrest
          · exact
              GroundTypeNormalization.withoutExecutableGroupsWithResponseName_namesNodup
                responseName
                (Execution.collectFields schema variableValues parentType
                  source rest)
                (collectFields_namesNodup schema
                  variableValues parentType source rest)
      · have hfalse : (fieldResponseName == responseName) = false := by
          cases hmatch : fieldResponseName == responseName
          · rfl
          · contradiction
        rw [withoutFieldSelectionsWithResponseName]
        simp [hfalse]
        cases hallow :
            Execution.selectionDirectivesAllowBool variableValues directives
        · rw [collectFields_field_directives_skipped_eq schema variableValues
            parentType source fieldResponseName fieldName arguments
            directives selectionSet
            (withoutFieldSelectionsWithResponseName schema responseName rest) hallow]
          rw [collectFields_field_directives_skipped_eq schema variableValues
            parentType source fieldResponseName fieldName arguments
            directives selectionSet rest hallow]
          exact hrest
        · rw [GroundTypeNormalization.collectFields_cons]
          simp [Execution.collectSelection, hallow]
          rw [GroundTypeNormalization.collectFields_cons]
          simp [Execution.collectSelection, hallow]
          rw [GroundTypeNormalization.withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
          have hsingleton :
              withoutExecutableGroupsWithResponseName
                responseName
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
            simp [withoutExecutableGroupsWithResponseName,
              hfalse]
          rw [hsingleton]
          rw [hrest]
  | Selection.inlineFragment none directives selectionSet :: rest => by
      have hselection :=
        collectFields_withoutFieldSelectionsWithResponseName_directives schema
          variableValues parentType source responseName selectionSet
      have hrest :=
        collectFields_withoutFieldSelectionsWithResponseName_directives schema
          variableValues parentType source responseName rest
      rw [withoutFieldSelectionsWithResponseName]
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues directives
      · rw [collectFields_inlineFragment_none_directives_skipped_eq schema
          variableValues parentType source directives
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
          (withoutFieldSelectionsWithResponseName schema responseName rest) hallow]
        rw [collectFields_inlineFragment_none_directives_skipped_eq schema
          variableValues parentType source directives selectionSet rest hallow]
        exact hrest
      · rw [collectFields_inlineFragment_none_directives_allowed_flatten schema
          variableValues parentType source directives
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
          (withoutFieldSelectionsWithResponseName schema responseName rest) hallow]
        rw [collectFields_inlineFragment_none_directives_allowed_flatten schema
          variableValues parentType source directives selectionSet rest hallow]
        rw [collectFields_append]
        rw [collectFields_append]
        rw [GroundTypeNormalization.withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
        rw [hselection, hrest]
  | Selection.inlineFragment (some typeCondition) directives selectionSet
      :: rest => by
      have hselection :=
        collectFields_withoutFieldSelectionsWithResponseName_directives schema
          variableValues parentType source responseName selectionSet
      have hrest :=
        collectFields_withoutFieldSelectionsWithResponseName_directives schema
          variableValues parentType source responseName rest
      rw [withoutFieldSelectionsWithResponseName]
      cases hallow :
          Execution.selectionDirectivesAllowBool variableValues directives
      · have hskip :
            (Execution.selectionDirectivesAllowBool variableValues directives
              && Execution.doesFragmentTypeApplyBool schema parentType source
                typeCondition) = false := by
          simp [hallow]
        rw [collectFields_inlineFragment_some_directives_skipped_eq schema
          variableValues parentType source typeCondition directives
          (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
          (withoutFieldSelectionsWithResponseName schema responseName rest) hskip]
        rw [collectFields_inlineFragment_some_directives_skipped_eq schema
          variableValues parentType source typeCondition directives selectionSet
          rest hskip]
        exact hrest
      · cases happly :
            Execution.doesFragmentTypeApplyBool schema parentType source
              typeCondition
        · have hskip :
              (Execution.selectionDirectivesAllowBool variableValues directives
                && Execution.doesFragmentTypeApplyBool schema parentType source
                  typeCondition) = false := by
            simp [hallow, happly]
          rw [collectFields_inlineFragment_some_directives_skipped_eq schema
            variableValues parentType source typeCondition directives
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
            (withoutFieldSelectionsWithResponseName schema responseName rest) hskip]
          rw [collectFields_inlineFragment_some_directives_skipped_eq schema
            variableValues parentType source typeCondition directives
            selectionSet rest hskip]
          exact hrest
        · rw [collectFields_inlineFragment_some_directives_allowed_flatten
            schema variableValues parentType source typeCondition directives
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
            (withoutFieldSelectionsWithResponseName schema responseName rest) hallow
            happly]
          rw [collectFields_inlineFragment_some_directives_allowed_flatten
            schema variableValues parentType source typeCondition directives
            selectionSet rest hallow happly]
          rw [collectFields_append]
          rw [collectFields_append]
          rw [GroundTypeNormalization.withoutExecutableGroupsWithResponseName_mergeExecutableGroups]
          rw [hselection, hrest]

theorem
    collectFields_withoutFieldSelectionsWithResponseName_eq_sourceRest_of_cons_directives
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (responseName : Name)
    (fields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    (selectionSet : List Selection)
    : Execution.collectFields schema variableValues parentType source selectionSet
        = (responseName, fields) :: sourceRest
      -> Execution.collectFields schema variableValues parentType source
            (withoutFieldSelectionsWithResponseName schema responseName selectionSet)
          = sourceRest := by
  intro hcollect
  have hfilter :=
    collectFields_withoutFieldSelectionsWithResponseName_directives schema
      variableValues parentType source responseName selectionSet
  have hnodup :
      executableGroupNamesNodup
        ((responseName, fields) :: sourceRest) := by
    simpa [hcollect] using
      collectFields_namesNodup schema variableValues
        parentType source selectionSet
  rw [hcollect] at hfilter
  exact hfilter.trans
    (GroundTypeNormalization.withoutExecutableGroupsWithResponseName_cons_self_of_namesNodup
      responseName fields sourceRest hnodup)

theorem
    collectFields_withoutFieldSelectionsWithResponseName_fieldHead_rest_eq_sourceRest_directives
    (schema : Schema) (variableValues : Execution.VariableValues) (parentType : Name)
    (source : Execution.ResolverValue ObjectRef) (responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (subselections rest : List Selection) (sourceFields : List Execution.ExecutableField)
    (sourceRest : List (Name × List Execution.ExecutableField))
    : let sourceField : Execution.ExecutableField :=
        {
          parentType := parentType,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := subselections
        }
      Execution.collectFields schema variableValues parentType source
          (Selection.field responseName fieldName arguments directives subselections
            :: rest)
        = (responseName, sourceField :: sourceFields) :: sourceRest
      -> Execution.collectFields schema variableValues parentType source
            (withoutFieldSelectionsWithResponseName schema responseName rest)
          = sourceRest := by
  intro sourceField hcollect
  have hfilteredAll :=
    collectFields_withoutFieldSelectionsWithResponseName_eq_sourceRest_of_cons_directives
      schema variableValues parentType source responseName
      (sourceField :: sourceFields) sourceRest
      (Selection.field responseName fieldName arguments directives
        subselections :: rest)
      (by simpa [sourceField] using hcollect)
  simpa [withoutFieldSelectionsWithResponseName] using hfilteredAll

theorem executeCollectedFields_staticCollect_fieldHead_filtered_tails_eq
    (schema : Schema)
    (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues)
    (variables : List BoolVar)
    (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    (normalizedField sourceField : Execution.ExecutableField)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail : List (Name × List Execution.ExecutableField))
    : sourceField
        = {
          parentType := lookupParent,
          responseName := responseName,
          fieldName := fieldName,
          arguments := arguments,
          selectionSet := selectionSet
        }
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (responseName, normalizedField :: normalizedFields) :: normalizedTail
      -> Execution.collectFields schema variableValues lookupParent source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (responseName, sourceField :: sourceFields) :: sourceTail
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (withoutFieldSelectionsWithResponseName schema responseName rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (withoutFieldSelectionsWithResponseName schema responseName rest)
      -> Execution.executeCollectedFields schema resolvers variableValues depth
            source normalizedTail
          = Execution.executeCollectedFields schema resolvers variableValues depth
              source sourceTail := by
  intro hsourceField hnormalizedCollect hsourceCollect hfiltered
  have hnormalizedFiltered :
      Execution.collectFields schema variableValues lookupParent source
          (withoutFieldSelectionsWithResponseName schema responseName
            (staticCollectForGround schema variables lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives
                selectionSet :: rest)))
        =
        normalizedTail := by
    exact
      collectFields_withoutFieldSelectionsWithResponseName_eq_sourceRest_of_cons_directives
        schema variableValues lookupParent source responseName
        (normalizedField :: normalizedFields) normalizedTail
        (staticCollectForGround schema variables lookupParent
          groundType boolCase
          (Selection.field responseName fieldName arguments directives
            selectionSet :: rest))
        hnormalizedCollect
  have hnormalizedTail :
      Execution.collectFields schema variableValues lookupParent source
          (staticCollectForGround schema variables lookupParent
            groundType boolCase
            (withoutFieldSelectionsWithResponseName schema responseName rest))
        =
        normalizedTail := by
    rw [← hnormalizedFiltered]
    rw [← staticCollectForGround_withoutFieldSelectionsWithResponseName]
    simp [withoutFieldSelectionsWithResponseName]
  have hsourceTail :
      Execution.collectFields schema variableValues lookupParent source
          (withoutFieldSelectionsWithResponseName schema responseName rest)
        =
        sourceTail := by
    exact
      collectFields_withoutFieldSelectionsWithResponseName_fieldHead_rest_eq_sourceRest_directives
        schema variableValues lookupParent source responseName fieldName
        arguments directives selectionSet rest sourceFields sourceTail
        (by simpa [hsourceField] using hsourceCollect)
  simpa [Execution.executeSelectionSet, Execution.executeRootSelectionSet,
    hnormalizedTail, hsourceTail]
    using hfiltered

theorem
    executeSelectionSet_filterSelectionSetBoolCase_field_allowed_lookup_some_duplicate_group_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (lookupParent groundType : Name) (source : Execution.ResolverValue ObjectRef)
    (boolCase : BoolCase) (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail : List (Name × List Execution.ExecutableField))
    : directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> Execution.collectFields schema variableValues lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
              }
              :: normalizedFields
            )
            :: normalizedTail
      -> Execution.collectFields schema variableValues lookupParent source
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceTail
      -> (match Execution.resolveFieldValue schema resolvers variableValues
                  fieldDefinition lookupParent fieldName arguments source with
          | some value =>
              Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType
                (Execution.mergedFieldSelectionSet
                  ({
                      parentType := lookupParent,
                      responseName := responseName,
                      fieldName := fieldName,
                      arguments := arguments,
                      selectionSet :=
                        normalizeBoolCaseForType schema boolCase
                          fieldDefinition.outputType.namedType selectionSet
                    }
                    :: normalizedFields))
                value
              = Execution.completeValue schema resolvers variableValues (depth - 1)
                  fieldDefinition.outputType
                  (Execution.mergedFieldSelectionSet
                    ({
                        parentType := lookupParent,
                        responseName := responseName,
                        fieldName := fieldName,
                        arguments := arguments,
                        selectionSet := selectionSet
                      }
                      :: sourceFields))
                  value
          | none => True)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (withoutFieldSelectionsWithResponseName schema responseName rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (withoutFieldSelectionsWithResponseName schema responseName rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent source
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent source
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hallow hlookup hnormalizedCollect hsourceCollect hcomplete hfiltered
  let normalizedField : Execution.ExecutableField := {
    parentType := lookupParent,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    selectionSet :=
      normalizeBoolCaseForType schema boolCase
        fieldDefinition.outputType.namedType selectionSet
  }
  let sourceField : Execution.ExecutableField := {
    parentType := lookupParent,
    responseName := responseName,
    fieldName := fieldName,
    arguments := arguments,
    selectionSet := selectionSet
  }
  have htail :
      Execution.executeCollectedFields schema resolvers variableValues depth
          source normalizedTail
        =
        Execution.executeCollectedFields schema resolvers variableValues depth
          source sourceTail := by
    exact executeCollectedFields_staticCollect_fieldHead_filtered_tails_eq
      schema resolvers variableValues
      (operationBoolVars operation) depth lookupParent
      groundType source boolCase responseName fieldName arguments directives
      selectionSet rest normalizedField sourceField normalizedFields
      sourceFields normalizedTail sourceTail rfl
      (by simpa [normalizedField] using hnormalizedCollect)
      (by simpa [sourceField] using hsourceCollect)
      hfiltered
  have hcompleteGrouped :
      match Execution.resolveFieldValue schema resolvers variableValues
          fieldDefinition lookupParent fieldName arguments source with
      | some value =>
          Execution.completeValue schema resolvers variableValues (depth - 1)
              fieldDefinition.outputType
              (normalizedField :: normalizedFields) value
            =
            Execution.completeValue schema resolvers variableValues (depth - 1)
              fieldDefinition.outputType (sourceField :: sourceFields) value
      | none => True := by
    cases hresolved
          : Execution.resolveFieldValue schema resolvers variableValues
              fieldDefinition lookupParent fieldName arguments source with
    | none =>
        simp []
    | some value =>
        simp []
        have hleft :=
          completeValue_eq_mergedFieldSelectionSet
            schema resolvers variableValues (depth - 1)
            fieldDefinition.outputType
            (normalizedField :: normalizedFields) value
        have hright :=
          completeValue_eq_mergedFieldSelectionSet
            schema resolvers variableValues (depth - 1)
            fieldDefinition.outputType
            (sourceField :: sourceFields) value
        have hmiddle :
            Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType
                (Execution.mergedFieldSelectionSet
                  (normalizedField :: normalizedFields)) value
              =
            Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType
                (Execution.mergedFieldSelectionSet
                  (sourceField :: sourceFields)) value := by
          simpa [normalizedField, sourceField, hresolved] using hcomplete
        exact hleft.trans (hmiddle.trans hright.symm)
  exact executeSelectionSet_staticCollectForGround_field_allowed_lookup_some_group_case
    schema resolvers variableValues
    (operationBoolVars operation) depth lookupParent
    groundType source boolCase responseName fieldName arguments directives
    selectionSet rest fieldDefinition normalizedFields sourceFields
    normalizedTail sourceTail hallow hlookup hnormalizedCollect hsourceCollect
    hcompleteGrouped htail

theorem
    executeSelectionSet_filterSelectionSetBoolCase_field_allowed_lookup_some_duplicate_group_projected_case
    (schema : Schema) (resolvers : Execution.Resolvers ObjectRef)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (lookupParent groundType : Name) (ref : ObjectRef) (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet rest : List Selection)
    (fieldDefinition : FieldDefinition)
    (normalizedFields sourceFields : List Execution.ExecutableField)
    (normalizedTail sourceTail : List (Name × List Execution.ExecutableField))
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (Selection.field responseName fieldName arguments directives
                      selectionSet
                    :: rest)
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.lookupField lookupParent fieldName = some fieldDefinition
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet :=
                  normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
              }
              :: normalizedFields
            )
            :: normalizedTail
      -> Execution.collectFields schema variableValues lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (Selection.field responseName fieldName arguments directives selectionSet
              :: rest)
          = (
              responseName,
              {
                parentType := lookupParent,
                responseName := responseName,
                fieldName := fieldName,
                arguments := arguments,
                selectionSet := selectionSet
              }
              :: sourceFields
            )
            :: sourceTail
      -> (match Execution.resolveFieldValue schema resolvers variableValues
                  fieldDefinition lookupParent fieldName arguments
                  (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType
                    ref) with
          | some value =>
              Execution.completeValue schema resolvers variableValues (depth - 1)
                fieldDefinition.outputType
                (normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
                  ++ mergeSelectionSets
                      (staticCollectCompleteScopedSelectionSet schema
                        (operationBoolVars operation) groundType
                        boolCase
                        (staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest)))
                value
              = Execution.completeValue schema resolvers variableValues (depth - 1)
                  fieldDefinition.outputType
                  (selectionSet
                    ++ mergeSelectionSets
                        (eraseCompleteScopedSelectionSet
                          (staticScopedFieldsWithResponseName schema boolCase
                            lookupParent groundType responseName rest)))
                  value
          | none => True)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (withoutFieldSelectionsWithResponseName schema responseName rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (withoutFieldSelectionsWithResponseName schema responseName rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            lookupParent
            (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
            (staticCollectForGround schema
              (operationBoolVars operation) lookupParent
              groundType boolCase
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              lookupParent
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref)
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest) := by
  intro hagrees hsourceVars hallow hlookup hnormalizedCollect hsourceCollect
    hprojectedComplete hfiltered
  have hnormalizedProjection :=
    mergedFieldSelectionSet_staticCollect_field_head_eq_staticScopedFields
      schema variableValues
      (operationBoolVars operation) lookupParent groundType
      (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) boolCase
      responseName fieldName arguments
      directives selectionSet rest fieldDefinition normalizedFields
      normalizedTail hallow hlookup hnormalizedCollect
  have hsourceProjection :=
    mergedFieldSelectionSet_source_field_head_eq_staticScopedFields schema
      variableValues operation lookupParent groundType
      boolCase ref
      responseName fieldName arguments directives selectionSet rest
      sourceFields sourceTail hagrees hsourceVars hallow hsourceCollect
  have hcomplete :
      match Execution.resolveFieldValue schema resolvers variableValues
          fieldDefinition lookupParent fieldName arguments
          (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) with
      | some value =>
          Execution.completeValue schema resolvers variableValues (depth - 1)
              fieldDefinition.outputType
              (Execution.mergedFieldSelectionSet
                ({
                  parentType := lookupParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet :=
                    normalizeBoolCaseForType schema boolCase
                      fieldDefinition.outputType.namedType selectionSet
                } :: normalizedFields))
              value
            =
            Execution.completeValue schema resolvers variableValues (depth - 1)
              fieldDefinition.outputType
              (Execution.mergedFieldSelectionSet
                ({
                  parentType := lookupParent,
                  responseName := responseName,
                  fieldName := fieldName,
                  arguments := arguments,
                  selectionSet := selectionSet
                } :: sourceFields))
              value
      | none => True := by
    cases hresolved
          : Execution.resolveFieldValue schema resolvers variableValues
              fieldDefinition lookupParent fieldName arguments
              (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType
                ref) with
    | none =>
        simp []
    | some value =>
        have hnormalizedProjectionMap :
            List.map Execution.selectionExecutableField
                (normalizeBoolCaseForType schema boolCase
                  fieldDefinition.outputType.namedType selectionSet
                ++ mergeSelectionSets
                  (staticCollectCompleteScopedSelectionSet schema
                    (operationBoolVars operation) groundType boolCase
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName rest)))
              =
            List.map Execution.selectionExecutableField
                (normalizeBoolCaseForType schema boolCase
                  fieldDefinition.outputType.namedType selectionSet)
              ++
            List.map Execution.selectionExecutableField
              (Execution.mergedFieldSelectionSet normalizedFields) := by
          have hmapped :=
            congrArg (List.map Execution.selectionExecutableField)
              hnormalizedProjection
          simpa [Execution.mergedFieldSelectionSet, List.map_append]
            using hmapped.symm
        have hsourceProjectionMap :
            List.map Execution.selectionExecutableField
                (selectionSet
                ++ mergeSelectionSets
                  (eraseCompleteScopedSelectionSet
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName rest)))
              =
            List.map Execution.selectionExecutableField selectionSet
              ++
            List.map Execution.selectionExecutableField
              (Execution.mergedFieldSelectionSet sourceFields) := by
          have hmapped :=
            congrArg (List.map Execution.selectionExecutableField)
              hsourceProjection
          simpa [Execution.mergedFieldSelectionSet, List.map_append]
            using hmapped.symm
        have hprojected :
            Execution.completeValue schema resolvers variableValues
                (depth - 1) fieldDefinition.outputType
                (List.map Execution.selectionExecutableField
                  (normalizeBoolCaseForType schema boolCase
                    fieldDefinition.outputType.namedType selectionSet
                  ++ mergeSelectionSets
                    (staticCollectCompleteScopedSelectionSet schema
                      (operationBoolVars operation) groundType boolCase
                      (staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest))))
                value
              =
            Execution.completeValue schema resolvers variableValues
                (depth - 1) fieldDefinition.outputType
                (List.map Execution.selectionExecutableField
                  (selectionSet
                  ++ mergeSelectionSets
                    (eraseCompleteScopedSelectionSet
                      (staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest))))
                value := by
          simpa [hresolved] using hprojectedComplete
        rw [hnormalizedProjectionMap, hsourceProjectionMap] at hprojected
        simpa [List.map_append] using hprojected
  exact
    executeSelectionSet_filterSelectionSetBoolCase_field_allowed_lookup_some_duplicate_group_case
      schema resolvers variableValues operation depth lookupParent groundType
      (Execution.ResolverValue.object (ObjectRef := ObjectRef) groundType ref) boolCase
      responseName fieldName
      arguments directives selectionSet rest fieldDefinition normalizedFields
      sourceFields normalizedTail sourceTail hallow hlookup
      (by
        simpa [] using hnormalizedCollect)
      (by
        simpa [] using hsourceCollect)
      hcomplete hfiltered

end CompleteNormalization

end NormalForm

end GraphQL
