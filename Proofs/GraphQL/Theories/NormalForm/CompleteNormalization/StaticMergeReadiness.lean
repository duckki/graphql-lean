import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ScopedStaticExecution
import Proofs.GraphQL.Theories.NormalForm.Shared.FieldMergeLookup

/-!
Merge-readiness and scoped field-head lookup facts for complete normalization.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem fieldsInSetCanMerge_inline_none_head_clear_directives
    (schema : Schema) (parentType : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType
        (Selection.inlineFragment none directives selectionSet :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.inlineFragment none [] selectionSet :: rest) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (Selection.inlineFragment none [] selectionSet :: rest) ?_
  dsimp
  intro left hleft right hright hresponse
  have liftMem :
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType
          (Selection.inlineFragment none [] selectionSet :: rest) ->
        scopedField ∈ FieldMerge.collectFields schema parentType
          (Selection.inlineFragment none directives selectionSet :: rest) := by
    intro scopedField hfield
    simpa [FieldMerge.collectFields] using hfield
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (liftMem left hleft) (liftMem right hright) hresponse

theorem fieldsInSetCanMerge_inline_some_head_clear_directives
    (schema : Schema) (parentType typeCondition : Name)
    (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : FieldMerge.fieldsInSetCanMerge schema parentType
        (Selection.inlineFragment (some typeCondition) directives selectionSet :: rest)
      -> FieldMerge.fieldsInSetCanMerge schema parentType
          (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest) := by
  intro hmerge
  unfold FieldMerge.fieldsInSetCanMerge
  refine FieldMerge.FieldsInSetCanMerge.intro parentType
    (Selection.inlineFragment (some typeCondition) [] selectionSet :: rest) ?_
  dsimp
  intro left hleft right hright hresponse
  have liftMem :
      ∀ scopedField,
        scopedField ∈ FieldMerge.collectFields schema parentType
          (Selection.inlineFragment (some typeCondition) [] selectionSet
            :: rest) ->
        scopedField ∈ FieldMerge.collectFields schema parentType
          (Selection.inlineFragment (some typeCondition) directives
            selectionSet :: rest) := by
    intro scopedField hfield
    simpa [FieldMerge.collectFields] using hfield
  exact FieldMerge.fieldsInSetCanMerge_pair hmerge
    (liftMem left hleft) (liftMem right hright) hresponse

theorem executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_field_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues)
    (operation : Operation)
    (hschema : SchemaWellFormedness.schemaWellFormed schema)
    (hfieldCase
      : ∀ depth execParent lookupParent groundType
            boolCase
            responseName fieldName arguments directives selectionSet
            (rest : List CompleteScopedSelection),
          schema.objectType execParent
          -> schema.typeIncludesObjectBool execParent groundType = true
          -> completeScopedSelectionSetSemanticsReady schema execParent
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
                }
                :: rest)
          -> completeScopedSelectionSetLookupValid schema
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
                }
                :: rest)
          -> completeScopedSelectionSetCanMerge schema execParent
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
                }
                :: rest)
          -> completeScopedSelectionSetGroundApplies schema groundType
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
                }
                :: rest)
          -> variableValuesAgreeWithCase variableValues boolCase
              (operationBoolVars operation)
          -> (∀ varName,
                varName
                  ∈ selectionSetBooleanVariables
                      (eraseCompleteScopedSelectionSet
                        ({
                            lookupParent := lookupParent,
                            selection :=
                              Selection.field responseName fieldName arguments
                                directives selectionSet
                          }
                          :: rest))
                -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
          -> directivesAllowIn boolCase directives = true
          -> Execution.executeSelectionSet schema resolvers variableValues depth
                execParent (.object groundType ())
                (staticCollectCompleteScopedSelectionSet schema
                  (operationBoolVars operation)
                  groundType boolCase
                  ({
                      lookupParent := lookupParent,
                      selection :=
                        Selection.field responseName fieldName arguments
                          directives selectionSet
                    }
                    :: rest))
              = Execution.executeSelectionSet schema resolvers variableValues depth
                  execParent (.object groundType ())
                  (eraseCompleteScopedSelectionSet
                    ({
                        lookupParent := lookupParent,
                        selection :=
                          Selection.field responseName fieldName arguments directives
                            selectionSet
                      }
                      :: rest)))
    : ∀ depth execParent groundType boolCase scopedSelections,
        schema.objectType execParent
        -> schema.typeIncludesObjectBool execParent groundType = true
        -> completeScopedSelectionSetSemanticsReady schema execParent scopedSelections
        -> completeScopedSelectionSetLookupValid schema scopedSelections
        -> completeScopedSelectionSetCanMerge schema execParent scopedSelections
        -> completeScopedSelectionSetGroundApplies schema groundType scopedSelections
        -> variableValuesAgreeWithCase variableValues boolCase
            (operationBoolVars operation)
        -> (∀ varName,
              varName
                ∈ selectionSetBooleanVariables
                    (eraseCompleteScopedSelectionSet scopedSelections)
              -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
        -> Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (staticCollectCompleteScopedSelectionSet schema
                (operationBoolVars operation)
                groundType boolCase scopedSelections)
            = Execution.executeSelectionSet schema resolvers variableValues depth
                execParent (.object groundType ())
                (eraseCompleteScopedSelectionSet scopedSelections)
  | depth, execParent, groundType, boolCase, [], _hobject,
    _hground, _hready, _hlookup, _hmerge, _happlies, _hagrees,
    _hsourceVars => by
      simp [staticCollectCompleteScopedSelectionSet,
        eraseCompleteScopedSelectionSet, Execution.executeSelectionSet]
  | depth, execParent, groundType, boolCase,
      scopedSelection :: rest, hobject, hground, hready, hlookup, hmerge,
      happlies, hagrees, hsourceVars => by
      cases scopedSelection with
      | mk lookupParent selection =>
          cases selection with
          | field responseName fieldName arguments directives selectionSet =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · apply
                  executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_skipped_execution_case
                    schema resolvers variableValues operation depth execParent
                    lookupParent groundType boolCase responseName
                    fieldName arguments directives selectionSet rest hagrees
                    hsourceVars hallow
                exact
                  executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_field_case
                    schema resolvers variableValues operation hschema
                    hfieldCase depth execParent groundType boolCase
                    rest hobject hground
                    (completeScopedSelectionSetSemanticsReady_tail hready)
                    (completeScopedSelectionSetLookupValid_tail hlookup)
                    (completeScopedSelectionSetCanMerge_tail schema
                      execParent
                      { lookupParent := lookupParent,
                        selection :=
                          Selection.field responseName fieldName arguments
                            directives selectionSet }
                      rest hmerge)
                    (completeScopedSelectionSetGroundApplies_tail happlies)
                    hagrees
                    (by
                      intro varName hmem
                      exact hsourceVars varName
                        (by
                          simp [eraseCompleteScopedSelectionSet,
                            eraseCompleteScopedSelection,
                            selectionSetBooleanVariables, hmem]))
              · exact
                  hfieldCase depth execParent lookupParent groundType
                    boolCase responseName fieldName arguments directives
                    selectionSet rest hobject hground hready hlookup hmerge
                    happlies hagrees hsourceVars hallow
          | inlineFragment typeCondition directives selectionSet =>
              cases typeCondition with
              | none =>
                  cases hallow :
                      directivesAllowIn boolCase directives
                  · apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_none_skipped_execution_case
                        schema resolvers variableValues operation depth
                        execParent lookupParent groundType boolCase
                        directives selectionSet rest hagrees hsourceVars hallow
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_field_case
                        schema resolvers variableValues operation hschema
                        hfieldCase depth execParent groundType
                        boolCase rest hobject hground
                        (completeScopedSelectionSetSemanticsReady_tail hready)
                        (completeScopedSelectionSetLookupValid_tail hlookup)
                        (completeScopedSelectionSetCanMerge_tail schema
                          execParent
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.inlineFragment none directives
                                selectionSet }
                          rest hmerge)
                        (completeScopedSelectionSetGroundApplies_tail happlies)
                        hagrees
                        (by
                          intro varName hmem
                          exact hsourceVars varName
                            (by
                              simp [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection,
                                selectionSetBooleanVariables, hmem]))
                  · apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_none_allowed_flatten_case
                        schema resolvers variableValues operation depth
                        execParent lookupParent groundType boolCase
                        directives selectionSet rest hagrees hsourceVars hallow
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_field_case
                        schema resolvers variableValues operation hschema
                        hfieldCase depth execParent groundType
                        boolCase
                        (completeScopedSelectionSet lookupParent selectionSet
                          ++ rest)
                        hobject hground
                        (completeScopedSelectionSetSemanticsReady_append
                          ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
                            schema execParent lookupParent selectionSet).mpr
                            (by
                              have hheadReady :
                                  selectionSemanticsReady
                                    schema execParent
                                    (Selection.inlineFragment none directives
                                      selectionSet) := by
                                unfold completeScopedSelectionSetSemanticsReady at hready
                                unfold selectionSetSemanticsReady at hready
                                exact hready _ (by
                                  simp [eraseCompleteScopedSelectionSet,
                                    eraseCompleteScopedSelection])
                              simpa [selectionSemanticsReady] using
                                hheadReady))
                          (completeScopedSelectionSetSemanticsReady_tail hready))
                        (completeScopedSelectionSetLookupValid_append
                          ((completeScopedSelectionSetLookupValid_completeScopedSelectionSet
                            schema lookupParent selectionSet).mpr
                            (by
                              have hheadLookup :
                                  selectionLookupValid
                                    schema lookupParent
                                    (Selection.inlineFragment none directives
                                      selectionSet) :=
                                hlookup
                                  { lookupParent := lookupParent,
                                    selection :=
                                      Selection.inlineFragment none directives
                                        selectionSet }
                                  (by simp)
                              simpa [selectionLookupValid] using hheadLookup))
                          (completeScopedSelectionSetLookupValid_tail hlookup))
                        (by
                          have hmergeNoDirectives :
                              FieldMerge.fieldsInSetCanMerge schema execParent
                                (Selection.inlineFragment none [] selectionSet
                                  :: eraseCompleteScopedSelectionSet rest) :=
                            fieldsInSetCanMerge_inline_none_head_clear_directives
                              schema execParent directives selectionSet
                              (eraseCompleteScopedSelectionSet rest)
                              (by
                                simpa [completeScopedSelectionSetCanMerge,
                                  eraseCompleteScopedSelectionSet,
                                  eraseCompleteScopedSelection] using hmerge)
                          simpa [completeScopedSelectionSetCanMerge,
                            eraseCompleteScopedSelectionSet_append,
                            eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
                            fieldsInSetCanMerge_inlineFragment_none_flatten
                              schema execParent selectionSet
                              (eraseCompleteScopedSelectionSet rest)
                              hmergeNoDirectives)
                        (completeScopedSelectionSetGroundApplies_append
                          (by
                            intro scopedSelection hmem
                            have hparent :=
                              completeScopedSelectionSet_lookupParent_eq hmem
                            rw [hparent]
                            exact happlies
                              { lookupParent := lookupParent,
                                selection :=
                                  Selection.inlineFragment none directives
                                    selectionSet }
                              (by simp))
                          (completeScopedSelectionSetGroundApplies_tail
                            happlies))
                        hagrees
                        (by
                          intro varName hmem
                          have hmemRaw :
                              varName ∈ selectionSetBooleanVariables
                                (selectionSet
                                  ++ eraseCompleteScopedSelectionSet rest) := by
                            simpa [eraseCompleteScopedSelectionSet_append,
                              eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
                              using hmem
                          have hsourceVarsRaw :
                              ∀ varName,
                                varName ∈ selectionSetBooleanVariables
                                  (Selection.inlineFragment none directives
                                      selectionSet
                                    :: eraseCompleteScopedSelectionSet rest) ->
                                varName ∈
                                  selectionSetBooleanVariables
                                    operation.selectionSet := by
                            intro candidate hcandidate
                            exact hsourceVars candidate
                              (by simpa [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection] using hcandidate)
                          rcases
                              List.mem_append.mp
                                (by
                                  simpa [selectionSetBooleanVariables_append]
                                    using hmemRaw) with hchild | htail
                          · exact
                              sourceSelectionSetVariables_inline_child
                                operation none directives selectionSet
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName hchild
                          · exact
                              sourceSelectionSetVariables_tail operation
                                (Selection.inlineFragment none directives
                                  selectionSet)
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName htail)
              | some typeCondition =>
                  cases hbranch :
                      directivesAllowIn boolCase directives
                        && schema.typeIncludesObjectBool typeCondition
                          groundType
                  · apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_some_skipped_execution_case
                        schema resolvers variableValues operation depth
                        execParent lookupParent groundType typeCondition
                        boolCase directives selectionSet rest
                        hagrees hsourceVars hbranch
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_field_case
                        schema resolvers variableValues operation hschema
                        hfieldCase depth execParent groundType
                        boolCase rest hobject hground
                        (completeScopedSelectionSetSemanticsReady_tail hready)
                        (completeScopedSelectionSetLookupValid_tail hlookup)
                        (completeScopedSelectionSetCanMerge_tail schema
                          execParent
                          { lookupParent := lookupParent,
                            selection :=
                              Selection.inlineFragment (some typeCondition)
                                directives selectionSet }
                          rest hmerge)
                        (completeScopedSelectionSetGroundApplies_tail happlies)
                        hagrees
                        (by
                          intro varName hmem
                          exact hsourceVars varName
                            (by
                              simp [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection,
                                selectionSetBooleanVariables, hmem]))
                  · have hallow :
                        directivesAllowIn boolCase
                            directives =
                          true := by
                      cases hallow' :
                          directivesAllowIn boolCase
                            directives
                      · simp [hallow'] at hbranch
                      · rfl
                    have hincludes :
                        schema.typeIncludesObjectBool typeCondition
                            groundType =
                          true := by
                      cases hincludes' :
                          schema.typeIncludesObjectBool typeCondition
                            groundType
                      · simp [hallow, hincludes'] at hbranch
                      · rfl
                    apply
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_some_allowed_flatten_case
                        schema resolvers variableValues operation depth
                        execParent lookupParent groundType typeCondition
                        boolCase directives selectionSet rest
                        hagrees hsourceVars hallow hincludes
                    have hobjectBool :
                        objectTypeNameBool schema execParent = true :=
                      GroundTypeNormalization.objectTypeNameBool_eq_true_of_objectType
                        schema hobject
                    have happly :
                        Execution.doesFragmentTypeApplyBool schema execParent
                            (Execution.ResolverValue.object (ObjectRef := PUnit)
                              groundType ()) typeCondition =
                          true := by
                      simpa [Execution.doesFragmentTypeApplyBool,
                        Execution.runtimeObjectType?] using hincludes
                    have hsource :
                        ∃ runtimeType ref,
                          (Execution.ResolverValue.object (ObjectRef := PUnit)
                              groundType () :
                              Execution.ResolverValue PUnit)
                            = .object runtimeType ref
                            ∧ schema.typeIncludesObjectBool execParent
                              runtimeType = true :=
                      ⟨groundType, (), rfl, hground⟩
                    have hoverlap :
                        schema.typesOverlapBool execParent typeCondition =
                          true := by
                      rw [← GroundTypeNormalization.doesFragmentTypeApplyBool_eq_typesOverlapBool_of_object_parent_source
                        schema hobjectBool hsource]
                      exact happly
                    exact
                      executeSelectionSet_staticCollectCompleteScopedSelectionSet_of_field_case
                        schema resolvers variableValues operation hschema
                        hfieldCase depth execParent groundType
                        boolCase
                        (completeScopedSelectionSet typeCondition selectionSet
                          ++ rest)
                        hobject hground
                        (completeScopedSelectionSetSemanticsReady_append
                          ((completeScopedSelectionSetSemanticsReady_completeScopedSelectionSet
                            schema execParent typeCondition selectionSet).mpr
                            (by
                              have hheadReady :
                                  selectionSemanticsReady
                                    schema execParent
                                    (Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet) := by
                                unfold completeScopedSelectionSetSemanticsReady at hready
                                unfold selectionSetSemanticsReady at hready
                                exact hready _ (by
                                  simp [eraseCompleteScopedSelectionSet,
                                    eraseCompleteScopedSelection])
                              have hpair :
                                  selectionSetLookupValid
                                    schema typeCondition
                                      selectionSet
                                    ∧
                                  (schema.typesOverlapBool execParent
                                      typeCondition = true ->
                                    selectionSetSemanticsReady
                                      schema
                                      execParent selectionSet) := by
                                simpa [selectionSemanticsReady] using
                                  hheadReady
                              exact hpair.2 hoverlap))
                          (completeScopedSelectionSetSemanticsReady_tail hready))
                        (completeScopedSelectionSetLookupValid_append
                          ((completeScopedSelectionSetLookupValid_completeScopedSelectionSet
                            schema typeCondition selectionSet).mpr
                            (by
                              have hheadLookup :
                                  selectionLookupValid
                                    schema lookupParent
                                    (Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet) :=
                                hlookup
                                  { lookupParent := lookupParent,
                                    selection :=
                                      Selection.inlineFragment
                                        (some typeCondition) directives
                                        selectionSet }
                                  (by simp)
                              simpa [selectionLookupValid] using hheadLookup))
                          (completeScopedSelectionSetLookupValid_tail hlookup))
                        (by
                          have hselectionParentLookup :
                              selectionSetLookupValid
                                schema execParent
                                selectionSet :=
                            selectionSetLookupValid_of_selectionSetSemanticsReady
                              selectionSet
                              (by
                                have hheadReady :
                                    selectionSemanticsReady
                                      schema execParent
                                      (Selection.inlineFragment
                                        (some typeCondition) directives
                                        selectionSet) := by
                                  unfold completeScopedSelectionSetSemanticsReady at hready
                                  unfold selectionSetSemanticsReady at hready
                                  exact hready _ (by
                                    simp [eraseCompleteScopedSelectionSet,
                                      eraseCompleteScopedSelection])
                                have hpair :
                                    selectionSetLookupValid
                                      schema typeCondition
                                        selectionSet
                                      ∧
                                    (schema.typesOverlapBool execParent
                                        typeCondition = true ->
                                      selectionSetSemanticsReady
                                        schema
                                        execParent selectionSet) := by
                                  simpa [selectionSemanticsReady] using
                                    hheadReady
                                exact hpair.2 hoverlap)
                          have hselectionTypeLookup :
                              selectionSetLookupValid
                                schema typeCondition
                                selectionSet := by
                            have hheadLookup :
                                selectionLookupValid
                                  schema lookupParent
                                  (Selection.inlineFragment
                                    (some typeCondition) directives
                                    selectionSet) :=
                              hlookup
                                { lookupParent := lookupParent,
                                  selection :=
                                    Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet }
                                (by simp)
                            simpa [selectionLookupValid] using hheadLookup
                          have htailLookup :
                              selectionSetLookupValid
                                schema execParent
                                (eraseCompleteScopedSelectionSet rest) :=
                            selectionSetLookupValid_of_selectionSetSemanticsReady
                              (eraseCompleteScopedSelectionSet rest)
                              (completeScopedSelectionSetSemanticsReady_tail
                                hready)
                          have hmergeNoDirectives :
                              FieldMerge.fieldsInSetCanMerge schema execParent
                                (Selection.inlineFragment
                                    (some typeCondition) [] selectionSet
                                  :: eraseCompleteScopedSelectionSet rest) :=
                            fieldsInSetCanMerge_inline_some_head_clear_directives
                              schema execParent typeCondition directives
                              selectionSet
                              (eraseCompleteScopedSelectionSet rest)
                              (by
                                simpa [completeScopedSelectionSetCanMerge,
                                  eraseCompleteScopedSelectionSet,
                                  eraseCompleteScopedSelection] using hmerge)
                          simpa [completeScopedSelectionSetCanMerge,
                            eraseCompleteScopedSelectionSet_append,
                            eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
                            fieldsInSetCanMerge_inlineFragment_some_overlap_flatten_object
                              schema execParent typeCondition selectionSet
                              (eraseCompleteScopedSelectionSet rest) hschema
                              hobject hoverlap hselectionParentLookup
                              hselectionTypeLookup htailLookup
                              hmergeNoDirectives)
                        (completeScopedSelectionSetGroundApplies_append
                          (by
                            intro scopedSelection hmem
                            have hparent :=
                              completeScopedSelectionSet_lookupParent_eq hmem
                            rw [hparent]
                            exact hincludes)
                          (completeScopedSelectionSetGroundApplies_tail
                            happlies))
                        hagrees
                        (by
                          intro varName hmem
                          have hmemRaw :
                              varName ∈ selectionSetBooleanVariables
                                (selectionSet
                                  ++ eraseCompleteScopedSelectionSet rest) := by
                            simpa [eraseCompleteScopedSelectionSet_append,
                              eraseCompleteScopedSelectionSet_completeScopedSelectionSet]
                              using hmem
                          have hsourceVarsRaw :
                              ∀ varName,
                                varName ∈ selectionSetBooleanVariables
                                  (Selection.inlineFragment
                                      (some typeCondition) directives
                                      selectionSet
                                    :: eraseCompleteScopedSelectionSet rest) ->
                                varName ∈
                                  selectionSetBooleanVariables
                                    operation.selectionSet := by
                            intro candidate hcandidate
                            exact hsourceVars candidate
                              (by simpa [eraseCompleteScopedSelectionSet,
                                eraseCompleteScopedSelection] using hcandidate)
                          rcases
                              List.mem_append.mp
                                (by
                                  simpa [selectionSetBooleanVariables_append]
                                    using hmemRaw) with hchild | htail
                          · exact
                              sourceSelectionSetVariables_inline_child
                                operation (some typeCondition) directives
                                selectionSet
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName hchild
                          · exact
                              sourceSelectionSetVariables_tail operation
                                (Selection.inlineFragment
                                  (some typeCondition) directives selectionSet)
                                (eraseCompleteScopedSelectionSet rest)
                                hsourceVarsRaw varName htail)
termination_by _depth _execParent _groundType _boolCase scopedSelections =>
  SelectionSet.size (eraseCompleteScopedSelectionSet scopedSelections)
decreasing_by
  all_goals
    try subst_vars
    try
      exact
        eraseCompleteScopedSelectionSet_tail_size_lt
          { lookupParent := lookupParent,
            selection :=
              Selection.field responseName fieldName arguments directives
                selectionSet }
          rest
    try
      exact
        eraseCompleteScopedSelectionSet_tail_size_lt
          { lookupParent := lookupParent,
            selection :=
              Selection.inlineFragment none directives selectionSet }
          rest
    try
      exact
        eraseCompleteScopedSelectionSet_tail_size_lt
          { lookupParent := lookupParent,
            selection :=
              Selection.inlineFragment (some typeCondition) directives
                selectionSet }
          rest
    try
      exact
        eraseCompleteScopedSelectionSet_inlineFragment_none_flatten_size_lt
          lookupParent selectionSet rest
    try
      exact
        eraseCompleteScopedSelectionSet_inlineFragment_some_flatten_size_lt
          lookupParent typeCondition selectionSet rest

theorem completeScopedFieldHead_lookupPair_of_semanticsReady_lookupValid
    (schema : Schema)
    (execParent lookupParent responseName fieldName : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
    (rest : List CompleteScopedSelection)
    : completeScopedSelectionSetSemanticsReady schema execParent
        ({
            lookupParent := lookupParent,
            selection :=
              Selection.field responseName fieldName arguments directives selectionSet
          }
          :: rest)
      -> completeScopedSelectionSetLookupValid schema
          ({
              lookupParent := lookupParent,
              selection :=
                Selection.field responseName fieldName arguments directives selectionSet
            }
            :: rest)
      -> ∃ execFieldDefinition lookupFieldDefinition,
          schema.lookupField execParent fieldName = some execFieldDefinition
          ∧ schema.lookupField lookupParent fieldName = some lookupFieldDefinition := by
  intro hready hlookup
  have hheadReady :
      selectionSemanticsReady schema execParent
        (Selection.field responseName fieldName arguments directives
          selectionSet) := by
    unfold completeScopedSelectionSetSemanticsReady at hready
    unfold selectionSetSemanticsReady at hready
    exact hready
      (Selection.field responseName fieldName arguments directives
        selectionSet)
      (by simp [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelection])
  rcases
      (by
        simpa [selectionSemanticsReady] using
          hheadReady) with
    ⟨execFieldDefinition, hexecLookup, _hchildReady⟩
  have hheadLookup :
      selectionLookupValid schema lookupParent
        (Selection.field responseName fieldName arguments directives
          selectionSet) :=
    hlookup
      { lookupParent := lookupParent,
        selection :=
          Selection.field responseName fieldName arguments directives
            selectionSet }
      (by simp)
  rcases
      (by
        simpa [selectionLookupValid] using
          hheadLookup) with
    ⟨lookupFieldDefinition, hlookupField⟩
  exact ⟨execFieldDefinition, lookupFieldDefinition, hexecLookup,
    hlookupField⟩

end CompleteNormalization

end NormalForm

end GraphQL
