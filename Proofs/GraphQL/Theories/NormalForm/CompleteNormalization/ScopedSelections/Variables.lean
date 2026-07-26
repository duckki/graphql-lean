import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.ScopedSelections.StaticFields

/-! Boolean-variable preservation for complete-normalization scoped selections. -/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name) (varName : BoolVar)
    : ∀ selectionSet,
        varName
          ∈ selectionSetBooleanVariables
              (eraseCompleteScopedSelectionSet
                (staticScopedFieldsWithResponseName schema boolCase lookupParent
                  groundType responseName selectionSet))
        -> varName ∈ selectionSetBooleanVariables selectionSet
  | [], hmem => by
      simp [staticScopedFieldsWithResponseName,
        eraseCompleteScopedSelectionSet, selectionSetBooleanVariables] at hmem
  | selection :: rest, hmem => by
      have hrest :=
        selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
          schema boolCase lookupParent groundType responseName varName rest
      cases selection with
      | field fieldResponseName fieldName arguments directives selectionSet =>
          cases hallow :
              directivesAllowIn boolCase directives
          · have hrestMem :
                varName ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName rest)) := by
                simpa [staticScopedFieldsWithResponseName, hallow] using hmem
            exact
              selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                varName
                (Selection.field fieldResponseName fieldName arguments
                  directives selectionSet)
                rest (hrest hrestMem)
          · cases hresponse : fieldResponseName == responseName
            · have hrestMem :
                  varName ∈ selectionSetBooleanVariables
                    (eraseCompleteScopedSelectionSet
                      (staticScopedFieldsWithResponseName schema boolCase
                        lookupParent groundType responseName rest)) := by
                  simpa [staticScopedFieldsWithResponseName, hallow,
                    hresponse] using hmem
              exact
                selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                  varName
                  (Selection.field fieldResponseName fieldName arguments
                    directives selectionSet)
                  rest (hrest hrestMem)
            · have hmem' :
                  varName ∈
                    selectionBooleanVariables
                        (Selection.field fieldResponseName fieldName arguments
                          directives selectionSet)
                      ++ selectionSetBooleanVariables
                        (eraseCompleteScopedSelectionSet
                          (staticScopedFieldsWithResponseName schema boolCase
                            lookupParent groundType responseName rest)) := by
                  simpa [staticScopedFieldsWithResponseName, hallow, hresponse,
                    eraseCompleteScopedSelectionSet,
                    eraseCompleteScopedSelection,
                    selectionSetBooleanVariables] using hmem
              rcases List.mem_append.mp hmem' with hhead | htail
              · exact
                  selectionBooleanVariables_mem_selectionSetBooleanVariables_head
                    varName
                    (Selection.field fieldResponseName fieldName arguments
                      directives selectionSet)
                    rest hhead
              · exact
                  selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                    varName
                    (Selection.field fieldResponseName fieldName arguments
                      directives selectionSet)
                    rest (hrest htail)
      | inlineFragment typeCondition directives selectionSet =>
          cases typeCondition with
          | none =>
              cases hallow :
                  directivesAllowIn boolCase directives
              · have hrestMem :
                    varName ∈ selectionSetBooleanVariables
                      (eraseCompleteScopedSelectionSet
                        (staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hallow] using hmem
                exact
                  selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                    varName
                    (Selection.inlineFragment none directives selectionSet)
                    rest (hrest hrestMem)
              · have hmem' :
                    varName ∈
                      selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              selectionSet))
                        ++ selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hallow,
                      eraseCompleteScopedSelectionSet_append,
                      selectionSetBooleanVariables_append] using hmem
                rcases List.mem_append.mp hmem' with hchild | htail
                · exact
                    childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_inline_head
                      varName none directives selectionSet rest
                      (selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
                        schema boolCase lookupParent groundType responseName
                        varName selectionSet hchild)
                · exact
                    selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                      varName
                      (Selection.inlineFragment none directives selectionSet)
                      rest (hrest htail)
          | some typeCondition =>
              cases hbranch :
                  directivesAllowIn boolCase directives
                    && schema.typeIncludesObjectBool typeCondition groundType
              · have hrestMem :
                    varName ∈ selectionSetBooleanVariables
                      (eraseCompleteScopedSelectionSet
                        (staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hbranch] using
                      hmem
                exact
                  selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                    varName
                    (Selection.inlineFragment (some typeCondition) directives
                      selectionSet)
                    rest (hrest hrestMem)
              · have hmem' :
                    varName ∈
                      selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase typeCondition groundType responseName
                              selectionSet))
                        ++ selectionSetBooleanVariables
                          (eraseCompleteScopedSelectionSet
                            (staticScopedFieldsWithResponseName schema
                              boolCase lookupParent groundType responseName
                              rest)) := by
                    simpa [staticScopedFieldsWithResponseName, hbranch,
                      eraseCompleteScopedSelectionSet_append,
                      selectionSetBooleanVariables_append] using hmem
                rcases List.mem_append.mp hmem' with hchild | htail
                · exact
                    childSelectionSetBooleanVariables_mem_selectionSetBooleanVariables_inline_head
                      varName (some typeCondition) directives selectionSet rest
                      (selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
                        schema boolCase typeCondition groundType responseName
                        varName selectionSet hchild)
                · exact
                    selectionSetBooleanVariables_mem_selectionSetBooleanVariables_tail
                      varName
                      (Selection.inlineFragment (some typeCondition) directives
                        selectionSet)
                      rest (hrest htail)

theorem sourceSelectionSetVariables_erase_staticScopedFieldsWithResponseName
    (operation : Operation) (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    (selectionSet : List Selection)
    : (∀ varName,
        varName ∈ selectionSetBooleanVariables selectionSet
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName
            ∈ selectionSetBooleanVariables
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase lookupParent
                    groundType responseName selectionSet))
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact hsourceVars varName
    (selectionSetBooleanVariables_erase_staticScopedFieldsWithResponseName_mem
      schema boolCase lookupParent groundType responseName varName
      selectionSet hmem)

theorem sourceSelectionSetVariables_merge_erase_staticScopedFieldsWithResponseName
    (operation : Operation) (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName : Name)
    (selectionSet : List Selection)
    : (∀ varName,
        varName ∈ selectionSetBooleanVariables selectionSet
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName
            ∈ selectionSetBooleanVariables
                (mergeSelectionSets
                  (eraseCompleteScopedSelectionSet
                    (staticScopedFieldsWithResponseName schema boolCase
                      lookupParent groundType responseName selectionSet)))
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  exact
    sourceSelectionSetVariables_erase_staticScopedFieldsWithResponseName
      operation schema boolCase lookupParent groundType responseName
      selectionSet hsourceVars varName
      (mergeSelectionSetsBooleanVariables_mem_selectionSetBooleanVariables
        varName
        (eraseCompleteScopedSelectionSet
          (staticScopedFieldsWithResponseName schema boolCase lookupParent
            groundType responseName selectionSet))
        hmem)

theorem sourceSelectionSetVariables_field_staticScoped_merged
    (operation : Operation)
    (schema : Schema) (boolCase : BoolCase)
    (lookupParent groundType responseName fieldName : Name)
    (arguments : List Argument) (directives : List DirectiveApplication)
    (selectionSet rest : List Selection)
    : (∀ varName,
        varName
          ∈ selectionSetBooleanVariables
              (Selection.field responseName fieldName arguments directives selectionSet
                :: rest)
        -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> ∀ varName,
          varName
            ∈ selectionSetBooleanVariables
                (selectionSet
                  ++ mergeSelectionSets
                      (eraseCompleteScopedSelectionSet
                        (staticScopedFieldsWithResponseName schema boolCase
                          lookupParent groundType responseName rest)))
          -> varName ∈ selectionSetBooleanVariables operation.selectionSet := by
  intro hsourceVars varName hmem
  have hmem' :
      varName ∈ selectionSetBooleanVariables selectionSet
        ∨ varName ∈ selectionSetBooleanVariables
          (mergeSelectionSets
            (eraseCompleteScopedSelectionSet
              (staticScopedFieldsWithResponseName schema boolCase
                lookupParent groundType responseName rest))) := by
    have happend :
        varName ∈
          selectionSetBooleanVariables selectionSet
            ++ selectionSetBooleanVariables
              (mergeSelectionSets
                (eraseCompleteScopedSelectionSet
                  (staticScopedFieldsWithResponseName schema boolCase
                    lookupParent groundType responseName rest))) := by
      simpa [selectionSetBooleanVariables_append] using hmem
    exact List.mem_append.mp happend
  rcases hmem' with hchild | htail
  · exact sourceSelectionSetVariables_field_child operation responseName
      fieldName arguments directives selectionSet rest hsourceVars varName
      hchild
  · exact
      sourceSelectionSetVariables_merge_erase_staticScopedFieldsWithResponseName
        operation schema boolCase lookupParent groundType responseName rest
        (sourceSelectionSetVariables_tail operation
          (Selection.field responseName fieldName arguments directives
            selectionSet)
          rest hsourceVars)
        varName htail

end CompleteNormalization

end NormalForm

end GraphQL
