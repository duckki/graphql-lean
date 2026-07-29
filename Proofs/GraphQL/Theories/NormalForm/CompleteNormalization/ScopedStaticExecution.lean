import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.StaticCollectionExecution

/-!
Scoped static-collection field and inline-fragment execution cases.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

theorem
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_none_skipped_execution_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (execParent lookupParent groundType : Name) (boolCase : BoolCase)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    ({
                        lookupParent := lookupParent,
                        selection :=
                          Selection.inlineFragment none directives selectionSet
                      }
                      :: rest))
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.inlineFragment none directives selectionSet
                }
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet
                ({
                    lookupParent := lookupParent,
                    selection :=
                      Selection.inlineFragment none directives selectionSet
                  }
                  :: rest)) := by
  intro hagrees hsourceVars hskip hrest
  have hsourceVarsRaw :
      ∀ varName,
        varName ∈ selectionSetBooleanVariables
          (Selection.inlineFragment none directives selectionSet
            :: eraseCompleteScopedSelectionSet rest) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
    intro varName hmem
    exact hsourceVars varName
      (by simpa [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelection] using hmem)
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation none directives selectionSet
      (eraseCompleteScopedSelectionSet rest) hagrees hsourceVarsRaw
  have hexecSkip :
      Execution.selectionDirectivesAllowBool variableValues directives =
        false := by
    rw [← hdirectiveEq]
    exact hskip
  rw [staticCollectCompleteScopedSelectionSet,
    staticCollectCompleteScopedSelection,
    staticCollectForGround_inline_none_skipped schema
      (operationBoolVars operation) lookupParent groundType
      boolCase directives selectionSet [] hskip]
  simp [staticCollectForGround]
  exact hrest.trans
    (executeSelectionSet_inlineFragment_none_directives_skipped_eq schema
      resolvers variableValues depth execParent (.object groundType ())
      directives selectionSet (eraseCompleteScopedSelectionSet rest)
      hexecSkip).symm

theorem
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_field_skipped_execution_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (execParent lookupParent groundType : Name) (boolCase : BoolCase)
    (responseName fieldName : Name) (arguments : List Argument)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection)
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
      -> directivesAllowIn boolCase directives = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.field responseName fieldName arguments directives
                      selectionSet
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
                  :: rest)) := by
  intro hagrees hsourceVars hskip hrest
  have hsourceVarsRaw :
      ∀ varName,
        varName ∈ selectionSetBooleanVariables
          (Selection.field responseName fieldName arguments directives
              selectionSet
            :: eraseCompleteScopedSelectionSet rest) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
    intro varName hmem
    exact hsourceVars varName
      (by simpa [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelection] using hmem)
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_field_head
      variableValues boolCase operation responseName fieldName arguments
      directives selectionSet (eraseCompleteScopedSelectionSet rest)
      hagrees hsourceVarsRaw
  have hexecSkip :
      Execution.selectionDirectivesAllowBool variableValues directives =
        false := by
    rw [← hdirectiveEq]
    exact hskip
  rw [staticCollectCompleteScopedSelectionSet,
    staticCollectCompleteScopedSelection,
    staticCollectForGround_field_skipped schema
      (operationBoolVars operation) lookupParent groundType
      responseName fieldName boolCase arguments directives selectionSet []
      hskip]
  simp [staticCollectForGround]
  exact hrest.trans
    (executeSelectionSet_field_directives_skipped_eq schema resolvers
      variableValues depth execParent (.object groundType ())
      responseName fieldName arguments directives selectionSet
      (eraseCompleteScopedSelectionSet rest) hexecSkip).symm

theorem
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_none_allowed_flatten_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (execParent lookupParent groundType : Name) (boolCase : BoolCase)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    ({
                        lookupParent := lookupParent,
                        selection :=
                          Selection.inlineFragment none directives selectionSet
                      }
                      :: rest))
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              (completeScopedSelectionSet lookupParent selectionSet ++ rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet
                (completeScopedSelectionSet lookupParent selectionSet ++ rest))
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.inlineFragment none directives selectionSet
                }
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet
                ({
                    lookupParent := lookupParent,
                    selection :=
                      Selection.inlineFragment none directives selectionSet
                  }
                  :: rest)) := by
  intro hagrees hsourceVars hallow hflatten
  have hsourceVarsRaw :
      ∀ varName,
        varName ∈ selectionSetBooleanVariables
          (Selection.inlineFragment none directives selectionSet
            :: eraseCompleteScopedSelectionSet rest) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
    intro varName hmem
    exact hsourceVars varName
      (by simpa [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelection] using hmem)
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation none directives selectionSet
      (eraseCompleteScopedSelectionSet rest) hagrees hsourceVarsRaw
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  have hnormalizedFlatten :
      staticCollectForGround schema
          (operationBoolVars operation) lookupParent
          groundType boolCase selectionSet
        ++
        staticCollectCompleteScopedSelectionSet schema
          (operationBoolVars operation) groundType
          boolCase rest
        =
      staticCollectCompleteScopedSelectionSet schema
        (operationBoolVars operation) groundType
        boolCase
        (completeScopedSelectionSet lookupParent selectionSet ++ rest) := by
    rw [staticCollectCompleteScopedSelectionSet_append,
      staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet]
  rw [staticCollectCompleteScopedSelectionSet,
    staticCollectCompleteScopedSelection,
    staticCollectForGround_inline_none_allowed schema
      (operationBoolVars operation) lookupParent groundType
      boolCase directives selectionSet [] hallow]
  simp [staticCollectForGround]
  rw [hnormalizedFlatten]
  have hflattenSource :
      Execution.executeSelectionSet schema resolvers variableValues depth
          execParent (.object groundType ())
          (staticCollectCompleteScopedSelectionSet schema
            (operationBoolVars operation) groundType
            boolCase
            (completeScopedSelectionSet lookupParent selectionSet ++ rest))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        execParent (.object groundType ())
        (selectionSet ++ eraseCompleteScopedSelectionSet rest) := by
    simpa [eraseCompleteScopedSelectionSet_append,
      eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
      hflatten
  exact
    hflattenSource.trans
      (executeSelectionSet_inlineFragment_none_directives_allowed_flatten
        schema resolvers variableValues depth execParent
        (.object groundType ()) directives selectionSet
        (eraseCompleteScopedSelectionSet rest) hexecAllow).symm

theorem
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_some_skipped_execution_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (execParent lookupParent groundType typeCondition : Name) (boolCase : BoolCase)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    ({
                        lookupParent := lookupParent,
                        selection :=
                          Selection.inlineFragment (some typeCondition) directives
                            selectionSet
                      }
                      :: rest))
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> (directivesAllowIn boolCase directives
            && schema.typeIncludesObjectBool typeCondition groundType)
          = false
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase rest)
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet rest)
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.inlineFragment (some typeCondition) directives selectionSet
                }
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet
                ({
                    lookupParent := lookupParent,
                    selection :=
                      Selection.inlineFragment (some typeCondition) directives
                        selectionSet
                  }
                  :: rest)) := by
  intro hagrees hsourceVars hskip hrest
  have hsourceVarsRaw :
      ∀ varName,
        varName ∈ selectionSetBooleanVariables
          (Selection.inlineFragment (some typeCondition) directives
              selectionSet
            :: eraseCompleteScopedSelectionSet rest) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
    intro varName hmem
    exact hsourceVars varName
      (by simpa [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelection] using hmem)
  have hbranchEq :=
    inlineSomeBranchAllowInCase_eq_execution_of_inline_head schema
      variableValues boolCase operation groundType typeCondition directives
      selectionSet (eraseCompleteScopedSelectionSet rest) hagrees
      hsourceVarsRaw
  have hexecSkip :
      (Execution.selectionDirectivesAllowBool variableValues directives
        && schema.typeIncludesObjectBool typeCondition groundType) = false := by
    rw [← hbranchEq]
    exact hskip
  rw [staticCollectCompleteScopedSelectionSet,
    staticCollectCompleteScopedSelection,
    staticCollectForGround_inline_some_skipped schema
      (operationBoolVars operation) lookupParent groundType
      typeCondition boolCase directives selectionSet [] hskip]
  simp [staticCollectForGround]
  exact hrest.trans
    (executeSelectionSet_inlineFragment_some_directives_skipped_eq_object
      schema resolvers variableValues depth execParent groundType
      typeCondition () directives selectionSet
      (eraseCompleteScopedSelectionSet rest) hexecSkip).symm

theorem
    executeSelectionSet_staticCollectCompleteScopedSelectionSet_inline_some_allowed_flatten_case
    (schema : Schema) (resolvers : Execution.Resolvers)
    (variableValues : Execution.VariableValues) (operation : Operation) (depth : Nat)
    (execParent lookupParent groundType typeCondition : Name) (boolCase : BoolCase)
    (directives : List DirectiveApplication) (selectionSet : List Selection)
    (rest : List CompleteScopedSelection)
    : variableValuesAgreeWithCase variableValues boolCase (operationBoolVars operation)
      -> (∀ varName,
            varName
              ∈ selectionSetBooleanVariables
                  (eraseCompleteScopedSelectionSet
                    ({
                        lookupParent := lookupParent,
                        selection :=
                          Selection.inlineFragment (some typeCondition) directives
                            selectionSet
                      }
                      :: rest))
            -> varName ∈ selectionSetBooleanVariables operation.selectionSet)
      -> directivesAllowIn boolCase directives = true
      -> schema.typeIncludesObjectBool typeCondition groundType = true
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              (completeScopedSelectionSet typeCondition selectionSet ++ rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet
                (completeScopedSelectionSet typeCondition selectionSet ++ rest))
      -> Execution.executeSelectionSet schema resolvers variableValues depth
            execParent (.object groundType ())
            (staticCollectCompleteScopedSelectionSet schema
              (operationBoolVars operation) groundType
              boolCase
              ({
                  lookupParent := lookupParent,
                  selection :=
                    Selection.inlineFragment (some typeCondition) directives selectionSet
                }
                :: rest))
          = Execution.executeSelectionSet schema resolvers variableValues depth
              execParent (.object groundType ())
              (eraseCompleteScopedSelectionSet
                ({
                    lookupParent := lookupParent,
                    selection :=
                      Selection.inlineFragment (some typeCondition) directives
                        selectionSet
                  }
                  :: rest)) := by
  intro hagrees hsourceVars hallow hincludes hflatten
  have hsourceVarsRaw :
      ∀ varName,
        varName ∈ selectionSetBooleanVariables
          (Selection.inlineFragment (some typeCondition) directives
              selectionSet
            :: eraseCompleteScopedSelectionSet rest) ->
        varName ∈ selectionSetBooleanVariables operation.selectionSet := by
    intro varName hmem
    exact hsourceVars varName
      (by simpa [eraseCompleteScopedSelectionSet,
        eraseCompleteScopedSelection] using hmem)
  have hdirectiveEq :=
    directivesAllowInCase_eq_execution_of_inline_head
      variableValues boolCase operation (some typeCondition) directives
      selectionSet (eraseCompleteScopedSelectionSet rest) hagrees
      hsourceVarsRaw
  have hexecAllow :
      Execution.selectionDirectivesAllowBool variableValues directives =
        true := by
    rw [← hdirectiveEq]
    exact hallow
  have hnormalizedFlatten :
      staticCollectForGround schema
          (operationBoolVars operation) typeCondition
          groundType boolCase selectionSet
        ++
        staticCollectCompleteScopedSelectionSet schema
          (operationBoolVars operation) groundType
          boolCase rest
        =
      staticCollectCompleteScopedSelectionSet schema
        (operationBoolVars operation) groundType
        boolCase
        (completeScopedSelectionSet typeCondition selectionSet ++ rest) := by
    rw [staticCollectCompleteScopedSelectionSet_append,
      staticCollectCompleteScopedSelectionSet_completeScopedSelectionSet]
  rw [staticCollectCompleteScopedSelectionSet,
    staticCollectCompleteScopedSelection,
    staticCollectForGround_inline_some_allowed schema
      (operationBoolVars operation) lookupParent groundType
      typeCondition boolCase directives selectionSet [] hallow hincludes]
  simp [staticCollectForGround]
  rw [hnormalizedFlatten]
  have hflattenSource :
      Execution.executeSelectionSet schema resolvers variableValues depth
          execParent (.object groundType ())
          (staticCollectCompleteScopedSelectionSet schema
            (operationBoolVars operation) groundType
            boolCase
            (completeScopedSelectionSet typeCondition selectionSet ++ rest))
        =
      Execution.executeSelectionSet schema resolvers variableValues depth
        execParent (.object groundType ())
        (selectionSet ++ eraseCompleteScopedSelectionSet rest) := by
    simpa [eraseCompleteScopedSelectionSet_append,
      eraseCompleteScopedSelectionSet_completeScopedSelectionSet] using
      hflatten
  exact
    hflattenSource.trans
      (executeSelectionSet_inlineFragment_some_directives_allowed_flatten_object
        schema resolvers variableValues depth execParent groundType
        typeCondition () directives selectionSet
        (eraseCompleteScopedSelectionSet rest) hexecAllow hincludes).symm

end CompleteNormalization

end NormalForm

end GraphQL
